// =============================================================================
// proxy_checker v9.3.0
// =============================================================================
//
// Batch proxy validator: concurrent SOCKS5/SOCKS4/HTTP checking, block-level
// ranking, realtime dashboard. Pure Rust std — no external crates.
//
// FEATURES (v9.3.0)
//   Protocols : SOCKS5 (auth), SOCKS4/4a, HTTP CONNECT (Basic auth)
//               auto port->protocol: 1080=SOCKS5, 80/8080=HTTP, else SOCKS5
//   Pipeline  : N fast threads + M detailed threads + dispatcher
//   Block lvl : L1 google -> L2 github -> L3 steamcommunity -> L4 voatiengviet
//   Dashboard : 30x{27+2N} frame, 100ms tick, 6s safety reload, realtime TTFB
//   Terminal  : ANSI (Unix/Win10+VT) / Win32 no-color (Win7/8/2012) / Simple
//   Interactive: prompts for input/timeout/threads/users/passwords on TTY
//   Auth expand: -u/-p generate (user,pass) combos for proxies without inline auth
//   Filters   : --sort speed|level  --min-level N  --max-ms N  --resume  --dry-run
//
// BUILD  : cargo build --release
// QUICK  : ./proxy_checker                    (interactive)
//          ./proxy_checker -i list.txt -th 5 -t 100
//
// =============================================================================

use std::collections::{HashMap, HashSet};
use std::fs::{File, OpenOptions};
use std::io::{self, BufRead, BufReader, IsTerminal, Read, Write};
use std::net::{Ipv4Addr, Ipv6Addr, SocketAddr, TcpStream, ToSocketAddrs};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::mpsc;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

// ============================================================================
//  CONSTANTS
// ============================================================================

const VERSION: &str = "9.3.0";
const PROG:    &str = "proxy_checker";

const DEFAULT_TIMEOUT_SECS:     u64   = 5;
const DEFAULT_FAST_THREADS:     usize = 100;
const DEFAULT_DETAILED_THREADS: usize = 10;
const DEFAULT_TICK_MS:          u64   = 100;
const DEFAULT_REFRESH_SECS:     u64   = 6;

const FAST_CHECK_HOST: &str = "example.com";
const FAST_CHECK_PORT: u16  = 80;

const BLOCK_HOSTS: &[(&str, u16)] = &[
    ("www.google.com",     80),
    ("github.com",         80),
    ("steamcommunity.com", 80),
    ("voatiengviet.com",   80),
];
const N_LEVELS: usize = BLOCK_HOSTS.len();

const DASH_W:   usize = 30;
const INNER_W: usize = DASH_W - 2;
const DASH_H:  usize = 27 + 2 * N_LEVELS;

const MAX_AUTH_COMBOS: usize = 50;

fn status_ok(code: u16) -> bool { (200..400).contains(&code) }

static VERBOSE: AtomicBool = AtomicBool::new(false);
macro_rules! vlog {
    ($($a:tt)*) => {{
        if VERBOSE.load(Ordering::Relaxed) { eprintln!($($a)*); }
    }};
}

// ============================================================================
//  WINDOWS FFI
// ============================================================================

#[cfg(windows)]
mod wincon {
    use std::ffi::c_void;

    pub type Handle = *mut c_void;

    #[repr(C)] #[derive(Copy, Clone, Default)]
    pub struct Coord { pub x: i16, pub y: i16 }

    #[repr(C)] #[derive(Copy, Clone, Default)]
    pub struct SmallRect { pub left: i16, pub top: i16, pub right: i16, pub bottom: i16 }

    #[repr(C)] #[derive(Copy, Clone, Default)]
    pub struct Csbi {
        pub size:                Coord,
        pub cursor_position:     Coord,
        pub attributes:          u16,
        pub window:              SmallRect,
        pub maximum_window_size: Coord,
    }

    const STD_OUTPUT_HANDLE:                  u32 = 0xFFFF_FFF5;
    const ENABLE_VIRTUAL_TERMINAL_PROCESSING: u32 = 0x0004;

    pub const ATTR_DEFAULT: u16 = 0x07;
    pub const ATTR_CYAN:    u16 = 0x0B;
    pub const ATTR_GREEN:   u16 = 0x0A;
    pub const ATTR_YELLOW:  u16 = 0x0E;
    pub const ATTR_RED:     u16 = 0x0C;
    pub const ATTR_GRAY:    u16 = 0x08;

    #[link(name = "kernel32")]
    extern "system" {
        fn GetStdHandle(n: u32) -> Handle;
        fn GetConsoleMode(h: Handle, m: *mut u32) -> i32;
        fn SetConsoleMode(h: Handle, m: u32) -> i32;
        fn GetConsoleScreenBufferInfo(h: Handle, info: *mut Csbi) -> i32;
        fn SetConsoleCursorPosition(h: Handle, pos: Coord) -> i32;
        fn FillConsoleOutputCharacterW(h: Handle, c: u16, n: u32, pos: Coord, w: *mut u32) -> i32;
        fn FillConsoleOutputAttribute  (h: Handle, a: u16, n: u32, pos: Coord, w: *mut u32) -> i32;
        fn SetConsoleTextAttribute(h: Handle, a: u16) -> i32;
        fn WriteConsoleW(h: Handle, buf: *const u16, len: u32, written: *mut u32, r: *const c_void) -> i32;
    }

    pub fn stdout_handle() -> Handle { unsafe { GetStdHandle(STD_OUTPUT_HANDLE) } }

    pub fn try_enable_vt() -> bool {
        unsafe {
            let h = stdout_handle();
            let mut mode = 0u32;
            if GetConsoleMode(h, &mut mode) == 0 { return false; }
            SetConsoleMode(h, mode | ENABLE_VIRTUAL_TERMINAL_PROCESSING) != 0
        }
    }

    pub fn get_info() -> Option<Csbi> {
        unsafe {
            let mut info = Csbi::default();
            if GetConsoleScreenBufferInfo(stdout_handle(), &mut info) != 0 { Some(info) } else { None }
        }
    }

    pub fn set_cursor(x: i16, y: i16) -> bool {
        unsafe { SetConsoleCursorPosition(stdout_handle(), Coord { x, y }) != 0 }
    }

    pub fn fill_line(y: i16, width: u32) -> bool {
        unsafe {
            let h = stdout_handle();
            let mut w = 0u32;
            let pos = Coord { x: 0, y };
            FillConsoleOutputCharacterW(h, b' ' as u16, width, pos, &mut w) != 0
                && FillConsoleOutputAttribute(h, ATTR_DEFAULT, width, pos, &mut w) != 0
        }
    }

    pub fn set_color(attr: u16) { unsafe { SetConsoleTextAttribute(stdout_handle(), attr); } }

    pub fn write_console(s: &str) -> bool {
        let wide: Vec<u16> = s.encode_utf16().collect();
        let mut written = 0u32;
        unsafe {
            WriteConsoleW(stdout_handle(), wide.as_ptr(), wide.len() as u32, &mut written, std::ptr::null()) != 0
        }
    }
}

// ============================================================================
//  COLOR + TERM MODE
// ============================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Color { Default, Cyan, Green, Yellow, Red, Gray }

impl Color {
    fn ansi(self) -> &'static str {
        match self {
            Color::Default => "\x1b[0m",
            Color::Cyan    => "\x1b[36m",
            Color::Green   => "\x1b[32m",
            Color::Yellow  => "\x1b[33m",
            Color::Red     => "\x1b[31m",
            Color::Gray    => "\x1b[90m",
        }
    }
    #[cfg(windows)]
    fn win_attr(self) -> u16 {
        use wincon::*;
        match self {
            Color::Default => ATTR_DEFAULT,
            Color::Cyan    => ATTR_CYAN,
            Color::Green   => ATTR_GREEN,
            Color::Yellow  => ATTR_YELLOW,
            Color::Red     => ATTR_RED,
            Color::Gray    => ATTR_GRAY,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TermMode {
    Ansi  { color: bool },
    Win32 { color: bool },
    Simple,
}

fn no_color_env() -> bool { std::env::var_os("NO_COLOR").is_some() }

fn detect_mode(force_simple: bool) -> TermMode {
    if force_simple { return TermMode::Simple; }
    if !io::stdout().is_terminal() { return TermMode::Simple; }

    #[cfg(windows)]
    {
        // Win10+ with VT support -> ANSI + color (unless NO_COLOR)
        if wincon::try_enable_vt() {
            return TermMode::Ansi { color: !no_color_env() };
        }
        // Win7/8/2012 (no VT) -> Win32, force NO COLOR per user preference
        if let Some(info) = wincon::get_info() {
            let w_avail = info.size.x as usize;
            let h_avail = (info.size.y - info.cursor_position.y) as usize;
            if w_avail >= DASH_W && h_avail >= DASH_H {
                return TermMode::Win32 { color: false };
            }
        }
        TermMode::Simple
    }

    #[cfg(not(windows))]
    {
        let term = std::env::var("TERM").unwrap_or_default();
        if term == "dumb" { return TermMode::Simple; }
        if let Ok(l) = std::env::var("LINES") {
            if l.parse::<usize>().map(|n| n < DASH_H).unwrap_or(false) {
                return TermMode::Simple;
            }
        }
        if let Ok(c) = std::env::var("COLUMNS") {
            if c.parse::<usize>().map(|n| n < DASH_W).unwrap_or(false) {
                return TermMode::Simple;
            }
        }
        TermMode::Ansi { color: !no_color_env() }
    }
}

fn prompt_color() -> bool {
    if no_color_env() { return false; }
    match detect_mode(false) {
        TermMode::Ansi { color }  => color,
        TermMode::Win32 { color } => color,
        TermMode::Simple          => false,
    }
}

// ============================================================================
//  TYPES
// ============================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Protocol { Socks5, Socks4, Http, Unknown }

impl Protocol {
    fn as_str(&self) -> &'static str {
        match self {
            Protocol::Socks5  => "socks5",
            Protocol::Socks4  => "socks4",
            Protocol::Http    => "http",
            Protocol::Unknown => "unknown",
        }
    }
    fn default_port(&self) -> u16 {
        match self {
            Protocol::Socks5 | Protocol::Socks4 | Protocol::Unknown => 1080,
            Protocol::Http                                          => 8080,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Proxy {
    protocol: Protocol,
    host:     String,
    port:     u16,
    auth:     Option<(String, String)>,
}

impl Proxy {
    fn to_url(&self) -> String {
        match &self.auth {
            Some((u, p)) => format!("{}://{}:{}@{}:{}", self.protocol.as_str(), u, p, self.host, self.port),
            None         => format!("{}://{}:{}", self.protocol.as_str(), self.host, self.port),
        }
    }
    fn with_protocol(&self, p: Protocol) -> Proxy {
        Proxy { protocol: p, host: self.host.clone(), port: self.port, auth: self.auth.clone() }
    }
}

// ============================================================================
//  CONFIG
// ============================================================================

#[derive(Clone)]
struct Config {
    input:            PathBuf,
    raw_good:         PathBuf,
    detailed_good:    PathBuf,
    nonetwork:        PathBuf,
    timeout:          Duration,
    fast_timeout:     Option<Duration>,
    detailed_timeout: Option<Duration>,
    fast_threads:     usize,
    detailed_threads: usize,
    tick:             Duration,
    refresh:          Duration,
    auto_detect:      bool,
    resume:           bool,
    dry_run:          bool,
    no_dash:          bool,
    force_simple:     bool,
    sort:             Option<SortBy>,
    min_level:        Option<u8>,
    max_ms:           Option<u64>,
    users:            Vec<String>,
    passwords:        Vec<String>,
}

#[derive(Clone, Copy, Debug)]
enum SortBy { Speed, Level }

impl Default for Config {
    fn default() -> Self {
        Self {
            input:            PathBuf::from("proxy.txt"),
            raw_good:         PathBuf::from("rawgood_proxy.txt"),
            detailed_good:    PathBuf::from("detailedgood_proxy.txt"),
            nonetwork:        PathBuf::from("nonetwork_proxy.txt"),
            timeout:          Duration::from_secs(DEFAULT_TIMEOUT_SECS),
            fast_timeout:     None,
            detailed_timeout: None,
            fast_threads:     DEFAULT_FAST_THREADS,
            detailed_threads: DEFAULT_DETAILED_THREADS,
            tick:             Duration::from_millis(DEFAULT_TICK_MS),
            refresh:          Duration::from_secs(DEFAULT_REFRESH_SECS),
            auto_detect:      false,
            resume:           false,
            dry_run:          false,
            no_dash:          false,
            force_simple:     false,
            sort:             None,
            min_level:        None,
            max_ms:           None,
            users:            Vec::new(),
            passwords:        Vec::new(),
        }
    }
}

impl Config {
    fn eff_fast_timeout(&self)     -> Duration { self.fast_timeout.unwrap_or(self.timeout) }
    fn eff_detailed_timeout(&self) -> Duration { self.detailed_timeout.unwrap_or(self.timeout) }
}

#[derive(Default, Clone)]
struct ArgFlags {
    input:     bool,
    timeout:   bool,
    threads:   bool,
    detailed:  bool,
    users:     bool,
    passwords: bool,
}

// ============================================================================
//  CLI
// ============================================================================

fn print_help() {
    println!(
r#"usage: {PROG} [OPTIONS]

Concurrent SOCKS5/SOCKS4/HTTP proxy validator with hierarchical block-level
probe and realtime dashboard.

When run without arguments on a TTY, prompts interactively for missing values.

input/output:
  -i, --input <file>        input proxy list            (default: proxy.txt)
                            use '-i -' to read from stdin
  -o, --raw <file>          raw pass-through list       (default: rawgood_proxy.txt)
      --detailed-file <f>   detailed speed+level list   (default: detailedgood_proxy.txt)
  -n, --nonetwork <file>    unreachable-google list     (default: nonetwork_proxy.txt)

threads / timeout (interactive defaults shown):
  -t, --threads <n>         fast-check threads          (default: {FT})
  -d, --detailed <n>        detailed-check threads      (default: {DT})
      --timeout <secs>      base timeout                (default: {TO})
  -th                       alias for --timeout
      --fast-timeout <secs> override fast-check timeout
      --detailed-timeout <secs>  override detailed-check timeout

auth lists (optional):
  -u, --users <list>        usernames: comma-separated OR file path
                            (each proxy w/o inline auth expanded per combo)
  -p, --passwords <list>    passwords: comma-separated OR file path

dashboard:
      --tick-ms <ms>        realtime tick interval      (default: {TICK})
      --refresh <secs>      full-screen reload interval (default: {REFRESH})
      --no-dash             disable dashboard
      --force-simple        force simple mode (\r progress)

behavior:
  -a, --auto                auto-detect protocol for bare 'ip:port' (S5 -> S4 -> HTTP)
                            (without -a: port 1080=SOCKS5, 80/8080=HTTP, else=SOCKS5)
  -r, --resume              skip proxies already present in output files
      --dry-run             parse and report only, do not probe

output filter / sort (applied to detailedgood_proxy.txt):
      --sort <speed|level>  sort by TTFB or block level
      --min-level <n>       keep only proxies at block level >= n (1..={NL})
      --max-ms <n>          keep only proxies with TTFB <= n ms

misc:
  -v, --verbose             per-proxy failure diagnostics (stderr)
  -V, --version             print version and exit
  -h, --help                show this help and exit

block level (hierarchical, stops at first failure):
  L1/{NL}  www.google.com         (required, TTFB measured)
  L2/{NL}  github.com
  L3/{NL}  steamcommunity.com
  L4/{NL}  voatiengviet.com
  (L2..L4 run in parallel after L1 passes)

input format:
  ip:port                     protocol by port (1080=S5, 80/8080=HTTP, else=S5)
  socks5://[user:pass@]ip:port
  socks4://ip:port  |  socks4a://ip:port
  http://[user:pass@]ip:port
  # comment                   ignored

terminal modes (auto-detected):
  ansi    Unix / Win10+ with VT (color, cursor, 100ms)
  win32   Win7/8/2012 without VT (NO color, cursor, 100ms)
  simple  pipe / log / TERM=dumb  (\r progress)

exit status:
  0   success
  1   runtime error (io, missing file)
  2   no proxy reached google.com
  3   no valid proxy in input
  4   command-line error
"#,
    PROG = PROG, FT = DEFAULT_FAST_THREADS, DT = DEFAULT_DETAILED_THREADS,
    TO = DEFAULT_TIMEOUT_SECS, TICK = DEFAULT_TICK_MS, REFRESH = DEFAULT_REFRESH_SECS,
    NL = N_LEVELS);
}

fn parse_args() -> Result<(Config, ArgFlags), String> {
    let args: Vec<String> = std::env::args().collect();
    let mut cfg = Config::default();
    let mut flags = ArgFlags::default();
    let mut i = 1;
    while i < args.len() {
        let a = args[i].clone();
        let mut next = |n: &str| -> Result<String, String> {
            i += 1; args.get(i).cloned().ok_or_else(|| format!("missing value for '{}'", n))
        };
        let pu64 = |s: String, n: &str| -> Result<u64, String> {
            s.parse::<u64>().map_err(|_| format!("invalid numeric value for '{}': '{}'", n, s))
        };
        let pus = |s: String, n: &str| -> Result<usize, String> {
            s.parse::<usize>().map_err(|_| format!("invalid numeric value for '{}': '{}'", n, s))
        };
        match a.as_str() {
            "-i" | "--input"     => { cfg.input = PathBuf::from(next(&a)?); flags.input = true; }
            "-t" | "--threads"   => { cfg.fast_threads = pus(next(&a)?, &a)?; flags.threads = true; }
            "-d" | "--detailed"  => { cfg.detailed_threads = pus(next(&a)?, &a)?; flags.detailed = true; }
            "--timeout" | "-th"  => { cfg.timeout = Duration::from_secs(pu64(next(&a)?, &a)?); flags.timeout = true; }
            "--fast-timeout"     => cfg.fast_timeout = Some(Duration::from_secs(pu64(next(&a)?, &a)?)),
            "--detailed-timeout" => cfg.detailed_timeout = Some(Duration::from_secs(pu64(next(&a)?, &a)?)),
            "--tick-ms"          => cfg.tick = Duration::from_millis(pu64(next(&a)?, &a)?),
            "--refresh"          => cfg.refresh = Duration::from_secs(pu64(next(&a)?, &a)?),
            "-o" | "--raw"         => cfg.raw_good = PathBuf::from(next(&a)?),
            "--detailed-file"      => cfg.detailed_good = PathBuf::from(next(&a)?),
            "-n" | "--nonetwork"   => cfg.nonetwork = PathBuf::from(next(&a)?),
            "-u" | "--users"       => { cfg.users = read_list(&next(&a)?); flags.users = true; }
            "-p" | "--passwords"   => { cfg.passwords = read_list(&next(&a)?); flags.passwords = true; }
            "-a" | "--auto"        => cfg.auto_detect = true,
            "-r" | "--resume"      => cfg.resume = true,
            "--dry-run"            => cfg.dry_run = true,
            "--no-dash"            => cfg.no_dash = true,
            "--force-simple"       => cfg.force_simple = true,
            "-v" | "--verbose"     => VERBOSE.store(true, Ordering::Relaxed),
            "-V" | "--version"     => { println!("{} {}", PROG, VERSION); std::process::exit(0); }
            "-h" | "--help"        => { print_help(); std::process::exit(0); }
            "--sort"               => {
                let v = next(&a)?;
                cfg.sort = Some(match v.as_str() {
                    "speed" => SortBy::Speed, "level" => SortBy::Level,
                    o => return Err(format!("invalid value for '--sort': '{}' (expected speed|level)", o)),
                });
            }
            "--min-level"          => {
                let n = pu64(next(&a)?, &a)? as u8;
                if n < 1 || n as usize > N_LEVELS {
                    return Err(format!("'--min-level' must be in range 1..={}", N_LEVELS));
                }
                cfg.min_level = Some(n);
            }
            "--max-ms"             => cfg.max_ms = Some(pu64(next(&a)?, &a)?),
            other                  => return Err(format!("unrecognized option '{}'", other)),
        }
        i += 1;
    }
    if cfg.fast_threads == 0     { return Err("'-t' must be >= 1".into()); }
    if cfg.detailed_threads == 0 { return Err("'-d' must be >= 1".into()); }
    if cfg.timeout.is_zero()     { return Err("'--timeout' must be >= 1".into()); }
    if cfg.tick.is_zero()        { return Err("'--tick-ms' must be >= 1".into()); }
    if cfg.refresh < cfg.tick    { return Err("'--refresh' must be >= '--tick-ms'".into()); }
    Ok((cfg, flags))
}

// ============================================================================
//  INPUT HELPERS
// ============================================================================

fn strip_quotes(s: &str) -> String {
    let mut t = s.trim().to_string();
    loop {
        let before = t.clone();
        t = t.trim().to_string();
        if t.len() >= 2 {
            let b = t.as_bytes();
            let f = b[0]; let l = b[t.len() - 1];
            if (f == b'"' && l == b'"') || (f == b'\'' && l == b'\'') {
                t = t[1..t.len() - 1].to_string();
            }
        }
        if t == before { break; }
    }
    t
}

fn read_list(s: &str) -> Vec<String> {
    let s = strip_quotes(s);
    if s.is_empty() { return Vec::new(); }
    if Path::new(&s).is_file() {
        if let Ok(c) = std::fs::read_to_string(&s) {
            return c.lines()
                .map(|l| l.trim().to_string())
                .filter(|l| !l.is_empty() && !l.starts_with('#'))
                .collect();
        }
    }
    s.split(',').map(|x| x.trim().to_string()).filter(|x| !x.is_empty()).collect()
}

fn prompt_str(label: &str, default: &str, color: bool) -> String {
    let (open, close)         = if color { ("\x1b[36m", "\x1b[0m") } else { ("", "") };
    let (dim_open, dim_close) = if color { ("\x1b[90m", "\x1b[0m") } else { ("", "") };
    if default.is_empty() {
        eprint!("{}{}{}: ", open, label, close);
    } else {
        eprint!("{}{}{} [{}{}{}]: ", open, label, close, dim_open, default, dim_close);
    }
    io::stderr().flush().ok();
    let mut s = String::new();
    if io::stdin().read_line(&mut s).unwrap_or(0) == 0 {
        return default.to_string();
    }
    let t = strip_quotes(s.trim());
    if t.is_empty() { default.to_string() } else { t }
}

fn infer_protocol_from_port(port: u16) -> Protocol {
    match port {
        1080      => Protocol::Socks5,
        80 | 8080 => Protocol::Http,
        _         => Protocol::Socks5,
    }
}

// ============================================================================
//  INTERACTIVE PROMPT
// ============================================================================

fn interactive_prompt(cfg: &mut Config, flags: &ArgFlags) -> bool {
    if !io::stdin().is_terminal() { return false; }

    let need_input     = !flags.input;
    let need_timeout   = !flags.timeout;
    let need_threads   = !flags.threads;
    let need_users     = !flags.users;
    let need_passwords = !flags.passwords;

    if !(need_input || need_timeout || need_threads || need_users || need_passwords) {
        return false;
    }

    let color = prompt_color();
    let (hdr_open, hdr_close) = if color { ("\x1b[1;36m", "\x1b[0m") } else { ("", "") };

    eprintln!("{}{} proxy checker v{}{}", hdr_open, PROG, VERSION, hdr_close);
    eprintln!("{}", if color { "\x1b[90m(Enter = default, drop path with quotes OK)\x1b[0m" } else { "(Enter = default, drop path with quotes OK)" });
    eprintln!();

    if need_input {
        loop {
            let s = prompt_str("input proxy file", "proxy.txt", color);
            let s = strip_quotes(&s);
            if s.is_empty() { continue; }
            if s == "-" || Path::new(&s).exists() {
                cfg.input = PathBuf::from(&s);
                break;
            }
            eprintln!("  ! file not found: {}", s);
        }
    }

    if need_timeout {
        let s = prompt_str("timeout (secs)", &DEFAULT_TIMEOUT_SECS.to_string(), color);
        if let Ok(n) = s.parse::<u64>() { if n > 0 { cfg.timeout = Duration::from_secs(n); } }
    }

    if need_threads {
        let s = prompt_str("fast threads", &DEFAULT_FAST_THREADS.to_string(), color);
        if let Ok(n) = s.parse::<usize>() { if n > 0 { cfg.fast_threads = n; } }
    }

    if need_users {
        let s = prompt_str("user list (optional, comma or file)", "", color);
        cfg.users = read_list(&s);
    }

    if need_passwords {
        let s = prompt_str("pass list (optional, comma or file)", "", color);
        cfg.passwords = read_list(&s);
    }

    eprintln!();
    true
}

// ============================================================================
//  INPUT RESOLUTION (fallback for non-interactive paths)
// ============================================================================

fn resolve_input(mut cfg: Config) -> Config {
    if cfg.input == Path::new("-") || cfg.input.exists() { return cfg; }
    eprintln!("{}: warning: file not found: {}", PROG, cfg.input.display());
    if !io::stdin().is_terminal() {
        eprintln!("{}: stdin is not a tty", PROG);
        std::process::exit(1);
    }
    let color = prompt_color();
    loop {
        let s = prompt_str("proxy file", "proxy.txt", color);
        let s = strip_quotes(&s);
        let cand = if s.is_empty() { PathBuf::from("proxy.txt") } else { PathBuf::from(&s) };
        if cand.exists() { cfg.input = cand; return cfg; }
        eprintln!("{}: error: '{}' not found", PROG, cand.display());
    }
}

// ============================================================================
//  BASE64
// ============================================================================

fn base64_encode(input: &[u8]) -> String {
    const C: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut o = String::with_capacity((input.len() + 2) / 3 * 4);
    for ch in input.chunks(3) {
        let b0 = ch[0] as u32;
        let b1 = ch.get(1).copied().unwrap_or(0) as u32;
        let b2 = ch.get(2).copied().unwrap_or(0) as u32;
        let n  = (b0 << 16) | (b1 << 8) | b2;
        o.push(C[(n >> 18) as usize & 0x3F] as char);
        o.push(C[(n >> 12) as usize & 0x3F] as char);
        o.push(if ch.len() > 1 { C[(n >> 6) as usize & 0x3F] as char } else { '=' });
        o.push(if ch.len() > 2 { C[n as usize & 0x3F] as char } else { '=' });
    }
    o
}

// ============================================================================
//  PARSING
// ============================================================================

fn parse_proxy(line: &str) -> Option<Proxy> {
    let line = line.trim();
    if line.is_empty() || line.starts_with('#') { return None; }

    let (proto, rest) = if let Some(r) = line.strip_prefix("socks5://")       { (Protocol::Socks5, r) }
        else if let Some(r) = line.strip_prefix("socks4://")                  { (Protocol::Socks4, r) }
        else if let Some(r) = line.strip_prefix("socks4a://")                 { (Protocol::Socks4, r) }
        else if let Some(r) = line.strip_prefix("http://")                    { (Protocol::Http, r) }
        else if let Some(r) = line.strip_prefix("https://")                   { (Protocol::Http, r) }
        else                                                                   { (Protocol::Unknown, line) };

    let (auth, rest) = match rest.rfind('@') {
        Some(at) => {
            let c = &rest[..at];
            let h = &rest[at + 1..];
            let creds = match c.find(':') {
                Some(p) => (c[..p].into(), c[p + 1..].into()),
                None    => (c.into(), String::new()),
            };
            (Some(creds), h)
        }
        None => (None, rest),
    };

    let (host, port) = if let Some(inner) = rest.strip_prefix('[') {
        let end  = inner.find(']')?;
        let h    = &inner[..end];
        let tail = &inner[end + 1..];
        let p = if tail.is_empty() { proto.default_port() }
                else { tail.strip_prefix(':')?.parse::<u16>().ok()? };
        (h.to_string(), p)
    } else if let Some((h, p)) = rest.rsplit_once(':') {
        (h.to_string(), p.parse::<u16>().ok()?)
    } else {
        (rest.to_string(), proto.default_port())
    };

    if host.is_empty() || port == 0 { return None; }
    let auth = if proto == Protocol::Socks4 { None } else { auth };
    Some(Proxy { protocol: proto, host, port, auth })
}

fn auth_combos(users: &[String], passes: &[String]) -> Vec<Option<(String, String)>> {
    if users.is_empty() && passes.is_empty() { return vec![None]; }
    let us: Vec<String> = if users.is_empty() { vec![String::new()] } else { users.to_vec() };
    let ps: Vec<String> = if passes.is_empty() { vec![String::new()] } else { passes.to_vec() };
    let mut out = Vec::new();
    for u in &us {
        for p in &ps {
            out.push(Some((u.clone(), p.clone())));
            if out.len() >= MAX_AUTH_COMBOS { return out; }
        }
    }
    out
}

fn load_proxies(cfg: &Config, done: &HashSet<String>) -> (Vec<Proxy>, usize, usize) {
    let reader: Box<dyn BufRead> = if cfg.input == Path::new("-") {
        Box::new(BufReader::new(io::stdin()))
    } else {
        match File::open(&cfg.input) {
            Ok(f)  => Box::new(BufReader::new(f)),
            Err(e) => {
                eprintln!("{}: cannot open {}: {}", PROG, cfg.input.display(), e);
                std::process::exit(1);
            }
        }
    };
    let mut seen = HashSet::new();
    let mut out  = Vec::new();
    let mut inv  = 0;
    let mut n    = 0;
    let expand_auth = !cfg.users.is_empty() || !cfg.passwords.is_empty();
    let combos = if expand_auth { auth_combos(&cfg.users, &cfg.passwords) } else { vec![None] };

    for l in reader.lines().flatten() {
        n += 1;
        let t = l.trim();
        if t.is_empty() || t.starts_with('#') { continue; }
        match parse_proxy(t) {
            Some(mut p) => {
                if p.protocol == Protocol::Unknown && !cfg.auto_detect {
                    p.protocol = infer_protocol_from_port(p.port);
                }
                if p.auth.is_none() && expand_auth {
                    for auth in &combos {
                        let mut np = p.clone();
                        np.auth = auth.clone();
                        if cfg.resume && done.contains(&np.to_url()) { continue; }
                        if seen.insert(np.clone()) { out.push(np); }
                    }
                } else {
                    if cfg.resume && done.contains(&p.to_url()) { continue; }
                    if seen.insert(p.clone()) { out.push(p); }
                }
            }
            None => inv += 1,
        }
    }
    (out, inv, n)
}

fn load_done_set(cfg: &Config) -> HashSet<String> {
    let mut s = HashSet::new();
    for path in [&cfg.raw_good, &cfg.detailed_good, &cfg.nonetwork] {
        if let Ok(f) = File::open(path) {
            for l in BufReader::new(f).lines().flatten() {
                if let Some(k) = l.split_whitespace().next() {
                    if !k.is_empty() { s.insert(k.into()); }
                }
            }
        }
    }
    s
}

// ============================================================================
//  NETWORK
// ============================================================================

fn tcp_connect(host: &str, port: u16, timeout: Duration) -> io::Result<TcpStream> {
    let addrs: Vec<SocketAddr> = (host, port).to_socket_addrs()?.collect();
    let mut last = None;
    for sa in addrs {
        match TcpStream::connect_timeout(&sa, timeout) {
            Ok(s) => {
                s.set_read_timeout(Some(timeout))?;
                s.set_write_timeout(Some(timeout))?;
                return Ok(s);
            }
            Err(e) => last = Some(e),
        }
    }
    Err(last.unwrap_or_else(|| io::Error::new(io::ErrorKind::NotFound, "no addr resolved")))
}

fn socks5_greeting(s: &mut TcpStream, auth: Option<&(String, String)>) -> io::Result<()> {
    let m: &[u8] = if auth.is_some() { &[0x00, 0x02] } else { &[0x00] };
    let mut req = vec![0x05u8, m.len() as u8];
    req.extend_from_slice(m);
    s.write_all(&req)?;
    let mut r = [0u8; 2];
    s.read_exact(&mut r)?;
    if r[0] != 0x05 { return Err(io::Error::new(io::ErrorKind::InvalidData, "socks5: bad version")); }
    match r[1] {
        0x00 => Ok(()),
        0x02 => {
            let (u, p) = auth.ok_or_else(|| io::Error::other("socks5: auth required but no credentials"))?;
            if u.len() > 255 || p.len() > 255 {
                return Err(io::Error::new(io::ErrorKind::InvalidInput, "socks5: auth credentials too long"));
            }
            let mut ar = vec![0x01u8, u.len() as u8];
            ar.extend_from_slice(u.as_bytes());
            ar.push(p.len() as u8);
            ar.extend_from_slice(p.as_bytes());
            s.write_all(&ar)?;
            let mut ar2 = [0u8; 2];
            s.read_exact(&mut ar2)?;
            if ar2 != [0x01, 0x00] { return Err(io::Error::other("socks5: authentication failed")); }
            Ok(())
        }
        0xFF => Err(io::Error::other("socks5: no acceptable auth method")),
        m    => Err(io::Error::other(format!("socks5: unsupported method 0x{:02x}", m))),
    }
}

fn socks5_connect(s: &mut TcpStream, target: &str, port: u16, auth: Option<&(String, String)>) -> io::Result<()> {
    socks5_greeting(s, auth)?;
    let mut req = vec![0x05u8, 0x01, 0x00];
    if let Ok(ip) = target.parse::<Ipv4Addr>() {
        req.push(0x01); req.extend_from_slice(&ip.octets());
    } else if let Ok(ip) = target.parse::<Ipv6Addr>() {
        req.push(0x04); req.extend_from_slice(&ip.octets());
    } else {
        let hb = target.as_bytes();
        if hb.len() > 255 { return Err(io::Error::new(io::ErrorKind::InvalidInput, "socks5: hostname too long")); }
        req.push(0x03); req.push(hb.len() as u8); req.extend_from_slice(hb);
    }
    req.extend_from_slice(&port.to_be_bytes());
    s.write_all(&req)?;
    let mut h = [0u8; 4];
    s.read_exact(&mut h)?;
    if h[0] != 0x05 { return Err(io::Error::new(io::ErrorKind::InvalidData, "socks5: bad version")); }
    if h[1] != 0x00 { return Err(io::Error::other(format!("socks5: connect rejected, rep=0x{:02x}", h[1]))); }
    match h[3] {
        0x01 => { let mut b = [0u8; 6];  s.read_exact(&mut b)?; }
        0x03 => { let mut l = [0u8; 1]; s.read_exact(&mut l)?;
                  let mut b = vec![0u8; l[0] as usize + 2]; s.read_exact(&mut b)?; }
        0x04 => { let mut b = [0u8; 18]; s.read_exact(&mut b)?; }
        x    => return Err(io::Error::new(io::ErrorKind::InvalidData, format!("socks5: bad atyp 0x{:02x}", x))),
    }
    Ok(())
}

fn socks4_connect(s: &mut TcpStream, target: &str, port: u16) -> io::Result<()> {
    let mut req = vec![0x04u8, 0x01];
    req.extend_from_slice(&port.to_be_bytes());
    let use_4a = match target.parse::<Ipv4Addr>() {
        Ok(ip) => { req.extend_from_slice(&ip.octets()); false }
        Err(_) => { req.extend_from_slice(&[0, 0, 0, 1]); true }
    };
    req.push(0x00);
    if use_4a {
        req.extend_from_slice(target.as_bytes());
        req.push(0x00);
    }
    s.write_all(&req)?;
    let mut r = [0u8; 8];
    s.read_exact(&mut r)?;
    if r[0] != 0x00 { return Err(io::Error::new(io::ErrorKind::InvalidData, "socks4: bad version")); }
    if r[1] != 0x5A { return Err(io::Error::other(format!("socks4: request rejected, code=0x{:02x}", r[1]))); }
    Ok(())
}

fn http_connect(s: &mut TcpStream, target: &str, port: u16, auth: Option<&(String, String)>) -> io::Result<()> {
    let mut req = format!("CONNECT {h}:{p} HTTP/1.1\r\nHost: {h}:{p}\r\n", h = target, p = port);
    if let Some((u, p)) = auth {
        let creds = base64_encode(format!("{}:{}", u, p).as_bytes());
        req.push_str(&format!("Proxy-Authorization: Basic {}\r\n", creds));
    }
    req.push_str("Proxy-Connection: Keep-Alive\r\n\r\n");
    s.write_all(req.as_bytes())?;
    let mut buf = Vec::with_capacity(512);
    let mut b = [0u8; 1];
    while buf.len() < 16384 {
        s.read_exact(&mut b)?;
        buf.push(b[0]);
        if buf.len() >= 4 && &buf[buf.len() - 4..] == b"\r\n\r\n" { break; }
    }
    if buf.len() >= 16384 {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "http: response headers too large"));
    }
    let resp  = String::from_utf8_lossy(&buf);
    let first = resp.lines().next().unwrap_or("");
    if !first.starts_with("HTTP/") {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "http: malformed status line"));
    }
    let code: u16 = first.split_whitespace().nth(1)
        .and_then(|s| s.parse().ok())
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "http: missing status code"))?;
    if code != 200 {
        return Err(io::Error::other(format!("http: CONNECT returned {}", code)));
    }
    Ok(())
}

// ============================================================================
//  CHECKS
// ============================================================================

fn fast_check(proxy: &Proxy, timeout: Duration) -> Option<Protocol> {
    let try_s5 = || match tcp_connect(&proxy.host, proxy.port, timeout) {
        Ok(mut s) => socks5_connect(&mut s, FAST_CHECK_HOST, FAST_CHECK_PORT, proxy.auth.as_ref()).is_ok(),
        Err(_) => false,
    };
    let try_s4 = || match tcp_connect(&proxy.host, proxy.port, timeout) {
        Ok(mut s) => socks4_connect(&mut s, FAST_CHECK_HOST, FAST_CHECK_PORT).is_ok(),
        Err(_) => false,
    };
    let try_ht = || match tcp_connect(&proxy.host, proxy.port, timeout) {
        Ok(mut s) => http_connect(&mut s, FAST_CHECK_HOST, FAST_CHECK_PORT, proxy.auth.as_ref()).is_ok(),
        Err(_) => false,
    };
    match proxy.protocol {
        Protocol::Socks5  => if try_s5() { Some(Protocol::Socks5) } else { None },
        Protocol::Socks4  => if try_s4() { Some(Protocol::Socks4) } else { None },
        Protocol::Http    => if try_ht() { Some(Protocol::Http)   } else { None },
        Protocol::Unknown => {
            if try_s5() { return Some(Protocol::Socks5); }
            if try_s4() { return Some(Protocol::Socks4); }
            if try_ht() { return Some(Protocol::Http);   }
            None
        }
    }
}

fn check_via_proxy(proxy: &Proxy, target: &str, port: u16, timeout: Duration) -> io::Result<Duration> {
    let start = Instant::now();
    let mut s = tcp_connect(&proxy.host, proxy.port, timeout)?;
    match proxy.protocol {
        Protocol::Socks5  => socks5_connect(&mut s, target, port, proxy.auth.as_ref())?,
        Protocol::Socks4  => socks4_connect(&mut s, target, port)?,
        Protocol::Http    => http_connect  (&mut s, target, port, proxy.auth.as_ref())?,
        Protocol::Unknown => return Err(io::Error::other("unknown protocol")),
    }
    let get = format!(
        "GET / HTTP/1.1\r\nHost: {}\r\nUser-Agent: Mozilla/5.0\r\nAccept: */*\r\nConnection: close\r\n\r\n",
        target
    );
    s.write_all(get.as_bytes())?;
    let mut b = [0u8; 1];
    s.read_exact(&mut b)?;
    let ttfb = start.elapsed();

    let mut status = Vec::with_capacity(128);
    status.push(b[0]);
    while status.len() < 256 && !status.ends_with(b"\r\n") && !status.ends_with(b"\n") {
        s.read_exact(&mut b)?;
        status.push(b[0]);
    }
    let line = String::from_utf8_lossy(&status);
    let mut parts = line.split_whitespace();
    if !parts.next().map_or(false, |p| p.starts_with("HTTP/")) {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "bad status line"));
    }
    let code: u16 = parts.next().and_then(|c| c.parse().ok()).unwrap_or(0);
    if !status_ok(code) {
        return Err(io::Error::other(format!("status {}", code)));
    }
    let mut headers = Vec::with_capacity(2048);
    while headers.len() < 8192 {
        s.read_exact(&mut b)?;
        headers.push(b[0]);
        if headers.ends_with(b"\r\n\r\n") || headers.ends_with(b"\n\n") { break; }
    }
    if !(headers.ends_with(b"\r\n\r\n") || headers.ends_with(b"\n\n")) {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "incomplete headers"));
    }
    Ok(ttfb)
}

fn detailed_check(proxy: &Proxy, timeout: Duration) -> Result<(Duration, u8), ()> {
    let dur = match check_via_proxy(proxy, BLOCK_HOSTS[0].0, BLOCK_HOSTS[0].1, timeout) {
        Ok(d) => d,
        Err(e) => { vlog!("[v] {} L1 fail: {}", proxy.to_url(), e); return Err(()); }
    };
    let results: Vec<bool> = thread::scope(|s| {
        let handles: Vec<_> = BLOCK_HOSTS.iter().skip(1)
            .map(|&(host, port)| s.spawn(move || {
                check_via_proxy(proxy, host, port, timeout).map_err(|e| {
                    vlog!("[v] {} {} fail: {}", proxy.to_url(), host, e);
                }).is_ok()
            }))
            .collect();
        handles.into_iter().map(|h| h.join().unwrap_or(false)).collect()
    });
    let mut level = 1u8;
    for (i, ok) in results.iter().enumerate() {
        if *ok { level = (i + 2) as u8; } else { break; }
    }
    Ok((dur, level))
}

// ============================================================================
//  UTILITIES
// ============================================================================

fn count_lines(path: &Path) -> usize {
    File::open(path).ok().map_or(0, |f| {
        BufReader::new(f).lines().flatten().filter(|l| !l.trim().is_empty()).count()
    })
}

fn parse_detailed_line(line: &str) -> Option<(u8, u64, String)> {
    let (_, rest) = line.rsplit_once(" - [")?;
    let (ms_str, rest2) = rest.split_once("ms] blocklv ")?;
    let (lv_str, _)     = rest2.split_once('/')?;
    let ms:    u64 = ms_str.trim().parse().ok()?;
    let level: u8  = lv_str.trim().parse().ok()?;
    Some((level, ms, line.trim().to_string()))
}

type TtfbStats = Vec<(u8, usize, u64, u64, u64)>;

fn post_process_detailed(cfg: &Config) -> TtfbStats {
    let content = match std::fs::read_to_string(&cfg.detailed_good) {
        Ok(c)  => c, Err(_) => return Vec::new(),
    };
    let mut entries: Vec<(u8, u64, String)> = content.lines()
        .filter_map(parse_detailed_line).collect();

    if let Some(min) = cfg.min_level { entries.retain(|(lv, _, _)| *lv >= min); }
    if let Some(max) = cfg.max_ms   { entries.retain(|(_, ms, _)| *ms <= max); }
    if let Some(by) = cfg.sort {
        match by {
            SortBy::Speed => entries.sort_by_key(|(_, ms, _)| *ms),
            SortBy::Level => entries.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1))),
        }
    }
    if cfg.sort.is_some() || cfg.min_level.is_some() || cfg.max_ms.is_some() {
        if let Ok(mut f) = File::create(&cfg.detailed_good) {
            for (_, _, line) in &entries { let _ = writeln!(f, "{}", line); }
        }
    }
    let mut map: HashMap<u8, Vec<u64>> = HashMap::new();
    for (lv, ms, _) in &entries { map.entry(*lv).or_default().push(*ms); }
    let mut stats: TtfbStats = map.into_iter().map(|(lv, v)| {
        let min = *v.iter().min().unwrap_or(&0);
        let max = *v.iter().max().unwrap_or(&0);
        let avg = v.iter().sum::<u64>() / v.len() as u64;
        (lv, v.len(), min, avg, max)
    }).collect();
    stats.sort_by_key(|(l, _, _, _, _)| *l);
    stats
}

// ============================================================================
//  DASHBOARD RENDER
// ============================================================================

fn bar(pct: f64, width: usize) -> String {
    let p = pct.clamp(0.0, 100.0);
    let filled = (((p / 100.0) * width as f64).round() as usize).min(width);
    format!("{}{}", "█".repeat(filled), "░".repeat(width - filled))
}

fn box_line(content: &str) -> String {
    let chars: Vec<char> = content.chars().collect();
    let inner = if chars.len() > INNER_W {
        chars.into_iter().take(INNER_W).collect::<String>()
    } else {
        let mut s: String = chars.into_iter().collect();
        let pad = INNER_W.saturating_sub(s.chars().count());
        s.push_str(&" ".repeat(pad));
        s
    };
    format!("│{}│", inner)
}

#[derive(Clone)]
struct DashLine { text: String, color: Color }

impl DashLine {
    fn new(text: impl Into<String>, color: Color) -> Self { Self { text: text.into(), color } }
    fn plain(text: impl Into<String>) -> Self { Self { text: text.into(), color: Color::Default } }
}

struct DashState<'a> {
    fast_done:    usize,
    fast_total:   usize,
    det_done:     usize,
    det_total:    usize,
    level_counts: &'a [usize],
    ttfb:         &'a [(u8, usize, u64, u64, u64)],
    elapsed:      f64,
    cfg:          &'a Config,
    done:         bool,
}

fn render_dashboard(st: DashState) -> Vec<DashLine> {
    let mut lines: Vec<DashLine> = Vec::with_capacity(DASH_H);
    let hline = format!("├{}┤", "─".repeat(INNER_W));

    lines.push(DashLine::new(format!("┌{}┐", "─".repeat(INNER_W)), Color::Cyan));
    lines.push(DashLine::new(box_line("      PROXY CHECKER v9"), Color::Cyan));
    lines.push(DashLine::new(hline.clone(), Color::Gray));

    lines.push(DashLine::plain(box_line(" FAST")));
    let fpct = if st.fast_total > 0 { st.fast_done as f64 / st.fast_total as f64 * 100.0 } else { 0.0 };
    let fcolor = if fpct >= 100.0 { Color::Green } else { Color::Cyan };
    lines.push(DashLine::new(box_line(&format!(" {}/{}  ({:.1}%)", st.fast_done, st.fast_total, fpct)), fcolor));
    lines.push(DashLine::new(box_line(&format!(" {}", bar(fpct, 20))), fcolor));
    let sp = if st.elapsed > 0.01 { st.fast_done as f64 / st.elapsed } else { 0.0 };
    let eta = if sp > 0.5 && st.fast_done < st.fast_total {
        ((st.fast_total - st.fast_done) as f64 / sp).round() as u64
    } else { 0 };
    lines.push(DashLine::plain(box_line(&format!(" {:.0}/s    ETA {}s", sp, eta))));
    lines.push(DashLine::new(hline.clone(), Color::Gray));

    lines.push(DashLine::plain(box_line(" DETAILED")));
    lines.push(DashLine::plain(box_line(&format!(" {}/{}", st.det_done, st.det_total))));
    let dpct = if st.det_total > 0 { st.det_done as f64 / st.det_total as f64 * 100.0 } else { 0.0 };
    lines.push(DashLine::new(box_line(&format!(" {}", bar(dpct, 20))), Color::Green));
    lines.push(DashLine::new(hline.clone(), Color::Gray));

    lines.push(DashLine::plain(box_line(" BLOCK LEVELS")));
    let max_cnt = st.level_counts.iter().skip(1).copied().max().unwrap_or(0).max(1);
    for i in 1..=N_LEVELS {
        let cnt = st.level_counts.get(i).copied().unwrap_or(0);
        let bw = ((cnt as f64 / max_cnt as f64) * 8.0).round() as usize;
        let b  = format!("{}{}", "█".repeat(bw), "░".repeat(8 - bw));
        let color = match i { 4 => Color::Cyan, 3 => Color::Green, 2 => Color::Yellow, _ => Color::Gray };
        lines.push(DashLine::new(box_line(&format!(" L{} {} {:>5}", i, b, cnt)), color));
    }
    lines.push(DashLine::new(hline.clone(), Color::Gray));

    lines.push(DashLine::plain(box_line(" STATUS")));
    let yn = |b: bool| if b { Color::Green } else { Color::Gray };
    lines.push(DashLine::new(box_line(&format!(" Auto     : {}", if st.cfg.auto_detect { "ON" } else { "OFF" })),
        yn(st.cfg.auto_detect)));
    lines.push(DashLine::new(box_line(&format!(" Resume   : {}", if st.cfg.resume { "ON" } else { "OFF" })),
        yn(st.cfg.resume)));
    lines.push(DashLine::plain(box_line(&format!(" Auth lst : {}/{}",
        st.cfg.users.len(), st.cfg.passwords.len()))));
    lines.push(DashLine::plain(box_line(&format!(" Sort     : {}",
        match st.cfg.sort { Some(SortBy::Speed) => "Speed", Some(SortBy::Level) => "Level", None => "-" }))));
    lines.push(DashLine::plain(box_line(&format!(" Min level: {}",
        st.cfg.min_level.map(|m| format!("{}/{}", m, N_LEVELS)).unwrap_or_else(|| "-".into())))));
    lines.push(DashLine::new(hline.clone(), Color::Gray));

    lines.push(DashLine::plain(box_line(" TTFB STATS (min/avg/max)")));
    let mut map: HashMap<u8, (u64, u64, u64)> = HashMap::new();
    for (lv, _c, min, avg, max) in st.ttfb { map.insert(*lv, (*min, *avg, *max)); }
    for i in 1..=N_LEVELS {
        match map.get(&(i as u8)) {
            Some((min, avg, max)) => lines.push(DashLine::new(
                box_line(&format!(" L{} {:>4}/{}/{}", i, min, avg, max)), Color::Default)),
            None                  => lines.push(DashLine::new(
                box_line(&format!(" L{}     -/-/-", i)), Color::Gray)),
        }
    }
    lines.push(DashLine::new(hline.clone(), Color::Gray));

    lines.push(DashLine::plain(box_line(" ELAPSED")));
    let el_color = if st.done { Color::Green } else { Color::Yellow };
    lines.push(DashLine::new(
        box_line(&format!(" {:.2}s {}", st.elapsed, if st.done { "done" } else { "..." })), el_color));
    lines.push(DashLine::plain(box_line("")));
    lines.push(DashLine::new(format!("└{}┘", "─".repeat(INNER_W)), Color::Cyan));

    debug_assert_eq!(lines.len(), DASH_H);
    lines
}

// ============================================================================
//  SCREEN ABSTRACTION
// ============================================================================

trait Screen: Send {
    fn init(&mut self);
    fn frame_start(&mut self, full: bool);
    fn line(&mut self, l: &DashLine);
    fn frame_end(&mut self);
    fn shutdown(&mut self);
}

struct AnsiScreen { use_color: bool, first: bool, buf: String }

impl AnsiScreen {
    fn new(color: bool) -> Self {
        Self { use_color: color, first: true, buf: String::with_capacity(4096) }
    }
}

impl Screen for AnsiScreen {
    fn init(&mut self) { print!("\x1b[?25l"); io::stdout().flush().ok(); }
    fn frame_start(&mut self, full: bool) {
        self.buf.clear();
        if self.first { self.buf.push_str("\x1b[s"); self.first = false; }
        else          { self.buf.push_str("\x1b[u"); }
        if full { self.buf.push_str("\x1b[0J"); }
    }
    fn line(&mut self, l: &DashLine) {
        self.buf.push_str("\x1b[2K");
        if self.use_color && l.color != Color::Default {
            self.buf.push_str(l.color.ansi());
            self.buf.push_str(&l.text);
            self.buf.push_str("\x1b[0m");
        } else {
            self.buf.push_str(&l.text);
        }
        self.buf.push_str("\r\n");
    }
    fn frame_end(&mut self) { print!("{}", self.buf); io::stdout().flush().ok(); }
    fn shutdown(&mut self) { print!("\x1b[?25h"); io::stdout().flush().ok(); }
}

#[cfg(windows)]
struct Win32Screen {
    saved_x: i16,
    saved_y: i16,
    use_color: bool,
}

#[cfg(windows)]
impl Win32Screen {
    fn new(color: bool) -> Option<Self> {
        let info = wincon::get_info()?;
        let w_avail = info.size.x as usize;
        let h_avail = (info.size.y - info.cursor_position.y) as usize;
        if w_avail < DASH_W || h_avail < DASH_H { return None; }
        Some(Self {
            saved_x: info.cursor_position.x,
            saved_y: info.cursor_position.y,
            use_color: color,
        })
    }
}

#[cfg(windows)]
impl Screen for Win32Screen {
    fn init(&mut self) {}
    fn frame_start(&mut self, full: bool) {
        if full {
            for i in 0..DASH_H {
                wincon::fill_line(self.saved_y + i as i16, DASH_W as u32);
            }
        }
        wincon::set_cursor(self.saved_x, self.saved_y);
    }
    fn line(&mut self, l: &DashLine) {
        let attr = if self.use_color { l.color.win_attr() } else { wincon::ATTR_DEFAULT };
        wincon::set_color(attr);
        wincon::write_console(&l.text);
        wincon::write_console("\r\n");
    }
    fn frame_end(&mut self) { wincon::set_color(wincon::ATTR_DEFAULT); }
    fn shutdown(&mut self)  { wincon::set_color(wincon::ATTR_DEFAULT); }
}

// ============================================================================
//  PROGRESS
// ============================================================================

type LevelStats = Vec<Mutex<(u64, u64, u64, u64)>>; // (min, max, sum, count)

struct Progress {
    fast_done:    Arc<AtomicUsize>,
    fast_total:   usize,
    det_done:     Arc<AtomicUsize>,
    det_total:    Arc<AtomicUsize>,
    level_counts: Arc<Vec<AtomicUsize>>,
    level_stats:  Arc<LevelStats>,
    stop:         Arc<AtomicBool>,
    start:        Instant,
    cfg:          Config,
    mode:         TermMode,
    screen:       Option<Box<dyn Screen>>,
}

impl Progress {
    fn spawn(self) -> thread::JoinHandle<()> {
        thread::spawn(move || self.run())
    }

    fn run(mut self) {
        let use_dash = !matches!(self.mode, TermMode::Simple);
        if use_dash { if let Some(s) = self.screen.as_mut() { s.init(); } }

        if use_dash { self.draw(true); }

        let mut last_full = Instant::now();
        while !self.stop.load(Ordering::Relaxed) {
            thread::sleep(self.cfg.tick);
            if self.stop.load(Ordering::Relaxed) { break; }
            if use_dash {
                let full = last_full.elapsed() >= self.cfg.refresh;
                self.draw(full);
                if full { last_full = Instant::now(); }
            } else {
                self.draw_simple();
            }
        }

        if use_dash {
            self.draw(true);
            if let Some(s) = self.screen.as_mut() { s.shutdown(); }
            println!();
        } else {
            eprintln!();
        }
    }

    fn build_live_stats(&self) -> TtfbStats {
        let mut out = TtfbStats::new();
        for (lv, m) in self.level_stats.iter().enumerate() {
            if let Ok(g) = m.lock() {
                if g.3 > 0 {
                    out.push((lv as u8, g.3 as usize, g.0, g.2 / g.3, g.1));
                }
            }
        }
        out
    }

    fn build_dash_state<'a>(&'a self, levels: &'a [usize], ttfb: &'a TtfbStats, done: bool) -> DashState<'a> {
        DashState {
            fast_done:    self.fast_done.load(Ordering::Relaxed),
            fast_total:   self.fast_total,
            det_done:     self.det_done.load(Ordering::Relaxed),
            det_total:    self.det_total.load(Ordering::Relaxed),
            level_counts: levels,
            ttfb,
            elapsed:      self.start.elapsed().as_secs_f64(),
            cfg:          &self.cfg,
            done,
        }
    }

    fn draw(&mut self, full: bool) {
        let stats = self.build_live_stats();
        let levels: Vec<usize> = self.level_counts.iter().map(|a| a.load(Ordering::Relaxed)).collect();
        let done = self.stop.load(Ordering::Relaxed);
        let state = self.build_dash_state(&levels, &stats, done);
        let lines = render_dashboard(state);
        if let Some(s) = self.screen.as_mut() {
            s.frame_start(full);
            for l in &lines { s.line(l); }
            s.frame_end();
        }
    }

    fn draw_simple(&self) {
        let fd = self.fast_done.load(Ordering::Relaxed);
        let dd = self.det_done.load(Ordering::Relaxed);
        let dt = self.det_total.load(Ordering::Relaxed);
        eprint!("\r[fast {}/{}] [detailed {}/{}]    ", fd, self.fast_total, dd, dt);
        io::stderr().flush().ok();
    }
}

// ============================================================================
//  MAIN
// ============================================================================

fn main() {
    let start = Instant::now();

    let (mut cfg, flags) = match parse_args() {
        Ok(c)  => c,
        Err(e) => {
            eprintln!("{}: error: {}", PROG, e);
            eprintln!("{}: try '--help'", PROG);
            std::process::exit(4);
        }
    };

    // Interactive prompts for any values not supplied via args (TTY only)
    interactive_prompt(&mut cfg, &flags);

    cfg = resolve_input(cfg);

    let done_set = if cfg.resume { load_done_set(&cfg) } else { HashSet::new() };
    let (proxies, invalid, lines_n) = load_proxies(&cfg, &done_set);
    let total = proxies.len();

    if cfg.dry_run {
        println!("{}: dry-run mode", PROG);
        println!("input   : {}", cfg.input.display());
        println!("lines   : {} (invalid: {})", lines_n, invalid);
        println!("valid   : {} unique proxies", total);
        let mut by: HashMap<&str, usize> = HashMap::new();
        for p in &proxies { *by.entry(p.protocol.as_str()).or_insert(0) += 1; }
        for (k, v) in by { println!("  {:<8} {}", k, v); }
        for (i, p) in proxies.iter().take(10).enumerate() {
            println!("  [{}] {}", i + 1, p.to_url());
        }
        if total > 10 { println!("  ... +{} more", total - 10); }
        return;
    }

    if total == 0 {
        eprintln!("{}: error: no valid proxy in input", PROG);
        std::process::exit(3);
    }

    for path in [&cfg.raw_good, &cfg.detailed_good, &cfg.nonetwork] {
        if !cfg.resume {
            if let Err(e) = File::create(path) {
                eprintln!("{}: cannot create {}: {}", PROG, path.display(), e);
                std::process::exit(1);
            }
        }
        if let Err(e) = OpenOptions::new().append(true).open(path) {
            eprintln!("{}: cannot open {} for append: {}", PROG, path.display(), e);
            std::process::exit(1);
        }
    }

    let mode = if cfg.no_dash { TermMode::Simple } else { detect_mode(cfg.force_simple) };

    // Build screen — with Win32 fallback to Simple if terminal too small
    let (mode, screen): (TermMode, Option<Box<dyn Screen>>) = match mode {
        TermMode::Ansi { color } => (
            TermMode::Ansi { color },
            Some(Box::new(AnsiScreen::new(color)) as Box<dyn Screen>),
        ),
        TermMode::Win32 { color } => {
            #[cfg(windows)]
            {
                match Win32Screen::new(color) {
                    Some(s) => (TermMode::Win32 { color }, Some(Box::new(s) as Box<dyn Screen>)),
                    None => {
                        if VERBOSE.load(Ordering::Relaxed) {
                            eprintln!("[v] win32 screen unavailable, falling back to simple");
                        }
                        (TermMode::Simple, None)
                    }
                }
            }
            #[cfg(not(windows))]
            {
                let _ = color;
                (TermMode::Simple, None)
            }
        }
        TermMode::Simple => (TermMode::Simple, None),
    };
    if VERBOSE.load(Ordering::Relaxed) { eprintln!("[v] term mode = {:?}", mode); }

    let fast_done     = Arc::new(AtomicUsize::new(0));
    let det_done      = Arc::new(AtomicUsize::new(0));
    let det_total     = Arc::new(AtomicUsize::new(0));
    let level_counts  = Arc::new((0..=N_LEVELS).map(|_| AtomicUsize::new(0)).collect::<Vec<_>>());
    let level_stats: Arc<LevelStats> = Arc::new(
        (0..=N_LEVELS).map(|_| Mutex::new((u64::MAX, 0u64, 0u64, 0u64))).collect()
    );
    let stop_progress = Arc::new(AtomicBool::new(false));

    let progress = Progress {
        fast_done:    Arc::clone(&fast_done),
        fast_total:   total,
        det_done:     Arc::clone(&det_done),
        det_total:    Arc::clone(&det_total),
        level_counts: Arc::clone(&level_counts),
        level_stats:  Arc::clone(&level_stats),
        stop:         Arc::clone(&stop_progress),
        start,
        cfg:          cfg.clone(),
        mode,
        screen,
    }.spawn();

    let mut worker_txs: Vec<mpsc::Sender<Proxy>> = Vec::new();
    let mut detailed_handles = Vec::with_capacity(cfg.detailed_threads);
    let detailed_timeout = cfg.eff_detailed_timeout();

    for _ in 0..cfg.detailed_threads {
        let (wtx, wrx) = mpsc::channel::<Proxy>();
        worker_txs.push(wtx);

        let dpath = cfg.detailed_good.clone();
        let npath = cfg.nonetwork.clone();
        let dd    = Arc::clone(&det_done);
        let lc    = Arc::clone(&level_counts);
        let ls    = Arc::clone(&level_stats);

        detailed_handles.push(thread::spawn(move || {
            let mut df = OpenOptions::new().create(true).append(true).open(&dpath)
                .expect("open detailed");
            let mut nf = OpenOptions::new().create(true).append(true).open(&npath)
                .expect("open nonetwork");
            for proxy in wrx {
                match detailed_check(&proxy, detailed_timeout) {
                    Ok((dur, level)) => {
                        let line = format!(
                            "{} - [{}ms] blocklv {}/{}\n",
                            proxy.to_url(), dur.as_millis(), level, N_LEVELS
                        );
                        let _ = df.write_all(line.as_bytes());
                        lc[level as usize].fetch_add(1, Ordering::Relaxed);

                        let ms = dur.as_millis() as u64;
                        if let Ok(mut s) = ls[level as usize].lock() {
                            if s.3 == 0 { s.0 = ms; s.1 = ms; }
                            else        { s.0 = s.0.min(ms); s.1 = s.1.max(ms); }
                            s.2 += ms;
                            s.3 += 1;
                        }
                    }
                    Err(_) => {
                        let line = format!("{}\n", proxy.to_url());
                        let _ = nf.write_all(line.as_bytes());
                    }
                }
                dd.fetch_add(1, Ordering::Relaxed);
            }
        }));
    }

    let raw_path  = cfg.raw_good.clone();
    let n_workers = worker_txs.len();
    let dt        = Arc::clone(&det_total);
    let (combined_tx, combined_rx) = mpsc::channel::<Proxy>();

    let dispatcher = thread::spawn(move || {
        let mut raw_file = OpenOptions::new().create(true).append(true).open(&raw_path)
            .expect("open raw");
        let mut idx = 0usize;
        for proxy in combined_rx {
            let _ = raw_file.write_all(format!("{}\n", proxy.to_url()).as_bytes());
            let _ = worker_txs[idx % n_workers].send(proxy);
            idx += 1;
            dt.fetch_add(1, Ordering::Relaxed);
        }
        idx
    });

    let queue        = Arc::new(proxies);
    let next_idx     = Arc::new(AtomicUsize::new(0));
    let n_threads    = cfg.fast_threads.min(queue.len()).max(1);
    let fast_timeout = cfg.eff_fast_timeout();

    let mut fast_handles = Vec::with_capacity(n_threads);
    for _ in 0..n_threads {
        let q  = Arc::clone(&queue);
        let ni = Arc::clone(&next_idx);
        let tx = combined_tx.clone();
        let fd = Arc::clone(&fast_done);

        fast_handles.push(thread::spawn(move || loop {
            let i = ni.fetch_add(1, Ordering::Relaxed);
            if i >= q.len() { break; }
            let proxy = &q[i];
            if let Some(real) = fast_check(proxy, fast_timeout) {
                let resolved = proxy.with_protocol(real);
                if tx.send(resolved).is_err() { break; }
            }
            fd.fetch_add(1, Ordering::Relaxed);
        }));
    }
    drop(combined_tx);

    for h in fast_handles     { let _ = h.join(); }
    let pass_count = dispatcher.join().unwrap_or(0);
    for h in detailed_handles { let _ = h.join(); }

    let stats = post_process_detailed(&cfg);

    stop_progress.store(true, Ordering::Relaxed);
    let _ = progress.join();

    let elapsed = start.elapsed();
    let raw_l = count_lines(&cfg.raw_good);
    let det_l = count_lines(&cfg.detailed_good);
    let non_l = count_lines(&cfg.nonetwork);

    println!();
    println!("done in {:.2}s", elapsed.as_secs_f64());
    if !stats.is_empty() {
        println!("ttfb by block level:");
        for (lv, cnt, min, avg, max) in &stats {
            println!("  L{}/{}: n={:<4}  min={:>5}ms  avg={:>5}ms  max={:>5}ms",
                     lv, N_LEVELS, cnt, min, avg, max);
        }
    }
    println!("in: {} | pass: {} | google: {} | dead: {}", total, pass_count, det_l, non_l);
    println!("raw: {} | detailed: {} | nonetwork: {}", raw_l, det_l, non_l);
    println!("out: {} / {} / {}", cfg.raw_good.display(), cfg.detailed_good.display(), cfg.nonetwork.display());

    std::process::exit(if det_l > 0 { 0 } else { 2 });
}

// ============================================================================
//  TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test] fn dash_height_formula() {
        assert_eq!(DASH_H, 27 + 2 * N_LEVELS);
        assert_eq!(DASH_H, 35);
    }

    #[test] fn dashboard_height_matches() {
        let cfg = Config::default();
        let levels = vec![0usize; N_LEVELS + 1];
        let lines = render_dashboard(DashState {
            fast_done: 0, fast_total: 1,
            det_done: 0, det_total: 1,
            level_counts: &levels, ttfb: &[],
            elapsed: 0.0, cfg: &cfg, done: false,
        });
        assert_eq!(lines.len(), DASH_H);
        for (i, l) in lines.iter().enumerate() {
            let w = l.text.chars().count();
            assert_eq!(w, DASH_W, "line {} = '{}' width {}", i + 1, l.text, w);
        }
    }

    #[test] fn box_line_exact_width() {
        assert_eq!(box_line("x").chars().count(), DASH_W);
        assert_eq!(box_line("").chars().count(), DASH_W);
        assert_eq!(box_line(&"a".repeat(100)).chars().count(), DASH_W);
    }

    #[test] fn bar_length() {
        for pct in [-10.0, 0.0, 25.0, 50.0, 99.9, 100.0, 200.0] {
            assert_eq!(bar(pct, 20).chars().count(), 20);
        }
    }

    #[test] fn bare_ip_port() {
        let p = parse_proxy("1.2.3.4:8080").unwrap();
        assert_eq!(p.protocol, Protocol::Unknown);
    }

    #[test] fn socks5_scheme() {
        let p = parse_proxy("socks5://1.2.3.4:9050").unwrap();
        assert_eq!(p.protocol, Protocol::Socks5);
    }

    #[test] fn http_auth() {
        let p = parse_proxy("http://admin:secret@1.2.3.4:8080").unwrap();
        assert_eq!(p.auth, Some(("admin".into(), "secret".into())));
    }

    #[test] fn base64_vectors() {
        assert_eq!(base64_encode(b"user:pass"), "dXNlcjpwYXNz");
    }

    #[test] fn colors_have_distinct_ansi() {
        let codes = [
            Color::Default.ansi(), Color::Cyan.ansi(), Color::Green.ansi(),
            Color::Yellow.ansi(), Color::Red.ansi(), Color::Gray.ansi(),
        ];
        let mut sorted: Vec<_> = codes.iter().collect();
        sorted.sort();
        sorted.dedup();
        assert_eq!(sorted.len(), codes.len());
    }

    // ---- new tests ----

    #[test] fn infer_port_to_protocol() {
        assert_eq!(infer_protocol_from_port(1080), Protocol::Socks5);
        assert_eq!(infer_protocol_from_port(80),   Protocol::Http);
        assert_eq!(infer_protocol_from_port(8080), Protocol::Http);
        assert_eq!(infer_protocol_from_port(3128), Protocol::Socks5);
        assert_eq!(infer_protocol_from_port(1),    Protocol::Socks5);
    }

    #[test] fn strip_quotes_variants() {
        assert_eq!(strip_quotes("/a/b"), "/a/b");
        assert_eq!(strip_quotes("\"/a/b\""), "/a/b");
        assert_eq!(strip_quotes("'/a/b'"), "/a/b");
        assert_eq!(strip_quotes("  \"'/a/b'\"  "), "/a/b");
        assert_eq!(strip_quotes(""), "");
    }

    #[test] fn read_list_comma() {
        assert_eq!(read_list("a,b,c"), vec!["a", "b", "c"]);
        assert_eq!(read_list(" a , b ,c "), vec!["a", "b", "c"]);
        assert_eq!(read_list(""), Vec::<String>::new());
        assert_eq!(read_list("only"), vec!["only"]);
    }

    #[test] fn auth_combo_expansion() {
        let empty: Vec<String> = vec![];
        assert_eq!(auth_combos(&empty, &empty).len(), 1);

        let u = vec!["u1".to_string()];
        let p = vec!["p1".to_string(), "p2".to_string()];
        let combos = auth_combos(&u, &p);
        assert_eq!(combos.len(), 2);
        assert_eq!(combos[0], Some(("u1".into(), "p1".into())));
        assert_eq!(combos[1], Some(("u1".into(), "p2".into())));
    }
}
