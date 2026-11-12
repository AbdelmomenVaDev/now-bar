//! The system's own cards: RAM and CPU alerts, Proton VPN, the internet, alarms and the Syrian
//! pound's rate. Each is a card of its own (an item of the live set with the id `sys:…`) while its
//! setting is on and its condition holds. The pure parts (thresholds, alarm times, the rate scrape)
//! come first, the samplers (Windows calls) after them; `app.rs` shows what [`SysCards::tick`] says.

use std::collections::{HashSet, VecDeque};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Mutex;
use std::time::Duration;

use crate::activities::api::Button;
use crate::activities::live::LiveState;
use crate::i18n::{decimal1, n_, percent, tr, trf};
use crate::settings::Settings;

/// The ids of the system cards in the live set.
pub const ID_RAM: &str = "sys:ram";
pub const ID_CPU: &str = "sys:cpu";
pub const ID_VPN: &str = "sys:vpn";
pub const ID_NET: &str = "sys:net";
pub const ID_ALARM: &str = "sys:alarm";
pub const ID_SYP: &str = "sys:syp";
pub const IDS: [&str; 6] = [ID_RAM, ID_CPU, ID_VPN, ID_NET, ID_ALARM, ID_SYP];

/// RAM: the card comes above 80 % and goes at 79 %.
pub const RAM_ON_ABOVE: u8 = 80;
pub const RAM_OFF_AT: u8 = 79;
/// CPU: the card comes above 60 % and goes at 59 % (of the last three readings' average).
pub const CPU_ON_ABOVE: u8 = 60;
pub const CPU_OFF_AT: u8 = 59;

/// A new VPN connection leads the stack this long, then waits behind the music.
const VPN_FRONT_MS: u64 = 6_000;
/// "Back online" stays this long.
const NET_BACK_MS: u64 = 5_000;
/// An alarm rings this long at most, repeating its sound.
const RING_MAX_MS: u64 = 120_000;
/// ...and plays its sound again this often (the sound itself lasts about six seconds).
const RING_REPEAT_MS: u64 = 8_000;
/// "Ertele" (snooze) puts the alarm off this long.
pub const SNOOZE_MIN: u64 = 5;

pub const RAM_ACCENT: (u8, u8, u8) = (0xE0, 0x5A, 0x4F);
pub const CPU_ACCENT: (u8, u8, u8) = (0xF0, 0x8A, 0x2B);
pub const VPN_ACCENT: (u8, u8, u8) = (0x6D, 0x4A, 0xFF);
pub const NET_ACCENT: (u8, u8, u8) = (0x2E, 0xA0, 0xF0);
pub const ALARM_ACCENT: (u8, u8, u8) = (0xF2, 0xB1, 0x2E);
pub const SYP_ACCENT: (u8, u8, u8) = (0x2F, 0xB3, 0x6B);

/// A reading above `on_above` switches a card on, one at or below `off_at` switches it off, and
/// in between it stays as it was (so a value hovering at the line doesn't flicker).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Gate(bool);

impl Gate {
    pub fn update(&mut self, value: u8, on_above: u8, off_at: u8) -> bool {
        if self.0 {
            if value <= off_at {
                self.0 = false;
            }
        } else if value > on_above {
            self.0 = true;
        }
        self.0
    }

    pub fn reset(&mut self) {
        self.0 = false;
    }
}

// ---- alarms --------------------------------------------------------------------------------

/// One alarm of the settings' list: a time of day, every day, and what to call it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Alarm {
    /// Minutes after midnight.
    pub minute: u16,
    pub label: String,
}

/// Arabic-Indic and Persian digits as Latin ones, the Arabic comma and semicolon as commas.
fn plain(text: &str) -> String {
    text.chars()
        .map(|c| match c {
            '\u{0660}'..='\u{0669}' => char::from(b'0' + (c as u32 - 0x0660) as u8),
            '\u{06F0}'..='\u{06F9}' => char::from(b'0' + (c as u32 - 0x06F0) as u8),
            '،' | '؛' | ';' | '\n' | '\r' => ',',
            '：' | '٫' => ':',
            c => c,
        })
        .collect()
}

/// "07:00 Uyan, 13:30" → two alarms. Each is a time `H:MM` or `HH:MM` and, after it, an optional
/// label; entries that aren't a time are skipped; at most 12.
pub fn parse_alarms(text: &str) -> Vec<Alarm> {
    let mut alarms = Vec::new();
    for entry in plain(text).split(',') {
        let entry = entry.trim();
        let (time, label) = entry.split_once(char::is_whitespace).unwrap_or((entry, ""));
        let Some((h, m)) = time.split_once(':') else { continue };
        let (Ok(h), Ok(m)) = (h.trim().parse::<u16>(), m.trim().parse::<u16>()) else { continue };
        if h < 24 && m < 60 && !alarms.iter().any(|a: &Alarm| a.minute == h * 60 + m) {
            alarms.push(Alarm { minute: h * 60 + m, label: label.trim().chars().take(40).collect() });
        }
        if alarms.len() == 12 {
            break;
        }
    }
    alarms
}

pub fn clock(minute: u16) -> String {
    format!("{:02}:{:02}", minute / 60, minute % 60)
}

/// The alarms whose minute is `now_minute` on `day` and haven't rung for it yet; `rung` remembers
/// (and forgets other days).
pub fn due(alarms: &[Alarm], day: i64, now_minute: u16, rung: &mut Vec<(i64, u16)>) -> Vec<Alarm> {
    rung.retain(|(d, _)| *d == day);
    let mut out = Vec::new();
    for a in alarms.iter().filter(|a| a.minute == now_minute) {
        if !rung.contains(&(day, a.minute)) {
            rung.push((day, a.minute));
            out.push(a.clone());
        }
    }
    out
}

// ---- the rate ------------------------------------------------------------------------------

/// The dollar's rate in Syrian pounds, as sp-today.com gives it for Damascus: whole *old* pounds
/// (the site also shows the new pound, which is a hundredth of an old one).
#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct Rate {
    pub buy: f64,
    pub sell: f64,
    /// The day's change in percent.
    pub change: f64,
    /// When it was fetched (Unix seconds).
    pub at: i64,
}

use serde::{Deserialize, Serialize};

pub const RATE_URL: &str = "https://sp-today.com/en";

/// The number after `key` in `text`.
fn number_after(text: &str, key: &str) -> Option<f64> {
    let rest = &text[text.find(key)? + key.len()..];
    let end = rest.find(|c: char| !(c.is_ascii_digit() || c == '.' || c == '-')).unwrap_or(rest.len());
    rest[..end].parse().ok()
}

/// The USD rate in the page's embedded data (`"code":"USD" … "damascus":{"buy":14625,"sell":14675,
/// "change":-0.17`); `None` when the page isn't shaped so.
pub fn parse_rate(page: &str, at: i64) -> Option<Rate> {
    // The data sits in a script as a JSON string: its quotes arrive escaped.
    let page = page.replace("\\\"", "\"");
    let usd = &page[page.find("\"code\":\"USD\"")?..];
    // Only this currency's block: it ends where the next currency's starts.
    let block = &usd[..usd[12..].find("\"code\":\"").map_or(usd.len(), |i| i + 12)];
    let city = &block[block.find("\"damascus\":{")?..];
    let (buy, sell) = (number_after(city, "\"buy\":")?, number_after(city, "\"sell\":")?);
    let change = number_after(city, "\"change\":").unwrap_or(0.0);
    (buy > 0.0 && sell >= buy).then_some(Rate { buy, sell, change, at })
}

/// "146.75": the new pound's figure for `old` (a hundredth), two decimals.
pub fn new_pounds(old: f64) -> String {
    let v = old / 100.0;
    if crate::i18n::lang() == crate::i18n::Language::Turkish {
        format!("{v:.2}").replace('.', ",")
    } else {
        format!("{v:.2}")
    }
}

/// "14,675": whole old pounds with thousands separated.
pub fn old_pounds(old: f64) -> String {
    let digits = format!("{}", old.round() as i64);
    let mut out = String::new();
    for (i, c) in digits.chars().rev().enumerate() {
        if i > 0 && i % 3 == 0 {
            out.push(',');
        }
        out.push(c);
    }
    out.chars().rev().collect()
}

fn rate_cache() -> Option<std::path::PathBuf> {
    std::env::var_os("LOCALAPPDATA").map(|d| std::path::PathBuf::from(d).join(crate::DIR).join("rate.json"))
}

#[derive(Default)]
struct RateSlot {
    rate: Option<Rate>,
    busy: bool,
    failed: bool,
    loaded: bool,
}

static RATE: Mutex<RateSlot> = Mutex::new(RateSlot { rate: None, busy: false, failed: false, loaded: false });

/// What a fetch is doing now: the last rate, whether one is under way, whether the last failed.
pub fn rate_now() -> (Option<Rate>, bool, bool) {
    let mut slot = RATE.lock().unwrap_or_else(|e| e.into_inner());
    if !slot.loaded {
        slot.loaded = true;
        slot.rate = rate_cache().and_then(|p| std::fs::read_to_string(p).ok()).and_then(|t| serde_json::from_str(&t).ok());
    }
    (slot.rate, slot.busy, slot.failed)
}

/// Asks sp-today.com now, off the UI thread (the card's "Güncelle"): the answer lands in
/// [`rate_now`]. Nothing asks by itself.
pub fn fetch_rate() {
    {
        let mut slot = RATE.lock().unwrap_or_else(|e| e.into_inner());
        if slot.busy {
            return;
        }
        slot.busy = true;
    }
    std::thread::spawn(|| {
        let got = crate::platform::http::get_text(RATE_URL).ok().and_then(|page| parse_rate(&page, unix_secs()));
        let mut slot = RATE.lock().unwrap_or_else(|e| e.into_inner());
        slot.busy = false;
        match got {
            Some(rate) => {
                slot.rate = Some(rate);
                slot.failed = false;
                if let (Some(path), Ok(json)) = (rate_cache(), serde_json::to_string(&rate)) {
                    let _ = std::fs::create_dir_all(path.parent().unwrap_or(std::path::Path::new(".")));
                    let _ = std::fs::write(path, json);
                }
            }
            None => slot.failed = true,
        }
    });
}

fn unix_secs() -> i64 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs() as i64).unwrap_or(0)
}

// ---- samplers ------------------------------------------------------------------------------

/// Memory in use, percent.
pub fn ram_percent() -> Option<u8> {
    use windows::Win32::System::SystemInformation::{GlobalMemoryStatusEx, MEMORYSTATUSEX};
    let mut m = MEMORYSTATUSEX { dwLength: std::mem::size_of::<MEMORYSTATUSEX>() as u32, ..Default::default() };
    unsafe { GlobalMemoryStatusEx(&mut m).ok()? };
    Some(m.dwMemoryLoad.min(100) as u8)
}

/// Busy percent between two readings of (idle, total) ticks.
pub fn cpu_between(before: (u64, u64), after: (u64, u64)) -> Option<u8> {
    let total = after.1.checked_sub(before.1).filter(|t| *t > 0)?;
    let idle = after.0.saturating_sub(before.0).min(total);
    Some(((total - idle) * 100 / total) as u8)
}

/// The processor's load, averaged over the last three readings.
#[derive(Default)]
pub struct CpuMeter {
    last: Option<(u64, u64)>,
    recent: VecDeque<u8>,
}

impl CpuMeter {
    /// Reads the counters now; the average once there is a reading to compare with.
    pub fn sample(&mut self) -> Option<u8> {
        use windows::Win32::Foundation::FILETIME;
        use windows::Win32::System::Threading::GetSystemTimes;
        let ticks = |f: FILETIME| (f.dwHighDateTime as u64) << 32 | f.dwLowDateTime as u64;
        let (mut idle, mut kernel, mut user) = (FILETIME::default(), FILETIME::default(), FILETIME::default());
        unsafe { GetSystemTimes(Some(&mut idle), Some(&mut kernel), Some(&mut user)).ok()? };
        // The kernel's time includes the idle's.
        let now = (ticks(idle), ticks(kernel) + ticks(user));
        let before = self.last.replace(now)?;
        self.push(cpu_between(before, now)?)
    }

    fn push(&mut self, pct: u8) -> Option<u8> {
        self.recent.push_back(pct);
        if self.recent.len() > 3 {
            self.recent.pop_front();
        }
        Some((self.recent.iter().map(|v| *v as u32).sum::<u32>() / self.recent.len() as u32) as u8)
    }

    pub fn reset(&mut self) {
        *self = CpuMeter::default();
    }
}

/// What the network worker found.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct NetState {
    /// The worker has looked at least once.
    pub known: bool,
    pub online: bool,
    /// The Proton VPN adapter's name while it is up.
    pub vpn: Option<String>,
}

static NET: Mutex<NetState> = Mutex::new(NetState { known: false, online: false, vpn: None });
static NET_WANTED: AtomicBool = AtomicBool::new(false);
static NET_STARTED: AtomicBool = AtomicBool::new(false);

/// Starts the network worker (once) and tells it whether anything wants its answers now.
pub fn net_wanted(wanted: bool) {
    NET_WANTED.store(wanted, Ordering::Relaxed);
    if wanted && !NET_STARTED.swap(true, Ordering::Relaxed) {
        std::thread::spawn(|| loop {
            if NET_WANTED.load(Ordering::Relaxed) {
                let state = NetState { known: true, online: internet_up(), vpn: proton_adapter() };
                *NET.lock().unwrap_or_else(|e| e.into_inner()) = state;
            }
            std::thread::sleep(Duration::from_secs(4));
        });
    }
}

pub fn net_state() -> NetState {
    NET.lock().unwrap_or_else(|e| e.into_inner()).clone()
}

/// Whether a well-known address takes a connection: any of Cloudflare's, Google's or Quad9's.
fn internet_up() -> bool {
    use std::net::{SocketAddr, TcpStream};
    ["1.1.1.1:443", "8.8.8.8:443", "9.9.9.9:443"]
        .iter()
        .filter_map(|a| a.parse::<SocketAddr>().ok())
        .any(|a| TcpStream::connect_timeout(&a, Duration::from_millis(1500)).is_ok())
}

/// The name of an adapter of Proton VPN's that is up (its WireGuard or OpenVPN tunnel).
fn proton_adapter() -> Option<String> {
    use windows::Win32::NetworkManagement::IpHelper::{GetAdaptersAddresses, GAA_FLAG_SKIP_ANYCAST, GAA_FLAG_SKIP_DNS_SERVER, GAA_FLAG_SKIP_MULTICAST, IP_ADAPTER_ADDRESSES_LH};
    use windows::Win32::NetworkManagement::Ndis::IfOperStatusUp;
    let flags = GAA_FLAG_SKIP_ANYCAST | GAA_FLAG_SKIP_MULTICAST | GAA_FLAG_SKIP_DNS_SERVER;
    let mut len = 16_384u32;
    let mut buf: Vec<u64> = Vec::new();
    for _ in 0..3 {
        buf = vec![0u64; (len as usize).div_ceil(8)];
        let rc = unsafe { GetAdaptersAddresses(0, flags, None, Some(buf.as_mut_ptr() as *mut IP_ADAPTER_ADDRESSES_LH), &mut len) };
        match rc {
            0 => break,
            111 => continue,
            _ => return None,
        }
    }
    let mut p = buf.as_ptr() as *const IP_ADAPTER_ADDRESSES_LH;
    while !p.is_null() {
        let a = unsafe { &*p };
        let text = |s: windows::core::PWSTR| if s.is_null() { String::new() } else { unsafe { s.to_string() }.unwrap_or_default() };
        let (name, desc) = (text(a.FriendlyName), text(a.Description));
        if a.OperStatus == IfOperStatusUp && (name.to_lowercase().contains("proton") || desc.to_lowercase().contains("proton")) {
            return Some(name);
        }
        p = a.Next;
    }
    None
}

// ---- the cards -----------------------------------------------------------------------------

/// One card as it should be now.
#[derive(Clone, Debug, PartialEq)]
pub struct Card {
    pub id: &'static str,
    pub title: String,
    pub text: String,
    /// The pill's and the card's right-hand figure.
    pub status: String,
    pub progress: Option<u8>,
    /// `Wait` leads the stack (and rings the pill), `Run` waits behind the music, `Done` is a
    /// moment.
    pub state: LiveState,
    pub glyph: char,
    pub accent: (u8, u8, u8),
    pub buttons: Vec<Button>,
}

/// What a tick says: the cards that exist now, and whether an alarm's sound plays.
#[derive(Debug, Default)]
pub struct Tick {
    pub cards: Vec<Card>,
    pub ring: bool,
}

/// The cards' state between ticks.
#[derive(Default)]
pub struct SysCards {
    ram: Gate,
    cpu: Gate,
    meter: CpuMeter,
    cpu_pct: Option<u8>,
    ram_pct: Option<u8>,
    vpn_since: Option<u64>,
    was_online: Option<bool>,
    back_at: Option<u64>,
    rung: Vec<(i64, u16)>,
    /// Alarms ringing now (what rang, since when, when its sound last played).
    ringing: Option<(Alarm, u64, u64)>,
    /// Snoozed: the alarm and the Unix second it rings again.
    snoozed: Option<(Alarm, i64)>,
    /// Cards the user closed: they stay away until their condition ends.
    dismissed: HashSet<&'static str>,
}

impl SysCards {
    /// `now`: GetTickCount64 ms; `unix`: Unix seconds; `utc_offset_s`: the local time's offset.
    pub fn tick(&mut self, s: &Settings, now: u64, unix: i64, utc_offset_s: i64) -> Tick {
        let mut cards: Vec<Card> = Vec::new();
        let mut ring = false;

        // RAM and CPU.
        if s.sys_ram {
            self.ram_pct = ram_percent();
        } else {
            self.ram_pct = None;
            self.ram.reset();
        }
        let ram_on = match self.ram_pct {
            Some(v) => self.ram.update(v, RAM_ON_ABOVE, RAM_OFF_AT),
            None => false,
        };
        if s.sys_cpu {
            if let Some(v) = self.meter.sample() {
                self.cpu_pct = Some(v);
            }
        } else {
            self.meter.reset();
            self.cpu_pct = None;
            self.cpu.reset();
        }
        let cpu_on = match self.cpu_pct {
            Some(v) => self.cpu.update(v, CPU_ON_ABOVE, CPU_OFF_AT),
            None => false,
        };
        if let (true, Some(v)) = (ram_on, self.ram_pct) {
            cards.push(Card {
                id: ID_RAM,
                title: "RAM".into(),
                text: tr("Bellek çok kullanılıyor").into(),
                status: percent(v),
                progress: Some(v),
                state: LiveState::Wait,
                glyph: '\u{EEA1}',
                accent: RAM_ACCENT,
                buttons: Vec::new(),
            });
        }
        if let (true, Some(v)) = (cpu_on, self.cpu_pct) {
            cards.push(Card {
                id: ID_CPU,
                title: "CPU".into(),
                text: tr("İşlemci yoğun çalışıyor").into(),
                status: percent(v),
                progress: Some(v),
                state: LiveState::Wait,
                glyph: '\u{E950}',
                accent: CPU_ACCENT,
                buttons: Vec::new(),
            });
        }

        // The network: Proton VPN, and the internet itself.
        net_wanted(s.sys_vpn || s.sys_net);
        let net = net_state();
        let vpn_up = s.sys_vpn && net.known && net.vpn.is_some();
        match (vpn_up, self.vpn_since) {
            (true, None) => self.vpn_since = Some(now),
            (false, Some(_)) => self.vpn_since = None,
            _ => {}
        }
        if let (true, Some(since)) = (vpn_up, self.vpn_since) {
            cards.push(Card {
                id: ID_VPN,
                title: "Proton VPN".into(),
                text: tr("VPN tüneli açık").into(),
                status: tr("Bağlı").into(),
                progress: None,
                state: if now.saturating_sub(since) < VPN_FRONT_MS { LiveState::Wait } else { LiveState::Run },
                glyph: '\u{E705}',
                accent: VPN_ACCENT,
                buttons: Vec::new(),
            });
        }
        if s.sys_net && net.known {
            match (self.was_online, net.online) {
                (Some(false), true) => self.back_at = Some(now),
                (_, false) => self.back_at = None,
                _ => {}
            }
            self.was_online = Some(net.online);
            let card = |state, status: &str, text: &str, glyph| Card {
                id: ID_NET,
                title: tr("İnternet").into(),
                text: tr(text).into(),
                status: tr(status).into(),
                progress: None,
                state,
                glyph,
                accent: NET_ACCENT,
                buttons: Vec::new(),
            };
            if !net.online {
                cards.push(card(LiveState::Wait, n_("Bağlı değil"), n_("İnternet bağlantısı kesildi"), '\u{EB5E}'));
            } else if self.back_at.is_some_and(|at| now.saturating_sub(at) < NET_BACK_MS) {
                cards.push(card(LiveState::Done, n_("Bağlandı"), n_("İnternet geri geldi"), '\u{E701}'));
            }
        } else {
            self.was_online = None;
            self.back_at = None;
        }

        // Alarms.
        if s.sys_alarm {
            let (local, alarms) = (unix + utc_offset_s, parse_alarms(&s.alarm_times));
            let (day, minute) = (local.div_euclid(86_400), (local.rem_euclid(86_400) / 60) as u16);
            let mut rings = due(&alarms, day, minute, &mut self.rung);
            if let Some((a, at)) = self.snoozed.clone() {
                if unix >= at {
                    self.snoozed = None;
                    rings.push(a);
                }
            }
            if let Some(a) = rings.into_iter().next() {
                self.ringing = Some((a, now, now));
                self.dismissed.remove(ID_ALARM);
                ring = true;
            }
            if let Some((a, since, last)) = self.ringing.clone() {
                if now.saturating_sub(since) >= RING_MAX_MS {
                    self.ringing = None;
                } else {
                    if now.saturating_sub(last) >= RING_REPEAT_MS {
                        self.ringing = Some((a.clone(), since, now));
                        ring = true;
                    }
                    cards.push(Card {
                        id: ID_ALARM,
                        title: if a.label.is_empty() { tr("Alarm").into() } else { a.label.clone() },
                        text: trf("{} · alarm çalıyor", &[&clock(a.minute)]),
                        status: clock(a.minute),
                        progress: None,
                        state: LiveState::Wait,
                        glyph: '\u{EA8F}',
                        accent: ALARM_ACCENT,
                        buttons: vec![
                            Button { id: "snooze".into(), label: trf("Ertele · {} dk", &[&SNOOZE_MIN]), uri: None },
                            Button { id: "stop".into(), label: tr("Durdur").into(), uri: None },
                        ],
                    });
                }
            }
        } else {
            self.ringing = None;
            self.snoozed = None;
        }

        // The rate: a card with what was last fetched; its button fetches again.
        if s.sys_syp {
            let (rate, busy, failed) = rate_now();
            let when = rate.map(|r| crate::activities::weather::clock_text(r.at + utc_offset_s).0).unwrap_or_default();
            let (status, text) = match rate {
                Some(r) if busy => (new_pounds(r.sell), tr("Güncelleniyor…").to_string()),
                Some(r) => {
                    let line = trf("Alış {} · eski lirayla {}–{}", &[&new_pounds(r.buy), &old_pounds(r.buy), &old_pounds(r.sell)]);
                    let line = if failed { format!("{} · {}", tr("Güncellenemedi"), when) } else { format!("{line} · {when}") };
                    (new_pounds(r.sell), line)
                }
                None if busy => ("…".into(), tr("Güncelleniyor…").to_string()),
                None if failed => ("—".into(), tr("Güncellenemedi").to_string()),
                None => ("—".into(), tr("Kuru almak için Güncelle'ye bas").to_string()),
            };
            let change = rate.map(|r| format!("{}{}%", if r.change > 0.0 { "+" } else { "" }, decimal1(r.change)));
            cards.push(Card {
                id: ID_SYP,
                title: match change {
                    Some(c) if !busy => format!("{} · {c}", tr("Dolar · Suriye lirası")),
                    _ => tr("Dolar · Suriye lirası").into(),
                },
                text,
                status,
                progress: None,
                state: LiveState::Run,
                glyph: '\u{E9D2}',
                accent: SYP_ACCENT,
                buttons: vec![Button { id: "refresh".into(), label: tr("Güncelle").into(), uri: None }],
            });
        }

        // A closed card stays away until its condition ends.
        let live: HashSet<&'static str> = cards.iter().map(|c| c.id).collect();
        self.dismissed.retain(|id| live.contains(id));
        cards.retain(|c| !self.dismissed.contains(c.id));
        Tick { cards, ring }
    }

    /// The user closed (or muted) a card.
    pub fn dismiss(&mut self, id: &str) {
        let Some(id) = IDS.iter().find(|i| **i == id) else { return };
        if *id == ID_ALARM {
            self.ringing = None;
            return;
        }
        self.dismissed.insert(id);
    }

    /// A card's button; `unix`: now in Unix seconds.
    pub fn button(&mut self, id: &str, button: &str, unix: i64) {
        match (id, button) {
            (ID_ALARM, "snooze") => {
                if let Some((a, _, _)) = self.ringing.take() {
                    self.snoozed = Some((a, unix + SNOOZE_MIN as i64 * 60));
                }
            }
            (ID_ALARM, "stop") => self.ringing = None,
            (ID_SYP, "refresh") => fetch_rate(),
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_gate_comes_above_the_line_and_goes_at_the_one_below() {
        let mut g = Gate::default();
        assert!(!g.update(80, RAM_ON_ABOVE, RAM_OFF_AT), "80 is not above 80");
        assert!(g.update(81, RAM_ON_ABOVE, RAM_OFF_AT));
        assert!(g.update(80, RAM_ON_ABOVE, RAM_OFF_AT), "between the two: stays");
        assert!(!g.update(79, RAM_ON_ABOVE, RAM_OFF_AT), "79: gone");
        assert!(!g.update(80, RAM_ON_ABOVE, RAM_OFF_AT), "and it needs more than 80 to come back");
    }

    #[test]
    fn the_cpu_line_is_sixty() {
        let mut g = Gate::default();
        assert!(!g.update(60, CPU_ON_ABOVE, CPU_OFF_AT));
        assert!(g.update(61, CPU_ON_ABOVE, CPU_OFF_AT));
        assert!(!g.update(59, CPU_ON_ABOVE, CPU_OFF_AT));
    }

    #[test]
    fn the_cpu_is_the_busy_share_of_the_ticks() {
        assert_eq!(cpu_between((100, 1_000), (400, 2_000)), Some(70));
        assert_eq!(cpu_between((100, 1_000), (100, 1_000)), None, "no time passed");
        assert_eq!(cpu_between((0, 0), (5_000, 1_000)), Some(0), "idle can't exceed the total");
        let mut m = CpuMeter::default();
        assert_eq!(m.push(90), Some(90));
        assert_eq!(m.push(30), Some(60));
        assert_eq!(m.push(60), Some(60));
        assert_eq!(m.push(0), Some(30), "the oldest reading leaves");
    }

    #[test]
    fn alarms_are_times_with_labels() {
        let a = parse_alarms("07:00 Uyan, 13:30\n٠٦:١٥ صلاة، 7:5, 25:00 x, abc, 07:00 again");
        assert_eq!(
            a,
            vec![
                Alarm { minute: 420, label: "Uyan".into() },
                Alarm { minute: 810, label: String::new() },
                Alarm { minute: 375, label: "صلاة".into() },
                Alarm { minute: 425, label: String::new() },
            ],
            "a second 07:00 is skipped, 25:00 and abc aren't times"
        );
        assert_eq!(clock(425), "07:05");
        assert!(parse_alarms("").is_empty());
    }

    #[test]
    fn an_alarm_rings_once_a_day() {
        let alarms = parse_alarms("07:00");
        let mut rung = Vec::new();
        assert!(due(&alarms, 20_000, 419, &mut rung).is_empty());
        assert_eq!(due(&alarms, 20_000, 420, &mut rung).len(), 1);
        assert!(due(&alarms, 20_000, 420, &mut rung).is_empty(), "the same minute again");
        assert_eq!(due(&alarms, 20_001, 420, &mut rung).len(), 1, "tomorrow");
        assert_eq!(rung, vec![(20_001, 420)], "yesterday is forgotten");
    }

    #[test]
    fn the_rate_comes_from_the_pages_data() {
        let page = r#"x self.__next_f.push([1,"5:[\"$\",{\"rates\":[{\"code\":\"USD\",\"slug\":\"us-dollar\",\"cities\":{\"damascus\":{\"buy\":14625,\"sell\":14675,\"change\":-0.17,\"prev_close\":14650},\"alhasakah\":{\"buy\":14700,\"sell\":14800}},\"updated_at\":\"t\"},{\"code\":\"EUR\",\"cities\":{\"damascus\":{\"buy\":16090,\"sell\":16280,\"change\":-0.19}}}]"#;
        let r = parse_rate(page, 5).expect("a rate");
        assert_eq!((r.buy, r.sell, r.change, r.at), (14625.0, 14675.0, -0.17, 5));
        crate::i18n::in_language(crate::i18n::Language::English, || {
            assert_eq!((new_pounds(r.sell), old_pounds(r.sell)), ("146.75".to_string(), "14,675".to_string()));
        });
        assert!(parse_rate("<html>nothing</html>", 0).is_none());
        let eur_only = page.replace("USD", "XXX");
        assert!(parse_rate(&eur_only, 0).is_none(), "no USD block");
    }

    #[test]
    fn a_closed_card_stays_away_until_its_condition_ends() {
        let mut s = SysCards::default();
        s.dismissed.insert(ID_RAM);
        // The condition holds: still closed.
        let held: HashSet<&'static str> = [ID_RAM].into_iter().collect();
        s.dismissed.retain(|id| held.contains(id));
        assert!(s.dismissed.contains(ID_RAM));
        // It ended: forgotten, so the next time it comes.
        let none: HashSet<&'static str> = HashSet::new();
        s.dismissed.retain(|id| none.contains(id));
        assert!(s.dismissed.is_empty());
        s.dismiss("sys:nothing");
        assert!(s.dismissed.is_empty());
    }

    /// The Windows calls and the site, for real: `cargo t -p pebbly sysmon_live -- --ignored --nocapture`.
    #[test]
    #[ignore]
    fn sysmon_live() {
        println!("ram: {:?}", ram_percent());
        let mut meter = CpuMeter::default();
        println!("cpu first: {:?}", meter.sample());
        std::thread::sleep(Duration::from_millis(1000));
        println!("cpu then: {:?}", meter.sample());
        println!("internet: {}", internet_up());
        println!("proton adapter: {:?}", proton_adapter());
        let page = crate::platform::http::get_text(RATE_URL).expect("the page");
        let rate = parse_rate(&page, 0);
        println!("rate: {rate:?}");
        assert!(rate.is_some());
    }

    #[test]
    fn snooze_rings_again_later() {
        let mut s = SysCards::default();
        s.ringing = Some((Alarm { minute: 420, label: "x".into() }, 0, 0));
        s.button(ID_ALARM, "snooze", 1_000);
        assert!(s.ringing.is_none());
        assert_eq!(s.snoozed.as_ref().map(|(_, at)| *at), Some(1_000 + SNOOZE_MIN as i64 * 60));
    }
}
