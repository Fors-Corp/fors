//! The host module (design §5.8 mechanism 2, §5.9, §7.2; F8): the ONLY
//! place in `fors-interp` that reads a real clock or real entropy, and the
//! response log that makes those reads recordable and replayable.
//!
//! Every capability response the interpreter can observe goes through an
//! [`Oracle`]:
//!
//! - `clock_mono` (`time.Clock.now`, ch10 R45): monotonic nanoseconds from an
//!   unspecified origin (this process's first read). Successive readings are
//!   made STRICTLY increasing (`max(real, previous + 1)`), which is still a
//!   monotonic clock and makes the corpus's reversed-pair test
//!   (`time-since-reversed-trap`) independent of the host clock's tick size.
//! - `clock_wall` (`time.Clock.wall`): UTC nanoseconds since the Unix epoch.
//! - `entropy_u64` (`rand.Rng.u64`/`fill`, ch10 R47): eight bytes of host
//!   entropy (`/dev/urandom`), little-endian.
//!
//! **Determinism (design §7.2).** In live mode every response is appended to
//! the log; `--oracle-record` writes that log ([`Oracle::log_bytes`]). In
//! replay mode ([`Oracle::replay`]) every response comes from the log, in
//! order, and NOTHING real is read: the live readers refuse with
//! [`OracleError::LiveReadUnderReplay`] and [`HostCounters::live_reads`]
//! stays 0, which the replay tests assert. A request whose kind differs from
//! the next logged entry, a request past the log's end, and a log with
//! entries left over when the run ends are each a NAMED [`OracleError`] —
//! never a silent divergence.
//!
//! **Record format** (byte-exact, line-oriented, every line `\n`-ended):
//!
//! ```text
//! fors-oracle-record 1
//! mono <u64 decimal>
//! wall <i64 decimal>
//! entropy <16 lowercase hex digits: the u64 drawn>
//! ```
//!
//! Every `mono` line's value is strictly greater than the previous `mono`
//! line's (the live oracle guarantees it; the parser refuses a record that
//! breaks it, so a replayed clock can never run backwards).
//!
//! The file system and the network have no live behaviour in M1 (design
//! §5.8: the corpus needs only their types, name validation and error
//! enums): reaching their host door is the interpreter's named refusal
//! (`InterpError::HostRefused`), counted in [`HostCounters::fs_host_calls`]
//! / [`HostCounters::net_host_calls`] — which is how
//! `fs_name_validation_issues_no_syscall` proves a rejected name never got
//! that far.

/// The record format's first line.
pub const RECORD_HEADER: &str = "fors-oracle-record 1";

/// One capability response.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum HostEvent {
    Mono(u64),
    Wall(i64),
    Entropy(u64),
}

impl HostEvent {
    fn kind(self) -> &'static str {
        match self {
            HostEvent::Mono(_) => "mono",
            HostEvent::Wall(_) => "wall",
            HostEvent::Entropy(_) => "entropy",
        }
    }

    /// The response's 64 bits (a `wall` reading as its two's complement).
    fn bits(self) -> u64 {
        match self {
            HostEvent::Mono(v) | HostEvent::Entropy(v) => v,
            HostEvent::Wall(v) => v as u64,
        }
    }

    pub(crate) fn line(self) -> String {
        match self {
            HostEvent::Mono(v) => format!("mono {v}\n"),
            HostEvent::Wall(v) => format!("wall {v}\n"),
            HostEvent::Entropy(v) => format!("entropy {v:016x}\n"),
        }
    }
}

/// A named host/oracle failure. Never a trap (ch02 R15's kinds are closed)
/// and never silent.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum OracleError {
    /// The replay log is not in the record format: `line` is 1-based.
    Malformed { line: usize, text: String },
    /// Replay: the program asked for `found` where the log's entry `index`
    /// (0-based) is `expected` — the run diverged from the recorded one.
    Mismatch {
        index: usize,
        expected: &'static str,
        found: &'static str,
    },
    /// Replay: the program asked for `wanted` after the log's `index`
    /// entries were all consumed.
    Exhausted { index: usize, wanted: &'static str },
    /// Replay: the run ended having consumed `consumed` of the log's
    /// `total` entries.
    Unconsumed { consumed: usize, total: usize },
    /// A live reader was reached in replay mode (structurally impossible;
    /// reported, never performed).
    LiveReadUnderReplay(&'static str),
    /// The host has no working entropy source (ch10 R47: then `main` never
    /// starts).
    EntropyUnavailable(String),
}

impl std::fmt::Display for OracleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OracleError::Malformed { line, text } => {
                write!(f, "oracle record line {line} is malformed: {text:?}")
            }
            OracleError::Mismatch {
                index,
                expected,
                found,
            } => write!(
                f,
                "oracle replay mismatch at entry {index}: the record has `{expected}`, the run \
                 asked for `{found}`"
            ),
            OracleError::Exhausted { index, wanted } => write!(
                f,
                "oracle replay exhausted: the run asked for `{wanted}` after all {index} \
                 recorded entries"
            ),
            OracleError::Unconsumed { consumed, total } => write!(
                f,
                "oracle replay ended with {} of {total} recorded entries unconsumed",
                total - consumed
            ),
            OracleError::LiveReadUnderReplay(what) => {
                write!(
                    f,
                    "a live `{what}` read was attempted under --oracle-replay"
                )
            }
            OracleError::EntropyUnavailable(why) => {
                write!(f, "no working host entropy source: {why}")
            }
        }
    }
}

impl std::error::Error for OracleError {}

/// What the host was asked for during a run. Deterministic counts (they
/// depend only on the program), except `live_reads`, which counts REAL
/// clock/entropy reads and is 0 by construction under replay.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct HostCounters {
    /// `clock_mono` + `clock_wall` responses served (live or replayed).
    pub clock_reads: u64,
    /// `entropy_u64` responses served (live or replayed).
    pub entropy_draws: u64,
    /// Real clock or entropy reads performed. 0 under replay.
    pub live_reads: u64,
    /// Times `fs.Dir`'s host door was reached (each one a would-be syscall).
    pub fs_host_calls: u64,
    /// Times `net.Net`'s host door was reached.
    pub net_host_calls: u64,
}

#[derive(Debug)]
enum Mode {
    Live {
        /// The monotonic origin: this process's first `clock_mono` read.
        base: Option<std::time::Instant>,
    },
    Replay {
        events: Vec<HostEvent>,
        at: usize,
    },
}

/// The run's capability-response source and log (design §7.2).
#[derive(Debug)]
pub struct Oracle {
    mode: Mode,
    log: Vec<HostEvent>,
    last_mono: Option<u64>,
    counters: HostCounters,
}

impl Default for Oracle {
    fn default() -> Oracle {
        Oracle::live()
    }
}

impl Oracle {
    /// Live responses from the real host, each one logged.
    pub fn live() -> Oracle {
        Oracle {
            mode: Mode::Live { base: None },
            log: Vec::new(),
            last_mono: None,
            counters: HostCounters::default(),
        }
    }

    /// Responses replayed from `record` (the record format above); no real
    /// clock or entropy is read for the whole run.
    pub fn replay(record: &[u8]) -> Result<Oracle, OracleError> {
        let events = parse_record(record)?;
        Ok(Oracle {
            mode: Mode::Replay { events, at: 0 },
            log: Vec::new(),
            last_mono: None,
            counters: HostCounters::default(),
        })
    }

    /// F10: responses replayed from already-parsed events (an
    /// [`crate::oracle::OracleRecord`]'s host section) — the same mode as
    /// [`Oracle::replay`], without a round trip through the text format.
    pub fn replay_events(events: Vec<HostEvent>) -> Oracle {
        Oracle {
            mode: Mode::Replay { events, at: 0 },
            log: Vec::new(),
            last_mono: None,
            counters: HostCounters::default(),
        }
    }

    /// F9's comptime oracle (design §6: "comptime mode starts with an empty
    /// capability table"): a replay of NO responses. It reads nothing real,
    /// and any request is the named [`OracleError`] divergence — although
    /// the intrinsic table's `comptime` column stops every clock and entropy
    /// door before it would ask.
    pub fn sealed() -> Oracle {
        Oracle {
            mode: Mode::Replay {
                events: Vec::new(),
                at: 0,
            },
            log: Vec::new(),
            last_mono: None,
            counters: HostCounters::default(),
        }
    }

    /// Is this a replay?
    pub fn is_replay(&self) -> bool {
        matches!(self.mode, Mode::Replay { .. })
    }

    /// The responses served so far, in order.
    pub fn events(&self) -> &[HostEvent] {
        &self.log
    }

    /// The record of this run, in the record format: `--oracle-record`'s
    /// file. Under replay it reproduces the replayed record byte for byte.
    pub fn log_bytes(&self) -> Vec<u8> {
        let mut out = format!("{RECORD_HEADER}\n").into_bytes();
        for e in &self.log {
            out.extend_from_slice(e.line().as_bytes());
        }
        out
    }

    pub fn counters(&self) -> HostCounters {
        self.counters
    }

    /// The end-of-run check: under replay every recorded entry must have
    /// been consumed, or the run diverged.
    pub fn finish(&self) -> Result<(), OracleError> {
        match &self.mode {
            Mode::Replay { events, at } if *at != events.len() => Err(OracleError::Unconsumed {
                consumed: *at,
                total: events.len(),
            }),
            _ => Ok(()),
        }
    }

    /// The entry shim's pre-`main` check (ch10 R47): a `main` that takes a
    /// `rand.Rng` starts only once a working entropy source exists. Under
    /// replay the record IS the source.
    pub fn ensure_entropy(&mut self) -> Result<(), OracleError> {
        match self.mode {
            Mode::Replay { .. } => Ok(()),
            Mode::Live { .. } => real_entropy_source_ok(),
        }
    }

    /// `time.Clock.now`'s reading.
    pub fn clock_mono(&mut self) -> Result<u64, OracleError> {
        self.counters.clock_reads += 1;
        let v = match self.next_replayed("mono")? {
            Some(bits) => bits,
            None => {
                let real = self.real_mono()?;
                // Strictly increasing: monotonic, and a reversed pair is
                // always observably reversed (module docs).
                match self.last_mono {
                    Some(prev) => real.max(prev.saturating_add(1)),
                    None => real,
                }
            }
        };
        self.last_mono = Some(v);
        self.log.push(HostEvent::Mono(v));
        Ok(v)
    }

    /// `time.Clock.wall`'s reading.
    pub fn clock_wall(&mut self) -> Result<i64, OracleError> {
        self.counters.clock_reads += 1;
        let v = match self.next_replayed("wall")? {
            Some(bits) => bits as i64,
            None => self.real_wall()?,
        };
        self.log.push(HostEvent::Wall(v));
        Ok(v)
    }

    /// `rand.Rng.u64`'s draw.
    pub fn entropy_u64(&mut self) -> Result<u64, OracleError> {
        self.counters.entropy_draws += 1;
        let v = match self.next_replayed("entropy")? {
            Some(bits) => bits,
            None => self.real_entropy()?,
        };
        self.log.push(HostEvent::Entropy(v));
        Ok(v)
    }

    /// `time.Clock.sleep`. Not a read, so not logged; skipped under replay,
    /// where the recorded clock readings already carry the elapsed time.
    pub fn sleep(&mut self, nanos: u64) {
        if let Mode::Live { .. } = self.mode {
            std::thread::sleep(std::time::Duration::from_nanos(nanos));
        }
    }

    /// Counts a reach of `fs.Dir`'s host door.
    pub fn note_fs_host_call(&mut self) {
        self.counters.fs_host_calls += 1;
    }

    /// Counts a reach of `net.Net`'s host door.
    pub fn note_net_host_call(&mut self) {
        self.counters.net_host_calls += 1;
    }

    /// Under replay, the bits of the next logged response, which must be of
    /// kind `wanted`; `None` in live mode.
    fn next_replayed(&mut self, wanted: &'static str) -> Result<Option<u64>, OracleError> {
        let Mode::Replay { events, at } = &mut self.mode else {
            return Ok(None);
        };
        let Some(&e) = events.get(*at) else {
            return Err(OracleError::Exhausted { index: *at, wanted });
        };
        if e.kind() != wanted {
            return Err(OracleError::Mismatch {
                index: *at,
                expected: e.kind(),
                found: wanted,
            });
        }
        *at += 1;
        Ok(Some(e.bits()))
    }

    // -- the real readers: the only real clock/entropy reads in the crate --

    fn real_mono(&mut self) -> Result<u64, OracleError> {
        let Mode::Live { base } = &mut self.mode else {
            return Err(OracleError::LiveReadUnderReplay("mono"));
        };
        self.counters.live_reads += 1;
        let now = std::time::Instant::now();
        let origin = *base.get_or_insert(now);
        let nanos = now.saturating_duration_since(origin).as_nanos();
        Ok(u64::try_from(nanos).unwrap_or(u64::MAX))
    }

    fn real_wall(&mut self) -> Result<i64, OracleError> {
        if self.is_replay() {
            return Err(OracleError::LiveReadUnderReplay("wall"));
        }
        self.counters.live_reads += 1;
        let now = std::time::SystemTime::now();
        Ok(match now.duration_since(std::time::UNIX_EPOCH) {
            Ok(d) => i64::try_from(d.as_nanos()).unwrap_or(i64::MAX),
            Err(e) => i64::try_from(e.duration().as_nanos())
                .map(|n| -n)
                .unwrap_or(i64::MIN),
        })
    }

    fn real_entropy(&mut self) -> Result<u64, OracleError> {
        if self.is_replay() {
            return Err(OracleError::LiveReadUnderReplay("entropy"));
        }
        self.counters.live_reads += 1;
        let mut b = [0u8; 8];
        read_real_entropy(&mut b)?;
        Ok(u64::from_le_bytes(b))
    }
}

#[cfg(unix)]
const ENTROPY_DEVICE: &str = "/dev/urandom";

#[cfg(unix)]
fn read_real_entropy(into: &mut [u8]) -> Result<(), OracleError> {
    use std::io::Read;
    std::fs::File::open(ENTROPY_DEVICE)
        .and_then(|mut f| f.read_exact(into))
        .map_err(|e| OracleError::EntropyUnavailable(format!("{ENTROPY_DEVICE}: {e}")))
}

#[cfg(not(unix))]
fn read_real_entropy(_into: &mut [u8]) -> Result<(), OracleError> {
    Err(OracleError::EntropyUnavailable(
        "this host has no supported entropy device".into(),
    ))
}

#[cfg(unix)]
fn real_entropy_source_ok() -> Result<(), OracleError> {
    std::fs::File::open(ENTROPY_DEVICE)
        .map(|_| ())
        .map_err(|e| OracleError::EntropyUnavailable(format!("{ENTROPY_DEVICE}: {e}")))
}

#[cfg(not(unix))]
fn real_entropy_source_ok() -> Result<(), OracleError> {
    Err(OracleError::EntropyUnavailable(
        "this host has no supported entropy device".into(),
    ))
}

/// Parses the record format. Strict: the header line first, then one event
/// per `\n`-terminated line, nothing else (no blank lines, no trailing
/// bytes), so a record round-trips byte for byte.
pub fn parse_record(record: &[u8]) -> Result<Vec<HostEvent>, OracleError> {
    let text = std::str::from_utf8(record).map_err(|_| OracleError::Malformed {
        line: 1,
        text: "not UTF-8".into(),
    })?;
    let malformed = |line: usize, t: &str| OracleError::Malformed {
        line,
        text: t.to_string(),
    };
    let Some(body) = text.strip_suffix('\n') else {
        return Err(malformed(1, "the record does not end with a newline"));
    };
    let mut lines = body.split('\n');
    if lines.next() != Some(RECORD_HEADER) {
        return Err(malformed(1, "missing `fors-oracle-record 1` header"));
    }
    let mut out = Vec::new();
    let mut last_mono: Option<u64> = None;
    for (i, l) in lines.enumerate() {
        let n = i + 2;
        let (kind, val) = l.split_once(' ').ok_or_else(|| malformed(n, l))?;
        let ev = match kind {
            "mono" => HostEvent::Mono(val.parse().map_err(|_| malformed(n, l))?),
            "wall" => HostEvent::Wall(val.parse().map_err(|_| malformed(n, l))?),
            "entropy"
                if val.len() == 16
                    && val
                        .bytes()
                        .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase()) =>
            {
                HostEvent::Entropy(u64::from_str_radix(val, 16).map_err(|_| malformed(n, l))?)
            }
            _ => return Err(malformed(n, l)),
        };
        // Canonical spelling only: the record must round-trip byte for byte.
        if ev.line() != format!("{l}\n") {
            return Err(malformed(n, l));
        }
        // A live oracle's `mono` readings are strictly increasing (module
        // docs), so a record whose are not was never one of its records:
        // refused here, by line, rather than replayed as a clock that went
        // backwards (which `time-since-reversed-trap` would then not trap
        // on — a silent divergence from every live run).
        if let HostEvent::Mono(v) = ev {
            if last_mono.is_some_and(|p| v <= p) {
                return Err(malformed(
                    n,
                    &format!("{l} (a `mono` reading not greater than the previous one)"),
                ));
            }
            last_mono = Some(v);
        }
        out.push(ev);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn live_mono_is_strictly_increasing_and_logged() {
        let mut o = Oracle::live();
        let a = o.clock_mono().unwrap();
        let b = o.clock_mono().unwrap();
        assert!(b > a, "{a} then {b}");
        assert_eq!(o.events(), &[HostEvent::Mono(a), HostEvent::Mono(b)]);
        assert_eq!(o.counters().live_reads, 2);
    }

    #[test]
    fn a_record_replays_byte_identically_and_reads_nothing_real() {
        let mut live = Oracle::live();
        live.clock_mono().unwrap();
        live.clock_wall().unwrap();
        live.entropy_u64().unwrap();
        live.clock_mono().unwrap();
        let rec = live.log_bytes();
        let mut re = Oracle::replay(&rec).unwrap();
        assert_eq!(
            re.clock_mono().unwrap(),
            match live.events()[0] {
                HostEvent::Mono(v) => v,
                _ => unreachable!(),
            }
        );
        re.clock_wall().unwrap();
        re.entropy_u64().unwrap();
        re.clock_mono().unwrap();
        re.finish().unwrap();
        assert_eq!(re.log_bytes(), rec);
        assert_eq!(re.counters().live_reads, 0);
        assert_eq!(re.counters().clock_reads, 3);
        assert_eq!(re.counters().entropy_draws, 1);
    }

    #[test]
    fn every_divergence_is_a_named_error() {
        let rec = format!("{RECORD_HEADER}\nmono 5\n");
        let mut o = Oracle::replay(rec.as_bytes()).unwrap();
        assert_eq!(
            o.entropy_u64(),
            Err(OracleError::Mismatch {
                index: 0,
                expected: "mono",
                found: "entropy"
            })
        );
        let mut o = Oracle::replay(rec.as_bytes()).unwrap();
        assert_eq!(
            o.finish(),
            Err(OracleError::Unconsumed {
                consumed: 0,
                total: 1
            })
        );
        assert_eq!(o.clock_mono(), Ok(5));
        assert_eq!(
            o.clock_mono(),
            Err(OracleError::Exhausted {
                index: 1,
                wanted: "mono"
            })
        );
        assert_eq!(o.counters().live_reads, 0);
    }

    #[test]
    fn a_malformed_record_is_refused_by_line() {
        // The refusal names the offending LINE (1-based, header is line 1).
        assert_eq!(
            Oracle::replay(format!("{RECORD_HEADER}\nmono 5\nwall 1\nmono 4\n").as_bytes())
                .err()
                .map(|e| match e {
                    OracleError::Malformed { line, .. } => line,
                    other => panic!("{other:?}"),
                }),
            Some(4)
        );
        for bad in [
            "".to_string(),
            "mono 1\n".to_string(),
            format!("{RECORD_HEADER}\nmono x\n"),
            format!("{RECORD_HEADER}\nmono 01\n"),
            format!("{RECORD_HEADER}\nentropy ABCDEF0123456789\n"),
            format!("{RECORD_HEADER}\nmono 1"),
            format!("{RECORD_HEADER}\n\n"),
            // A clock that stands still or goes backwards is no live
            // oracle's record.
            format!("{RECORD_HEADER}\nmono 5\nmono 5\n"),
            format!("{RECORD_HEADER}\nmono 5\nwall 1\nmono 4\n"),
        ] {
            assert!(
                matches!(
                    Oracle::replay(bad.as_bytes()),
                    Err(OracleError::Malformed { .. })
                ),
                "{bad:?}"
            );
        }
    }

    #[test]
    fn real_clock_and_entropy_reads_live_only_in_this_module() {
        // design §7.2: "nothing reads ... `std::time`" outside the host
        // door. Grep every OTHER source file of the crate.
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
        for entry in std::fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            if path.file_name().and_then(|n| n.to_str()) == Some("host.rs") {
                continue;
            }
            let src = std::fs::read_to_string(&path).unwrap();
            for needle in ["Instant::now", "SystemTime", "urandom", "getrandom"] {
                assert!(
                    !src.contains(needle),
                    "{} names `{needle}`: real clock/entropy reads belong in host.rs",
                    path.display()
                );
            }
        }
    }
}
