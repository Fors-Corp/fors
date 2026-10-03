//! F10: the [`OracleRecord`] — design §7.1's complete, content-addressed
//! record of ONE run, and the record/replay plumbing over it (shared with
//! F8's response log, [`crate::host`]).
//!
//! A record holds everything a run observed and everything it produced:
//!
//! - **inputs**: the program's content address ([`program_digest`]: the
//!   target, the entry, and every reachable declaration's `fmir_hash`,
//!   string bytes and intrinsic names, in call-graph order) and the target
//!   hash (design §5.1's `Config`);
//! - **every host observation**: the capability responses (clock readings,
//!   entropy draws) in the order the run asked for them — exactly F8's
//!   response log, so a record can drive [`crate::host::Oracle::replay_events`];
//! - **outputs**: the exact `stdout` and `stderr` bytes, and the exit — a
//!   status (0, 1, 2, or `ub:`'s 70), a trap KIND plus a site digest, or a
//!   `ub:` class plus a site digest (design §7.1's `Exit`);
//! - **the step count** (design §7.1: recorded for cost regression, never
//!   compared across engines; §7.2: compared across runs of ONE engine as a
//!   nondeterminism detector).
//!
//! What is deliberately NOT in it: the `ub:` report's message text, the
//! Q7 backtrace and any host path — diagnostic payload that is not part of
//! the observable behaviour (§7.2a: a backtrace is never part of the
//! record). The site digest is `hash(kind ‖ line ‖ col)`: design §7.1 also
//! folds in the declaration key and file, which [`crate::Outcome`] does not
//! carry; lowered instructions carry `SiteId(0)` today, so every site is
//! `0:0` until lowering records real sites, and the digest is exactly as
//! informative as the line/col it is built from.
//!
//! **Record format** (byte-exact; the encoding IS the content):
//!
//! ```text
//! fors-run-record 1
//! program <32 lowercase hex>
//! target <32 lowercase hex>
//! exit status <decimal>            | exit trap <kind> <16 hex> | exit ub <class> <16 hex>
//! steps <decimal>
//! host <decimal count>
//! <count lines in F8's response-log line format: mono / wall / entropy>
//! stdout <decimal byte length>
//! <exactly that many bytes>
//! stderr <decimal byte length>
//! <exactly that many bytes>
//! ```
//!
//! (each byte section is followed by one `\n` of framing). The record's
//! content address is [`OracleRecord::id`]: the 128-bit `hash_bytes` of that
//! encoding. Parsing is strict ([`OracleRecord::from_bytes`]): anything that
//! does not re-encode to the same bytes is refused, so equal ids mean equal
//! records and a record round-trips byte for byte.

use fors_fmir::inst::Callee;
use fors_fmir::op::TrapKind;

use crate::exec::{Exit, InterpError, Outcome};
use crate::host::{HostEvent, Oracle};
use crate::program::Program;
use crate::shim::{ExitStatus, HostEnv, entry_exit};
use crate::ub::UbClass;

/// The record format's first line.
pub const RUN_RECORD_HEADER: &str = "fors-run-record 1";

/// How the run ended, as the record states it (design §7.1's `Exit`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RecordExit {
    /// A process exit status: 0, 1 (an error left `main`), 2 (`Stdout`
    /// latched on return).
    Status(i32),
    /// A program trap: its kind and the site digest.
    Trap { kind: TrapKind, site: u64 },
    /// A `ub:` report (status 70 on a real process): its class and the site
    /// digest.
    Ub { class: UbClass, site: u64 },
}

/// design §7.1's complete record of one run. See the module docs for what
/// each field is and the byte format.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct OracleRecord {
    pub program: u128,
    pub target: u128,
    pub exit: RecordExit,
    pub steps: u64,
    pub host: Vec<HostEvent>,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}

/// A record that does not parse, by line (1-based) and reason.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct RecordError {
    pub line: usize,
    pub reason: String,
}

impl std::fmt::Display for RecordError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "run record line {}: {}", self.line, self.reason)
    }
}

impl std::error::Error for RecordError {}

/// The content address of `prog` as an oracle INPUT: the target, the entry
/// function's name, then every declaration reachable from the entry through
/// direct calls, in discovery order — its name, `fmir_hash`, string bytes
/// and intrinsic names (sorted, so the side tables' push order is not
/// content). Two programs with equal digests run identically on one host.
pub fn program_digest(prog: &Program) -> u128 {
    let mut b = b"fors-program 1\0".to_vec();
    b.extend_from_slice(&crate::comptime::target_hash(&prog.config).to_le_bytes());
    match prog.fns.get(prog.entry) {
        Some(f) => crate::comptime::put_bytes(&mut b, f.name.as_bytes()),
        None => crate::comptime::put_bytes(&mut b, b""),
    }
    let order = if prog.entry < prog.fns.len() {
        crate::comptime::reach(prog)
    } else {
        Vec::new()
    };
    b.extend_from_slice(&(order.len() as u64).to_le_bytes());
    for fi in order {
        let f = &prog.fns[fi];
        crate::comptime::put_bytes(&mut b, f.name.as_bytes());
        b.extend_from_slice(&fors_fmir::encode::fmir_hash(&f.decl).to_le_bytes());
        let mut strings = f.strings.clone();
        strings.sort();
        b.extend_from_slice(&(strings.len() as u64).to_le_bytes());
        for (id, bytes) in &strings {
            b.extend_from_slice(&id.to_le_bytes());
            crate::comptime::put_bytes(&mut b, bytes);
        }
        let mut intr = f.intrinsics.clone();
        intr.sort();
        b.extend_from_slice(&(intr.len() as u64).to_le_bytes());
        for (sym, name) in &intr {
            b.extend_from_slice(&sym.to_le_bytes());
            crate::comptime::put_bytes(&mut b, name.as_bytes());
        }
        // The callees by key, so two programs whose bodies hash equal but
        // whose call targets differ are different inputs.
        for row in &f.decl.insts.calls {
            if let Callee::Direct(key) = row.callee {
                b.extend_from_slice(&key.0.to_le_bytes());
            }
        }
    }
    fors_index::fingerprint::hash_bytes(&b)
}

/// `hash(kind ‖ line ‖ col)`, folded to 64 bits (module docs).
pub fn site_digest(kind: &str, site: Option<(u32, u32)>) -> u64 {
    let (line, col) = site.unwrap_or((0, 0));
    let mut b = b"fors-site 1\0".to_vec();
    crate::comptime::put_bytes(&mut b, kind.as_bytes());
    b.extend_from_slice(&line.to_le_bytes());
    b.extend_from_slice(&col.to_le_bytes());
    let h = fors_index::fingerprint::hash_bytes(&b);
    (h as u64) ^ ((h >> 64) as u64)
}

impl OracleRecord {
    /// The record of `outcome`, a run of `prog` whose capability responses
    /// were `host` (an oracle's [`Oracle::events`]).
    pub fn of(prog: &Program, outcome: &Outcome, host: &[HostEvent]) -> OracleRecord {
        let exit = match (outcome.exit, entry_exit(outcome)) {
            (Exit::Ub(class), _) => RecordExit::Ub {
                class,
                site: site_digest(class.as_str(), outcome.site),
            },
            (_, ExitStatus::Trap(kind)) => RecordExit::Trap {
                kind,
                site: site_digest(kind.as_str(), outcome.site),
            },
            (_, ExitStatus::Status(code)) => RecordExit::Status(code),
        };
        OracleRecord {
            program: program_digest(prog),
            target: crate::comptime::target_hash(&prog.config),
            exit,
            steps: outcome.steps,
            host: host.to_vec(),
            stdout: outcome.stdout.clone(),
            stderr: outcome.stderr.clone(),
        }
    }

    /// The canonical bytes (module docs' format).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = format!(
            "{RUN_RECORD_HEADER}\nprogram {:032x}\ntarget {:032x}\n",
            self.program, self.target
        )
        .into_bytes();
        let exit = match self.exit {
            RecordExit::Status(c) => format!("exit status {c}\n"),
            RecordExit::Trap { kind, site } => format!("exit trap {} {site:016x}\n", kind.as_str()),
            RecordExit::Ub { class, site } => format!("exit ub {} {site:016x}\n", class.as_str()),
        };
        out.extend_from_slice(exit.as_bytes());
        out.extend_from_slice(
            format!("steps {}\nhost {}\n", self.steps, self.host.len()).as_bytes(),
        );
        for e in &self.host {
            out.extend_from_slice(e.line().as_bytes());
        }
        for (name, bytes) in [("stdout", &self.stdout), ("stderr", &self.stderr)] {
            out.extend_from_slice(format!("{name} {}\n", bytes.len()).as_bytes());
            out.extend_from_slice(bytes);
            out.push(b'\n');
        }
        out
    }

    /// The content address: 32 lowercase hex digits of `hash_bytes` over
    /// [`OracleRecord::to_bytes`].
    pub fn id(&self) -> String {
        format!(
            "{:032x}",
            fors_index::fingerprint::hash_bytes(&self.to_bytes())
        )
    }

    /// F8's response-log bytes for this record's host section: what
    /// `--oracle-record` writes and [`Oracle::replay`] reads.
    pub fn host_log_bytes(&self) -> Vec<u8> {
        let mut out = format!("{}\n", crate::host::RECORD_HEADER).into_bytes();
        for e in &self.host {
            out.extend_from_slice(e.line().as_bytes());
        }
        out
    }

    /// Parses [`OracleRecord::to_bytes`]. Strict: the parsed record must
    /// re-encode to exactly `bytes`.
    pub fn from_bytes(bytes: &[u8]) -> Result<OracleRecord, RecordError> {
        let mut r = Reader {
            b: bytes,
            at: 0,
            line: 0,
        };
        let err = |line: usize, reason: &str| RecordError {
            line,
            reason: reason.to_string(),
        };
        if r.line_text()? != RUN_RECORD_HEADER {
            return Err(err(1, "missing `fors-run-record 1` header"));
        }
        let program = r.hex128("program")?;
        let target = r.hex128("target")?;
        let exit_line = r.line_text()?;
        let ln = r.line;
        let parts: Vec<&str> = exit_line.split(' ').collect();
        let exit = match parts.as_slice() {
            ["exit", "status", c] => {
                RecordExit::Status(c.parse().map_err(|_| err(ln, "bad exit status"))?)
            }
            ["exit", "trap", k, site] => RecordExit::Trap {
                kind: TrapKind::parse_name(k).ok_or_else(|| err(ln, "unknown trap kind"))?,
                site: hex64(site).ok_or_else(|| err(ln, "bad site digest"))?,
            },
            ["exit", "ub", c, site] => RecordExit::Ub {
                class: UbClass::ALL
                    .into_iter()
                    .find(|u| u.as_str() == *c)
                    .ok_or_else(|| err(ln, "unknown ub class"))?,
                site: hex64(site).ok_or_else(|| err(ln, "bad site digest"))?,
            },
            _ => return Err(err(ln, "malformed `exit` line")),
        };
        let steps = r.decimal("steps")?;
        let n = r.decimal("host")?;
        let mut log = format!("{}\n", crate::host::RECORD_HEADER);
        for _ in 0..n {
            log.push_str(r.line_text()?);
            log.push('\n');
        }
        let host =
            crate::host::parse_record(log.as_bytes()).map_err(|e| err(r.line, &e.to_string()))?;
        let stdout = r.section("stdout")?;
        let stderr = r.section("stderr")?;
        if r.at != bytes.len() {
            return Err(err(r.line + 1, "trailing bytes after the `stderr` section"));
        }
        let rec = OracleRecord {
            program,
            target,
            exit,
            steps,
            host,
            stdout,
            stderr,
        };
        if rec.to_bytes() != bytes {
            return Err(err(
                0,
                "not in canonical form (does not re-encode byte for byte)",
            ));
        }
        Ok(rec)
    }

    /// The first field in which two records differ, or `None` if they are
    /// byte-identical. Field order is the format's.
    pub fn first_difference(&self, other: &OracleRecord) -> Option<&'static str> {
        if self.program != other.program {
            Some("program")
        } else if self.target != other.target {
            Some("target")
        } else if self.exit != other.exit {
            Some("exit")
        } else if self.steps != other.steps {
            Some("steps")
        } else if self.host != other.host {
            Some("host")
        } else if self.stdout != other.stdout {
            Some("stdout")
        } else if self.stderr != other.stderr {
            Some("stderr")
        } else {
            None
        }
    }
}

fn hex64(s: &str) -> Option<u64> {
    (s.len() == 16
        && s.bytes()
            .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase()))
    .then(|| u64::from_str_radix(s, 16).ok())
    .flatten()
}

struct Reader<'a> {
    b: &'a [u8],
    at: usize,
    line: usize,
}

impl<'a> Reader<'a> {
    fn line_text(&mut self) -> Result<&'a str, RecordError> {
        self.line += 1;
        let rest = &self.b[self.at.min(self.b.len())..];
        let Some(end) = rest.iter().position(|&c| c == b'\n') else {
            return Err(RecordError {
                line: self.line,
                reason: "unexpected end of record".into(),
            });
        };
        self.at += end + 1;
        std::str::from_utf8(&rest[..end]).map_err(|_| RecordError {
            line: self.line,
            reason: "not UTF-8".into(),
        })
    }

    fn field(&mut self, name: &str) -> Result<&'a str, RecordError> {
        let l = self.line_text()?;
        l.strip_prefix(name)
            .and_then(|r| r.strip_prefix(' '))
            .ok_or_else(|| RecordError {
                line: self.line,
                reason: format!("expected `{name} ...`"),
            })
    }

    fn hex128(&mut self, name: &str) -> Result<u128, RecordError> {
        let v = self.field(name)?;
        let ok = v.len() == 32
            && v.bytes()
                .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase());
        ok.then(|| u128::from_str_radix(v, 16).ok())
            .flatten()
            .ok_or_else(|| RecordError {
                line: self.line,
                reason: format!("`{name}` is not 32 lowercase hex digits"),
            })
    }

    fn decimal(&mut self, name: &str) -> Result<u64, RecordError> {
        let v = self.field(name)?;
        v.parse().map_err(|_| RecordError {
            line: self.line,
            reason: format!("`{name}` is not a decimal count"),
        })
    }

    fn section(&mut self, name: &str) -> Result<Vec<u8>, RecordError> {
        let n = usize::try_from(self.decimal(name)?).unwrap_or(usize::MAX);
        let end = self.at.checked_add(n).filter(|e| *e < self.b.len());
        let Some(end) = end.filter(|e| self.b[*e] == b'\n') else {
            return Err(RecordError {
                line: self.line,
                reason: format!("`{name}` section is shorter than its length or unframed"),
            });
        };
        let out = self.b[self.at..end].to_vec();
        self.line += out.iter().filter(|&&c| c == b'\n').count() + 1;
        self.at = end + 1;
        Ok(out)
    }
}

/// Runs `prog` with `oracle` and returns the record of the run (F8's
/// [`crate::run_with_oracle`], recorded).
pub fn run_recorded(
    prog: &Program,
    tys: &fors_fir::ty::TyStore,
    host: &HostEnv,
    oracle: &mut Oracle,
) -> Result<OracleRecord, InterpError> {
    run_recorded_capped(prog, tys, host, oracle, u64::MAX)
}

/// As [`run_recorded`], under [`crate::exec::run_with_oracle_capped`]'s
/// step cap.
pub fn run_recorded_capped(
    prog: &Program,
    tys: &fors_fir::ty::TyStore,
    host: &HostEnv,
    oracle: &mut Oracle,
    max_steps: u64,
) -> Result<OracleRecord, InterpError> {
    let outcome = crate::exec::run_with_oracle_capped(prog, tys, host, oracle, max_steps)?;
    Ok(OracleRecord::of(prog, &outcome, oracle.events()))
}

/// Re-runs `prog` serving every capability response from `record` (no real
/// clock or entropy is read) and returns the NEW run's record. The caller
/// compares it with `record` ([`OracleRecord::first_difference`]): a
/// deterministic interpreter reproduces it byte for byte (design §7.2).
pub fn replay_recorded(
    prog: &Program,
    tys: &fors_fir::ty::TyStore,
    host: &HostEnv,
    record: &OracleRecord,
) -> Result<OracleRecord, InterpError> {
    replay_recorded_capped(prog, tys, host, record, u64::MAX)
}

/// As [`replay_recorded`], under a step cap.
pub fn replay_recorded_capped(
    prog: &Program,
    tys: &fors_fir::ty::TyStore,
    host: &HostEnv,
    record: &OracleRecord,
    max_steps: u64,
) -> Result<OracleRecord, InterpError> {
    let mut oracle = Oracle::replay_events(record.host.clone());
    run_recorded_capped(prog, tys, host, &mut oracle, max_steps)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> OracleRecord {
        OracleRecord {
            program: 0x0123_4567_89ab_cdef_0011_2233_4455_6677,
            target: 7,
            exit: RecordExit::Trap {
                kind: TrapKind::Bounds,
                site: 0xdead_beef,
            },
            steps: 42,
            host: vec![
                HostEvent::Mono(5),
                HostEvent::Entropy(0xff),
                HostEvent::Wall(-3),
            ],
            stdout: b"a\nb".to_vec(),
            stderr: b"\n\nstderr 3\n".to_vec(),
        }
    }

    #[test]
    fn a_record_round_trips_byte_for_byte() {
        for r in [
            sample(),
            OracleRecord {
                exit: RecordExit::Status(2),
                host: Vec::new(),
                stdout: Vec::new(),
                stderr: Vec::new(),
                ..sample()
            },
            OracleRecord {
                exit: RecordExit::Ub {
                    class: UbClass::UninitRead,
                    site: 1,
                },
                ..sample()
            },
        ] {
            let b = r.to_bytes();
            assert_eq!(OracleRecord::from_bytes(&b), Ok(r.clone()));
            assert_eq!(OracleRecord::from_bytes(&b).unwrap().id(), r.id());
        }
    }

    #[test]
    fn every_field_moves_the_content_address() {
        let base = sample();
        let variants = [
            OracleRecord {
                program: 1,
                ..sample()
            },
            OracleRecord {
                target: 8,
                ..sample()
            },
            OracleRecord {
                exit: RecordExit::Status(0),
                ..sample()
            },
            OracleRecord {
                steps: 43,
                ..sample()
            },
            OracleRecord {
                host: vec![HostEvent::Mono(6)],
                ..sample()
            },
            OracleRecord {
                stdout: b"a\nc".to_vec(),
                ..sample()
            },
            OracleRecord {
                stderr: Vec::new(),
                ..sample()
            },
        ];
        for v in variants {
            assert_ne!(v.id(), base.id());
            assert!(v.first_difference(&base).is_some());
        }
        assert_eq!(base.first_difference(&sample()), None);
    }

    #[test]
    fn a_malformed_or_non_canonical_record_is_refused() {
        let good = sample().to_bytes();
        let mut truncated = good.clone();
        truncated.pop();
        assert!(OracleRecord::from_bytes(&truncated).is_err());
        let mut trailing = good.clone();
        trailing.push(b'x');
        assert!(OracleRecord::from_bytes(&trailing).is_err());
        let text = String::from_utf8_lossy(&good).replace("steps 42", "steps 042");
        assert!(OracleRecord::from_bytes(text.as_bytes()).is_err());
        let text = String::from_utf8_lossy(&good).replace("exit trap bounds", "exit trap nope");
        assert!(OracleRecord::from_bytes(text.as_bytes()).is_err());
        assert!(OracleRecord::from_bytes(b"fors-oracle-record 1\n").is_err());
    }
}
