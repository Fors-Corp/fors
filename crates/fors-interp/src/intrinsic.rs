//! The closed intrinsic table (design §5.8 mechanism 2, §6) with its
//! explicit `comptime` column.
//!
//! Every host-effect or primitive door the interpreter opens is ONE row
//! here, and the dispatch loop consults the row before it runs the door:
//! an intrinsic outside the table is [`crate::InterpError::UnknownIntrinsic`],
//! an intrinsic whose `comptime` cell is [`When::Forbidden`] reached in
//! comptime mode is a BUILD error naming the intrinsic and the site
//! ([`crate::comptime::ComptimeFault::ForbiddenIntrinsic`], ch04 R12), and
//! one whose `run` cell is forbidden reached at run time is
//! [`crate::InterpError::NotAtRunTime`]. That is how ch04 R12's "no
//! capability value, clock, RNG, env read, or ambient I/O" becomes a
//! mechanical check rather than a review promise (design §5.8).
//!
//! The design's abstract rows (`@alloc`, `@fd_write`, `@clock_mono`, ...)
//! are realised by the concrete names lowering emits; [`IntrinsicRow::design`]
//! names which abstract row each one realises. `@alloc`/`@free`/`@memcpy`/
//! `@memset`/`@size_of`/`@align_of` are FMIR OPCODES in this interpreter
//! (`alloc`, `free`, ...), not intrinsic calls, so they need no row: an
//! opcode carries no host effect and is allowed in both modes.
//!
//! **The documented route for a new door** (design §5.8: "no increment may
//! make a std method interpreter-resident without adding a row to the
//! intrinsic table"): add the row here with BOTH columns decided, add its
//! arm to `exec::exec_intrinsic`, and `every_row_is_dispatched` /
//! `every_dispatched_name_has_a_row` keep the two in lockstep.

/// One cell of the table: may the door be opened in this mode?
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum When {
    Allowed,
    Forbidden,
}

/// One row of the closed table.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct IntrinsicRow {
    /// The name lowering emits (`Callee::Intrinsic`'s resolved symbol).
    pub name: &'static str,
    /// The design §5.8 row this realises (`@fd_write`, `@clock_mono`, ...),
    /// or the stand-in family it belongs to.
    pub design: &'static str,
    /// Run mode.
    pub run: When,
    /// Comptime mode (ch04 R12): forbidden for every capability, clock,
    /// entropy and ambient-I/O door; allowed for pure data primitives and
    /// for `input_read`, the declared-inputs map.
    pub comptime: When,
}

pub(crate) const STDOUT_WRITE_LINE: &str = "stdout_write_line";
pub(crate) const STDOUT_WRITE_UINT: &str = "stdout_write_uint";
pub(crate) const STDERR_WRITE_LINE: &str = "stderr_write_line";
pub(crate) const STR_BYTE_LEN: &str = "str_byte_len";
pub(crate) const STR_BYTE_AT: &str = "str_byte_at";
pub(crate) const STR_BYTE_SLICE: &str = "str_byte_slice";
pub(crate) const SEQ_LEN: &str = "seq_len";
pub(crate) const AGG_UNINIT: &str = "agg_uninit";
pub(crate) const STR_EQ: &str = "str_eq";
pub(crate) const CLOCK_MONO: &str = "clock_mono";
pub(crate) const CLOCK_WALL: &str = "clock_wall";
pub(crate) const CLOCK_SLEEP: &str = "clock_sleep";
pub(crate) const ENTROPY_U64: &str = "entropy_u64";
pub(crate) const FS_DOOR: &str = "fs_door";
pub(crate) const NET_DOOR: &str = "net_door";
pub(crate) const INPUT_READ: &str = "input_read";

use When::{Allowed, Forbidden};

/// The table. Order is presentation only; names are unique
/// (`names_are_unique`).
pub const TABLE: &[IntrinsicRow] = &[
    // Ambient I/O: `io`'s writers over `@fd_write` (ch04 R12 "ambient I/O").
    IntrinsicRow {
        name: STDOUT_WRITE_LINE,
        design: "@fd_write",
        run: Allowed,
        comptime: Forbidden,
    },
    IntrinsicRow {
        name: STDOUT_WRITE_UINT,
        design: "@fd_write",
        run: Allowed,
        comptime: Forbidden,
    },
    // F10: `io.Stderr.write_line` to the standard ERROR descriptor (design
    // §7.1's record carries `stderr` bytes; §7.2a's trap tests observe the
    // lines before the trap line there). Ambient I/O like its two twins.
    IntrinsicRow {
        name: STDERR_WRITE_LINE,
        design: "@fd_write",
        run: Allowed,
        comptime: Forbidden,
    },
    // Pure data primitives (design §5.8's `Str`/sequence stand-ins): no host
    // effect, so allowed in both modes.
    IntrinsicRow {
        name: STR_BYTE_LEN,
        design: "Str byte primitive",
        run: Allowed,
        comptime: Allowed,
    },
    IntrinsicRow {
        name: STR_BYTE_AT,
        design: "Str byte primitive",
        run: Allowed,
        comptime: Allowed,
    },
    IntrinsicRow {
        name: STR_BYTE_SLICE,
        design: "Str byte primitive",
        run: Allowed,
        comptime: Allowed,
    },
    IntrinsicRow {
        name: STR_EQ,
        design: "Str byte primitive",
        run: Allowed,
        comptime: Allowed,
    },
    IntrinsicRow {
        name: SEQ_LEN,
        design: "sequence length",
        run: Allowed,
        comptime: Allowed,
    },
    IntrinsicRow {
        name: AGG_UNINIT,
        design: "@alloc (uninitialised aggregate)",
        run: Allowed,
        comptime: Allowed,
    },
    // Capability doors (ch04 R12: no capability value, clock or RNG).
    IntrinsicRow {
        name: CLOCK_MONO,
        design: "@clock_mono",
        run: Allowed,
        comptime: Forbidden,
    },
    IntrinsicRow {
        name: CLOCK_WALL,
        design: "@clock_wall",
        run: Allowed,
        comptime: Forbidden,
    },
    IntrinsicRow {
        name: CLOCK_SLEEP,
        design: "@clock_mono (sleep)",
        run: Allowed,
        comptime: Forbidden,
    },
    IntrinsicRow {
        name: ENTROPY_U64,
        design: "@entropy",
        run: Allowed,
        comptime: Forbidden,
    },
    IntrinsicRow {
        name: FS_DOOR,
        design: "fs.Dir host door",
        run: Allowed,
        comptime: Forbidden,
    },
    IntrinsicRow {
        name: NET_DOOR,
        design: "net.Net host door",
        run: Allowed,
        comptime: Forbidden,
    },
    // The inverse row (ch10 R42, ch04 R13): comptime-only, reads the
    // declared-inputs map and never a descriptor.
    IntrinsicRow {
        name: INPUT_READ,
        design: "@input_read",
        run: Forbidden,
        comptime: Allowed,
    },
];

/// The row for `name`, if the table has one.
pub fn lookup(name: &str) -> Option<&'static IntrinsicRow> {
    TABLE.iter().find(|r| r.name == name)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_are_unique() {
        for (i, a) in TABLE.iter().enumerate() {
            for b in &TABLE[i + 1..] {
                assert_ne!(a.name, b.name, "duplicate intrinsic row");
            }
        }
    }

    /// ch04 R12's list, mechanically: every capability, clock, entropy and
    /// ambient-I/O door is forbidden at comptime, and `input_read` is the
    /// only row forbidden at run time.
    #[test]
    fn comptime_column_forbids_every_host_door() {
        for name in [
            STDOUT_WRITE_LINE,
            STDOUT_WRITE_UINT,
            STDERR_WRITE_LINE,
            CLOCK_MONO,
            CLOCK_WALL,
            CLOCK_SLEEP,
            ENTROPY_U64,
            FS_DOOR,
            NET_DOOR,
        ] {
            assert_eq!(lookup(name).map(|r| r.comptime), Some(When::Forbidden));
        }
        let run_forbidden: Vec<_> = TABLE
            .iter()
            .filter(|r| r.run == When::Forbidden)
            .map(|r| r.name)
            .collect();
        assert_eq!(run_forbidden, vec![INPUT_READ]);
    }

    /// Every row has an arm in the dispatcher and every arm a row: the
    /// dispatcher's source names each row's constant exactly once as a
    /// match arm, and names no intrinsic string the table lacks.
    #[test]
    fn every_row_is_dispatched() {
        let src = include_str!("exec.rs");
        let body = src
            .split("fn exec_intrinsic(")
            .nth(1)
            .expect("exec_intrinsic exists");
        let body = body.split("\nfn ").next().unwrap_or(body);
        for row in TABLE {
            let konst = const_name(row.name);
            assert!(
                body.contains(&format!("intrinsic::{konst}")),
                "intrinsic row `{}` has no arm in exec_intrinsic",
                row.name
            );
        }
        for line in body.lines() {
            if let Some(rest) = line.trim().split("intrinsic::").nth(1) {
                let ident: String = rest
                    .chars()
                    .take_while(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || *c == '_')
                    .collect();
                if ident.is_empty() {
                    continue;
                }
                assert!(
                    TABLE.iter().any(|r| const_name(r.name) == ident),
                    "exec_intrinsic dispatches `{ident}`, which has no table row"
                );
            }
        }
    }

    fn const_name(name: &str) -> String {
        name.to_ascii_uppercase()
    }
}
