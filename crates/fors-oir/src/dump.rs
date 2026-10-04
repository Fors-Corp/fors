//! A one-line-per-row text dump of an [`OirFunc`], for `--dump-oir` style
//! debugging and test failure messages. Values print as `%vN:ty`, slots as
//! `$sN(root R)`, alias classes as `{root R, convention|affine}`.

use std::fmt::Write as _;

use crate::ir::{AliasClass, AliasSource, NONE, OirFunc, OirOp, Term};

pub fn dump(f: &OirFunc) -> String {
    let mut out = String::new();
    let _ = writeln!(
        out,
        "oir decl {} ({} values, {} rows, {} slots)",
        f.decl,
        f.values.len(),
        f.rows.len(),
        f.slots.len()
    );
    for (i, s) in f.slots.iter().enumerate() {
        let _ = writeln!(out, "  slot $s{i} root {} {}", s.root, s.ty.name());
    }
    for (i, s) in f.strings.iter().enumerate() {
        let _ = writeln!(out, "  string #{i} {:?}", String::from_utf8_lossy(s));
    }
    let r = &f.rows;
    for i in 0..r.len() {
        let mut line = String::from("  ");
        if r.dst[i] != NONE {
            let d = r.dst[i] as usize;
            let _ = write!(line, "%v{} = ", d,);
            if f.values.secret.get(d) == Some(&true) {
                line.push_str("secret ");
            }
        }
        line.push_str(r.op[i].name());
        if let OirOp::Icmp(p) = r.op[i] {
            let _ = write!(line, ".{p:?}");
        }
        if !r.mode[i].name().is_empty() {
            let _ = write!(line, ".{}", r.mode[i].name());
        }
        match r.op[i] {
            OirOp::ConstInt => {
                let bits = (u64::from(r.b[i]) << 32) | u64::from(r.a[i]);
                let _ = write!(line, " {bits:#x}");
            }
            OirOp::ConstBool => {
                let _ = write!(line, " {}", r.a[i] != 0);
            }
            OirOp::ConstStr => {
                let _ = write!(line, " #{}", r.a[i]);
            }
            OirOp::SlotLoad => {
                let _ = write!(line, " $s{}", r.a[i]);
            }
            OirOp::SlotStore => {
                let _ = write!(line, " $s{}, %v{}", r.a[i], r.b[i]);
            }
            _ => {
                for v in [r.a[i], r.b[i]] {
                    if v != NONE {
                        let _ = write!(line, " %v{v}");
                    }
                }
            }
        }
        let _ = write!(line, " : {}", r.ty[i].name());
        if let Some(AliasClass::Root { root, source }) = r.alias[i] {
            let src = match source {
                AliasSource::Convention => "convention",
                AliasSource::Affine => "affine",
            };
            let _ = write!(line, " {{root {root}, {src}}}");
        }
        let _ = writeln!(out, "{line}");
    }
    match f.term {
        Term::Ret => out.push_str("  ret\n"),
        Term::Trap(k) => {
            let _ = writeln!(out, "  trap {}", k.as_str());
        }
    }
    out
}
