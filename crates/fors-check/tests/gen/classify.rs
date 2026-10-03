//! The verdict of one checked program: what happened, against what the
//! generator promised (a clean program is accepted; a mutated one is rejected
//! with the mutation's code at the mutation's site).

use std::collections::HashMap;

use crate::ast::Id;
use crate::run::{CheckResult, Diag};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Class {
    /// A clean program the checker accepted, silently and completely.
    AcceptedAsExpected,
    /// A mutated program rejected with the expected code at the expected site
    /// (and nothing else).
    RejectedAsExpected,
    /// A clean program the checker rejected.
    FalseRejection,
    /// A mutated program rejected, but with no diagnostic of the expected code.
    WrongCode,
    /// The expected code is there, but not at the expected site.
    WrongSite,
    /// The expected diagnostic is there at its site, with others besides.
    Cascade,
    /// A mutated program the checker accepted.
    Missed,
    /// `check_build` (or the query path) panicked.
    Panic,
    /// A node typed `TY_ERROR` with no diagnostic (silent.rs's sweep).
    SilentTyError,
    /// The query DAG and `check_build` disagree about the diagnostics.
    QueryDisagree,
    /// The generator emitted text that does not parse.
    GenParse,
    /// The generator emitted text that does not resolve.
    GenResolve,
    /// The generator itself panicked.
    GenPanic,
    /// A mutation produced text that does not parse or resolve (a mutation
    /// bug, never a checker verdict).
    MutBroken,
}

impl Class {
    pub fn label(self) -> &'static str {
        match self {
            Class::AcceptedAsExpected => "accepted-as-expected",
            Class::RejectedAsExpected => "rejected-with-expected-code-at-site",
            Class::FalseRejection => "FALSE REJECTION",
            Class::WrongCode => "WRONG CODE",
            Class::WrongSite => "WRONG SITE",
            Class::Cascade => "CASCADE (expected + extra diagnostics)",
            Class::Missed => "MISSED",
            Class::Panic => "PANIC",
            Class::SilentTyError => "SILENT TY_ERROR",
            Class::QueryDisagree => "QUERY DISAGREES",
            Class::GenParse => "GENERATOR: does not parse",
            Class::GenResolve => "GENERATOR: does not resolve",
            Class::GenPanic => "GENERATOR PANIC",
            Class::MutBroken => "MUTATION: broken program",
        }
    }

    /// The classes that are the soundness test's pass condition.
    pub fn is_good(self) -> bool {
        matches!(self, Class::AcceptedAsExpected | Class::RejectedAsExpected)
    }

    pub const ALL: [Class; 14] = [
        Class::AcceptedAsExpected,
        Class::RejectedAsExpected,
        Class::FalseRejection,
        Class::WrongCode,
        Class::WrongSite,
        Class::Cascade,
        Class::Missed,
        Class::Panic,
        Class::SilentTyError,
        Class::QueryDisagree,
        Class::GenParse,
        Class::GenResolve,
        Class::GenPanic,
        Class::MutBroken,
    ];
}

/// What a mutation promises.
#[derive(Clone, Debug)]
pub struct Expect {
    pub code: String,
    /// The node whose span must contain the diagnostic's start.
    pub target: Id,
    pub note: String,
}

#[derive(Clone, Debug)]
pub struct Verdict {
    pub class: Class,
    pub detail: String,
}

fn rows(ds: &[Diag], text: &str) -> String {
    ds.iter()
        .map(|d| {
            let (l, c) = line_col(text, d.start);
            format!(
                "{} at {l}:{c} (site {}): {}",
                d.code,
                d.site,
                d.msg.chars().take(100).collect::<String>()
            )
        })
        .collect::<Vec<_>>()
        .join("; ")
}

pub fn line_col(text: &str, at: u32) -> (usize, usize) {
    let at = (at as usize).min(text.len());
    let line = text[..at].matches('\n').count() + 1;
    let bol = text[..at].rfind('\n').map_or(0, |i| i + 1);
    (line, at - bol + 1)
}

/// Classifies one check of `text` against `expect` (`None` for a clean
/// program). `spans` are the rendered node spans.
pub fn classify(
    res: &CheckResult,
    text: &str,
    spans: &HashMap<Id, (u32, u32)>,
    expect: Option<&Expect>,
) -> Verdict {
    let v = |class, detail: String| Verdict { class, detail };
    if let Some(p) = &res.panic {
        return v(Class::Panic, p.lines().next().unwrap_or("").to_string());
    }
    match expect {
        None => {
            if !res.parse.is_empty() {
                return v(Class::GenParse, res.parse.join("; "));
            }
            if !res.resolve.is_empty() {
                return v(Class::GenResolve, res.resolve.join("; "));
            }
            if !res.diags.is_empty() {
                return v(Class::FalseRejection, rows(&res.diags, text));
            }
            if !res.silent.is_empty() {
                return v(Class::SilentTyError, res.silent.join("; "));
            }
            v(Class::AcceptedAsExpected, String::new())
        }
        Some(e) => {
            if !res.parse.is_empty() {
                return v(Class::MutBroken, format!("parse: {}", res.parse.join("; ")));
            }
            if !res.resolve.is_empty() {
                return v(
                    Class::MutBroken,
                    format!("resolve: {}", res.resolve.join("; ")),
                );
            }
            let Some(&(lo, hi)) = spans.get(&e.target) else {
                return v(
                    Class::MutBroken,
                    format!("the target node {} has no span", e.target),
                );
            };
            if res.diags.is_empty() {
                let silent = if res.silent.is_empty() {
                    String::new()
                } else {
                    format!(" (and {} silent TY_ERROR nodes)", res.silent.len())
                };
                return v(
                    Class::Missed,
                    format!("accepted; expected {}{silent}", e.code),
                );
            }
            let with_code: Vec<&Diag> = res.diags.iter().filter(|d| d.code == e.code).collect();
            if with_code.is_empty() {
                return v(
                    Class::WrongCode,
                    format!("expected {}; got {}", e.code, rows(&res.diags, text)),
                );
            }
            let at_site: Vec<&Diag> = with_code
                .iter()
                .copied()
                .filter(|d| d.start >= lo && d.start <= hi)
                .collect();
            if at_site.is_empty() {
                let (el, ec) = line_col(text, lo);
                return v(
                    Class::WrongSite,
                    format!(
                        "expected {} within {el}:{ec}..{}; got {}",
                        e.code,
                        line_col(text, hi).0,
                        rows(&res.diags, text)
                    ),
                );
            }
            if res.diags.len() > 1 {
                return v(Class::Cascade, rows(&res.diags, text));
            }
            v(Class::RejectedAsExpected, String::new())
        }
    }
}
