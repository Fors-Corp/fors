//! The in-flight stack and cycle recovery (design §9: "explicit in-flight
//! stack for cycle detection with a caller-declared `on_cycle` recovery
//! value").
//!
//! A cycle is not an engine error and never a panic: design §10 requires
//! "one diagnostic at the lexicographically least `DeclKey` and `TY_ERROR`
//! elsewhere", which is a decision only the query set can make. So the
//! engine detects the re-entry, charges it, asks the query set for the
//! recovery value through [`crate::Queries::on_cycle`], and — crucially —
//! does NOT memoise it: a recovery value is not a computed value, and
//! caching it would make the cycle's answer depend on which node the build
//! happened to demand first.

use crate::key::QueryKey;

/// One in-flight query.
pub(crate) struct Frame {
    pub(crate) node: u32,
    /// The dependencies read so far by this frame. Committed to the arena
    /// when the computation returns a value; dropped on cancellation, so a
    /// cancelled computation leaves the node exactly as it was.
    pub(crate) deps: Vec<u32>,
    /// Whether reads taken while this frame is on top become dependency
    /// edges. False for the frame a *verification* walk pushes: those reads
    /// ask "did you change?", and recording them would add an edge the
    /// query never took.
    pub(crate) attribute: bool,
}

/// The in-flight path, for a cycle report the query set can render.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cycle {
    /// The key demanded again while already in flight.
    pub at: QueryKey,
    /// The stack from the outermost in-flight query to `at`'s first
    /// occurrence, in order.
    pub path: Vec<QueryKey>,
}

/// A demand abandoned because the cancellation flag was set. Nothing was
/// written: every node is exactly as it was before the demand.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Cancelled;

impl std::fmt::Display for Cancelled {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("query cancelled")
    }
}
