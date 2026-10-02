//! ch04 R21's closed root-capability type set, shared by lowering (which
//! knows a type's nominal identity) and the interpreter's entry shim (which
//! constructs one value per `main` parameter by that identity and reads no
//! checker output — ch05 R3). FMIR instructions never carry this: it is a
//! side-table fact about `main`'s signature, written by lowering into
//! [`crate::names::TypeNames::roots`] the same way F3's render names are.
//!
//! ch04 R7: only the entry shim, which is not Fors source, creates a value
//! of one of these types. The list MUST NOT be extended except by editing
//! ch04 R21; [`RootCap::ALL`] is that list, in R21's order.

/// One of the twelve root-capability types of ch04 R21.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum RootCap {
    Stdout,
    Stderr,
    Stdin,
    Dir,
    Net,
    Exec,
    Clock,
    Rng,
    Env,
    Args,
    Device,
    Heap,
}

impl RootCap {
    /// ch04 R21's list, in its own order.
    pub const ALL: [RootCap; 12] = [
        RootCap::Stdout,
        RootCap::Stderr,
        RootCap::Stdin,
        RootCap::Dir,
        RootCap::Net,
        RootCap::Exec,
        RootCap::Clock,
        RootCap::Rng,
        RootCap::Env,
        RootCap::Args,
        RootCap::Device,
        RootCap::Heap,
    ];

    /// `(std module path, type name)` — the NOMINAL identity ch04 R8
    /// decides by resolution, never by spelling.
    pub fn path(self) -> (&'static str, &'static str) {
        match self {
            RootCap::Stdout => ("std.io", "Stdout"),
            RootCap::Stderr => ("std.io", "Stderr"),
            RootCap::Stdin => ("std.io", "Stdin"),
            RootCap::Dir => ("std.fs", "Dir"),
            RootCap::Net => ("std.net", "Net"),
            RootCap::Exec => ("std.proc", "Exec"),
            RootCap::Clock => ("std.time", "Clock"),
            RootCap::Rng => ("std.rand", "Rng"),
            RootCap::Env => ("std.env", "Env"),
            RootCap::Args => ("std.env", "Args"),
            RootCap::Device => ("std.gpu", "Device"),
            RootCap::Heap => ("std.mem", "Heap"),
        }
    }

    /// The capability word ch04 R21 pairs with the type in root `needs`
    /// (`fs.Dir` pairs with `fs.read` OR `fs.write`, written here as the
    /// first; `mem.Heap` pairs with none, because allocation is not
    /// authority).
    pub fn capability(self) -> Option<&'static str> {
        match self {
            RootCap::Stdout => Some("io.stdout"),
            RootCap::Stderr => Some("io.stderr"),
            RootCap::Stdin => Some("io.stdin"),
            RootCap::Dir => Some("fs.read"),
            RootCap::Net => Some("net"),
            RootCap::Exec => Some("exec"),
            RootCap::Clock => Some("clock"),
            RootCap::Rng => Some("rng"),
            RootCap::Env | RootCap::Args => Some("env"),
            RootCap::Device => Some("gpu"),
            RootCap::Heap => None,
        }
    }

    /// The root-capability type named `module.name`, if it is one. `module`
    /// is the dotted path of the std module that DECLARES the type (what
    /// resolution reached), never a user spelling.
    pub fn from_path(module: &str, name: &str) -> Option<RootCap> {
        RootCap::ALL
            .into_iter()
            .find(|c| c.path() == (module, name))
    }

    /// `std.time.Clock`-shaped display path.
    pub fn display(self) -> String {
        let (m, n) = self.path();
        format!("{m}.{n}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_list_is_closed_at_twelve_distinct_types() {
        let mut paths: Vec<_> = RootCap::ALL.iter().map(|c| c.path()).collect();
        paths.sort();
        paths.dedup();
        assert_eq!(paths.len(), 12);
        for c in RootCap::ALL {
            let (m, n) = c.path();
            assert_eq!(RootCap::from_path(m, n), Some(c));
        }
        // A user type that merely spells the name is not one (ch04 R8).
        assert_eq!(RootCap::from_path("io", "Stdout"), None);
        assert_eq!(RootCap::from_path("app.time", "Clock"), None);
        assert_eq!(RootCap::Heap.capability(), None);
    }
}
