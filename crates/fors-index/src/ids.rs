//! `u32` newtypes indexing the columns owned by [`crate::FileTable`],
//! [`crate::ModuleTable`], [`crate::DeclTable`] and the future scope /
//! def tables. Each is just an index: no data lives on the type itself,
//! so a table's columns are the only storage (data-oriented, no
//! `Box`/`Rc` per entity).

macro_rules! index_newtype {
    ($name:ident) => {
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
        pub struct $name(pub u32);

        impl $name {
            pub fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

index_newtype!(FileId);
index_newtype!(ModuleId);
index_newtype!(DeclId);
index_newtype!(ScopeId);
index_newtype!(DefId);
