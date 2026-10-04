//! Alias classes of slot rows (ch05 R4/R5, §2.1): a local or parameter root
//! is `AliasClass::Root { root, source }`, with `source` taken from the FMIR
//! `AliasSeed` when the row carries one and otherwise from what the root is
//! (a parameter's root by convention, a local's by affine ownership).
//! `CopyFrom`/`Init` are deliberately seedless in FMIR (their identity is
//! the `PlaceRow`, `fors-fmir/src/op.rs::is_memory_producing`), so the
//! derivation from the root is the common case.

use fors_fmir::alias::AliasSeed;

use crate::ir::{AliasClass, AliasSource};

/// The class of root `root` in a function with `n_params` parameters, given
/// the row's FMIR seed. `Err` names a seed M2-0 cannot carry (arena brands
/// and split halves reach only projected places, which M2-0 refuses).
pub fn class_of_root(
    root: u32,
    n_params: u32,
    seed: AliasSeed,
) -> Result<AliasClass, &'static str> {
    let source = match seed {
        AliasSeed::Conv(_) => AliasSource::Convention,
        AliasSeed::Own(_) => AliasSource::Affine,
        AliasSeed::None if root < n_params => AliasSource::Convention,
        AliasSeed::None => AliasSource::Affine,
        AliasSeed::Arena(_) => return Err("arena-brand alias seed on a scalar root"),
        AliasSeed::Split { .. } => return Err("split alias seed on a scalar root"),
    };
    Ok(AliasClass::Root { root, source })
}

#[cfg(test)]
mod tests {
    use super::*;
    use fors_fir::sig::Conv;
    use fors_fmir::ids::PlaceId;

    #[test]
    fn locals_are_affine_and_params_are_by_convention() {
        let c = |root, seed| class_of_root(root, 2, seed).unwrap();
        assert_eq!(
            c(0, AliasSeed::None),
            AliasClass::Root {
                root: 0,
                source: AliasSource::Convention
            }
        );
        assert_eq!(
            c(5, AliasSeed::None),
            AliasClass::Root {
                root: 5,
                source: AliasSource::Affine
            }
        );
        assert_eq!(
            c(5, AliasSeed::Conv(Conv::Let)),
            AliasClass::Root {
                root: 5,
                source: AliasSource::Convention
            }
        );
        assert_eq!(
            c(0, AliasSeed::Own(PlaceId(0))),
            AliasClass::Root {
                root: 0,
                source: AliasSource::Affine
            }
        );
        assert!(
            class_of_root(
                3,
                0,
                AliasSeed::Split {
                    parent: PlaceId(0),
                    side: 1
                }
            )
            .is_err()
        );
    }
}
