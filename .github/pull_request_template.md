## What this changes

<!-- One paragraph. If it changes what `.fors` programs are legal, say so here
     and put `BREAKING CHANGE:` in the commit body - that bumps the language
     version, per CONTRIBUTING.md. -->

## Verification

<!-- The gates you ran yourself, with their output. The CI checks are a floor,
     not the review. -->

- [ ] `RUSTFLAGS="-D warnings" cargo test --workspace`
- [ ] `python3 tools/ref/fors_parse.py tests/conformance` → `bad: 0`
- [ ] the two parsers agree (differential test)
- [ ] language change: corpus updated, `fors check std` clean

## Versions

<!-- Language: unchanged, or bumped to lang-vX.Y.Z (a BREAKING change).
     Compiler: unchanged, or bumped to compiler-vX.Y.Z. -->
