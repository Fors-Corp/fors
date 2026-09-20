# Contributing to Fors

## Commits

Conventional Commits, with a scope naming the subsystem that moved:

```
<type>(<scope>): <subject in the imperative, lower case, no full stop>

<body: what changed and why; what a verifier caught, if anything>

BREAKING CHANGE: <only when existing .fors programs stop compiling>
```

**Types** — `feat` (new capability), `fix` (defect), `docs`, `refactor`,
`perf`, `test`, `build`, `ci`, `chore`.

**Scopes** — the areas that exist: `spec`, `lex`, `syntax`, `index`,
`resolve`, `check`, `fir`, `query`, `fmt`, `lsp`, `cli`, `std`, `corpus`,
`bench`, `spike`, `plan`, `ci`. A change spanning several takes the one it is
really about, or no scope if it is genuinely repo-wide.

**`BREAKING CHANGE` means one thing here**: a `.fors` program that compiled
before this commit does not compile after it (or compiles to different
behaviour). Compiler-internal API churn is not breaking — nothing outside this
repository depends on it yet. A breaking commit bumps the **language** version.

## Two version streams

A language and the compiler that implements it are different artefacts with
different compatibility promises, so they carry separate numbers.

| Stream | Where | Bumps when |
|---|---|---|
| **Language** `lang-vX.Y.Z` | `docs/spec/VERSION` | MINOR: a decision round changes what programs are legal (pre-1.0, so breaking changes are MINOR). PATCH: a rule is clarified without changing which programs compile. |
| **Compiler** `compiler-vX.Y.Z` | `[workspace.package] version` | PATCH: a verified increment lands. MINOR: the compiler starts implementing a new language version. |

`CHANGELOG.md` records which compiler version implements which language
version. The language number is the one a `.fors` program is written against;
the compiler number is the one to cite in a bug report.

## Tags

Every verified increment is tagged. A tag marks a state whose gates were
actually run — not an arbitrary commit:

- `cargo test --workspace` green with `RUSTFLAGS="-D warnings"`
- the independent reference parser agrees with the corpus (`bad: 0`)
- the two parsers agree with each other (the differential test)
- for a language change, the corpus reflects it and `fors check std` is clean

## Pull requests

Everything lands through a pull request; `main` only moves through one. A PR
must pass tests + parser gates, the formatting gate, clippy with warnings
denied, and CodeQL. The author verifies the work before opening the PR — the
checks are a floor, not the review.
