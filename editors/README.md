# Fors editor support

What is here:

- `fors.tmLanguage.json` — a TextMate grammar for Fors, `scopeName`
  `source.fors`, covering comments (including the corpus's `//!`
  test-metadata convention), both string forms, every numeric literal form
  and suffix, the full reserved-word set split into scope families, `@`
  attributes, function/struct/enum/trait/const declaration names, operators,
  punctuation, and the handful of positions ch07's own disambiguation rules
  make lexically decidable for type-vs-value coloring (`->`, `raises`, and
  the qualifiers `iso`/`imm`/`secret`/`dyn`, which is what makes
  `f[iso Buf]()`'s `Buf` colour as a type even inside `[...]`).
- `language-configuration.json` — comment tokens, bracket pairs,
  auto-closing pairs and surrounding pairs, for editors (VS Code and
  anything else that reads this format) to use independently of the
  grammar.
- `vscode/` — a minimal VS Code extension that contributes the `fors`
  language and points at the one grammar file above by relative path (never
  a copy — see `vscode/README.md` for local install steps).

There is exactly one copy of the grammar. Nothing under `vscode/` duplicates
it; `vscode/package.json`'s grammar contribution references
`../fors.tmLanguage.json` directly.

## How the oracle test works

A hand-authored TextMate grammar is worthless if it silently drifts from
the real lexer — a keyword the grammar forgets renders as a plain
identifier, and a fictitious one paints ordinary code like a keyword. Since
there is no dependency-free way to run an actual Oniguruma/TextMate engine
from Rust, `crates/fors-lex/tests/tmlanguage.rs` checks everything that
*is* checkable without one:

1. It parses `fors.tmLanguage.json` with a small hand-written JSON reader
   (no dependency — `crates/fors-lex` takes none, and adding one for a test
   is out of scope for this change).
2. It extracts every keyword alternative out of every grammar pattern
   shaped exactly `\b(a|b|c)\b` (the shape every reserved-word family in
   this grammar uses, and *only* those families — a pattern with any extra
   context, like the ones combining a keyword with its following name, or
   the `set` and `soa` contextual-keyword patterns, is deliberately shaped
   differently so it is excluded from this extraction).
3. It compares that set, by name, against two independent sources: the
   real `fors_lex::keyword_kind` (the ground truth — what the lexer
   actually recognizes) and the reserved-word list as ch07 itself states it
   in prose (`docs/spec/07-grammar.md`, "Keywords — reserved"). All three
   must agree exactly; a missing or an invented keyword fails the test and
   prints the difference by name.
4. It walks every regex string in the grammar (every `match`, `begin`,
   `end`) and checks it is a structurally plausible Oniguruma pattern:
   balanced brackets and parentheses, no empty alternation, and none of the
   constructs TextMate's engine does not support (variable-length
   lookbehind, `\K`, recursion).
5. It checks every `name`/`captures[..].name` scope in the grammar ends in
   `.fors`, that the grammar declares `scopeName: "source.fors"` and
   `fileTypes: ["fors"]`, and that the VS Code extension's `package.json`
   declares the `.fors` extension and points its grammar contribution at
   the single `fors.tmLanguage.json` file (never a second copy).

Run it with `cargo test -p fors-lex --test tmlanguage`.

## Why Fors is not in GitHub Linguist yet

Linguist — the library GitHub uses to detect and colour a repository's
languages — requires a submitted language to have its own
syntax-highlighting grammar (what this directory now provides) *and* to
already be in real use: roughly 2000 files of that extension, indexed by
GitHub search, added in the last year, across many *unique, non-fork*
repositories. New and experimental languages are routinely rejected even
with a working grammar in hand, precisely because that usage bar isn't met
yet.

The Fors repository is currently private, so none of its `.fors` files are
indexed by GitHub search at all, independent of the file-count threshold.
Nothing here changes that — it can't be changed by writing a grammar. What
this directory *does* do is remove the other prerequisite ahead of time:
when the repository is public and in active use, submitting Fors to
Linguist needs a grammar to point at, and now there is one, already
cross-checked against the real lexer instead of hand-guessed.
