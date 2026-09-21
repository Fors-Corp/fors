# Fors syntax highlighting for VS Code

A minimal, dependency-free VS Code extension: `package.json` declares the
`fors` language (extension `.fors`) and points VS Code at two files that live
one directory up, `../fors.tmLanguage.json` (the grammar) and
`../language-configuration.json` (comment tokens, bracket pairs,
auto-closing and surrounding pairs). Nothing here is duplicated or built —
there is no `node_modules`, no compile step, and no bundling; VS Code loads
the JSON files directly.

This extension gives you **highlighting only**. It does not provide
diagnostics, completion, go-to-definition or any other language-server
feature. Fors has a real language server (`crates/fors-lsp`, a separate
binary you build and point your editor at); install it and configure it
independently of this extension. The two are complementary: this extension
colours the text; the LSP understands it.

## Install locally

VS Code loads unpacked extensions from its extensions folder. Pick one:

**Symlink (recommended — edits to the grammar take effect on next reload,
no reinstall):**

```sh
ln -s "$(pwd)" ~/.vscode/extensions/fors-syntax
```

Run that from `editors/vscode/` (this directory). Restart VS Code, or run
"Developer: Reload Window" from the command palette.

**Copy (a frozen snapshot instead of a live link):**

```sh
cp -R "$(pwd)" ~/.vscode/extensions/fors-syntax
```

On Windows, the extensions folder is `%USERPROFILE%\.vscode\extensions`.

After installing either way, open any `.fors` file; VS Code should report
the language as "Fors" in the status bar and colour the source according to
your active theme's mapping of the standard TextMate scopes this grammar
uses (`keyword.control`, `storage.type`, `string.quoted.double`,
`comment.line`, `constant.numeric`, `entity.name.function`, and so on — see
`../README.md` for the full scope list and how it is kept honest).

## Uninstall

Remove (or unlink) `~/.vscode/extensions/fors-syntax` and reload the window.
