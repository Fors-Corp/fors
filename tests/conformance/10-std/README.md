# ch10 conformance corpus — the standard-library surface

Each test cites its rule as `10.Sk`; `detail` starts with the expected
code (`S00nn`), or an `N00nn`/`T00nn`/`ch01 Rk`/trap kind where another
chapter's rule decides. Directives and expectation kinds are
`tests/conformance/README.md`'s.

The authoritative list of names is `docs/spec/10-std.md`'s "Conformance
tests" section (159 names from rounds 1-5, plus 55 added in round 6). Every
file here parses clean under `fors parse` and is silent under `fors check`
unless its `detail` names an N/A code (`crates/fors-resolve/tests/conformance.rs`).

Round 6 (2026-09-20) added 35 files and migrated five: the adaptors and
consumers became PROVIDED METHODS of `Iterator` (Rules 32-35), so
`mem.map` … `mem.try_for_each` are gone and a chain is one expression;
`Vec`, `Map` and `String` are linear ALWAYS and their element-dropping
operations moved to `T: Droppable` impl blocks (Rule 11c), leaving
`deinit_empty` and its `pre` as the only trap this rule keeps —
`linear-element-container-deinit-trap` is now
`vec-deinit-empty-nonempty-trap`.

## Present (83)

- `adaptor-chain-accepted`
- `adaptor-with-raising-closure-rejected`
- `alloc-failure-is-error-value-accepted`
- `alloc-without-question-rejected`
- `buffer-fields-public-accepted`
- `buffer-in-module-without-allocator-accepted`
- `buffer-index-past-len-trap`
- `buffer-one-type-argument-rejected`
- `chain-adaptor-absent-rejected`
- `child-not-waited-at-question-rejected`
- `conn-not-shutdown-at-question-rejected`
- `consumer-count-method-accepted`
- `consumer-fold-method-accepted`
- `container-of-linear-not-iterated-by-value-rejected`
- `defer-not-run-on-trap`
- `discard-linear-rejected`
- `entries-not-closed-rejected`
- `file-not-closed-rejected`
- `fixed-allocator-in-needs-empty-module-accepted`
- `free-brand-laundering-rejected`
- `free-function-adaptor-absent-rejected`
- `free-function-consumer-absent-rejected`
- `free-wrong-brand-rejected`
- `fs-name-dotdot-invalid-run-ok`
- `fs-read-needs-capability-rejected`
- `fs-read-to-string-outside-comptime-rejected`
- `hardware-threads-no-capability-accepted`
- `heap-brand-mismatch-rejected`
- `heap-brand-named-by-parameter-accepted`
- `heap-stored-in-field-rejected`
- `index-loop-mutates-accepted`
- `item-named-as-std-prelude-addition-rejected`
- `iter-mut-not-provided-rejected`
- `iterator-next-not-raises-rejected`
- `linear-array-field-in-buffer-rejected`
- `linear-buffer-element-rejected`
- `linear-discard-rejected`
- `linear-in-user-struct-inherits-rejected`
- `linear-moved-to-caller-accepted`
- `main-heap-parameter-accepted`
- `main-raises-exit-status-one-run-error`
- `map-deinit-linear-value-rejected`
- `own-dropped-without-deinit-rejected`
- `own-sent-to-unstructured-task-rejected`
- `prelude-alloc-error-without-import-accepted`
- `prelude-buffer-without-import-accepted`
- `prelude-page-allocator-without-import-accepted`
- `prelude-vec-without-import-accepted`
- `rand-bounded-zero-trap`
- `rand-pcg-needs-no-capability-accepted`
- `rand-rng-needs-capability-rejected`
- `result-type-absent-rejected`
- `scoped-iter-chain-keeps-borrow-rejected`
- `sigpipe-ignored-write-latches-run-ok`
- `std-fn-without-capability-value-rejected`
- `std-iterator-inherent-name-clash-rejected`
- `stdout-check-surfaces-error-accepted`
- `str-index-is-bytes-run-ok`
- `str-slice-non-boundary-raises-run-ok`
- `string-dropped-rejected`
- `time-now-is-monotonic-run-ok`
- `time-since-reversed-trap`
- `try-collect-into-is-free-function-accepted`
- `try-for-each-error-propagates-run-ok`
- `try-for-each-method-accepted`
- `two-tasks-one-allocator-rejected`
- `vec-clear-linear-element-rejected`
- `vec-consumed-by-defer-accepted`
- `vec-consumed-by-errdefer-then-returned-accepted`
- `vec-deinit-empty-nonempty-trap`
- `vec-deinit-linear-element-rejected`
- `vec-dropped-at-question-rejected`
- `vec-dropped-without-deinit-rejected`
- `vec-errdefer-normal-exit-unconsumed-rejected`
- `vec-linear-always-empty-deinit-accepted`
- `vec-linear-element-pop-then-deinit-empty-accepted`
- `vec-not-shared-rejected`
- `vec-push-wrong-brand-allocator-rejected`
- `write-line-without-question-accepted-run-ok`
- `writer-flush-requires-question-rejected`
- `zip-scoped-and-owned-accepted`
- `zip-two-scoped-sources-rejected`
- `zip-two-scoped-sources-local-accepted`

## Pending (111)

Named and owned by ch10, not yet written. They need either the type
checker (most of the `check-error` ones) or a runnable std (`run-ok`,
`run-error`, `trap`). Round 6 closed the two open questions that blocked a
group of them (linearity, and `main`'s raised error), and the names that
round covered have moved to Present.

- `adaptor-does-not-allocate-accepted`
- `alloc-failure-not-trap-run-ok`
- `alloc-zeroed-is-zero-run-ok`
- `allocator-as-dyn-rejected`
- `allocator-not-copyable-rejected`
- `allocator-not-shared-rejected`
- `allocator-stored-in-field-rejected`
- `allocator-trait-impl-complete-accepted`
- `arena-ref-versus-bump-accepted`
- `audit-finds-unlisted-unsafe-slice-rejected`
- `block-bytes-raw-is-unsafe-accepted`
- `block-not-copyable-rejected`
- `buffer-copyable-iff-element-accepted`
- `buffer-into-iter-accepted`
- `bump-reset-kills-blocks-rejected`
- `capability-value-required-rejected`
- `channel-absent-rejected`
- `char-literal-absent-rejected`
- `counting-assert-empty-trap`
- `counting-bytes-live-run-ok`
- `deinit-then-use-rejected`
- `double-free-rejected`
- `env-get-into-not-set-run-ok`
- `env-get-into-too-small-run-ok`
- `env-mutation-absent-rejected`
- `error-enum-is-copyable-accepted`
- `ffi-cstr-to-str-raises-accepted`
- `ffi-import-taints-module-rejected`
- `file-dropped-without-close-rejected`
- `fixed-allocator-exhausted-raises-run-ok`
- `flush-after-main-run-ok`
- `fold-is-left-to-right-run-ok`
- `for-moves-named-iterator-rejected`
- `for-over-items-accepted`
- `for-over-iter-accepted`
- `formatting-has-no-locale-run-ok`
- `free-is-total-accepted`
- `fs-entries-not-iterator-accepted`
- `fs-file-not-closed-rejected`
- `fs-name-with-slash-rejected-run-ok`
- `fs-open-dir-downward-only-accepted`
- `fs-read-to-string-undeclared-input-rejected`
- `gpu-info-total-accepted`
- `gpu-kernel-launch-absent-rejected`
- `grow-failure-keeps-block-accepted`
- `grow-invalidates-slice-rejected`
- `hash-for-float-rejected`
- `importer-of-std-mem-has-no-syscall-accepted`
- `into-form-allocates-nothing-accepted`
- `iter-mut-absent-rejected`
- `iter-while-mutating-rejected`
- `iter-yields-copies-accepted`
- `iterator-next-raises-rejected`
- `layout-align-not-power-of-two-rejected`
- `layout-array-overflow-raises-run-ok`
- `lock-absent-rejected`
- `main-heap-needs-entry-rejected`
- `main-heap-twice-rejected`
- `map-at-absent-trap`
- `map-fixed-seed-deterministic-run-ok`
- `map-get-non-copyable-value-rejected`
- `map-insert-returns-old-run-ok`
- `needs-and-use-both-required-rejected`
- `net-client-absent-rejected`
- `net-conn-not-shutdown-rejected`
- `net-timeout-error-from-accepted`
- `option-not-used-for-failure-rejected`
- `option-unwrap-absent-rejected`
- `own-get-scoped-escape-rejected`
- `parallel-fold-absent-rejected`
- `path-type-absent-rejected`
- `per-task-fixed-allocator-accepted`
- `prelude-name-and-mem-path-same-entity-accepted`
- `proc-child-not-waited-rejected`
- `proc-run-needs-exec-rejected`
- `raises-callable-to-pure-adaptor-rejected`
- `rand-fill-into-secret-accepted`
- `rand-pcg-reproducible-run-ok`
- `reduce-is-the-only-parallel-accepted`
- `set-self-in-std-rejected`
- `sink-self-deinit-implicit-move-accepted`
- `slice-copy-from-length-trap`
- `slice-fill-accepted`
- `slice-from-vec-needs-unsafe-rejected`
- `sort-is-deterministic-run-ok`
- `std-fn-without-allocator-allocates-rejected`
- `std-introduces-no-new-trap-kind-rejected`
- `std-module-syscall-sealed-accepted`
- `std-ships-no-error-from-rejected`
- `std-submodule-not-importable-rejected`
- `std-type-layout-not-guaranteed-rejected`
- `std-unknown-module-rejected`
- `stderr-unbuffered-before-trap-run-ok`
- `stdout-lost-on-trap-trap`
- `str-from-string-scoped-rejected`
- `str-literal-not-scoped-accepted`
- `str-shared-accepted`
- `str-slice-out-of-range-trap`
- `string-from-utf8-split-accepted`
- `text-compare-is-bytewise-run-ok`
- `time-wall-has-no-zone-accepted`
- `try-collect-into-needs-allocator-rejected`
- `try-fold-propagates-accepted`
- `try-sort-by-propagates-accepted`
- `two-failure-modes-in-one-call-rejected`
- `vec-growth-schedule-run-ok`
- `vec-into-iter-absent-rejected`
- `vec-items-is-unsafe-accepted`
- `vec-new-in-synth-position-rejected`
- `with-page-allocator-no-capability-accepted`
- `write-int-base-ten-run-ok`
