# Mach-O clone-patch-resign feasibility spike

## Verdict: GO, with caveats

Clone-to-new-inode + patch + selective-rehash + rename works, is functionally
correct, is provably kernel-enforced (negative control gets killed), and
scales sub-linearly with image size, unlike codesign -f -s - or a full
relink, both of which scale with total file size.

## What had to be rewritten
Only the CodeDirectory page-hash slots covering the patched byte range, for
every CodeDirectory blob in the SuperBlob (ad-hoc arm64 binaries here had
exactly one, SHA-256; alternates at CS slots 0x1000-0x1005 are also handled,
since Developer-ID binaries often carry more than one CD). Nothing else
changes: CD header fields (hashOffset, nCodeSlots, codeLimit) are unaffected
since patching doesn't move/resize code, no special slots (Info.plist/
requirements hash) are touched since ad-hoc signatures don't hash the CD
itself, and LC_CODE_SIGNATURE's offset/size are fixed.

## Measured (median / p95 ms, 50 reps)

| Operation | 1MB image | 50MB image |
|---|---|---|
| resign.py, 1-page patch | 0.54 / 1.00 | 1.25 / 1.93 |
| resign.py, 16-page patch | 0.78 / 1.38 | 1.35 / 1.93 |
| codesign -f -s - | 14.96 / 16.07 | 83.46 / 185.72 |
| full clang relink | 62.61 / 67.57 | 90.82 / 206.51 |

The resign path is 30-70x faster than codesign and 60-100x faster than a
relink, and its cost is dominated by clonefile/open/close overhead, not
image size (100x size increase caused only ~2.3x time increase). Both
baselines scale with file size as expected (whole-file re-hash / full link).

## Executed-then-patched hard cases
- Clone to new inode, then execute: after executing the original once,
  clone_patch_rename (new inode) + re-exec printed the patched value, exit 0.
  Inode changed as expected; the kernel's per-vnode cache was no obstacle.
- Patch the SAME inode in place after one execution, hashes correctly fixed:
  the second execution was killed by SIGKILL. This is the empirical case
  that justifies clone-to-new-inode: in-place patching of an already-run
  vnode is unsafe regardless of hash correctness.
- Negative control (patch without fixing hashes): killed by SIGKILL; codesign
  --verify independently reports "invalid signature (code or signature have
  been modified)" — the test can fail and enforcement is real.

## Caveats
- CD page size here was 4096 (log2 field), not the 16K VM page arm64/APFS
  otherwise uses; don't conflate the two in the real implementation.
- Ad-hoc, linker-signed, no hardened runtime only. A Developer-ID/CMS-signed
  binary's detached CMS blob signs the CD's own hash; patching invalidates
  that too and can't be fixed without the signing key. Safe only for the
  compiler's own ad-hoc output.
- Chained fixups / debug-info were not exercised; a patch dirtying bytes
  outside its intended range (e.g. rebase info) needs an expanded dirty set.
- clonefile(2) needs APFS; falls back to a plain copy and reports it, but
  the real implementation must surface this, not silently degrade.
- Only single-CD (SHA-256) binaries were exercised; the multi-CD (SHA-1 +
  SHA-256) alternates path is implemented but untested here.

## What the real Rust implementation must do differently
Detect/report clonefile fallback explicitly, parse all embedded
CodeDirectories, derive the dirty-page set from the actual diff, and
refuse/full-resign any non-ad-hoc target, since only ad-hoc signatures
are safely patchable this way.

## Verification addendum (independent re-run, 2026-09-19)

The acceptance test was re-run 31 times by the session's verifier instead of trusting a single run.

| Path | Runs | Result |
|---|---:|---|
| Case A: clonefile to a NEW inode, patch, rehash dirty slots, rename | 31 | 31 x exit 0, prints 42 |
| Case B: patch the SAME inode in place after it has executed (hashes fixed correctly) | 31 | 19 x SIGKILL, 12 x exit 0 |
| Negative control (patched, hashes not fixed) | 31 | killed every time |

**Correction to the body of this report:** in-place patching of an executed inode is not "killed"; it is
**non-deterministic** (about 60 percent SIGKILL here), which is worse: it would surface in a compiler as a
flaky crash, not a reproducible one. The new-inode step is therefore mandatory for correctness, not an
optimisation, and the Rust implementation MUST assert that the inode changed before reporting a successful
incremental link. Verdict unchanged: **GO with caveats** (ad-hoc signatures only; keep DWARF out of signed
pages; clonefile needs APFS, so detect and report the copy fallback).
