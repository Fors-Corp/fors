#!/usr/bin/env python3
"""
Acceptance test for the clone-patch-resign spike.
Exit code 0 only on full success of the positive-path assertions.
The negative control and the "same inode after exec" case are recorded but
are EXPECTED to demonstrate failure -- that is what proves the mechanism
(and the test) actually discriminates good signatures from bad ones.
"""
import os
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import resign
import toy_lib

WORK = tempfile.mkdtemp(prefix="macho_resign_spike_")
RESULTS = {}


def run(path):
    p = subprocess.run([path], capture_output=True, text=True)
    return p.returncode, p.stdout.strip(), p.stderr.strip()


def signal_desc(returncode):
    if returncode < 0:
        import signal
        try:
            name = signal.Signals(-returncode).name
        except ValueError:
            name = "?"
        return f"killed by signal {-returncode} ({name})"
    return f"exit code {returncode}"


def section(title):
    print(f"\n=== {title} ===")


def main():
    ok = True

    section("1. build toy + baseline run")
    toy = os.path.join(WORK, "toy")
    toy_lib.build_toy(toy, pad_bytes=0)
    rc, out, err = run(toy)
    print(f"baseline: rc={rc} out={out!r}")
    RESULTS["baseline"] = {"rc": rc, "out": out}
    ok &= (rc == 0 and out == "41")

    offset = toy_lib.find_value_offset(toy)
    print(f"magic value file offset = {offset}")

    section("2. positive path: clone-patch-rename (new inode), expect prints 42")
    positive = os.path.join(WORK, "toy_positive")
    shutil.copyfile(toy, positive)
    os.chmod(positive, 0o700)  # owner only: the spike runs these itself
    info = resign.clone_patch_rename(positive, offset, toy_lib.i32le(42))
    print("resign info:", info)
    rc, out, err = run(positive)
    print(f"patched: rc={rc} out={out!r}")
    RESULTS["positive_patch"] = {"rc": rc, "out": out, "resign_info": info}
    ok &= (rc == 0 and out == "42")

    section("3. codesign --verify --verbose on the patched clone")
    p = subprocess.run(["codesign", "--verify", "--verbose", positive],
                        capture_output=True, text=True)
    verdict = (p.stdout + p.stderr).strip()
    print(f"codesign rc={p.returncode}: {verdict}")
    RESULTS["codesign_verify_positive"] = {"rc": p.returncode, "verdict": verdict}
    ok &= (p.returncode == 0)

    section("4. NEGATIVE CONTROL: patch a clone's bytes WITHOUT fixing hashes")
    negative = os.path.join(WORK, "toy_negative")
    shutil.copyfile(toy, negative)
    os.chmod(negative, 0o700)  # owner only: the spike runs these itself
    resign.patch_and_resign(negative, offset, toy_lib.i32le(42), fix_hashes=False)
    rc, out, err = run(negative)
    desc = signal_desc(rc)
    print(f"negative control run: {desc}, stdout={out!r} stderr={err!r}")
    RESULTS["negative_control"] = {"rc": rc, "desc": desc, "out": out, "stderr": err}
    p2 = subprocess.run(["codesign", "--verify", "--verbose", negative],
                         capture_output=True, text=True)
    neg_verdict = (p2.stdout + p2.stderr).strip()
    print(f"codesign on negative control rc={p2.returncode}: {neg_verdict}")
    RESULTS["codesign_verify_negative"] = {"rc": p2.returncode, "verdict": neg_verdict}
    # This proves the test CAN fail: unpatched hashes must not silently succeed.
    negative_control_demonstrates_failure = (rc != 0) or (p2.returncode != 0)
    RESULTS["negative_control_demonstrates_failure"] = negative_control_demonstrates_failure
    ok &= negative_control_demonstrates_failure

    section("5. HARD CASE A: execute, then clone-patch-rename, then execute again")
    hard_a = os.path.join(WORK, "toy_hard_a")
    shutil.copyfile(toy, hard_a)
    os.chmod(hard_a, 0o700)  # owner only: the spike runs these itself
    ino_before = os.stat(hard_a).st_ino
    rc1, out1, _ = run(hard_a)
    print(f"exec #1 (pre-patch): rc={rc1} out={out1!r} inode={ino_before}")
    info_a = resign.clone_patch_rename(hard_a, offset, toy_lib.i32le(42))
    ino_after = os.stat(hard_a).st_ino
    rc2, out2, err2 = run(hard_a)
    desc2 = signal_desc(rc2)
    print(f"exec #2 (post clone-patch-rename): {desc2} out={out2!r} inode={ino_after} "
          f"(inode changed: {ino_before != ino_after})")
    RESULTS["hard_case_A_exec_then_clone_patch_rename"] = {
        "exec1": {"rc": rc1, "out": out1},
        "inode_before": ino_before, "inode_after": ino_after,
        "inode_changed": ino_before != ino_after,
        "exec2": {"rc": rc2, "out": out2, "desc": desc2},
    }
    ok &= (rc1 == 0 and out1 == "41" and rc2 == 0 and out2 == "42" and ino_before != ino_after)

    section("6. HARD CASE B: execute, then patch the SAME inode in place")
    hard_b = os.path.join(WORK, "toy_hard_b")
    shutil.copyfile(toy, hard_b)
    os.chmod(hard_b, 0o700)  # owner only: the spike runs these itself
    ino_b = os.stat(hard_b).st_ino
    rcb1, outb1, _ = run(hard_b)
    print(f"exec #1 (pre-patch): rc={rcb1} out={outb1!r} inode={ino_b}")
    # Patch bytes AND correctly fix the hashes, but on the SAME inode/file
    # descriptor lineage that has already been executed once.
    resign.patch_and_resign(hard_b, offset, toy_lib.i32le(42), fix_hashes=True)
    ino_b2 = os.stat(hard_b).st_ino
    rcb2, outb2, errb2 = run(hard_b)
    descb2 = signal_desc(rcb2)
    print(f"exec #2 (post in-place patch, same inode {ino_b2}): {descb2} "
          f"out={outb2!r} stderr={errb2!r}")
    RESULTS["hard_case_B_exec_then_patch_same_inode"] = {
        "exec1": {"rc": rcb1, "out": outb1},
        "inode": ino_b, "inode_after": ino_b2,
        "exec2": {"rc": rcb2, "out": outb2, "desc": descb2, "stderr": errb2},
    }
    # No assertion baked in here either way -- this is the empirical
    # data point the report needs, whichever way the kernel behaves.

    print("\n=== SUMMARY ===")
    import json
    print(json.dumps(RESULTS, indent=2))

    print(f"\nOVERALL: {'PASS' if ok else 'FAIL'}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
