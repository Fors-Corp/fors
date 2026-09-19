#!/usr/bin/env python3
"""
resign.py -- clone-patch-resign a Mach-O ad-hoc-signed arm64 executable.

Mechanism under test for the Fors compiler feasibility spike:
  1. clone the target file to a NEW inode (clonefile(2) on APFS)
  2. patch dirty bytes at a given file offset in the clone
  3. recompute SHA-256 only for the CodeDirectory page slots the patch touched
     (for every embedded CodeDirectory -- ad-hoc binaries can carry more than one)
  4. fsync, then rename() the clone over the original path

Stdlib only: struct, hashlib, ctypes, os, subprocess, time.
"""
import ctypes
import hashlib
import os
import struct
import sys
import tempfile

# ---- Mach-O / code signing constants ----
MH_MAGIC_64 = 0xFEEDFACF
LC_SEGMENT_64 = 0x19
LC_CODE_SIGNATURE = 0x1D
LC_REQ_DYLD = 0x80000000

CSMAGIC_EMBEDDED_SIGNATURE = 0xFADE0CC0
CSMAGIC_CODEDIRECTORY = 0xFADE0C02

CSSLOT_CODEDIRECTORY = 0
# alternate code directories occupy slot indices 0x1000 .. 0x1005
CSSLOT_ALTERNATE_CODEDIRECTORIES = 0x1000
CSSLOT_ALTERNATE_CODEDIRECTORY_MAX = 5

CS_HASHTYPE_SHA1 = 1
CS_HASHTYPE_SHA256 = 2
CS_HASHTYPE_SHA256_TRUNCATED = 3
CS_HASHTYPE_SHA384 = 4

HASH_FUNCS = {
    CS_HASHTYPE_SHA1: lambda b: hashlib.sha1(b).digest(),
    CS_HASHTYPE_SHA256: lambda b: hashlib.sha256(b).digest(),
    CS_HASHTYPE_SHA256_TRUNCATED: lambda b: hashlib.sha256(b).digest()[:20],
    CS_HASHTYPE_SHA384: lambda b: hashlib.sha384(b).digest(),
}


class ResignError(RuntimeError):
    pass


# ---------------------------------------------------------------------------
# clonefile(2) via ctypes, with a copy fallback that is reported to the caller
# ---------------------------------------------------------------------------

def clone_file(src: str, dst: str) -> str:
    """Returns 'clonefile' or 'copy-fallback' depending on what actually happened."""
    libc = ctypes.CDLL(None, use_errno=True)
    try:
        clonefile = libc.clonefile
        clonefile.argtypes = [ctypes.c_char_p, ctypes.c_char_p, ctypes.c_int]
        clonefile.restype = ctypes.c_int
    except AttributeError:
        clonefile = None

    if os.path.exists(dst):
        os.unlink(dst)

    if clonefile is not None:
        rc = clonefile(src.encode(), dst.encode(), 0)
        if rc == 0:
            return "clonefile"
        errno = ctypes.get_errno()
        # fall through to copy fallback, report why
        sys.stderr.write(
            f"[resign] clonefile() failed (errno={errno}: {os.strerror(errno)}), "
            f"falling back to copy\n"
        )

    # Fallback: plain copy (NOT a new-inode-cheap clone; correctness only)
    import shutil
    shutil.copyfile(src, dst)
    return "copy-fallback"


# ---------------------------------------------------------------------------
# Mach-O parsing
# ---------------------------------------------------------------------------

class CodeDirectory:
    def __init__(self, blob_offset, cd_offset, header):
        (self.magic, self.length, self.version, self.flags, self.hashOffset,
         self.identOffset, self.nSpecialSlots, self.nCodeSlots, self.codeLimit,
         self.hashSize, self.hashType, self.platform, self.pageSizeLog2,
         self.spare2) = header
        self.blob_offset = blob_offset  # absolute file offset of this CD blob
        self.page_size = 1 << self.pageSizeLog2 if self.pageSizeLog2 else 4096

    def slot_file_offset(self, slot_index: int) -> int:
        """Absolute file offset of the hash bytes for code-page `slot_index`."""
        return self.blob_offset + self.hashOffset + slot_index * self.hashSize

    def pages_for_range(self, start: int, length: int):
        """Yield code-slot indices whose page overlaps [start, start+length)."""
        if length <= 0:
            return
        first_page = start // self.page_size
        last_byte = start + length - 1
        last_page = last_byte // self.page_size
        for p in range(first_page, last_page + 1):
            if p < self.nCodeSlots:
                yield p

    def page_content_range(self, slot_index: int):
        page_start = slot_index * self.page_size
        page_end = min(page_start + self.page_size, self.codeLimit)
        return page_start, page_end - page_start


CD_HEADER_FMT = ">IIIIIIIIIBBBBI"
CD_HEADER_SIZE = struct.calcsize(CD_HEADER_FMT)


def parse_mach_header(f):
    f.seek(0)
    data = f.read(32)
    magic, cputype, cpusubtype, filetype, ncmds, sizeofcmds, flags, reserved = \
        struct.unpack("<IiiIIIII", data)
    if magic != MH_MAGIC_64:
        raise ResignError(f"not a 64-bit Mach-O (magic=0x{magic:x})")
    return dict(ncmds=ncmds, sizeofcmds=sizeofcmds, header_size=32)


def find_code_signature_load_command(f, header):
    f.seek(header["header_size"])
    offset = header["header_size"]
    for _ in range(header["ncmds"]):
        cmd, cmdsize = struct.unpack("<II", f.read(8))
        if cmd == LC_CODE_SIGNATURE:
            rest = f.read(cmdsize - 8)
            dataoff, datasize = struct.unpack("<II", rest[:8])
            return dataoff, datasize
        f.seek(offset + cmdsize)
        offset += cmdsize
    return None


def parse_code_directories(f, cs_offset, cs_size):
    """Returns a list of CodeDirectory objects (primary + alternates)."""
    f.seek(cs_offset)
    sb = f.read(12)
    magic, length, count = struct.unpack(">III", sb)
    if magic != CSMAGIC_EMBEDDED_SIGNATURE:
        raise ResignError(f"no embedded SuperBlob (magic=0x{magic:x}) -- binary not signed?")

    entries = []
    for i in range(count):
        f.seek(cs_offset + 12 + i * 8)
        blob_type, blob_offset = struct.unpack(">II", f.read(8))
        entries.append((blob_type, blob_offset))

    cds = []
    for blob_type, blob_offset in entries:
        is_cd_slot = (blob_type == CSSLOT_CODEDIRECTORY) or \
            (CSSLOT_ALTERNATE_CODEDIRECTORIES <= blob_type <=
             CSSLOT_ALTERNATE_CODEDIRECTORIES + CSSLOT_ALTERNATE_CODEDIRECTORY_MAX)
        if not is_cd_slot:
            continue
        abs_off = cs_offset + blob_offset
        f.seek(abs_off)
        magic2, length2 = struct.unpack(">II", f.read(8))
        if magic2 != CSMAGIC_CODEDIRECTORY:
            continue
        f.seek(abs_off)
        header = struct.unpack(CD_HEADER_FMT, f.read(CD_HEADER_SIZE))
        cds.append(CodeDirectory(abs_off, abs_off, header))
    if not cds:
        raise ResignError("SuperBlob has no CodeDirectory blob")
    return cds


def load_signature_info(path):
    with open(path, "rb") as f:
        header = parse_mach_header(f)
        cs = find_code_signature_load_command(f, header)
        if cs is None:
            raise ResignError("no LC_CODE_SIGNATURE load command -- binary not signed")
        cs_offset, cs_size = cs
        cds = parse_code_directories(f, cs_offset, cs_size)
    return cs_offset, cs_size, cds


# ---------------------------------------------------------------------------
# Patch + selective re-hash
# ---------------------------------------------------------------------------

def patch_and_resign(path: str, patch_offset: int, patch_bytes: bytes,
                      fix_hashes: bool = True):
    """
    Patches `patch_bytes` at `patch_offset` directly into `path` and (if
    fix_hashes) recomputes exactly the CodeDirectory page-hash slots that
    the patch touches, for every CodeDirectory found. fsyncs before return.
    Returns dict with diagnostic info (slots touched per CD, etc).
    """
    cs_offset, cs_size, cds = load_signature_info(path)

    for cd in cds:
        if patch_offset + len(patch_bytes) > cd.codeLimit:
            raise ResignError(
                f"patch [{patch_offset}, {patch_offset+len(patch_bytes)}) "
                f"exceeds codeLimit={cd.codeLimit} -- refusing to patch signature data"
            )

    fd = os.open(path, os.O_RDWR)
    try:
        os.lseek(fd, patch_offset, os.SEEK_SET)
        os.write(fd, patch_bytes)

        touched = {}
        if fix_hashes:
            for idx, cd in enumerate(cds):
                slots = sorted(set(cd.pages_for_range(patch_offset, len(patch_bytes))))
                hash_fn = HASH_FUNCS.get(cd.hashType)
                if hash_fn is None:
                    raise ResignError(f"unsupported hashType={cd.hashType}")
                for slot in slots:
                    page_off, page_len = cd.page_content_range(slot)
                    os.lseek(fd, page_off, os.SEEK_SET)
                    page_data = os.read(fd, page_len)
                    new_hash = hash_fn(page_data)
                    slot_off = cd.slot_file_offset(slot)
                    os.lseek(fd, slot_off, os.SEEK_SET)
                    os.write(fd, new_hash[:cd.hashSize])
                touched[idx] = slots
        os.fsync(fd)
    finally:
        os.close(fd)
    return {"code_directories": len(cds), "slots_touched": touched}


def clone_patch_rename(target_path: str, patch_offset: int, patch_bytes: bytes,
                        fix_hashes: bool = True):
    """
    Full pipeline: clone target -> patch clone -> resign clone -> rename over
    target. Returns dict with timing-relevant diagnostic info including which
    clone strategy was used.
    """
    d = os.path.dirname(os.path.abspath(target_path))
    tmp_path = os.path.join(d, f".{os.path.basename(target_path)}.resign_tmp_{os.getpid()}_{id(patch_bytes)}")
    strategy = clone_file(target_path, tmp_path)
    try:
        info = patch_and_resign(tmp_path, patch_offset, patch_bytes, fix_hashes=fix_hashes)
        os.rename(tmp_path, target_path)
    except Exception:
        if os.path.exists(tmp_path):
            os.unlink(tmp_path)
        raise
    info["clone_strategy"] = strategy
    return info


def _cli():
    import argparse
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="cmd", required=True)

    pc = sub.add_parser("clone-patch-rename")
    pc.add_argument("target")
    pc.add_argument("offset", type=lambda s: int(s, 0))
    pc.add_argument("hexbytes")
    pc.add_argument("--no-fix-hashes", action="store_true")

    pp = sub.add_parser("patch-inplace")
    pp.add_argument("target")
    pp.add_argument("offset", type=lambda s: int(s, 0))
    pp.add_argument("hexbytes")
    pp.add_argument("--no-fix-hashes", action="store_true")

    pi = sub.add_parser("info")
    pi.add_argument("target")

    args = p.parse_args()
    if args.cmd == "info":
        cs_offset, cs_size, cds = load_signature_info(args.target)
        print(f"LC_CODE_SIGNATURE: offset=0x{cs_offset:x} size={cs_size}")
        for i, cd in enumerate(cds):
            print(f"  CD[{i}] version=0x{cd.version:x} hashType={cd.hashType} "
                  f"hashSize={cd.hashSize} pageSize={cd.page_size} "
                  f"nCodeSlots={cd.nCodeSlots} codeLimit={cd.codeLimit}")
        return

    data = bytes.fromhex(args.hexbytes)
    if args.cmd == "clone-patch-rename":
        result = clone_patch_rename(args.target, args.offset, data,
                                     fix_hashes=not args.no_fix_hashes)
    else:
        result = patch_and_resign(args.target, args.offset, data,
                                   fix_hashes=not args.no_fix_hashes)
    print(result)


if __name__ == "__main__":
    _cli()
