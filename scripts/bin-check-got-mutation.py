#!/usr/bin/env python3
"""The binary check rejects an executable whose GOT slots are writable (#1093).

usage: bin-check-got-mutation.py BUNDLE_DIR LINK_CHECK [WORKDIR]

BUNDLE_DIR: a `cargo fv` bin-check directory (`target/fv/<mode>/bin-check/<tag>/`, its
`bundle.json`) of an executable whose program has GOT pairs (`adrp`/`ldr`; e.g.
examples/bigframe-unwind, 105 of them). The script copies the executable, zeroes the size of its
`PT_GNU_RELRO` header (the `.got` slots are then in a writable segment, neither `ro` nor
`relro`), points a copy of the bundle at it and runs `LINK_CHECK DIR --dead-cleanup --prune`.
It checks that link-check first passes on the original (`theorem:` named, exit 0) and then
reports `GOT: FAIL`, names no theorem and exits 1 on the copy, while the checker, the binary
checks and the code map still pass: `GotOk` alone rejects it (before #1093 this file was
`verified`). Exit 0 when both hold.
"""
import json
import pathlib
import shutil
import struct
import subprocess
import sys
import tempfile

PT_GNU_RELRO = 0x6474E552


def run(lc, d):
    p = subprocess.run([lc, str(d), "--dead-cleanup", "--prune"], capture_output=True, text=True)
    out = p.stdout + p.stderr
    field = lambda k: next((l.strip()[len(k):] for l in out.splitlines() if l.strip().startswith(k)), None)
    return p.returncode, field


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    src, lc = pathlib.Path(sys.argv[1]), sys.argv[2]
    work = pathlib.Path(sys.argv[3] if len(sys.argv) > 3 else tempfile.mkdtemp(prefix="got-mutation-"))
    rc, f = run(lc, src)
    if rc != 0 or not (f("theorem: ") or "none").startswith("E2E."):
        print(f"FAIL: the original is not verified (rc={rc}, theorem: {f('theorem: ')})")
        return 1
    b = json.loads((src / "bundle.json").read_text())
    exe = work / "exe"
    shutil.copy(b["exe"], exe)
    data = bytearray(exe.read_bytes())
    phoff = struct.unpack_from("<Q", data, 0x20)[0]
    phent, phnum = struct.unpack_from("<HH", data, 0x36)
    n = 0
    for i in range(phnum):
        o = phoff + i * phent
        if struct.unpack_from("<I", data, o)[0] == PT_GNU_RELRO:
            struct.pack_into("<QQ", data, o + 32, 0, 0)
            n += 1
    if n == 0:
        print("FAIL: no PT_GNU_RELRO header")
        return 1
    exe.write_bytes(data)
    b["exe"] = str(exe)
    (work / "b").mkdir(exist_ok=True)
    (work / "b" / "bundle.json").write_text(json.dumps(b))
    rc, f = run(lc, work / "b")
    got, thm = f("GOT: ") or "", f("theorem: ") or ""
    print(f"mutated: rc={rc}; okB: {f('okB: ')}; binary: {f('binary: ')}; code map: {f('code map: ')}; GOT: {got}; theorem: {thm}")
    ok = (rc == 1 and got.startswith("FAIL") and thm == "none (GotOk fails)" and f("okB: ") == "true"
          and (f("binary: ") or "").startswith("ok") and f("code map: ") == "ok")
    print("OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
