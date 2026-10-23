#!/usr/bin/env python3
"""Dynamic count of uninitialised stack reads by Lean-compiled code (UninitSem step 1c).

    uninit_dyn.py OUT.jsonl EXE...

For each `cargo fv` test executable: the Lean-compiled functions (nm: `__fvlean$` markers, as
scripts/fv-exec-trace.py), its test list (`--list`), then every test alone
(`--exact NAME --test-threads=1`) under a plugin-enabled qemu-aarch64 with uninit_plugin.so.
One JSON line per test run: exe, test, exit code, plugin summary.
"""
import json, os, subprocess, sys, tempfile

QEMU = os.environ.get("UNINIT_QEMU", "/tmp/uninitsem_qemu/qemu-10.2.1/build/qemu-aarch64")
PLUGIN = os.environ.get("UNINIT_PLUGIN", "/tmp/uninitsem_qemu/uninit_plugin.so")


def lean_funcs(exe, path):
    out = subprocess.run(["nm", "-S", exe], capture_output=True, text=True, check=True).stdout
    markers, funcs = set(), {}
    for l in out.splitlines():
        p = l.split()
        if p[-1].startswith("__fvlean$"):
            markers.add(int(p[0], 16))
        elif len(p) == 4 and p[2] in "tTwW" and int(p[1], 16) > 0:
            funcs.setdefault(int(p[0], 16), (int(p[1], 16), p[3]))
    n = 0
    with open(path, "w") as fh:
        for a in sorted(markers):
            if a in funcs:
                fh.write(f"{a:x} {a + funcs[a][0]:x} {funcs[a][1]}\n")
                n += 1
    return n


def main():
    outp, exes = sys.argv[1], sys.argv[2:]
    with open(outp, "w") as out, tempfile.TemporaryDirectory(prefix="uninitsem_") as tmp:
        for exe in exes:
            fl = os.path.join(tmp, "funcs.txt")
            nf = lean_funcs(exe, fl)
            lst = subprocess.run(["qemu-aarch64-static", exe, "--list", "--format=terse"],
                                 capture_output=True, text=True).stdout
            tests = [l[: -len(": test")] for l in lst.splitlines() if l.endswith(": test")]
            print(f"{exe}: {nf} Lean functions, {len(tests)} tests", flush=True)
            for t in tests:
                po = os.path.join(tmp, "plugin.json")
                if os.path.exists(po):
                    os.remove(po)
                r = subprocess.run([QEMU, "-plugin", f"{PLUGIN},funcs={fl},out={po}", exe,
                                    "--exact", t, "--test-threads=1", "-q"],
                                   capture_output=True, text=True, timeout=1800)
                summ = [json.loads(l) for l in open(po)] if os.path.exists(po) else []
                rec = {"exe": exe, "test": t, "rc": r.returncode, "plugin": summ}
                out.write(json.dumps(rec) + "\n"); out.flush()
                h = sum(s["hits"] for s in summ)
                print(f"  {t}: rc {r.returncode}, hits {h}", flush=True)


main()
