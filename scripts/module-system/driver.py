#!/usr/bin/env python3
"""Port-fix driver: build TARGETS on the ported tree (unmeasured, nice'd), apply the automatic
fixes to every failed module (autofix.py for meta errors, coreall/addall for decide/rfl/kernel
errors), repeat until a round changes nothing. Writes /home/user/ms/runs/<label>/driver.log.

usage: driver.py LABEL TARGET...
"""
import os, pathlib, re, subprocess, sys, time

label, targets = sys.argv[1], sys.argv[2:]
MS = pathlib.Path("/home/user/ms")
REPO = pathlib.Path("/home/user/workspace/repo")
outdir = MS / "runs" / label
outdir.mkdir(parents=True, exist_ok=True)
dlog = open(outdir / "driver.log", "a")


def say(*a):
    print(time.strftime("%H:%M:%S"), *a, file=dlog, flush=True)


REDUCE = re.compile(r"unsolved goals|maximum recursion|made no progress|Tactic `(decide|rfl)` failed|Application type mismatch|type mismatch|\(kernel\)|not definitionally equal|did not reduce|"
                    r"The rfl tactic failed|failed to reduce to true|Decidable` instance")
manual = {}
INTERP = re.compile(r"native_decide|IR of declaration|native implementation|\(interpreter\)")
CRASH = re.compile(r"exited with code (134|137)|signal 9|permission denied \(error code: 13\)")


def coreall_fix(m):
    r = subprocess.run([str(MS / "coreall.sh"), m], capture_output=True, text=True)
    union = (MS / "core-union.txt").read_text().split()
    lines = []
    for l in r.stdout.splitlines():
        mm, _, rest = l.partition(":")
        lines.append(mm + ": " + (" ".join(union) if "NOTBUILT" in rest else rest))
    add = subprocess.run(["python3", str(MS / "addall.py")], input="\n".join(lines) + "\n",
                         capture_output=True, text=True).stdout.strip()
    return bool(add.strip())


def fix_ux(failed, sched):
    """Un-expose mode: apply one fix per failed module and let the next round rebuild them all
    in parallel (no per-module rebuilds)."""
    changed = 0
    subprocess.run([str(MS / "mkidx.sh"), "/tmp/ms_idx_all.txt"], capture_output=True)
    for m in failed:
        log = sched / f"{m}.log"
        txt = log.read_text(errors="replace") if log.exists() else ""
        if CRASH.search(txt):
            say(f"  retry (crash/permission) {m}")
            changed += 1
            continue
        out = subprocess.run(["python3", str(MS / "autofix.py"), str(log)], cwd=REPO,
                             capture_output=True, text=True).stdout.strip()
        mode = "autofix"
        for flag in ([], ["--closure"], ["--files"]):
            if out:
                break
            out = subprocess.run(["python3", str(MS / "expose.py"), *flag, "/tmp/ms_idx_all.txt", str(log)],
                                 capture_output=True, text=True).stdout.strip()
            mode = "expose" + (flag[0] if flag else "")
        if out:
            if mode.startswith("expose"):
                with open(outdir / "exposed.tsv", "a") as ef:
                    ef.write("".join(f"{m}\t{l}\n" for l in out.splitlines()))
            say(f"  {mode} {m}: {out.count(chr(10)) + 1}: {out.replace(chr(10), '; ')[:300]}")
            changed += 1
        else:
            errs = [l[:200] for l in txt.splitlines() if l.startswith("error")][:3]
            say(f"  MANUAL {m}: {' | '.join(errs)}")
    return changed


def fix(failed, sched):
    if os.environ.get("UNEXPOSE"):
        return fix_ux(failed, sched)
    """Fix each failed module in place: autofix / import all, then rebuild it alone, repeat."""
    changed = 0
    for m in failed:
        if m in manual:
            continue
        log = sched / f"{m}.log"
        tried_core = False
        tried_mirror = tried_crash = False
        ok = False
        for it in range(25):
            txt = log.read_text(errors="replace") if log.exists() else ""
            out = subprocess.run(["python3", str(MS / "autofix.py"), str(log)], cwd=REPO,
                                 capture_output=True, text=True).stdout.strip()
            exp = ""
            if not out and os.environ.get("UNEXPOSE"):
                subprocess.run([str(MS / "mkidx.sh"), "/tmp/ms_idx_all.txt"], capture_output=True)
                exp = subprocess.run(["python3", str(MS / "expose.py"), "/tmp/ms_idx_all.txt", str(log)],
                                     capture_output=True, text=True).stdout.strip()
                if not exp:
                    exp = subprocess.run(["python3", str(MS / "expose.py"), "--closure", "/tmp/ms_idx_all.txt",
                                          str(log)], capture_output=True, text=True).stdout.strip()
                if not exp:
                    exp = subprocess.run(["python3", str(MS / "expose.py"), "--files", "/tmp/ms_idx_all.txt",
                                          str(log)], capture_output=True, text=True).stdout.strip()
                if exp:
                    with open(outdir / "exposed.tsv", "a") as ef:
                        ef.write("".join(f"{m}\t{l}\n" for l in exp.splitlines()))
                    say(f"  expose for {m}: {exp.count(chr(10)) + 1} defs: {exp.replace(chr(10), '; ')[:300]}")
            if exp:
                pass
            elif out:
                say(f"  autofix {m}: {out.replace(chr(10), '; ')}")
            elif INTERP.search(txt) and not tried_mirror:
                tried_mirror = True
                f = REPO / (m.replace(".", "/") + ".lean")
                n = subprocess.run(["python3", str(MS / "metamirror.py"), str(f)], capture_output=True,
                                   text=True).stdout.strip()
                if n in ("", "0"):
                    break
                say(f"  meta import mirror {m}: {n}")
            elif CRASH.search(txt) and not tried_crash:
                tried_crash = True
                say(f"  retry alone (crash/OOM) {m}")
            elif REDUCE.search(txt) and not tried_core and not os.environ.get("UNEXPOSE"):
                tried_core = True
                if coreall_fix(m):
                    say(f"  import all {m}")
                else:
                    break
            else:
                break
            changed += 1
            r = subprocess.run([str(MS / "try.sh"), m], capture_output=True, text=True)
            log = pathlib.Path(f"/tmp/ms_try_{m}.log")
            if "rc=0" in r.stdout:
                ok = True
                say(f"  fixed {m}")
                break
        if not ok:
            manual[m] = log.read_text(errors="replace") if log.exists() else ""
            errs = [l[:200] for l in manual[m].splitlines() if l.startswith("error")][:3]
            say(f"  MANUAL {m}: {' | '.join(errs)}")
    return changed


for rnd in range(1, 80):
    sched = outdir / f"r{rnd}"
    env = dict(os.environ, FV_LAKE_CACHE=str(MS / "cache-port-dev"))
    cmd = ["python3", "scripts/lake-serial-build.py", "--out", str(sched),
           "--record", str(outdir / "peaks.tsv"), "--profile", str(MS / "profile-ci.tsv"),
           "--profile", "scripts/lake-module-peaks.tsv", "--budget", os.environ.get("BUDGET", "7G"),
           "--max-jobs", os.environ.get("JOBS", "2"), "--heavy", "12G", "--heavy-avail", "20G",
           "--pause-avail", "3G", "--margin", "1.0", "--min-cap", "2G", "--max-cap", "28G",
           "--no-dedup", *targets]
    say(f"round {rnd}: build")
    done_fix = set()
    changed = 0
    f = open(outdir / f"r{rnd}.log", "w")
    proc = subprocess.Popen(cmd, cwd=REPO, env=env, stdout=f, stderr=subprocess.STDOUT)
    while True:
        try:
            rc = proc.wait(timeout=30)
            fin = True
        except subprocess.TimeoutExpired:
            fin = False
        log = (outdir / f"r{rnd}.log").read_text()
        failed = sorted(set(re.findall(r"done (\S+) rc=[1-9]\d* .*-> fail", log)) - done_fix)
        if os.environ.get("UNEXPOSE") and not fin:
            continue
        changed += fix(failed, sched)
        done_fix |= set(failed)
        if fin:
            break
    built = len(re.findall(r"built -> ok", log))
    say(f"round {rnd}: rc={rc} built={built} failed={len(done_fix)} changed={changed}")
    if rc == 0 and not done_fix:
        say("all built")
        break
    if not changed:
        say("no automatic fix left; stopping")
        break
(outdir / "DONE").write_text("\n".join(sorted(manual)) + "\n")
