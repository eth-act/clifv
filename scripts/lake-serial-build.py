#!/usr/bin/env python3
"""Memory-aware Lake build scheduler: one memcapped `lake build <Module>` per module, in import
order, packing light modules side by side and running heavy ones alone.

usage: scripts/lake-serial-build.py [options] TARGET...

TARGET is a module (`FV.Opt.Proof.RuleImm`), a prefix ending in `.` (`FV.Opt.Proof.`), or a
library name (`FV`, `FVTest`, `Corpus`). The targets and all their local imports are built.
Run from the worktree root (or pass --root). Afterwards `lake build FV FVTest <exes>` only links.

Each module gets its own `scripts/memcap.sh` scope with cap = recorded peak × --margin + 0.5G
(clamped to [--min-cap, --max-cap]; --default-cap for modules without a record). Recorded peaks
come from the --profile TSVs (`module<TAB>peak_mb<TAB>seconds`; later files override earlier
ones); every module actually built here is appended to --record, so estimates improve.

Launch rules (checked every second):
  * light modules (recorded peak <= --heavy, cap <= --budget): run concurrently while the sum of
    caps <= --budget and at most --max-jobs run;
  * heavy modules (recorded peak > --heavy, or cap > --budget): run alone, and only when
    MemAvailable >= --heavy-avail, no other lean process has RSS above --heavy and no other memcap
    scope has MemoryMax (with --others-by-usage: current usage) above --heavy; otherwise they are
    deferred while light work continues;
  * nothing new starts while MemAvailable < --pause-avail;
  * a module killed at its cap (exit 137/143, or lean reporting signal 9) is retried alone at
    twice the cap (at most --max-cap).
Ready modules are started longest-remaining-critical-path first (recorded seconds); when the first
one does not fit the budget, it reserves it and only modules that cannot delay it are backfilled.

Logs: OUT/sched.log (one line per start/finish) and OUT/<module>.log / .time.
"""
import argparse, os, pathlib, re, subprocess, sys, time, tomllib

GiB = 1024 ** 3
CGROUP_APPS = pathlib.Path(f"/sys/fs/cgroup/user.slice/user-{os.getuid()}.slice/"
                           f"user@{os.getuid()}.service/app.slice")


def size(s):
    s = s.strip().upper()
    mult = {"G": GiB, "M": 1024 ** 2, "K": 1024}
    return int(float(s[:-1]) * mult[s[-1]]) if s[-1] in mult else int(s)


def gib(n):
    return f"{n // GiB}G" if n % GiB == 0 else f"{n / GiB:.1f}G"


def mem_available():
    for line in open("/proc/meminfo"):
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) * 1024
    return 0


def other_heavy_scopes(mine, heavy, by_usage=False):
    """Memcap scopes (systemd-run --scope) of other jobs that may use (by_usage: that do use) more
    than `heavy` bytes, and other lean processes whose RSS is above `heavy`."""
    out = []
    for s in CGROUP_APPS.glob("run-*.scope"):
        try:
            procs = set(map(int, (s / "cgroup.procs").read_text().split()))
            if not procs or procs & mine:
                continue
            mx = (s / "memory.max").read_text().strip()
            cur = int((s / "memory.current").read_text())
        except (OSError, ValueError):
            continue
        if cur > heavy or (not by_usage and (mx == "max" or int(mx) > heavy)):
            out.append(s.name)
    for d in pathlib.Path("/proc").iterdir():
        if not d.name.isdigit() or int(d.name) in mine:
            continue
        try:
            if (d / "comm").read_text().strip() != "lean":
                continue
            rss = int(re.search(r"VmRSS:\s+(\d+)", (d / "status").read_text()).group(1)) * 1024
        except (OSError, AttributeError):
            continue
        if rss > heavy:
            out.append(f"lean:{d.name}")
    return out


def load_modules(root):
    cfg = tomllib.loads((root / "lakefile.toml").read_text())
    libs = {}
    for lib in cfg.get("lean_lib", []):
        libs[lib["name"]] = root / lib.get("srcDir", ".")
    mods = {}
    for name, base in libs.items():
        for p in (base / name).rglob("*.lean"):
            mods[".".join(p.relative_to(base).with_suffix("").parts)] = p
        if (base / f"{name}.lean").exists():
            mods[name] = base / f"{name}.lean"
    imports = {}
    pat = re.compile(r"^(?:public\s+|meta\s+|private\s+)*import\s+(\S+)")
    for m, p in mods.items():
        deps = []
        for line in p.read_text(errors="replace").splitlines():
            mm = pat.match(line)
            if mm and mm.group(1) in mods:
                deps.append(mm.group(1))
        imports[m] = deps
    return libs, mods, imports


def load_profile(paths):
    prof = {}
    for p in paths:
        p = pathlib.Path(p)
        if not p.exists():
            continue
        for line in p.read_text().splitlines():
            f = line.split("\t")
            if len(f) >= 3 and not line.startswith("#"):
                prof[f[0]] = (int(f[1]) * 1024 ** 2, float(f[2]))
    return prof


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("targets", nargs="+")
    ap.add_argument("--root", default=".")
    ap.add_argument("--out", default=None, help="log dir (default /tmp/lake-serial-build-<pid>)")
    ap.add_argument("--budget", default="16G", help="sum of caps of concurrent light modules")
    ap.add_argument("--max-jobs", type=int, default=6)
    ap.add_argument("--heavy", default="12G", help="caps above this run alone")
    ap.add_argument("--heavy-avail", default="30G", help="MemAvailable needed to start a heavy module")
    ap.add_argument("--pause-avail", default="10G", help="start nothing while MemAvailable is below")
    ap.add_argument("--others-by-usage", action="store_true",
                    help="heavy gate: count other memcap scopes by current usage, not by their cap")
    ap.add_argument("--margin", type=float, default=1.2)
    ap.add_argument("--min-cap", default="3G")
    ap.add_argument("--default-cap", default="6G")
    ap.add_argument("--max-cap", default="22G")
    ap.add_argument("--profile", action="append",
                    help="peak TSVs (default scripts/lake-module-peaks.tsv, .lake/lake-module-peaks.tsv)")
    ap.add_argument("--record", default=".lake/lake-module-peaks.tsv")
    ap.add_argument("--dry-run", action="store_true", help="print the plan and exit")
    a = ap.parse_args()

    root = pathlib.Path(a.root).resolve()
    out = pathlib.Path(a.out or f"/tmp/lake-serial-build-{os.getpid()}")
    budget, heavy = size(a.budget), size(a.heavy)
    heavy_avail, pause_avail = size(a.heavy_avail), size(a.pause_avail)
    min_cap, default_cap, max_cap = size(a.min_cap), size(a.default_cap), size(a.max_cap)
    record = root / a.record
    profiles = a.profile or [root / "scripts/lake-module-peaks.tsv", record]

    libs, mods, imports = load_modules(root)
    prof = load_profile(profiles)

    roots = set()
    for t in a.targets:
        if t in libs:
            roots |= {m for m in mods if m == t or m.startswith(t + ".")}
        elif t.endswith("."):
            roots |= {m for m in mods if m.startswith(t)}
        elif t in mods:
            roots.add(t)
        else:
            sys.exit(f"unknown target {t}")
    want, stack = set(), list(roots)
    while stack:
        m = stack.pop()
        if m not in want:
            want.add(m)
            stack.extend(imports[m])

    def est_cap(m):
        if m not in prof:
            return default_cap
        c = prof[m][0] * a.margin + GiB // 2
        c = int(-(-c // GiB)) * GiB  # round up to whole GiB
        return max(min_cap, min(max_cap, c))

    cap = {m: est_cap(m) for m in want}
    secs = {m: prof.get(m, (0, 60.0))[1] for m in want}
    rdeps = {m: [] for m in want}
    for m in want:
        for d in imports[m]:
            rdeps[d].append(m)
    crit = {}

    def critical(m):
        # longest recorded-seconds path from m to any dependent sink
        todo = [m]
        while todo:
            x = todo[-1]
            pend = [r for r in rdeps[x] if r not in crit]
            if pend:
                todo.extend(pend)
                continue
            todo.pop()
            crit[x] = secs[x] + max((crit[r] for r in rdeps[x]), default=0)
        return crit[m]
    for m in want:
        critical(m)

    def is_heavy(m, c):
        return prof.get(m, (0, 0))[0] > heavy or c > budget

    nheavy = sum(1 for m in want if is_heavy(m, cap[m]))
    print(f"{len(want)} modules ({nheavy} heavy, {sum(1 for m in want if m not in prof)} "
          f"without a record); critical path {max(crit.values(), default=0) / 3600:.2f} h, "
          f"serial {sum(secs.values()) / 3600:.2f} h (recorded)")
    if a.dry_run:
        for m in sorted(want, key=lambda m: -cap[m])[:20]:
            print(f"  {gib(cap[m]):>4} {secs[m]:7.0f}s {m}")
        return 0

    out.mkdir(parents=True, exist_ok=True)
    log = open(out / "sched.log", "a")
    record.parent.mkdir(parents=True, exist_ok=True)
    rec = open(record, "a")

    def say(s):
        line = time.strftime("%H:%M:%S ") + s
        log.write(line + "\n"); log.flush()
        print(line, flush=True)

    status = {}            # m -> ok | fail | blocked
    running = {}           # m -> (Popen, t0, cap)
    solo_set = set()       # running modules that must run alone
    retry_cap = {}         # m -> cap for the solo retry after an OOM kill
    t_start = time.time()
    built = 0

    def start(m, c):
        env = dict(os.environ, FV_MEMCAP=f"{c // 2 ** 20}M",
                   LEAN_NUM_THREADS=os.environ.get("LEAN_NUM_THREADS", "2"))
        f = open(out / f"{m}.log", "w")
        p = subprocess.Popen(["/usr/bin/time", "-v", "-o", str(out / f"{m}.time"),
                              str(root / "scripts/memcap.sh"), "lake", "build", m],
                             cwd=root, env=env, stdout=f, stderr=subprocess.STDOUT)
        running[m] = (p, time.time(), c)
        say(f"start {m} cap={gib(c)} running={len(running)} "
            f"avail={gib(mem_available())}")

    def my_pids():
        pids = {os.getpid()}
        for p, _, _ in running.values():
            pids.add(p.pid)
        # children of /usr/bin/time (the systemd-run scope members)
        try:
            for d in pathlib.Path("/proc").iterdir():
                if d.name.isdigit():
                    try:
                        ppid = int((d / "stat").read_text().rsplit(")", 1)[1].split()[1])
                    except (OSError, IndexError, ValueError):
                        continue
                    if ppid in pids:
                        pids.add(int(d.name))
        except OSError:
            pass
        return pids

    say(f"want {len(want)} modules budget={gib(budget)} max_jobs={a.max_jobs} heavy>{gib(heavy)}")
    last_wait = ""
    while True:
        for m, (p, t0, c) in list(running.items()):
            rc = p.poll()
            if rc is None:
                continue
            del running[m]
            solo_set.discard(m)
            dt = time.time() - t0
            rss = 0
            try:
                t = (out / f"{m}.time").read_text()
                rss = int(re.search(r"Maximum resident set size \(kbytes\): (\d+)", t).group(1)) * 1024
            except (OSError, AttributeError):
                pass
            text = (out / f"{m}.log").read_text(errors="replace")
            did_build = re.search(r"Built " + re.escape(m) + r"\b", text) is not None
            oom = rc in (137, 143) or re.search(r"exit code (137|143)|signal 9|Killed", text)
            if rc == 0:
                status[m] = "ok"
                if did_build:
                    built += 1
                    rec.write(f"{m}\t{rss // 2 ** 20}\t{dt:.0f}\n"); rec.flush()
            elif oom and c < max_cap:
                retry_cap[m] = min(max_cap, 2 * c)
            else:
                status[m] = "fail"
            say(f"done {m} rc={rc} {dt:.0f}s maxrss={rss / GiB:.1f}G "
                f"{'built' if did_build else 'up-to-date'} -> "
                f"{status.get(m, 'retry ' + gib(retry_cap.get(m, 0)))}")
        changed = True
        while changed:
            changed = False
            for m in want:
                if m not in status and any(status.get(d) in ("fail", "blocked") for d in imports[m]):
                    status[m] = "blocked"; changed = True
        pending = [m for m in want if m not in status and m not in running]
        ready = sorted((m for m in pending if all(status.get(d) == "ok" for d in imports[m])),
                       key=lambda m: (-crit[m], m))
        if not running and not ready:
            break
        avail = mem_available()
        wait = ""
        if avail < pause_avail:
            wait = f"paused: MemAvailable {gib(avail)} < {gib(pause_avail)}"
        elif not (solo_set & running.keys()):
            used = sum(c for (_, _, c) in running.values())
            now = time.time()
            reserve = None  # (shadow time, spare budget then) held for the first light module that did not fit
            for m in ready:
                c = retry_cap.get(m, cap[m])
                if is_heavy(m, c):
                    others = other_heavy_scopes(my_pids(), heavy, a.others_by_usage)
                    if avail < heavy_avail or others:
                        wait = (f"deferring heavy {m} ({gib(c)}): avail {gib(avail)}"
                                f"{', other heavy scopes ' + ' '.join(others) if others else ''}")
                        continue
                elif m not in retry_cap:
                    if len(running) >= a.max_jobs:
                        break
                    fits = used + c <= budget
                    if reserve is None and not fits:
                        # reserve the budget for m: when do enough running modules finish?
                        free, shadow = budget - used, now
                        for end, cc in sorted((max(now, t0 + secs[x]), cc)
                                              for x, (_, t0, cc) in running.items()):
                            free, shadow = free + cc, end
                            if free >= c:
                                break
                        reserve = (shadow, free - c)
                        continue
                    if reserve is not None:
                        # backfill only what cannot delay the reserved module
                        shadow, spare = reserve
                        if not fits or (now + secs[m] > shadow and c > spare):
                            continue
                        if now + secs[m] > shadow:
                            reserve = (shadow, spare - c)
                    start(m, c)
                    used += c
                    if mem_available() < pause_avail:
                        break
                    continue
                # solo: heavy module (gate passed) or retry after an OOM kill; drain first
                if running:
                    wait = f"draining for solo {m} ({gib(c)})"
                    break
                start(m, c)
                solo_set.add(m)
                break
        key = re.sub(r"[\d.]+G", "", wait)
        if wait and key != last_wait:
            say(wait)
        last_wait = key
        time.sleep(1)

    dt = time.time() - t_start
    for k in ("fail", "blocked"):
        bad = sorted(m for m in want if status.get(m) == k)
        if bad:
            say(f"{k} ({len(bad)}): " + " ".join(bad))
    ok = sum(1 for m in want if status.get(m) == "ok")
    say(f"END {ok}/{len(want)} ok, {built} built, wall {dt / 60:.1f} min")
    return 0 if ok == len(want) else 1


if __name__ == "__main__":
    sys.exit(main())
