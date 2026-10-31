#!/usr/bin/env python3
"""Memory-aware Lake build scheduler: one memcapped `lake build <Module>` per module that needs
building, in import order, packing light modules side by side and running heavy ones alone.

usage: scripts/lake-serial-build.py [options] TARGET...

TARGET is a module (`FV.Opt.Proof.RuleImm`), a prefix ending in `.` (`FV.Opt.Proof.`), or a
library name (`FV`, `FVTest`, `Corpus`). The targets and all their local imports are built.
Run from the worktree root (or pass --root). Afterwards `lake build FV FVTest <exes>` only links.

Which modules need building (batch check, off with --no-batch-check): one
`lake build --no-build <all wanted modules>` restores everything that is built or in the shared
cache (FV_LAKE_CACHE) and names the modules that are out of date; Lake does not look at their
dependents, so those stay unknown. Whenever modules whose imports are all done have not been
checked yet, one more `lake build --no-build` over all of them settles them (about 1-2 s each, instead
of one `lake build <M>` process per module). At the end, one check over every module confirms that
nothing is out of date (anything Lake still reports is built, at most 3 rounds).

Each module that needs building gets its own `scripts/memcap.sh` scope with cap = recorded peak ×
--margin + 0.5G (clamped to [--min-cap, --max-cap]; --default-cap for modules without a record).
Recorded peaks come from the --profile TSVs (`module<TAB>peak_mb<TAB>seconds`; later files
override earlier ones); every module actually built here is appended to --record with its scope's
cgroup memory.peak (all of lean's memory, as the cap counts it; GNU time's maxrss if no cgroup).

Cross-worktree dedup (with FV_LAKE_CACHE or LAKE_CACHE_DIR; off with --no-dedup): before
building a module the scheduler takes an flock in <cache>/.fv-inflight/, keyed by a hash of the
toolchain, lakefile.toml, lake-manifest.json and the sources of the module and its transitive
imports (equal keys imply equal Lake input traces). If another scheduler holds it, the module waits
(without using the budget) until that build ends, then `lake build <M>` restores it from the cache
(or builds it, if the other build failed).

Launch rules (checked every second):
  * light modules (recorded peak <= --heavy, cap <= --budget): run concurrently while the sum of
    caps <= --budget and at most --max-jobs run;
  * heavy modules (recorded peak > --heavy, or cap > --budget): run alone, and only when
    MemAvailable >= --heavy-avail, no other lean process has RSS above --heavy and no other memcap
    scope has MemoryMax (with --others-by-usage: current usage) above --heavy; otherwise they are
    deferred while light work continues (a deferred module is first probed once with
    `lake build --no-build`: if it is already built or in the cache, it counts as done). Waiting
    heavy modules queue machine-wide, oldest first (/tmp/clifv-heavy-queue): only the head may
    start, and every scheduler leaves room in the clifv slice for the head's recorded peak;
  * clifv slice (the systemd slice of every memcap scope, $FV_SLICE, default clifv.slice; skipped
    if it has no MemoryHigh/MemoryMax or with --no-slice-gate): a module starts only if its
    recorded peak fits under the slice's limit minus --slice-margin, counting the slice's current
    non-file memory plus what this scheduler's running modules are still expected to add
    (above the limit, the kernel throttles every clifv build and systemd-oomd kills scopes);
  * nothing new starts while MemAvailable < --pause-avail;
  * a module killed at its own cap (its scope's memory.events `oom` > 0; without that information,
    exit 137/143 or lean reporting signal 9) is retried alone at twice the cap (at most --max-cap);
    a module killed from outside (systemd-oomd under global memory pressure, the slice's limit) is
    retried at the same cap, up to 3 times; with --retry-failed, any other failed module is
    retried once alone at its cap.
Ready modules are started longest-remaining-critical-path first (recorded seconds); when the first
one does not fit the budget, it reserves it and only modules that cannot delay it are backfilled.
A module that must run alone (heavy, or a retry) keeps its turn once it starts draining: until the
running modules finish, only modules whose recorded seconds end before theirs start.

Logs: OUT/sched.log (one line per start/finish/check) and OUT/<module>.log / .time / .mem.
"""
import argparse, fcntl, hashlib, os, pathlib, re, signal, subprocess, sys, time, tomllib

GiB = 1024 ** 3
CGROUP_USER = pathlib.Path(f"/sys/fs/cgroup/user.slice/user-{os.getuid()}.slice/"
                           f"user@{os.getuid()}.service")
SLICE = CGROUP_USER / os.environ.get("FV_SLICE", "clifv.slice")
HEAVY_QUEUE = pathlib.Path("/tmp/clifv-heavy-queue")
EXTERNAL_RETRIES = 3


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
    for s in (CGROUP_USER / "app.slice").glob("run-*.scope"):
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


def slice_room():
    """Bytes the clifv slice can still take before its MemoryHigh/MemoryMax: limit minus current
    usage without page cache (reclaimable). None if the slice has no limit (or no cgroup)."""
    try:
        lims = [int(v) for v in ((SLICE / "memory.high").read_text().strip(),
                                 (SLICE / "memory.max").read_text().strip()) if v != "max"]
        cur = int((SLICE / "memory.current").read_text())
        stat = dict(line.split() for line in (SLICE / "memory.stat").read_text().splitlines())
        cur -= int(stat.get("file", 0))
    except (OSError, ValueError):
        return None
    return min(lims) - cur if lims else None


def read_int(p):
    try:
        return int(p.read_text().split()[0])
    except (OSError, ValueError, IndexError):
        return None


def pid_alive(pid):
    try:
        return "lake-serial-build" in pathlib.Path(f"/proc/{pid}/cmdline").read_bytes().decode(errors="replace")
    except OSError:
        return False


def heavy_queue_head():
    """Oldest live ticket of /tmp/clifv-heavy-queue: (pid, peak bytes, module) or None."""
    best = None
    try:
        files = list(HEAVY_QUEUE.iterdir())
    except OSError:
        return None
    for f in files:
        try:
            t, pid = map(int, f.name.split("-"))
            est, mod = f.read_text().split()[:2]
        except (OSError, ValueError):
            continue
        if not pid_alive(pid):
            try:
                f.unlink()
            except OSError:
                pass
            continue
        if best is None or (t, pid) < best[0]:
            best = ((t, pid), pid, int(est), mod)
    return best[1:] if best else None


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


def source_keys(root, mods, imports, want):
    """Dedup key per module: hash of the toolchain, lakefile, manifest, the module's name and
    source, and its imports' keys. Equal keys imply equal Lake input traces; a collision would only
    cost a needless wait (the module is then built or restored by `lake build` as usual)."""
    salt = hashlib.sha256()
    for f in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        p = root / f
        salt.update(f.encode() + b"\0" + (p.read_bytes() if p.exists() else b"") + b"\0")
    keys = {}
    for m0 in want:
        todo = [m0]
        while todo:
            m = todo[-1]
            if m in keys:
                todo.pop()
                continue
            pend = [d for d in imports[m] if d not in keys]
            if pend:
                todo.extend(pend)
                continue
            todo.pop()
            h = salt.copy()
            h.update(m.encode() + b"\0" + mods[m].read_bytes() + b"\0")
            for d in sorted(set(imports[m])):
                h.update(keys[d].encode())
            keys[m] = h.hexdigest()[:32]
    return keys


def archive_failed_attempt(out, module, source, unit, cap, rc, seconds):
    """Preserve the failed files before start() can truncate them for a retry."""
    import json
    attempt = out / "failed-attempts" / f"{unit}-{time.time_ns()}"
    attempt.mkdir(parents=True)
    artifacts = {}
    for suffix in ("log", "mem", "time"):
        path = out / f"{module}.{suffix}"
        if path.is_file():
            data = path.read_bytes()
            (attempt / path.name).write_bytes(data)
            artifacts[path.name] = hashlib.sha256(data).hexdigest()
    (attempt / "attempt.json").write_text(json.dumps({
        "module": module, "unit": unit, "cap_bytes": cap,
        "returncode": rc, "seconds": seconds,
        "module_source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "artifacts": artifacts,
    }, indent=2) + "\n")
    return attempt


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("targets", nargs="+")
    ap.add_argument("--root", default=".")
    ap.add_argument("--out", default=None, help="log dir (default ${TMPDIR:-/tmp}/lake-serial-build-<pid>)")
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
    ap.add_argument("--only", metavar="FILE",
                    help="build only the modules listed in FILE (whitespace-separated); their "
                         "other imports count as built (CI: earlier waves, restored from the cache); "
                         "any the batch check finds out of date are scheduled here too")
    ap.add_argument("--retry-failed", action="store_true",
                    help="retry a failed module once, alone (CI: wall-clock limits such as "
                         "bv_decide's SAT timeout can fail on a loaded runner)")
    ap.add_argument("--no-batch-check", action="store_true",
                    help="start one `lake build <M>` per module, also for modules that are built or "
                         "cached (the behaviour before the batch check)")
    ap.add_argument("--no-dedup", action="store_true",
                    help="do not wait for other worktrees that are building the same module")
    ap.add_argument("--no-slice-gate", action="store_true",
                    help="ignore the clifv slice's memory limit and the machine-wide heavy queue")
    ap.add_argument("--slice-margin", default="4G",
                    help="headroom kept below the clifv slice's MemoryHigh/MemoryMax")
    a = ap.parse_args()
    for sig in (signal.SIGTERM, signal.SIGHUP):
        signal.signal(sig, lambda s, _f: sys.exit(128 + s))  # run the clean-up in main()'s finally

    root = pathlib.Path(a.root).resolve()
    out = pathlib.Path(a.out or f"{os.environ.get('TMPDIR') or '/tmp'}/lake-serial-build-{os.getpid()}")
    budget, heavy = size(a.budget), size(a.heavy)
    heavy_avail, pause_avail = size(a.heavy_avail), size(a.pause_avail)
    min_cap, default_cap, max_cap = size(a.min_cap), size(a.default_cap), size(a.max_cap)
    slice_margin = size(a.slice_margin)
    record = root / a.record
    profiles = a.profile or [root / "scripts/lake-module-peaks.tsv", record]
    memcap = str(root / "scripts/memcap.sh")

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
    assumed = set()
    if a.only:
        only = set(pathlib.Path(a.only).read_text().split())
        if only - want:
            sys.exit(f"--only lists modules outside the targets: {sorted(only - want)[:5]}")
        assumed = want - only

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

    def est_peak(m, c):
        # expected peak for the slice gate: the recorded one, else half the cap
        return prof[m][0] if m in prof else c // 2

    def downstream(ms):
        seen, todo = set(), list(ms)
        while todo:
            for r in rdeps.get(todo.pop(), []):
                if r not in seen:
                    seen.add(r)
                    todo.append(r)
        return seen

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

    status = {m: "ok" for m in assumed}  # m -> ok | fail | blocked
    running = {}           # m -> (Popen, t0, cap, unit)
    solo_set = set()       # running modules that must run alone
    retry_cap = {}         # m -> cap for the solo retry (after an OOM kill, or --retry-failed)
    retried = set()        # modules already retried alone after a failure (--retry-failed)
    external = {}          # m -> kills from outside (systemd-oomd, slice limit), retried at the same cap
    probed = set()         # deferred heavy modules already checked with `lake build --no-build`
    ood = set()            # modules a batch check reported out of date (their imports were done)
    polled = {}            # m -> highest memory.peak seen while running
    t_start = time.time()
    built = 0
    seq = 0
    me = os.getpid()

    # ---- batch up-to-date check ------------------------------------------------------------
    failed_job = re.compile(r"^✖ \[\d+/\d+\] (\S+) (\S+)", re.M)
    nchecks, tcheck = 0, 0.0

    def batch_check(ms):
        """One `lake build --no-build` over ms (Lake restores whatever is built or cached): the set
        of modules Lake reports out of date, or None if Lake failed some other way."""
        nonlocal nchecks, tcheck
        t0 = time.time()
        env = dict(os.environ, FV_MEMCAP="4G")
        r = subprocess.run([memcap, "lake", "build", "--no-build", *sorted(ms)], cwd=root, env=env,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                           errors="replace")
        nchecks += 1
        tcheck += time.time() - t0
        jobs = failed_job.findall(r.stdout)
        bad = {n for v, n in jobs if v == "Building" and n in mods}
        if r.returncode != 0 and (not bad or len(bad) < len(jobs)):
            (out / f"check{nchecks}.log").write_text(r.stdout)
            say(f"check of {len(ms)} modules: lake rc={r.returncode} without a clear out-of-date "
                f"list (out/check{nchecks}.log); building them one by one")
            return None
        return bad

    def unassume(bad):
        """--only: an import assumed built that Lake reports out of date is not in the cache (e.g.
        an earlier shard's copy of one of its imports lost to a differing copy from another shard:
        Lean's output is not always reproducible). Schedule it and the assumed modules importing
        it here, instead of letting the first `lake build <M>` that needs them rebuild them
        unscheduled (CI run 40769795369: `lake build FV.Opt.Proof.RuleAll` rebuilt 42 imports
        side by side, swapped, and took 3 h)."""
        stale = bad & assumed
        if not stale:
            return
        redo = stale | (downstream(stale) & assumed)
        assumed.difference_update(redo)
        for m in redo:
            del status[m]
        ood.update(stale)
        if inflight:
            keys.update(source_keys(root, mods, imports, redo))
        say(f"{len(stale)} imports assumed built are not in the cache; building them and "
            f"{len(redo) - len(stale)} assumed importers here: {' '.join(sorted(stale))}")

    def settle(ms, what):
        """Batch-check ms: reported -> ood; unreported with no reported import -> ok. The rest
        (what="all": modules importing a reported one) stay unknown; for what="ready" (all their
        imports done) anything Lake did not settle is built one by one."""
        ms = set(ms)
        t0 = time.time()
        bad = batch_check(ms)
        if bad is None:
            ood.update(ms)
            return
        unassume(bad)
        unknown = downstream(bad)
        fresh = ms - bad - unknown
        for m in fresh:
            status[m] = "ok"
        ood.update(bad & ms if what == "all" else ms - fresh)
        say(f"check ({what}) {len(ms)} modules in {time.time() - t0:.1f}s: {len(fresh)} up-to-date, "
            f"{len(bad & ms)} out of date, {len(ms & unknown)} wait for those")

    # ---- cross-worktree in-flight dedup -----------------------------------------------------
    cache_dir = os.environ.get("FV_LAKE_CACHE") or os.environ.get("LAKE_CACHE_DIR")
    inflight = pathlib.Path(cache_dir) / ".fv-inflight" if cache_dir and not a.no_dedup else None
    keys = {}
    if inflight:
        try:
            inflight.mkdir(parents=True, exist_ok=True)
            keys = source_keys(root, mods, imports, want - assumed)
        except OSError as e:
            say(f"dedup off: {e}")
            inflight = None
    locks = {}             # m -> (fd, path) held while m builds
    peer_wait = {}         # m -> time we first found another worktree building it
    deduped = 0

    def claim(m):
        """Take m's in-flight lock (True), or False if another scheduler is building m."""
        nonlocal deduped
        if inflight is None or m in locks:
            return True
        path = inflight / f"{keys[m]}.lock"
        while True:
            fd = os.open(path, os.O_RDWR | os.O_CREAT | os.O_CLOEXEC, 0o644)
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                if m not in peer_wait:
                    peer_wait[m] = time.time()
                    try:
                        holder = os.read(fd, 300).decode(errors="replace").strip()
                    except OSError:
                        holder = "?"
                    say(f"wait {m}: another worktree is building it ({holder})")
                os.close(fd)
                return False
            try:
                same = os.stat(path).st_ino == os.fstat(fd).st_ino
            except FileNotFoundError:
                same = False
            if same:
                break
            os.close(fd)  # the holder removed the file after we opened it: retry on the new one
        os.ftruncate(fd, 0)
        os.write(fd, f"{root} pid {me}".encode())
        locks[m] = (fd, path)
        if m in peer_wait:
            deduped += 1
            say(f"peer done {m} after {time.time() - peer_wait.pop(m):.0f}s; restoring it")
        return True

    def release(m):
        if m in locks:
            fd, path = locks.pop(m)
            try:
                os.unlink(path)
            except OSError:
                pass
            os.close(fd)

    # ---- machine-wide heavy queue -------------------------------------------------------------
    use_slice = not a.no_slice_gate
    ticket = None          # (path, module) of this scheduler's waiting heavy module
    queued_at = {}         # m -> time it first queued (keeps its place when it re-queues)

    def enqueue(m, est):
        nonlocal ticket
        if not use_slice:
            return
        if ticket and ticket[1] == m:
            return
        dequeue()
        try:
            HEAVY_QUEUE.mkdir(mode=0o777, exist_ok=True)
            HEAVY_QUEUE.chmod(0o1777)
        except OSError:
            pass
        try:
            p = HEAVY_QUEUE / f"{queued_at.setdefault(m, time.time_ns())}-{me}"
            p.write_text(f"{est} {m}\n")
            ticket = (p, m)
        except OSError:
            pass

    def dequeue():
        nonlocal ticket
        if ticket:
            try:
                ticket[0].unlink()
            except OSError:
                pass
            ticket = None

    build_dir = (root / ".lake/build").resolve()
    perm_denied = re.compile(r"permission denied \(error code: 13\)\s*\n\s*file: (\S+)")
    perm_fixed = set()     # modules retried after unlinking read-only outputs

    def unlink_readonly(paths):
        """Remove read-only files (hard links into the shared Lake cache, mode 0444) under
        .lake/build. Lean rewrites .ilean/.c in place (open with O_TRUNC), which fails with
        `permission denied (error code: 13)` on such a link; unlinking first lets it write a new
        file and leaves the cache entry, shared with every other worktree, untouched."""
        n = 0
        for p in paths:
            try:
                p = pathlib.Path(p)
                if build_dir not in p.resolve().parents or p.stat().st_mode & 0o200:
                    continue
                p.unlink()
                n += 1
            except OSError:
                pass
        return n

    def outputs(m):
        """m's files in .lake/build (lib/lean/<M>.*, ir/<M>.*)."""
        rel = m.replace(".", "/")
        stem = rel.rsplit("/", 1)[-1]
        for d in (build_dir / "lib/lean", build_dir / "ir"):
            parent = (d / rel).parent
            try:
                yield from (q for q in parent.iterdir() if q.name.split(".", 1)[0] == stem)
            except OSError:
                pass

    def module_of(path):
        for d in (build_dir / "lib/lean", build_dir / "ir"):
            try:
                rel = pathlib.Path(path).relative_to(d)
            except ValueError:
                continue
            return ".".join(rel.parent.parts + (rel.name.split(".", 1)[0],))
        return None

    def start(m, c):
        nonlocal seq
        seq += 1
        unit = f"fvb-{me}-{seq}-" + re.sub(r"[^A-Za-z0-9_.:-]", "_", m)[:120]
        if m in ood:
            # known out of date: its old outputs are stale anyway (see unlink_readonly)
            unlink_readonly(outputs(m))
        for ext in ("mem", "time"):
            (out / f"{m}.{ext}").unlink(missing_ok=True)
        env = dict(os.environ, FV_MEMCAP=f"{c // 2 ** 20}M",
                   LEAN_NUM_THREADS=os.environ.get("LEAN_NUM_THREADS", "2"),
                   FV_MEMCAP_UNIT=unit, FV_MEMCAP_STATS=str(out / f"{m}.mem"))
        f = open(out / f"{m}.log", "w")
        timing = (["/usr/bin/time", "-v", "-o", str(out / f"{m}.time")]
                  if pathlib.Path("/usr/bin/time").is_file() else
                  [sys.executable, str(root / "scripts/lake-time.py"), str(out / f"{m}.time")])
        # own process group: on exit (SIGTERM, Ctrl-C, crash) the scheduler stops its builds, so a
        # restarted scheduler never builds a module twice in one worktree (the second lean then
        # fails writing over the first one's read-only cache links)
        p = subprocess.Popen([*timing, memcap, "lake", "build", m], cwd=root, env=env, stdout=f,
                             stderr=subprocess.STDOUT, start_new_session=True)
        running[m] = (p, time.time(), c, unit)
        polled.pop(m, None)
        say(f"start {m} cap={gib(c)} running={len(running)} "
            f"avail={gib(mem_available())}")

    def up_to_date(m):
        # `lake build --no-build` fails without building if m is out of date; with the shared
        # cache it also restores m's artifacts. Lake alone needs little memory.
        env = dict(os.environ, FV_MEMCAP="4G")
        r = subprocess.run([memcap, "lake", "build", "--no-build", m],
                           cwd=root, env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        return r.returncode == 0

    def my_pids():
        pids = {me}
        for p, _, _, _ in running.values():
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

    def mem_stats(m):
        try:
            return {k: int(v) for k, v in
                    (line.split() for line in (out / f"{m}.mem").read_text().splitlines())}
        except (OSError, ValueError):
            return None

    def oomd_killed(unit, t0):
        try:
            r = subprocess.run(["journalctl", "-u", "systemd-oomd", "-q", "--no-pager", "-o", "cat",
                                f"--since=@{int(t0)}", "-g", re.escape(unit)],
                               stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True, timeout=30)
            return bool(r.stdout.strip())
        except (OSError, subprocess.SubprocessError):
            return False

    say(f"want {len(want)} modules ({len(assumed)} assumed built) budget={gib(budget)} "
        f"max_jobs={a.max_jobs} heavy>{gib(heavy)}")
    batch = not a.no_batch_check
    if batch and want - assumed:
        settle(want - assumed, "all")
    verify_rounds = 0
    last_wait = ""
    draining = None  # the solo module waiting for the running ones to finish
    try:
        while True:
            for m, (p, t0, c, unit) in list(running.items()):
                pk = read_int(SLICE / f"{unit}.scope" / "memory.peak")
                if pk:
                    polled[m] = max(polled.get(m, 0), pk)
                rc = p.poll()
                if rc is None:
                    continue
                del running[m]
                solo_set.discard(m)
                release(m)
                dt = time.time() - t0
                rss = 0
                try:
                    t = (out / f"{m}.time").read_text()
                    rss = int(re.search(r"Maximum resident set size \(kbytes\): (\d+)", t).group(1)) * 1024
                except (OSError, AttributeError):
                    pass
                st = mem_stats(m)
                peak = (st or {}).get("peak") or polled.get(m, 0)
                text = (out / f"{m}.log").read_text(errors="replace")
                did_build = re.search(r"Built " + re.escape(m) + r"\b", text) is not None
                killed = (rc in (137, 143) or bool(st and st.get("oom"))
                          or re.search(r"exit code (137|143)|signal 9|Killed", text) is not None)
                # killed at its own cap: the scope's oom counter (the stats file); without it (a
                # kill from outside stops the whole scope), not if systemd-oomd logged the kill
                # or the last polled peak was clearly below the cap
                oomd = False
                if killed and not (st and "oom" in st):
                    oomd = oomd_killed(unit, t0)
                own = (st["oom"] > 0 if st and "oom" in st
                       else not (oomd or (m in polled and polled[m] < 0.9 * c)))
                why = ""
                if rc != 0:
                    archive_failed_attempt(out, m, mods[m], unit, c, rc, dt)
                if rc == 0:
                    status[m] = "ok"
                    if did_build:
                        built += 1
                        rec.write(f"{m}\t{(peak or rss) // 2 ** 20}\t{dt:.0f}\n"); rec.flush()
                elif (bad_files := perm_denied.findall(text)) and m not in perm_fixed:
                    # a module Lake rebuilt over a read-only cache link: unlink, retry once
                    perm_fixed.add(m)
                    n = unlink_readonly([q for b in bad_files if (x := module_of(b))
                                         for q in outputs(x)])
                    why = f" after unlinking {n} read-only cache links"
                elif killed and not own and external.get(m, 0) < EXTERNAL_RETRIES:
                    # killed from outside: back to the queue at the same cap (not alone)
                    external[m] = external.get(m, 0) + 1
                    why = " (killed by systemd-oomd)" if oomd else " (killed from outside)"
                elif killed and own and c < max_cap:
                    retry_cap[m] = min(max_cap, 2 * c)
                elif a.retry_failed and m not in retried:
                    retried.add(m)
                    retry_cap[m] = c
                else:
                    status[m] = "fail"
                after = (status[m] if m in status else
                         f"retry {gib(c)}{why}" if m not in retry_cap else
                         f"retry {gib(retry_cap[m])}")
                say(f"done {m} rc={rc} {dt:.0f}s maxrss={rss / GiB:.1f}G cgpeak={peak / GiB:.1f}G "
                    f"{'built' if did_build else 'up-to-date'} -> {after}")
            changed = True
            while changed:
                changed = False
                for m in want:
                    if m not in status and any(status.get(d) in ("fail", "blocked") for d in imports[m]):
                        status[m] = "blocked"; changed = True
            pending = [m for m in want if m not in status and m not in running]
            ready = sorted((m for m in pending if all(status.get(d) == "ok" for d in imports[m])),
                           key=lambda m: (-crit[m], m))
            if batch:
                unchecked = [m for m in ready if m not in ood]
                if unchecked:
                    settle(unchecked, "ready")
                    continue
            if not running and not ready:
                if not (batch and verify_rounds < 3 and want - assumed):
                    break
                verify_rounds += 1
                bad = batch_check(want - assumed)
                nassumed = len(assumed)
                unassume(bad or set())
                redo = {m for m in (bad or ()) if status.get(m) == "ok" and m not in assumed}
                if not redo and len(assumed) == nassumed:
                    if bad is None:
                        say("final check inconclusive (see above)")
                    break
                for m in redo | downstream(redo):
                    if status.get(m) == "ok" and m not in assumed:
                        del status[m]
                ood.update(redo)
                say(f"final check: {len(redo)} modules still out of date: {' '.join(sorted(redo)[:10])}")
                continue
            avail = mem_available()
            wait = ""
            room = slice_room() if use_slice else None
            head = heavy_queue_head() if use_slice else None
            if room is not None:
                room -= slice_margin
                for x, (_, _, cx, ux) in running.items():
                    cur = read_int(SLICE / f"{ux}.scope" / "memory.current") or 0
                    room -= max(0, est_peak(x, cx) - cur)
                if head and head[0] != me:
                    room -= head[1]   # leave room for the oldest waiting heavy module
            if avail < pause_avail:
                wait = f"paused: MemAvailable {gib(avail)} < {gib(pause_avail)}"
            elif not (solo_set & running.keys()):
                used = sum(c for (_, _, c, _) in running.values())
                now = time.time()
                reserve = None  # (shadow time, spare budget then) held for the first light module that did not fit
                # A solo module that is draining keeps its turn: it goes first, and until it starts
                # only modules expected to finish before the running ones do (solo_shadow) start.
                # Without this, modules ranked above it kept the scheduler busy and it never ran.
                solo_shadow = None
                if draining not in ready:
                    draining = None
                for m in ([draining] if draining else []) + [m for m in ready if m != draining]:
                    c = retry_cap.get(m, cap[m])
                    est = est_peak(m, c)
                    if is_heavy(m, c):
                        others = other_heavy_scopes(my_pids(), heavy, a.others_by_usage)
                        queued = head is not None and head[0] != me
                        if avail < heavy_avail or others or queued or (room is not None and room < est):
                            # a heavy module that is already built (or in the cache) need not wait
                            if m not in probed:
                                probed.add(m)
                                if up_to_date(m):
                                    status[m] = "ok"
                                    say(f"done {m} up-to-date (probe) -> ok")
                                    if ticket and ticket[1] == m:
                                        dequeue()
                                    continue
                            if not (ticket and ticket[1] != m):
                                enqueue(m, est)
                            wait = (f"deferring heavy {m} ({gib(c)}): avail {gib(avail)}"
                                    f"{', other heavy scopes ' + ' '.join(others) if others else ''}"
                                    f"{', queued behind ' + head[2] if queued else ''}"
                                    f"{', clifv slice room ' + gib(max(room, 0)) if room is not None and room < est else ''}")
                            continue
                    elif m not in retry_cap:
                        if len(running) >= a.max_jobs:
                            break
                        if solo_shadow is not None and now + secs[m] > solo_shadow:
                            continue
                        if room is not None and est > room:
                            wait = f"clifv slice: room {gib(max(room, 0))} < {gib(est)} for {m}"
                            break
                        fits = used + c <= budget
                        if reserve is None and not fits:
                            # reserve the budget for m: when do enough running modules finish?
                            free, shadow = budget - used, now
                            for end, cc in sorted((max(now, t0 + secs[x]), cc)
                                                  for x, (_, t0, cc, _) in running.items()):
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
                        if not claim(m):
                            continue
                        start(m, c)
                        used += c
                        if room is not None:
                            room -= est
                        if mem_available() < pause_avail:
                            break
                        continue
                    # solo: heavy module (gate passed) or retry after an OOM kill; drain first
                    if solo_shadow is not None:
                        continue  # another solo module is draining
                    if running:
                        # our own light modules hold the memory, not the machine: do not block
                        # the other schedulers' heavy modules meanwhile (m keeps its queue place)
                        if ticket and ticket[1] == m:
                            dequeue()
                        draining = m
                        solo_shadow = max(max(now, t0 + secs[x]) for x, (_, t0, _, _) in running.items())
                        wait = f"draining for solo {m} ({gib(c)})"
                        continue
                    if not claim(m):
                        continue
                    if ticket and ticket[1] == m:
                        dequeue()
                    start(m, c)
                    solo_set.add(m)
                    draining = None
                    break
            key = re.sub(r"[\d.]+G", "", wait)
            if wait and key != last_wait:
                say(wait)
            last_wait = key
            time.sleep(1)
    finally:
        if running:
            say(f"stopping {len(running)} running builds: {' '.join(sorted(running))}")
            for sig in (signal.SIGTERM, signal.SIGKILL):
                for p, _, _, unit in running.values():
                    try:
                        os.killpg(p.pid, sig)
                    except OSError:
                        pass
                    subprocess.run(["systemctl", "--user", "kill", f"--signal={sig.name}",
                                    f"{unit}.scope"], stdout=subprocess.DEVNULL,
                                   stderr=subprocess.DEVNULL)
                t_end = time.time() + 10
                while time.time() < t_end and any(p.poll() is None for p, _, _, _ in running.values()):
                    time.sleep(0.2)
        dequeue()
        for m in list(locks):
            release(m)

    dt = time.time() - t_start
    for k in ("fail", "blocked"):
        bad = sorted(m for m in want if status.get(m) == k)
        if bad:
            say(f"{k} ({len(bad)}): " + " ".join(bad))
    ok = sum(1 for m in want if status.get(m) == "ok")
    if batch:
        say(f"{nchecks} batch checks, {tcheck:.0f}s; {deduped} modules restored after another "
            f"worktree built them")
    say(f"END {ok}/{len(want)} ok, {built} built, wall {dt / 60:.1f} min")
    return 0 if ok == len(want) else 1


if __name__ == "__main__":
    sys.exit(main())
