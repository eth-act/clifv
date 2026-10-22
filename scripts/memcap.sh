#!/usr/bin/env bash
# Run a command in its own memory-capped cgroup scope. If it (and its children, e.g. every
# `lean` process lake starts) exceed the cap, only this scope is killed (exit 137). The global
# OOM killer never fires, so the agent harness and the other agents survive.
#
# usage: scripts/memcap.sh <cmd> [args...]     cap: $FV_MEMCAP (default 16G)
#        FV_MEMCAP_OFF=1 runs <cmd> without a scope (CI runners: one job per VM, and swap must
#        stay usable for the modules that peak above the runner's RAM; .github/workflows/full-gate.yml)
#
# Optional (scripts/lake-serial-build.py sets both): FV_MEMCAP_UNIT=<name> names the scope
# <name>.scope (default: systemd's run-*.scope); FV_MEMCAP_STATS=<file> makes the scope write, when
# <cmd> exits, `peak <bytes>` (the scope's cgroup memory.peak: the real peak of lean and every
# other process in it, not lake's RSS) and its memory.events `oom`/`oom_kill` counters to <file>.
# `oom` > 0 means the scope hit its own cap; a scope killed from outside (systemd-oomd under
# global memory pressure, or the slice's limit) writes either no file or `oom 0`.
# The watchdog fallback writes the same file (peak = polled tree RSS, `oom 1` if it killed).
#
# Fallback: if the systemd user manager is unreachable (e.g. user@<uid> was OOM-killed and not
# restarted, so `systemd-run --user` says "Failed to connect to bus"), <cmd> runs in its own
# session/process group under a watchdog that polls the process tree's resident memory every
# 0.2 s (RssAnon + RssShmem from /proc; file-backed pages such as mmapped .olean files are
# reclaimable, like a cgroup's page cache, and shared between lean processes, so they are not
# counted) and SIGKILLs the whole tree with exit 137 above the cap. The watchdog is a child
# subreaper, so orphaned grandchildren stay in the tree. Exit status, signals and
# stdout/stderr pass through; one line on stderr says the fallback is in use. No RLIMIT_AS:
# Lean reserves far more virtual memory than it uses.
#
# Why: runaway Lean elaboration or kernel reduction (e.g. `decide`/`rfl` over the exported ISLE
# rule data) has reached 37-58 GB RSS on this 62 GB machine, which triggered global OOM kills.
# Those kills aborted the agent harness, which kills every running agent.
set -euo pipefail
# Shared Lake artifact cache (docs/TO-PROVE.md §7): with FV_LAKE_CACHE=<dir>, Lake stores each
# built module in <dir> (content-addressed by its input trace) and hard-links it back into
# .lake/build, so a worktree whose sources match an earlier build anywhere reuses it instead of
# rebuilding. <dir> should be on the worktrees' filesystem (hard links; else Lake copies).
if [ -n "${FV_LAKE_CACHE:-}" ]; then
  export LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true LAKE_CACHE_DIR="$FV_LAKE_CACHE"
fi
if [ -n "${FV_MEMCAP_OFF:-}" ]; then
  exec "$@"
fi
if systemctl --user show-environment >/dev/null 2>&1; then
  # All scopes go into one slice ($FV_SLICE, default clifv.slice) so the sum of every agent's
  # builds is capped too: the slice unit (~/.config/systemd/user/clifv.slice, see docs/USAGE.md)
  # sets MemoryMax/MemoryHigh for clifv as a whole, and a runaway kills a clifv module (the
  # scheduler retries it) instead of the global OOM killer picking random processes.
  # Without that unit file systemd creates an uncapped slice, i.e. today's behaviour.
  opts=()
  if [ -n "${FV_MEMCAP_UNIT:-}" ]; then opts=(--unit="$FV_MEMCAP_UNIT"); fi
  if [ -n "${FV_MEMCAP_STATS:-}" ]; then
    # A small sh stays in the scope while <cmd> runs and reads the scope's counters at the end;
    # OOMPolicy=continue keeps it alive when the kernel kills a process at the cap (the default
    # policy stops the whole scope, so <cmd> then fails with 143 and no file is written).
    opts+=(-p OOMPolicy=continue)
    # shellcheck disable=SC2016
    set -- sh -c '"$@"; rc=$?; d=/sys/fs/cgroup$(sed -n "s/^0:://p" /proc/self/cgroup)
      { printf "peak %s\n" "$(cat "$d/memory.peak")"; grep -E "^oom(_kill)? " "$d/memory.events"
      } > "$FV_MEMCAP_STATS" 2>/dev/null; exit $rc' memcap "$@"
  fi
  exec systemd-run --user --scope --quiet --slice="${FV_SLICE:-clifv.slice}" ${opts[@]+"${opts[@]}"} \
    -p MemoryMax="${FV_MEMCAP:-16G}" -p MemorySwapMax=0 -p TasksMax=infinity "$@"
fi
# shellcheck disable=SC2016
watchdog='
import ctypes, os, signal, subprocess, sys, time

cap_s, cmd = sys.argv[1], sys.argv[2:]

def size(s):
    s = s.strip()
    if s.endswith("%"):
        with open("/proc/meminfo") as f:
            total = int(f.readline().split()[1]) * 1024
        return int(total * float(s[:-1]) / 100)
    m = {"K": 1, "M": 2, "G": 3, "T": 4}.get(s[-1:].upper())
    return int(float(s[:-1]) * 1024 ** m) if m else int(s)

cap = size(cap_s)
if not cmd:
    sys.exit("memcap: no command")
ctypes.CDLL(None).prctl(36, 1, 0, 0, 0)  # PR_SET_CHILD_SUBREAPER
print(f"memcap: systemd user manager unreachable; fallback watchdog caps the process tree "
      f"at {cap_s} (RSS polled from /proc, SIGKILL + exit 137)", file=sys.stderr, flush=True)
try:
    child = subprocess.Popen(cmd, close_fds=False, start_new_session=True).pid
except OSError as e:
    print(f"memcap: {cmd[0]}: {e.strerror}", file=sys.stderr)
    sys.exit(127 if isinstance(e, FileNotFoundError) else 126)

def forward(sig, _frame):
    try:
        os.killpg(child, sig)
    except ProcessLookupError:
        pass

for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP, signal.SIGQUIT):
    if signal.getsignal(sig) is not signal.SIG_IGN:
        signal.signal(sig, forward)

me = os.getpid()

def tree():
    out, todo = [], [me]
    while todo:
        p = todo.pop()
        try:
            for t in os.listdir(f"/proc/{p}/task"):
                with open(f"/proc/{p}/task/{t}/children") as f:
                    todo.extend(map(int, f.read().split()))
        except OSError:
            pass
        if p != me:
            out.append(p)
    return out

def rss(p):
    n = 0
    try:
        with open(f"/proc/{p}/status") as f:
            for line in f:
                if line.startswith(("RssAnon:", "RssShmem:")):
                    n += int(line.split()[1]) * 1024
    except OSError:
        pass
    return n

status = None
def reap():  # reap the command and any orphans reparented to us
    global status
    while True:
        try:
            pid, st = os.waitpid(-1, os.WNOHANG)
        except ChildProcessError:
            return
        if pid == 0:
            return
        if pid == child:
            status = st

peak = 0

def stats(oom):
    path = os.environ.get("FV_MEMCAP_STATS")
    if path:
        try:
            with open(path, "w") as f:
                f.write(f"peak {peak}\noom {oom}\noom_kill {oom}\n")
        except OSError:
            pass

while True:
    reap()
    if status is not None:
        break
    procs = tree()
    used = sum(map(rss, procs))
    peak = max(peak, used)
    if used > cap:
        for _ in range(500):
            try:
                os.killpg(child, signal.SIGKILL)
            except ProcessLookupError:
                pass
            for p in procs:
                try:
                    os.kill(p, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            time.sleep(0.01)
            reap()
            procs = tree()
            if not procs:
                break
        print(f"memcap: process tree RSS {used / 2**30:.2f} GiB exceeded cap {cap_s}; killed",
              file=sys.stderr, flush=True)
        stats(1)
        sys.exit(137)
    time.sleep(0.2)

stats(0)

if os.WIFSIGNALED(status):
    sig = os.WTERMSIG(status)
    signal.signal(sig, signal.SIG_DFL)
    os.kill(me, sig)
    sys.exit(128 + sig)
sys.exit(os.waitstatus_to_exitcode(status))
'
exec python3 -c "$watchdog" "${FV_MEMCAP:-16G}" "$@"
