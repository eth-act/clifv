#!/usr/bin/env python3
"""Summarize measured scheduler runs: wall time, modules built, summed module seconds, peaks."""
import pathlib, re, sys

for label in sys.argv[1:]:
    d = pathlib.Path("/home/user/ms/runs") / label
    res = (d / "result").read_text().strip() if (d / "result").exists() else "running"
    log = (d / "build.log").read_text() if (d / "build.log").exists() else ""
    built = re.findall(r"done (\S+) rc=0 (\d+)s maxrss=([\d.]+)G cgpeak=([\d.]+)G built", log)
    failed = re.findall(r"done (\S+) rc=([1-9]\d*)", log)
    secs = sum(int(b[1]) for b in built)
    top = max(built, key=lambda b: float(b[3]), default=None)
    mem = [l.split() for l in (d / "mem.log").read_text().splitlines()] if (d / "mem.log").exists() else []
    used = max((int(m[1]) - int(m[2])) / 2**20 for m in mem if len(m) >= 3) if mem else 0
    print(f"{label}: {res}\n  built {len(built)} modules, failed {len(set(f[0] for f in failed))}, "
          f"module-seconds {secs} ({secs/3600:.2f} h), max module anon peak {top[3] if top else 0}G "
          f"({top[0] if top else '-'}), mean anon peak {sum(float(b[3]) for b in built)/max(1,len(built)):.2f}G, "
          f"max machine used {used:.1f} GiB")
