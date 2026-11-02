#!/usr/bin/env python3
"""Compare measured module builds with scripts/lake-module-peaks.tsv, report drift, and optionally
write the measurements back into the table.

usage: scripts/peaks-update.py [options] SCHED_DIR...

SCHED_DIR is a scheduler log directory (lake-serial-build.py --out; a full-gate shard's
shard-logs-*/sched). For every module it built (`done M rc=0 ...s ... built` in sched.log; the last
such line counts), it reads the wall seconds from sched.log and lean's maximum RSS from <M>.time
(the quantity the table records). Seconds are divided by --time-scale, and additionally by the
--prefix-scale factor of the module's prefix, to bring them into the table's units (CI runners:
see FULL_GATE_TIME_SCALE in .github/workflows/full-gate.yml).

Drift (printed one per line, `drift <kind> <module> <recorded> -> <measured>`):
  * slower / faster: measured seconds differ from the record by more than --factor and by more than
    --min-secs;
  * memory: measured peak above record x --factor and more than --min-mb above it (a cap computed
    from the record would kill the module); lower peaks are reported as `memory-lower`;
  * new: no record.
With --write, the table's rows for drifted and new modules are replaced by the measurements
(--write-all: every measured module), keeping the header and sorting the rows.
Exit status 0 (report only), also with drift.
"""
import argparse, pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
TABLE = ROOT / "scripts/lake-module-peaks.tsv"
DONE = re.compile(r"done (\S+) rc=0 (\d+)s maxrss=([\d.]+)G \S+ built")


def read_table(path):
    header, rows = [], {}
    for line in pathlib.Path(path).read_text().splitlines():
        f = line.split("\t")
        if line.startswith("#") or len(f) < 3:
            header.append(line)
        else:
            rows[f[0]] = (int(f[1]), float(f[2]))
    return header, rows


def read_sched(d):
    """{module: (peak MB, seconds)} of the modules a scheduler run built."""
    d = pathlib.Path(d)
    log = d / "sched.log"
    out = {}
    if not log.exists():
        return out
    for m, secs, rss_g in DONE.findall(log.read_text(errors="replace")):
        mb = round(float(rss_g) * 1024)
        t = d / f"{m}.time"
        if t.exists():
            mo = re.search(r"Maximum resident set size \(kbytes\): (\d+)", t.read_text(errors="replace"))
            if mo:
                mb = int(mo.group(1)) // 1024
        out[m] = (mb, float(secs))
    return out


def scale_of(m, time_scale, prefix_scale):
    f = time_scale
    for p, x in prefix_scale:
        if m.startswith(p):
            f *= x
            break
    return f


def drift(rows, measured, factor=2.0, min_secs=60.0, min_mb=1024):
    """[(kind, module, recorded, measured)] for measured (peak MB, table-unit seconds)."""
    out = []
    for m, (mb, secs) in sorted(measured.items()):
        if m not in rows:
            out.append(("new", m, None, (mb, secs)))
            continue
        rmb, rsecs = rows[m]
        if secs > rsecs * factor and secs - rsecs > min_secs:
            out.append(("slower", m, (rmb, rsecs), (mb, secs)))
        elif secs * factor < rsecs and rsecs - secs > min_secs:
            out.append(("faster", m, (rmb, rsecs), (mb, secs)))
        if mb > rmb * factor and mb - rmb > min_mb:
            out.append(("memory", m, (rmb, rsecs), (mb, secs)))
        elif mb * factor < rmb and rmb - mb > min_mb:
            out.append(("memory-lower", m, (rmb, rsecs), (mb, secs)))
    return out


def fmt(kind, m, rec, meas):
    show = lambda v: "none" if v is None else f"{v[1]:.0f}s/{v[0] / 1024:.1f}G"
    return f"drift {kind} {m} {show(rec)} -> {show(meas)}"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("dirs", nargs="+")
    ap.add_argument("--table", default=str(TABLE))
    ap.add_argument("--time-scale", type=float, default=1.0)
    ap.add_argument("--prefix-scale", action="append", default=[], metavar="PREFIX=F")
    ap.add_argument("--factor", type=float, default=2.0)
    ap.add_argument("--min-secs", type=float, default=60.0)
    ap.add_argument("--min-mb", type=int, default=1024)
    ap.add_argument("--no-new", action="store_true", help="do not list modules without a record")
    ap.add_argument("--write", action="store_true", help="replace drifted and new rows")
    ap.add_argument("--write-all", action="store_true", help="replace every measured row")
    a = ap.parse_args()
    prefix_scale = sorted(((p, float(x)) for p, x in (s.split("=", 1) for s in a.prefix_scale)),
                          key=lambda px: -len(px[0]))
    header, rows = read_table(a.table)
    measured = {}
    for d in a.dirs:
        for m, (mb, secs) in read_sched(d).items():
            measured[m] = (mb, secs / scale_of(m, a.time_scale, prefix_scale))
    found = drift(rows, measured, a.factor, a.min_secs, a.min_mb)
    for k, m, rec, meas in found:
        if not (a.no_new and k == "new"):
            print(fmt(k, m, rec, meas))
    kinds = {}
    for k, *_ in found:
        kinds[k] = kinds.get(k, 0) + 1
    print(f"drift summary: {len(measured)} modules measured; "
          + (", ".join(f"{n} {k}" for k, n in sorted(kinds.items())) or "no drift"))
    if a.write or a.write_all:
        upd = set(measured) if a.write_all else {m for _, m, _, _ in found}
        for m in upd:
            mb, secs = measured[m]
            rows[m] = (mb, max(1.0, round(secs)))
        lines = header + [f"{m}\t{mb}\t{secs:.0f}" for m, (mb, secs) in sorted(rows.items())]
        pathlib.Path(a.table).write_text("\n".join(lines) + "\n")
        print(f"wrote {a.table}: {len(upd)} rows replaced")
    return 0


if __name__ == "__main__":
    sys.exit(main())
