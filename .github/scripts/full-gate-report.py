#!/usr/bin/env python3
"""Markdown report of a full-gate run (.github/workflows/full-gate.yml) for the job summary and
the continuous-gate issue.

usage: full-gate-report.py REPORT_DIR      (env NEEDS: toJSON(needs) of the report job)

REPORT_DIR holds the downloaded artifacts: gate-*/summary.txt (one line per gate),
shard-logs-w<W>-<S>/sched/sched.log (scheduler logs) and ci-plan/ci-plan.json.
The first line is `**Result: GREEN …` iff every build and gate job succeeded (or was skipped
because there was nothing to build).
"""
import json, os, pathlib, re, sys

GATES = ["assemble", "audit", "crate-proofs", "e2e", "runtime", "cargo-fv"]
BUILD = ["plan", "wave1", "wave2", "wave3"]


def main():
    rep = pathlib.Path(sys.argv[1])
    needs = json.loads(os.environ.get("NEEDS", "{}"))
    res = {k: v.get("result", "?") for k, v in needs.items()}
    green = all(res.get(k) in ("success", "skipped") for k in BUILD) and \
        all(res.get(k) == "success" for k in GATES)
    sha = os.environ.get("GITHUB_SHA", "?")
    run = (f"{os.environ.get('GITHUB_SERVER_URL', '')}/{os.environ.get('GITHUB_REPOSITORY', '')}"
           f"/actions/runs/{os.environ.get('GITHUB_RUN_ID', '')}")
    out = [f"**Result: {'GREEN' if green else 'RED'}** — full gate (CI) on `{sha[:8]}` "
           f"({os.environ.get('GITHUB_EVENT_NAME', '?')}, {os.environ.get('GITHUB_REF_NAME', '?')}): {run}",
           "", "| job | result |", "|---|---|"]
    out += [f"| {k} | {res.get(k, '-')} |" for k in BUILD + GATES]
    out += ["", "Gate lines:", "```"]
    for f in sorted(rep.glob("gate-*/summary.txt")):
        out += [l for l in f.read_text().splitlines() if l.strip()]
    out += ["```"]

    plan_f = rep / "ci-plan" / "ci-plan.json"
    if plan_f.exists():
        plan = json.loads(plan_f.read_text())
        waves = [w for w in plan["waves"] if w]
        out += ["", f"Build plan: {plan['planned']} modules "
                f"({'all' if plan['all'] else 'changed since ' + str(plan['base'])[:8] + ' and importers'}), "
                f"{' + '.join(str(len(w)) for w in waves) or 'no'} shards, "
                f"estimate {plan['estimate_s'] / 3600:.2f} h."]
    shards, mods = [], []
    for log in sorted(rep.glob("shard-logs-*/sched/sched.log")):
        name = log.parent.parent.name.removeprefix("shard-logs-")
        text = log.read_text(errors="replace")
        end = re.findall(r"END (\d+)/(\d+) ok, (\d+) built, wall ([\d.]+) min", text)
        if end:
            ok, n, built, wall = end[-1]
            shards.append((float(wall), f"{name}: {built} built, {ok}/{n} ok, {float(wall):.0f} min"))
        for m, secs, rss in re.findall(r"done (\S+) rc=0 (\d+)s maxrss=([\d.]+)G built", text):
            mods.append((m, int(secs), float(rss)))
    if shards:
        shards.sort(reverse=True)
        out += ["", "<details><summary>Shards (scheduler wall time)</summary>", "", "```"]
        out += [s for _, s in shards] + ["```", "", "</details>"]
    if mods:
        out += ["", "<details><summary>Heaviest modules on the runners</summary>", "", "```"]
        for m, secs, rss in sorted(mods, key=lambda x: -x[2])[:12]:
            out.append(f"{rss:5.1f}G {secs:6d}s {m}")
        out += ["--- longest", *(f"{rss:5.1f}G {secs:6d}s {m}"
                                 for m, secs, rss in sorted(mods, key=lambda x: -x[1])[:8])]
        out += ["```", "", "</details>"]
    print("\n".join(out))
    return 0


if __name__ == "__main__":
    sys.exit(main())
