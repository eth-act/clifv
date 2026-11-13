#!/usr/bin/env python3
"""Fail when an output that matched on the baseline `main` commit no longer matches: an exact
output, or an honest one (the proved compiler's output identical to stock, for a function
`backend_correct` covers; `stock-compiler-compare.py`).

Reads the run's CI summary (`stock-comparison-ci.py`). On a pull request, the label LABEL
accepts the losses; it is read when this job runs, so re-running the job after labelling
passes. On `main` there is no override: the commit is marked, and the next push compares
with it. When no baseline exists there is nothing to compare, and the check passes; when one
exists but could not be retrieved or read, the check fails (the label does not override that).

MEASURE_RESULT is the result of the workflow's measuring job ("Build and compare"). Anything
but `success` (it failed, ran out of time, lost its runner, was cancelled) means there is no
measurement of this commit: the check fails with "no result", whatever an earlier attempt
measured and whatever the labels say, since lost matches cannot be ruled out (#1018: a skipped
check read as a pass). Without the variable the summary alone decides (a missing summary fails).
"""
import argparse
import json
import os
from pathlib import Path
import subprocess

LABEL = "stock-comparison-accept-losses"
MEMBER = "ci-comparison.ci-summary.json"
SHOWN = 50
NO_RESULT = "No stock-comparison result"


def newest_summary(directory):
    """The newest attempt's summary among the downloaded `stock-comparison-summary-N` artifacts.
    download-artifact extracts a single match into the directory itself and several into
    subdirectories, so search both."""
    found = [json.loads(path.read_text()) for path in sorted(directory.rglob(MEMBER))]
    if not found:
        raise SystemExit("no summary artifact")
    return max(found, key=lambda summary: summary.get("run_attempt", 0))


def pr_labels(repo, number):
    out = subprocess.run(["gh", "api", f"repos/{repo}/pulls/{number}", "--jq", "[.labels[].name]"],
                         check=True, capture_output=True, text=True).stdout
    return json.loads(out)


def entry(e):
    test, variant, stage, position, name = e
    return f"{test} {name} ({stage}, variant {variant}, function {position})"


def listed_losses(b, what):
    """Report lines naming the lost outputs of one metric's comparison `b`."""
    lines = [f"{what} that matched on main and no longer match ({b['lost_count']}):"]
    lines += [f"- {entry(e)}" for e in b["lost"][:SHOWN]]
    if b["lost_count"] > SHOWN:
        lines.append(f"- ... and {b['lost_count'] - SHOWN} more (see the summary artifact)")
    return lines


def check(summary, run_id, head, labels):
    """(exit status, report lines)."""
    if summary.get("run_id") != run_id or summary.get("head_sha") != head:
        raise SystemExit("summary does not belong to this run and commit")
    b = summary["baseline_comparison"]
    if not b["available"] and b.get("failed") is not False:
        return 1, [f"The main baseline could not be retrieved or read: {b['reason']}.",
                   "Without it, lost matches cannot be ruled out. Re-run all jobs of this workflow run."]
    if not b["available"]:
        return 0, [f"No main baseline to compare with: {b['reason']}."]
    lines = [f"Compared with main {b['head_sha'][:12]} (run {b['run_id']}): "
             f"+{b['gained_count']} / -{b['lost_count']} exact outputs."]
    p = b.get("proved")
    if not isinstance(p, dict) or not p.get("available") and p.get("failed") is not False:
        why = p.get("reason") if isinstance(p, dict) else "the summary has no honest comparison"
        return 1, lines + [f"The honest metric could not be compared with main: {why}.",
                           "Without it, lost honest matches cannot be ruled out."]
    if p["available"]:
        lines.append(f"Honest metric (proved compiler, backend_correct): +{p['gained_count']} / -{p['lost_count']} "
                     f"({p['baseline_proved_exact_code_artifacts']} -> "
                     f"{p['baseline_proved_exact_code_artifacts'] - p['lost_count'] + p['gained_count']}).")
    else:
        lines.append(f"Honest metric: no main baseline to compare with: {p['reason']}.")
    if b["harness_changed"]:
        lines.append("The measuring code changed since then: " + ", ".join(b["harness_changed"]) + ".")
    if b["lost_count"]:
        lines += listed_losses(b, "Outputs")
    if p["available"] and p["lost_count"]:
        lines += listed_losses(p, "Honest outputs")
    if not b["lost_count"] and not (p["available"] and p["lost_count"]):
        return 0, lines
    if labels is not None and LABEL in labels:
        lines.append(f"Accepted by the label {LABEL}.")
        return 0, lines
    lines.append(f"If the losses are intended, add the label {LABEL} to the pull request and re-run this job."
                 if labels is not None else "Pushes to main have no override.")
    return 1, lines


def no_result(result, run_id):
    """Report lines when the measuring job did not succeed."""
    if result == "failure":
        how = "it failed, ran out of time or lost its runner; its annotations and log say which"
        rerun = f"Re-run the failed jobs of this workflow run (`gh run rerun {run_id} --failed`)."
    else:
        # `--failed` re-runs failed jobs and the jobs that need them: after a cancelled (or
        # skipped) measuring job that is this job alone, which would fail again unmeasured
        how = ("it was cancelled: by hand, at the job's time limit, or because a newer commit or event of the "
               "pull request started another run of this workflow" if result == "cancelled" else
               "it did not run to a result")
        rerun = (f"If a newer run of this workflow exists for the same commit or pull request, that run's result is "
                 f"the one that counts and this one needs nothing. Otherwise re-run all jobs of this workflow run "
                 f"(`gh run rerun {run_id}`; `--failed` would re-run this job only).")
    return [f"{NO_RESULT}: the job \"Build and compare\" ended as `{result or 'unknown'}` ({how}). "
            "Nothing was measured for this commit in this run, so lost matches cannot be ruled out.",
            f"{rerun} The label {LABEL} does not override a missing measurement."]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("summaries", type=Path, help="directory with the downloaded summary artifacts")
    args = parser.parse_args()
    run_id = int(os.environ["GITHUB_RUN_ID"])
    measured = os.environ.get("MEASURE_RESULT")
    if measured is not None and measured != "success":
        status, lines = 1, no_result(measured, run_id)
        print(f"::error title={NO_RESULT}::{' '.join(lines)}")
    else:
        number = os.environ.get("PR_NUMBER", "")
        labels = pr_labels(os.environ["GITHUB_REPOSITORY"], number) if number else None
        status, lines = check(newest_summary(args.summaries), run_id, os.environ["CI_HEAD_SHA"], labels)
    print("\n".join(lines))
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as out:
            out.write("### Lost matches\n\n" + "\n\n".join(lines) + "\n")
    return status


if __name__ == "__main__":
    raise SystemExit(main())
