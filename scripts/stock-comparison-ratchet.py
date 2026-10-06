#!/usr/bin/env python3
"""Fail when an output that matched on the baseline `main` commit no longer matches.

Reads the run's CI summary (`stock-comparison-ci.py`). On a pull request, the label LABEL
accepts the losses; it is read when this job runs, so re-running the job after labelling
passes. On `main` there is no override: the commit is marked, and the next push compares
with it. When no baseline exists there is nothing to compare, and the check passes; when one
exists but could not be retrieved or read, the check fails (the label does not override that).
"""
import argparse
import json
import os
from pathlib import Path
import subprocess

LABEL = "stock-comparison-accept-losses"
MEMBER = "ci-comparison.ci-summary.json"
SHOWN = 50


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
    if b["harness_changed"]:
        lines.append("The measuring code changed since then: " + ", ".join(b["harness_changed"]) + ".")
    if not b["lost_count"]:
        return 0, lines
    lines.append(f"Outputs that matched on main and no longer match ({b['lost_count']}):")
    lines += [f"- {entry(e)}" for e in b["lost"][:SHOWN]]
    if b["lost_count"] > SHOWN:
        lines.append(f"- ... and {b['lost_count'] - SHOWN} more (see the summary artifact)")
    if labels is not None and LABEL in labels:
        lines.append(f"Accepted by the label {LABEL}.")
        return 0, lines
    lines.append(f"If the losses are intended, add the label {LABEL} to the pull request and re-run this job."
                 if labels is not None else "Pushes to main have no override.")
    return 1, lines


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("summaries", type=Path, help="directory with the downloaded summary artifacts")
    args = parser.parse_args()
    number = os.environ.get("PR_NUMBER", "")
    labels = pr_labels(os.environ["GITHUB_REPOSITORY"], number) if number else None
    status, lines = check(newest_summary(args.summaries), int(os.environ["GITHUB_RUN_ID"]),
                          os.environ["CI_HEAD_SHA"], labels)
    print("\n".join(lines))
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as out:
            out.write("### Lost matches\n\n" + "\n\n".join(lines) + "\n")
    return status


if __name__ == "__main__":
    raise SystemExit(main())
