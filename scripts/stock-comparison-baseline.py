#!/usr/bin/env python3
"""Find the comparison summary of the main commit that the tested commit is based on.

Scans the newest push runs of the comparison workflow on `main`, skips the current run, and takes
the first whose commit is an ancestor of the tested commit and that saved a summary artifact
(only a completed measurement saves one). A pull request is therefore compared with the `main`
commit it branched from (or last merged), not with a newer `main` it does not contain.

Writes `--out`: {"available": true, "run_id", "run_attempt", "head_sha", "summary"}, or
{"available": false, "reason"}. A missing baseline is not an error: there is nothing to compare.
Needs `gh` with GH_TOKEN (actions: read) and the full git history of the tested commit and main.
"""
import argparse
import io
import json
import os
from pathlib import Path
import re
import subprocess
import zipfile

WORKFLOW = "stock-compiler-comparison.yml"
PREFIX = "stock-comparison-summary-"
MEMBER = "ci-comparison.ci-summary.json"
LIMIT = 1024 * 1024
RUNS = 100


def gh_api(path):
    return subprocess.run(["gh", "api", path], check=True, capture_output=True).stdout


def is_ancestor(sha, head):
    status = subprocess.run(["git", "merge-base", "--is-ancestor", sha, head], capture_output=True).returncode
    if status not in (0, 1):
        return False  # unknown commit, e.g. history not fetched
    return status == 0


def read_summary(archive):
    """The single summary member of an artifact archive, bounded, without extracting files."""
    with zipfile.ZipFile(io.BytesIO(archive)) as zf:
        entries = zf.infolist()
        if len(entries) != 1 or entries[0].filename != MEMBER or entries[0].file_size > LIMIT:
            raise ValueError("unexpected summary archive contents")
        return json.loads(zf.read(entries[0]))


def find(repo, head, current_run, api=gh_api, ancestor=is_ancestor):
    query = f"repos/{repo}/actions/workflows/{WORKFLOW}/runs?branch=main&event=push&status=completed&per_page={RUNS}"
    runs = json.loads(api(query))["workflow_runs"]
    for run in sorted(runs, key=lambda r: r["id"], reverse=True):
        if run["id"] == current_run or run["event"] != "push" or run["head_branch"] != "main":
            continue
        if not re.fullmatch(r"[0-9a-f]{40}", run["head_sha"]) or not ancestor(run["head_sha"], head):
            continue
        listed = json.loads(api(f"repos/{repo}/actions/runs/{run['id']}/artifacts?per_page=100"))["artifacts"]
        summaries = [a for a in listed if re.fullmatch(re.escape(PREFIX) + r"[1-9][0-9]*", a["name"])
                     and not a["expired"] and a["size_in_bytes"] <= LIMIT]
        if not summaries:
            continue  # this run did not complete a measurement; an older ancestor may have
        artifact = max(summaries, key=lambda a: int(a["name"].removeprefix(PREFIX)))
        summary = read_summary(api(f"repos/{repo}/actions/artifacts/{artifact['id']}/zip"))
        return {"available": True, "run_id": run["id"], "run_attempt": int(artifact["name"].removeprefix(PREFIX)),
                "head_sha": run["head_sha"], "summary": summary}
    return {"available": False,
            "reason": f"none of the last {RUNS} main push runs is an ancestor of this commit with an unexpired summary"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head", required=True, help="the tested commit")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    try:
        found = find(os.environ["GITHUB_REPOSITORY"], args.head, int(os.environ["GITHUB_RUN_ID"]))
    except (subprocess.CalledProcessError, ValueError, KeyError, zipfile.BadZipFile) as error:
        found = {"available": False, "reason": f"baseline lookup failed: {type(error).__name__}"}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(found) + "\n")
    if found["available"]:
        print(f"Baseline: main {found['head_sha'][:12]}, run {found['run_id']} attempt {found['run_attempt']}")
    else:
        print("No baseline:", found["reason"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
