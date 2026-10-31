#!/usr/bin/env python3
"""Optional shadow measurements. Missing/timeout results are unknown, never agreement."""
import datetime as dt
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time


def read_record(directory):
    return json.loads((directory / "result.json").read_text())


def write_record(directory, record):
    temporary = directory / "result.tmp"
    temporary.write_text(json.dumps(record, indent=2) + "\n")
    temporary.replace(directory / "result.json")


def measure(directory, name, command, seconds):
    start = time.monotonic()
    with (directory / f"{name}.log").open("w") as log:
        try:
            # Foreground mode lets memcap/systemd own the command's process group.
            rc = subprocess.run(["timeout", "--foreground", "--signal=TERM", "--kill-after=15s", str(seconds),
                                 *command], stdout=log, stderr=subprocess.STDOUT,
                                env={**os.environ, "TURBO_LEAN_TELEMETRY": "off",
                                     "TURBO_LEAN_HOME": str(directory.parent / "turbo-cas")}).returncode
        except OSError as error:
            log.write(str(error) + "\n")
            rc = 127
    return {"ok": None if rc in (124, 137, 127) or rc < 0 else rc == 0,
            "exit_code": rc, "wall_s": round(time.monotonic() - start, 3), "command": command}


def comparison(record):
    stock, turbo = record["stock_ok"], record["turbo_ok"]
    return stock != turbo if isinstance(stock, bool) and isinstance(turbo, bool) else None


def api(path, paginate=False):
    if not paginate:
        return json.loads(subprocess.check_output(["gh", "api", path], text=True))
    # Explicit pages also work with older gh versions without --slurp.
    pages = []
    while True:
        page = api(f"{path}&page={len(pages) + 1}")
        pages.append(page)
        if len(page["jobs"]) < 100:
            return pages


def stock(record):
    """Only original Full gate job conclusions may populate stock_ok."""
    repository = os.environ["GITHUB_REPOSITORY"]
    event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text())
    automatic = record["event"] == "workflow_run"
    trigger = event.get("workflow_run", {}) if automatic else {}
    run_id = str(trigger.get("id", "")) if automatic else os.environ.get("STOCK_RUN_ID", "")
    if not re.fullmatch(r"[1-9][0-9]*", run_id):
        raise ValueError("a completed same-repository Full gate run ID is required")
    run = api(f"repos/{repository}/actions/runs/{run_id}")
    # Read the triggering attempt, even if a later rerun has already started.
    attempt = trigger.get("run_attempt") if automatic else run["run_attempt"]
    run = api(f"repos/{repository}/actions/runs/{run_id}/attempts/{attempt}")
    if (run["name"] != "Full gate" or run["path"] != ".github/workflows/full-gate.yml"
            or run["head_repository"]["full_name"] != repository
            or run["event"] not in ("push", "schedule", "workflow_dispatch")
            or run["status"] != "completed"
            or not re.fullmatch(r"[0-9a-f]{40}", run["head_sha"])):
        raise ValueError("stock source must be a completed same-repository Full gate run")
    if automatic and (run["head_branch"] != "main" or run["head_sha"] != trigger["head_sha"]):
        raise ValueError("automatic shadow accepts only the triggering main revision")
    record.update(commit=run["head_sha"], stock_run_id=run_id, stock_run_attempt=attempt,
                  stock_run_conclusion=run["conclusion"], stock_branch=run["head_branch"],
                  stock_run_event=run["event"])
    pages = api(f"repos/{repository}/actions/runs/{run_id}/attempts/{attempt}/jobs?per_page=100", True)
    jobs = [job for page in pages for job in page["jobs"]]
    plan = [job for job in jobs if job["name"] == "Plan"]
    builds = [job for job in jobs if job["name"].startswith("Build wave ")
              or job["name"] == "Assemble build and executables"]
    assemble = [job for job in builds if job["name"] == "Assemble build and executables"]
    record["stock_jobs"] = [{key: job.get(key) for key in
                             ("id", "name", "conclusion", "started_at", "completed_at")}
                            for job in [*plan, *builds]]
    if builds:
        record["stock_source"] = f"Full gate run {run_id}, attempt {attempt}: build waves and assemble job conclusions"
        if any(job["conclusion"] == "failure" for job in builds):
            record["stock_ok"] = False
        elif (len(assemble) == 1 and assemble[0]["conclusion"] == "success"
              and all(job["conclusion"] in ("success", "skipped") for job in builds)):
            record["stock_ok"] = True
        starts = [dt.datetime.fromisoformat(job["started_at"].replace("Z", "+00:00"))
                  for job in builds if job.get("started_at") and job["conclusion"] != "skipped"]
        ends = [dt.datetime.fromisoformat(job["completed_at"].replace("Z", "+00:00"))
                for job in builds if job.get("completed_at") and job["conclusion"] != "skipped"]
        if starts and ends:
            record["wall_s"]["stock"] = (max(ends) - min(starts)).total_seconds()
    record["eligible"] = (run["conclusion"] == "success" and record["stock_ok"] is True
                          and len(plan) == 1 and plan[0]["conclusion"] == "success")


def main():
    directory = Path(os.environ["SHADOW_DIR"])
    directory.mkdir(parents=True, exist_ok=True)
    action = sys.argv[1]
    if action == "init":
        record = {"schema": 2, "commit": None, "base": None,
                  "turbo_lean_sha": os.environ["TURBO_SHA"], "stock_ok": None, "stock_source": None,
                  "turbo_ok": None, "discrepancy": None, "wall_s": {"stock": None, "turbo": None},
                  "pr_ok": None, "eligible": False,
                  "event": os.environ["GITHUB_EVENT_NAME"], "run_id": os.environ["GITHUB_RUN_ID"],
                  "run_attempt": os.environ["GITHUB_RUN_ATTEMPT"], "commands": {}}
        write_record(directory, record)
        return
    record = read_record(directory)
    if action == "stock":
        try:
            stock(record)
        except (subprocess.CalledProcessError, ValueError, KeyError, OSError) as error:
            record["stock_lookup_error"] = str(error)
            record["eligible"] = False
        with open(os.environ["GITHUB_OUTPUT"], "a") as output:
            output.write(f"eligible={str(record['eligible']).lower()}\n")
            if record["eligible"]:
                output.write(f"commit={record['commit']}\nrun={record['stock_run_id']}\n")
        # Save evidence even when the lookup fails; the main path remains gated off.
    elif action == "base":
        base = os.environ.get("PR_BASE") or subprocess.check_output(
            ["git", "rev-parse", "HEAD~1"], text=True).strip()
        if not re.fullmatch(r"[0-9a-f]{40}", base):
            raise ValueError("base must be a full commit SHA")
        subprocess.run(["git", "cat-file", "-e", f"{base}^{{commit}}"], check=True)
        record["base"] = base
    elif action in ("ci", "pr"):
        if not record["eligible"] or not record["base"]:
            raise ValueError("verification requires successful stock provenance and a valid base")
        command = [str(Path(os.environ["RUNNER_TEMP"]) / "turbo-install/bin/turbo-lean"),
                   "--no-daemon", "--no-telemetry", "--no-auto-worktree-link",
                   "ci-verify" if action == "ci" else "pr-verify", "--base", record["base"],
                   "--receipt", str(directory / f"{action}-receipt.json")]
        if action == "pr":
            command.append("--disallow-statement-changes")
        result = measure(directory, action, ["scripts/memcap.sh", *command], 900)
        record["commands"][action] = result
        record["turbo_ok" if action == "ci" else "pr_ok"] = result["ok"]
        if action == "ci":
            record["wall_s"]["turbo"] = result["wall_s"]
    elif action != "report":
        raise SystemExit(f"unknown action: {action}")
    record["discrepancy"] = comparison(record)
    write_record(directory, record)
    if action == "report":
        summary = ("### turbo-lean shadow (non-blocking)\n\n"
                   f"Commit `{record['commit']}`, turbo-lean `{record['turbo_lean_sha']}`.\n\n"
                   f"Stock: `{record['stock_ok']}`; turbo CI: `{record['turbo_ok']}`; "
                   f"discrepancy: `{record['discrepancy']}`; PR policy: `{record['pr_ok']}`.\n\n"
                   "`null` is incomplete, not agreement. Failed-stock runs do not count toward "
                   "the 20-commit record. Inspect result.json and logs; timings are not a "
                   "speedup claim. See docs/turbo-lean-shadow.md.\n")
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as output:
            output.write(summary)


if __name__ == "__main__":
    main()
