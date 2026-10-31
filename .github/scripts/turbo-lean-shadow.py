#!/usr/bin/env python3
"""Optional shadow measurements. Missing/timeout results are unknown, never agreement."""
import datetime as dt
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import tomllib


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
            # timeout terminates the whole process group; --no-daemon bounds turbo's children.
            rc = subprocess.run(["timeout", "--signal=TERM", "--kill-after=15s", str(seconds),
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


def main():
    directory = Path(os.environ["SHADOW_DIR"])
    directory.mkdir(parents=True, exist_ok=True)
    action = sys.argv[1]
    if action == "init":
        base = os.environ.get("PR_BASE") or subprocess.check_output(
            ["git", "rev-parse", "HEAD~1"], text=True).strip()
        subprocess.run(["git", "cat-file", "-e", f"{base}^{{commit}}"], check=True)
        record = {"schema": 1, "commit": os.environ["TEST_COMMIT"], "base": base,
                  "turbo_lean_sha": os.environ["TURBO_SHA"], "stock_ok": None,
                  "turbo_ok": None, "discrepancy": None, "wall_s": {"stock": None, "turbo": None},
                  "pr_ok": None, "prior_stock_job_result": os.environ["STOCK_RESULT"],
                  "event": os.environ["GITHUB_EVENT_NAME"], "run_id": os.environ["GITHUB_RUN_ID"],
                  "run_attempt": os.environ["GITHUB_RUN_ATTEMPT"], "commands": {}}
        write_record(directory, record)
        return
    record = read_record(directory)
    if action == "stock":
        if record["event"] == "pull_request":
            # Match the full-gate Lean target set; the compiler comparison is not a proof verdict.
            scheduler = ["python3", "scripts/lake-serial-build.py", "--budget", "15G",
                         "--heavy", "12G", "--heavy-avail", "0", "--pause-avail", "1G",
                         "--max-jobs", "3", "--margin", "1.0", "--max-cap", "48G",
                         "--no-slice-gate", "--out", str(directory / "stock-scheduler"),
                         "FV", "FVTest", "Corpus"]
            result = measure(directory, "stock-modules", scheduler, 14400)
            record["commands"]["stock_modules"] = result
            if result["ok"] is True:
                config = tomllib.loads(Path("lakefile.toml").read_text())
                exes = [entry["name"] for entry in config.get("lean_exe", [])]
                link = measure(directory, "stock-executables",
                               ["scripts/memcap.sh", "lake", "build", "FV", "FVTest", "Corpus", *exes], 1800)
                record["commands"]["stock_executables"] = link
                result = {**link, "wall_s": round(link["wall_s"] + result["wall_s"], 3)}
            record["commands"]["stock"] = result
            record["stock_ok"], record["wall_s"]["stock"] = result["ok"], result["wall_s"]
            record["stock_source"] = "shadow-only cached stock Lake reference, full-gate Lean targets"
        else:
            status = record["prior_stock_job_result"]
            record["stock_ok"] = {"success": True, "failure": False}.get(status)
            record["stock_source"] = "existing Full gate assemble (waves + all Lean targets/executables)"
            try:
                pages = json.loads(subprocess.check_output([
                    "gh", "api", "--paginate", "--slurp",
                    f"repos/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{record['run_id']}"
                    f"/attempts/{record['run_attempt']}/jobs?per_page=100"], text=True))
                jobs = [job for page in pages for job in page["jobs"]
                        if job["name"].startswith("Build wave ")
                        or job["name"] == "Assemble build and executables"]
                starts = [dt.datetime.fromisoformat(job["started_at"].replace("Z", "+00:00"))
                          for job in jobs if job.get("started_at")]
                ends = [dt.datetime.fromisoformat(job["completed_at"].replace("Z", "+00:00"))
                        for job in jobs if job.get("completed_at")]
                if starts and ends:
                    record["wall_s"]["stock"] = (max(ends) - min(starts)).total_seconds()
            except (subprocess.CalledProcessError, ValueError, KeyError) as error:
                record["stock_timing_error"] = str(error)
    elif action in ("ci", "pr"):
        command = [str(Path(os.environ["RUNNER_TEMP"]) / "turbo-install/bin/turbo-lean"),
                   "--no-daemon", "--no-telemetry", "--no-auto-worktree-link",
                   "ci-verify" if action == "ci" else "pr-verify", "--base", record["base"],
                   "--receipt", str(directory / f"{action}-receipt.json")]
        if action == "pr":
            command.append("--disallow-statement-changes")
        # Same ordinary read-only CI token permissions as stock; no workflow_run/target elevation.
        result = measure(directory, action, ["scripts/memcap.sh", *command], 1800)
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
                   "`null` is incomplete, not agreement. Inspect result.json and logs; "
                   "timings are not a speedup claim. See docs/turbo-lean-shadow.md.\n")
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as output:
            output.write(summary)


if __name__ == "__main__":
    main()
