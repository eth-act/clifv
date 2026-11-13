#!/usr/bin/env python3
"""Choose the Full gate build the stock comparison takes its Lean executables from (#1018).

The comparison runs four Lean executables (EXES). Their import cone is a small part of the tree,
but a plain `lake build` of it on one hosted runner (16 GB, no swap) lost the runner or ran out
of time after every Lean source change. The Full gate (.github/workflows/full-gate.yml) builds
the same modules on many runners and publishes the result as the artifact `lake-full`, a staged
Lake cache. Lake's cache is keyed by each module's inputs (its source, its imports, the
toolchain and the Lake configuration), so any such build is a correct starting point: Lake
restores what matches and builds the rest. No module of the cone reads a file while it
elaborates (the executables read their inputs when they run), so there is no input Lake does
not trace (#1012 is about modules outside the cone).

This script picks the build that leaves the least to build for the tested commit:

1. the Full gate runs on the tested commit itself, then
2. the newest runs (up to CANDIDATES) that hold an unexpired `lake-full`, on any branch of this
   repository (a squashed pull request has the tree of the branch head its Full gate ran on),

each counted only if it is a run of the Full gate workflow of this repository (not of a fork,
not a pull_request run) and its build is complete (its assemble job succeeded; no
`lake-full-missing`). For each, the
modules of the cone whose source differs from that run's commit, and their importers, are what
would be built (scripts/ci-build-plan.py's rule); the candidate with the fewest recorded seconds
of them wins, the first one with nothing to build ends the search.

Writes `--out`: {"run", "head_sha", "branch", "same_commit", "to_build", "cone", "estimate_s",
"reason"} (`run` is null when there is no usable build: everything in the cone is then built by
scripts/lake-serial-build.py, within memory and a time limit, see
.github/scripts/stock-comparison-lean.sh). With --github-output, appends `run=<id or empty>` to
$GITHUB_OUTPUT. A failed lookup (the API, git) exits non-zero: the job fails with that message
instead of building everything.
Needs `gh` with GH_TOKEN (actions: read) and a checkout of the tested commit as HEAD.

`--print exes` / `--print roots` list the executables and their root modules (one per line).
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tomllib

HERE = Path(__file__).resolve().parent
WORKFLOW = "full-gate.yml"
WORKFLOW_PATH = ".github/workflows/" + WORKFLOW
ARTIFACT, MISSING = "lake-full", "lake-full-missing"
ASSEMBLE = "Assemble build and executables"  # the job of full-gate.yml that uploads them
# The executables scripts/stock-compiler-comparison.sh builds (test_stock_comparison_lean_build.py
# checks the two lists against each other).
EXES = ["lean-backend", "lean-backend-lowering-trace", "lean-stock-lowering-compare", "lean-stock-lowering-test"]
EVENTS = {"push", "workflow_dispatch", "schedule"}
CANDIDATES = 20
DEFAULT_SECS = 60.0  # a module without a record in scripts/lake-module-peaks.tsv
TIME_SCALE = 2.0     # runner seconds per recorded second (as the Full gate's Plan job)


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, HERE / file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def gh_api(path):
    return subprocess.run(["gh", "api", path], check=True, capture_output=True).stdout


def exe_roots(root):
    """The root module of each executable of EXES, in that order."""
    exes = {e["name"]: e["root"] for e in tomllib.loads((root / "lakefile.toml").read_text()).get("lean_exe", [])}
    absent = [e for e in EXES if e not in exes]
    if absent:
        raise ValueError(f"lakefile.toml has no lean_exe {' '.join(absent)}")
    return [exes[e] for e in EXES]


class Tree:
    """The checked-out tree: the executables' import cone and what a baseline leaves to build."""

    def __init__(self, root):
        self.root = Path(root).resolve()
        self.plan = load("ci_build_plan", "ci-build-plan.py")
        lsb = self.plan.lsb
        self.libs, self.mods, self.imports = lsb.load_modules(self.root)
        self.secs = {m: s for m, (_, s) in lsb.load_profile([self.root / "scripts/lake-module-peaks.tsv"]).items()}
        missing = [r for r in exe_roots(self.root) if r not in self.mods]
        if missing:
            raise ValueError(f"no source for the executable root module(s) {' '.join(missing)}")
        self.cone, stack = set(), exe_roots(self.root)
        while stack:
            m = stack.pop()
            if m not in self.cone:
                self.cone.add(m)
                stack.extend(self.imports[m])
        self.importers = {m: [] for m in self.cone}
        for m in self.cone:
            for d in self.imports[m]:
                self.importers[d].append(m)

    def has_commit(self, sha):
        if subprocess.run(["git", "cat-file", "-e", f"{sha}^{{commit}}"], cwd=self.root,
                          capture_output=True).returncode == 0:
            return True
        # Not --depth: a shallow boundary would make stock-comparison-baseline.py's ancestry
        # test refuse the checkout.
        subprocess.run(["git", "fetch", "-q", "origin", sha], cwd=self.root, capture_output=True)
        return subprocess.run(["git", "cat-file", "-e", f"{sha}^{{commit}}"], cwd=self.root,
                              capture_output=True).returncode == 0

    def to_build(self, sha):
        """Modules of the cone that a complete build of commit `sha` does not provide for HEAD."""
        changed = self.plan.changed_modules(self.root, sha, self.libs, self.mods)
        if changed is None:  # the toolchain or the Lake configuration differs, or git failed
            return set(self.cone)
        out, stack = set(), [m for m in changed if m in self.cone]
        while stack:
            m = stack.pop()
            if m not in out:
                out.add(m)
                stack.extend(self.importers[m])
        return out

    def estimate(self, modules):
        return TIME_SCALE * sum(self.secs.get(m, DEFAULT_SECS) for m in modules)


def assemble_result(repo, run_id, api):
    """Conclusion of the run's newest assemble job (None: none, or not finished).

    `filter=latest` lists the jobs of the newest attempt. A job that an attempt did not run
    again is listed there with the conclusion it had (seen on run 43460163729: after only
    "Check lost matches" was re-run, attempt 2 lists "Build and compare" as `success` under a
    new job id), so re-running a gate job of a Full gate run does not hide its assemble job,
    and a re-run of the assemble job itself replaces the old conclusion."""
    found, page = [], 1
    while True:
        listed = json.loads(api(f"repos/{repo}/actions/runs/{run_id}/jobs?filter=latest&per_page=100&page={page}"))
        found += [job for job in listed["jobs"] if job["name"] == ASSEMBLE]
        if not listed["jobs"] or page * 100 >= listed.get("total_count", 0):
            break
        page += 1
    if not found:
        return None
    return max(found, key=lambda job: (job.get("run_attempt") or 0, job.get("id") or 0)).get("conclusion")


def usable(repo, run, api):
    """Why `run` (a workflow run object) cannot be the build, or None. Two API calls."""
    if run.get("path", "").split("@")[0] != WORKFLOW_PATH:
        return "not a Full gate run"
    if run.get("event") not in EVENTS:
        return f"a {run.get('event')} run"
    if (run.get("head_repository") or {}).get("full_name") != repo:
        return "a run of another repository"
    if not re.fullmatch(r"[0-9a-f]{40}", run.get("head_sha") or ""):
        return "no commit"
    names = {a["name"] for a in json.loads(api(f"repos/{repo}/actions/runs/{run['id']}/artifacts?per_page=100"))["artifacts"]
             if not a["expired"]}
    if ARTIFACT not in names:
        return f"no unexpired {ARTIFACT}"
    if MISSING in names:
        return "a partial build"
    # The assemble job uploads `lake-full` before the list of missing modules and fails after
    # both: without the list (the job is still running, or it lost its runner between the two
    # uploads) a partial build looks complete. Only the job's success says it is.
    assembled = assemble_result(repo, run["id"], api)
    if assembled != "success":
        return f"its assemble job is {assembled or 'not finished'}"
    return None


def candidates(repo, head, api):
    """Run objects to consider: the Full gate runs on `head`, then the runs of the newest
    unexpired `lake-full` artifacts. Each run once."""
    seen = set()
    same = json.loads(api(f"repos/{repo}/actions/workflows/{WORKFLOW}/runs?head_sha={head}&per_page=100"))
    for run in sorted(same["workflow_runs"], key=lambda r: r["id"], reverse=True):
        if run["id"] not in seen:
            seen.add(run["id"])
            yield run
    listed = json.loads(api(f"repos/{repo}/actions/artifacts?name={ARTIFACT}&per_page=100"))["artifacts"]
    newest = sorted((a for a in listed if not a["expired"] and a.get("workflow_run")),
                    key=lambda a: a["created_at"], reverse=True)
    ids = []
    for a in newest:
        run_id = a["workflow_run"].get("id")
        if isinstance(run_id, int) and run_id not in seen and run_id not in ids:
            ids.append(run_id)
    for run_id in ids[:CANDIDATES]:
        seen.add(run_id)
        yield json.loads(api(f"repos/{repo}/actions/runs/{run_id}"))


def result(tree, run, head, modules, reason):
    return {"run": run["id"] if run else None, "head_sha": run["head_sha"] if run else None,
            "branch": run.get("head_branch") if run else None,
            "same_commit": bool(run) and run["head_sha"] == head,
            "to_build": len(modules), "cone": len(tree.cone),
            "estimate_s": round(tree.estimate(modules)), "reason": reason}


def find(repo, head, tree, api=gh_api, log=print):
    best = None
    for run in candidates(repo, head, api):
        why = usable(repo, run, api)
        if why is None and not tree.has_commit(run["head_sha"]):
            why = "its commit cannot be fetched"
        if why is not None:
            log(f"run {run.get('id')}: {why}")
            continue
        modules = tree.to_build(run["head_sha"])
        cost = tree.estimate(modules)
        log(f"run {run['id']} ({run.get('head_branch')} {run['head_sha'][:12]}): "
            f"{len(modules)} of {len(tree.cone)} modules to build, about {cost / 60:.0f} min of Lean")
        if best is None or cost < best[0]:
            best = (cost, run, modules)
        if not modules:
            break
    if best is None:
        return result(tree, None, head, tree.cone, f"no complete unexpired {ARTIFACT} of a Full gate run")
    _, run, modules = best
    return result(tree, run, head, modules, "the Full gate build of this commit" if run["head_sha"] == head
                  else "the Full gate build that leaves the least to build")


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--head", help="the tested commit (checked out as HEAD)")
    parser.add_argument("--out", type=Path)
    parser.add_argument("--root", type=Path, default=HERE.parent)
    parser.add_argument("--github-output", action="store_true")
    parser.add_argument("--print", choices=["exes", "roots"], dest="show")
    args = parser.parse_args()
    if args.show:
        print("\n".join(EXES if args.show == "exes" else exe_roots(args.root.resolve())))
        return 0
    if not args.out or not re.fullmatch(r"[0-9a-f]{40}", args.head or ""):
        parser.error("--head (a full commit id) and --out are required")
    repo = os.environ["GITHUB_REPOSITORY"]
    try:
        tree = Tree(args.root)
        checked_out = subprocess.run(["git", "rev-parse", "HEAD"], cwd=tree.root, check=True,
                                     capture_output=True, text=True).stdout.strip()
        if checked_out != args.head:
            raise ValueError(f"HEAD is {checked_out}, not the tested commit")
        found = find(repo, args.head, tree)
    except Exception as error:  # reported as a failed lookup; the job stops here
        detail = str(error)
        if isinstance(error, subprocess.CalledProcessError):
            stderr = error.stderr.decode(errors="replace") if isinstance(error.stderr, bytes) else error.stderr
            print(stderr, file=sys.stderr)
            detail = f"{' '.join(error.cmd[:3])} exited with status {error.returncode}"
        print(f"::error title=No stock-comparison result::the lookup of a Full gate build failed "
              f"({type(error).__name__}: {detail}); nothing was measured. Re-run this job.")
        return 1
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(found) + "\n")
    minutes = found["estimate_s"] / 60
    if found["run"] is None:
        line = (f"{found['reason']}: all {found['cone']} modules are built here (scheduled within memory; "
                f"about {minutes:.0f} min of Lean)")
        print(f"::warning title=Stock comparison builds its Lean executables from nothing::{line}")
    else:
        line = (f"Lean build: Full gate run {found['run']} ({found['branch']} {found['head_sha'][:12]}; "
                f"{found['reason']}): {found['to_build']} of {found['cone']} modules to build here, "
                f"about {minutes:.0f} min of Lean")
        print(line)
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as out:
            out.write(line + "\n\n")
    if args.github_output:
        with open(os.environ["GITHUB_OUTPUT"], "a") as out:
            out.write(f"run={found['run'] or ''}\nto-build={found['to_build']}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
