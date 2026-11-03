"""Run only after the parent confirms the source share returned."""
from pathlib import Path
import datetime
import hashlib
import importlib.util
import json
import os
import psutil
import re
import shutil
import subprocess
import tomllib

D = Path(__file__).resolve().parent
Q = D.parent
E = Q.parent
R = Q / "validation-package-v1"
G = Path("/home/lee/clifv/.worktrees/loop-20261102")
P = E / "892-joint-current-context-v2/package"
L = D / "passed-four-real-audit-v1"
L.mkdir(exist_ok=False)
PROPOSAL = D / "ordinary2GiB-four-root-alternative-v1.json"
EXPECTED_PROPOSAL = "35e3ee2cdb3d4221aca17937a4ff3a88c199b6036f8d87daa57e9598efa6e6df"
records = []
outputs = {}
protected = {}
axes = {}
last_stage = "setup"
status = "STOPPED"
error = None


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1048576):
            digest.update(chunk)
    return digest.hexdigest()


def save_json(path, data):
    path.write_text(json.dumps(data, indent=2) + "\n")


def source_path(name):
    return Path(name.replace(".", "/") + ".lean")


def closure(name, graph):
    found = set()
    pending = [name]
    while pending:
        item = pending.pop()
        if item in found:
            continue
        found.add(item)
        pending.extend(graph[item])
    return found


def active_writers(targets):
    found = []
    for proc in psutil.process_iter(["uids", "name", "status", "cmdline"]):
        try:
            if proc.info["uids"].real != os.getuid():
                continue
            if proc.info["name"] not in ["lean", "lake"] or proc.info["status"] == "zombie":
                continue
            argv = proc.info["cmdline"] or []
            cwd = proc.cwd()
            owns_prefix = any(cwd.startswith(str(root)) or any(str(root) in arg for arg in argv)
                              for root in [R, G])
            owns_target = any(any(name.replace(".", "/") + suffix in arg
                                 for suffix in [".lean", ".c"] for arg in argv)
                              for name in targets)
            if owns_prefix or owns_target:
                found.append({"pid": proc.pid, "cwd": cwd, "argv": argv})
        except (psutil.NoSuchProcess, psutil.AccessDenied):
            continue
    return found


def artifacts(name):
    files = {}
    for area in ["lib/lean", "ir"]:
        stem = R / ".lake/build" / area / name.replace(".", "/")
        for path in sorted(stem.parent.glob(stem.name + ".*")):
            if path.is_file():
                files[str(path.relative_to(R))] = sha(path)
    return files


def check_protected():
    for rel, expected in protected.items():
        assert sha(R / rel) == expected, ("Protected output changed", rel)


def run(label, argv, allowed=(0,)):
    global last_stage
    last_stage = label
    stats = L / (label + ".mem")
    log = L / (label + ".log")
    child_env = dict(env, FV_MEMCAP_STATS=str(stats), FV_MEMCAP_UNIT="worker-o-memory-four-" + label)
    with log.open("w") as stream:
        code = subprocess.call([str(P / "scripts/memcap.sh"), *argv], cwd=R,
                               env=child_env, stdout=stream, stderr=subprocess.STDOUT)
    memory = stats.read_text() if stats.exists() else "MISSING_MEMORY_RECORD"
    record = {"label": label, "cwd": str(R), "argv": argv, "exit": code,
              "log_sha256": sha(log), "memory": memory}
    records.append(record)
    save_json(L / "progress.json", records)
    print(label, code, flush=True)
    assert code in allowed, (label, code)
    assert "oom 0\n" in memory and "oom_kill 0\n" in memory, (label, memory)
    return code


try:
    assert sha(PROPOSAL) == EXPECTED_PROPOSAL
    proposal = json.loads(PROPOSAL.read_text())
    previous_path = D / "ordinary2GiB-four-root-run-v1/receipt.json"
    assert sha(previous_path) == "e599cad15f7674a603e6940fa35d928d2f41fafccfa8970f5c8dd91500874ba0"
    previous = json.loads(previous_path.read_text())
    targets = list(previous["passed_targets"])
    assert len(targets) == 4
    configs = proposal["config_records"]["R"]
    for rel, expected in configs.items():
        assert sha(R / rel) == expected, rel
    for row in proposal["targets4"]:
        assert sha(R / source_path(row["target"])) == row["source_sha256"]
    for name, entry in previous["passed_targets"].items():
        for rel, expected in entry["artifacts"].items():
            assert sha(R / rel) == expected, (name, rel)
    protected = previous["protected_outputs"]
    check_protected()
    for proc in psutil.process_iter(["uids", "name", "status", "cmdline"]):
        try:
            if proc.info["uids"].real != os.getuid() or proc.info["name"] not in ["lean", "lake"]:
                continue
            if proc.info["status"] == "zombie":
                continue
            assert not proc.cwd().startswith(str(R)), ("R writer", proc.pid)
        except (psutil.NoSuchProcess, psutil.AccessDenied):
            continue
    env = dict(os.environ)
    for key in ["FV_MEMCAP_OFF", "FV_LAKE_CACHE", "LEAN_PATH", "LEAN_SYSROOT", "LEAN_SRC_PATH", "LAKE_CACHE_DIR"]:
        env.pop(key, None)
    env.update(PATH="/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:" + env["PATH"],
               FV_ROOT=str(R), FV_MEMCAP="2G", LAKE_ARTIFACT_CACHE="false",
               LAKE_RESTORE_ARTIFACTS="false", LEAN_NUM_THREADS="1", OMP_NUM_THREADS="1", OMP_THREAD_LIMIT="1")
    run("passed-four-normal", ["lake", "build", "--no-build", *targets])
    audit = L / "memory-four-roots.lean"
    audit.write_text("\n".join("import " + name for name in targets) + "\n\n" +
                     "".join("#print axioms " + name + "\n" for name in proposal["audit_roots"]))
    run("real-five-root-audit", ["python3", str(P / "scripts/axiom-audit.py"), "--cwd", str(R),
                                "--log-dir", str(L / "audit"), str(audit)])
    spec = importlib.util.spec_from_file_location("four_root_axioms",
        E / "general7-main-candidate-v1/old-axiom-preservation-v1/axiom_records.py")
    collector = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(collector)
    for log in (L / "audit").glob("*.log"):
        for name, values in collector.parse_records(log.read_text()):
            assert name not in axes
            axes[name] = sorted(values)
    assert set(axes) == set(proposal["audit_roots"])
    assert all(set(values) <= {"Classical.choice", "Quot.sound", "propext"} for values in axes.values())
    assert axes["Backend.Stock.Memory.SretCopy.CfgClass"] == []
    check_protected()
    for name, entry in previous["passed_targets"].items():
        for rel, expected in entry["artifacts"].items():
            assert sha(R / rel) == expected
    status = "PASSED_FOUR_PROPER_CURRENT_ROOTS_AND_REAL_FIVE_ROOT_AUDIT"
except BaseException as exc:
    error = repr(exc)
    raise
finally:
    save_json(L / "receipt.json", {
        "status": status, "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "last_stage": last_stage, "error": error, "records": records,
        "axiom_sets": axes, "prior_four_root_receipt_sha256":
            "e599cad15f7674a603e6940fa35d928d2f41fafccfa8970f5c8dd91500874ba0",
        "new_provider_or_descendant_kernels": [], "protected_outputs": protected,
        "affected22_and_baseline1357": "OPEN; stopped affected22 receipt preserved",
        "full_original_goal_complete": False})
