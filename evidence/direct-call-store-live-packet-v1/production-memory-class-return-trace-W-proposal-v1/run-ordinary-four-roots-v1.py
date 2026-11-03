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
L = D / "ordinary2GiB-four-root-run-v1"
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
    context = json.loads((D / "source-context.json").read_text())
    graph = context["graph"]
    targets = [row["target"] for row in proposal["targets4"]]
    expected_keys = {row["target"]: row["expected_key"] for row in proposal["targets4"]}
    assert len(targets) == 4
    assert not active_writers(targets), active_writers(targets)
    configs = proposal["config_records"]["R"]
    for rel, expected in configs.items():
        assert sha(R / rel) == expected, ("Config changed", rel)
    config = tomllib.loads((R / "lakefile.toml").read_text())
    assert "-j1" in config.get("weakLeanArgs", []), "R must retain explicit weak -j1"
    owned_new = {"FV.E2E." + name for name in json.loads((D / "manifest.json").read_text())["modules"]}
    baseline = sorted(set(graph) - owned_new)
    assert len(baseline) == 1357
    for name in baseline:
        assert sha(R / source_path(name)) == context["sources"][name]["sha256"], ("Source changed", name)

    # Preserve every passed W output and both proper donor outputs.
    progress = json.loads((Q / "return-trace-progress-current8f-v1.json").read_text())
    for entry in progress["verified_return_providers"].values():
        receipt_path = Path(entry["receipt"])
        assert sha(receipt_path) == entry["sha256"]
        receipt = json.loads(receipt_path.read_text())
        source_outputs = receipt.get("outputs", receipt.get("changed_owned_outputs", {}))
        for key, value in source_outputs.items():
            current = value.get("artifacts", {}) if isinstance(value, dict) else {key: value}
            for rel, expected in current.items():
                assert sha(R / rel) == expected, ("Passed W output changed", rel)
                protected[rel] = expected
    donors = json.loads((D / "two-proper-donor-reuse-v1/receipt.json").read_text())
    for entry in donors["copied"].values():
        for rel, expected in entry["artifacts"].items():
            assert sha(R / rel) == expected, ("Passed donor changed", rel)
            protected[rel] = expected
    save_json(L / "protected-before.json", protected)

    env = dict(os.environ)
    for key in ["FV_MEMCAP_OFF", "FV_LAKE_CACHE", "LEAN_PATH", "LEAN_SYSROOT", "LEAN_SRC_PATH", "LAKE_CACHE_DIR"]:
        env.pop(key, None)
    env.update(PATH="/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:" + env["PATH"],
               FV_ROOT=str(R), FV_MEMCAP="2G", LAKE_ARTIFACT_CACHE="false",
               LAKE_RESTORE_ARTIFACTS="false", LEAN_NUM_THREADS="1",
               OMP_NUM_THREADS="1", OMP_THREAD_LIMIT="1")

    for index, name in enumerate(targets):
        assert not active_writers([name]), active_writers([name])
        dependency_names = sorted(closure(name, graph) - {name})
        run("dependencies-" + str(index), ["lake", "build", "--no-build", *dependency_names])
        run("key-" + str(index), ["lake", "query", "--no-build", "+" + name + ":depHash"])
        keys = re.findall(r"^[0-9a-f]{16}$", (L / ("key-" + str(index) + ".log")).read_text(), re.M)
        assert keys == [expected_keys[name]], ("Current key changed", name, keys)
        before = artifacts(name)
        for rel, expected in before.items():
            path = R / rel
            assert not path.is_symlink() and path.stat().st_uid == os.getuid()
            assert path.stat().st_nlink == 1 and str(path.parent.resolve()).startswith(str(R.resolve()))
            saved = L / "preserved-old-targets" / rel
            saved.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, saved)
            assert sha(saved) == expected
        save_json(L / ("old-target-" + str(index) + ".json"), before)
        ready = run("ready-" + str(index), ["lake", "build", "--no-build", name], allowed=(0, 3))
        if ready == 3:
            rejected = re.findall(r"✖ .* Building ([\w.]+)", (L / ("ready-" + str(index) + ".log")).read_text())
            assert set(rejected) == {name}, ("Unexpected rejected dependency", name, rejected)
            run("kernel-" + str(index), ["lake", "-v", "build", "+" + name + ":leanArts"])
        run("normal-" + str(index), ["lake", "build", "--no-build", name])
        trace = R / ".lake/build/lib/lean" / Path(name.replace(".", "/") + ".trace")
        metadata = json.loads(trace.read_text())
        assert metadata.get("inputs") and not metadata.get("synthetic"), ("Unsupported target provenance", name)
        assert metadata["depHash"] == keys[0]
        after = artifacts(name)
        promotable = {rel: value for rel, value in after.items()
                      if ".c.o" not in rel and not rel.endswith((".o", ".bc"))}
        outputs[name] = {"native_key": keys[0], "trace_sha256": sha(trace),
                         "artifacts": promotable, "all_retained_target_files": after,
                         "fresh_kernel": ready == 3, "old_outputs_preserved": True}
        save_json(L / "passed-targets.json", outputs)
        check_protected()

    # These descendants are checks only. A rejection stops this four-root run.
    run("affected22-normal", ["lake", "build", "--no-build", *proposal["affected_baseline22"]])
    audit = L / "memory-four-roots.lean"
    audit.write_text("\n".join("import " + name for name in targets) + "\n\n" +
                     "".join("#print axioms " + name + "\n" for name in proposal["audit_roots"]))
    run("real-audit-five", ["python3", str(P / "scripts/axiom-audit.py"), "--cwd", str(R),
                            "--log-dir", str(L / "audit"), str(audit)])
    spec = importlib.util.spec_from_file_location("memory_four_axioms",
        E / "general7-main-candidate-v1/old-axiom-preservation-v1/axiom_records.py")
    collector = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(collector)
    for log in (L / "audit").glob("*.log"):
        for name, values in collector.parse_records(log.read_text()):
            assert name not in axes, ("Duplicate audit root", name)
            axes[name] = sorted(values)
    assert set(axes) == set(proposal["audit_roots"])
    assert all(set(values) <= {"Classical.choice", "Quot.sound", "propext"} for values in axes.values())
    assert axes["Backend.Stock.Memory.SretCopy.CfgClass"] == []
    run("baseline1357-normal", ["lake", "build", "--no-build", *baseline])
    check_protected()
    for rel, expected in configs.items():
        assert sha(R / rel) == expected, rel
    for name in baseline:
        assert sha(R / source_path(name)) == context["sources"][name]["sha256"], name
    status = "PASSED_FOUR_CURRENT8F_ROOTS_AFFECTED22_AUDIT5_BASELINE1357"
except BaseException as exc:
    error = repr(exc)
    raise
finally:
    stopped = []
    if records and records[-1]["exit"] == 3:
        stopped = re.findall(r"✖ .* Building ([\w.]+)",
                             (L / (records[-1]["label"] + ".log")).read_text())
    save_json(L / "receipt.json", {
        "status": status, "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "proposal_sha256": EXPECTED_PROPOSAL, "last_stage": last_stage, "error": error,
        "records": records, "passed_targets": outputs, "axiom_sets": axes,
        "rejected_targets_on_stop": stopped, "conditional_descendant_kernels": [],
        "protected_outputs": protected, "actual_source_and_config_context": "current8f frozen proposal",
        "reassignment_scope": "four named roots only; Loop exact-output reuse requires parent review",
        "no_shared_prefix_or_cache_writes": True, "no_compiler_signalled": True,
        "full_original_goal_complete": False})
