#!/usr/bin/env python3
"""Validate normal Stock mixed modules, real linked artifacts and emitted proofs.

Run after building FV/FVTest and lean-backend/lean-link/link-check, with the same
shared Lake cache. --output must be a new directory outside the source tree.
Every compiler subprocess uses memcap.sh, sequentially, without proof timeouts.
This integration gate supplements the full corpus, trust and identity gates.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def expected_roots(prefix="Mixed"):
    roots = set()
    for mode in ("Plain", "Cleanup"):
        for policy in ("Strict", "Fallback"):
            roots.add(f"Stock{prefix}6{mode}{policy}Global")
        roots.add(f"Stock{prefix}2{mode}FallbackGlobal")
        roots.add(f"Stock{prefix}6Mixed{mode}FallbackGlobal")
        roots.add(f"Stock{prefix}2Retained{mode}FallbackGlobal")
    roots.update((f"Stock{prefix}33CleanupFallbackGlobal", f"Stock{prefix}33CleanupFallbackEntries"))
    return roots


def proof_order(directory, prefix="Mixed"):
    """Use actual local imports, including Input and per-entry proof slices."""
    files = {".".join(p.relative_to(directory).with_suffix("").parts): p
             for p in (directory / "Crates").rglob("*.lean")}
    roots = {p.stem for p in (directory / "Crates").glob("*.lean")}
    if roots != expected_roots(prefix):
        raise RuntimeError(f"unexpected generated roots: missing={expected_roots(prefix)-roots}, extra={roots-expected_roots(prefix)}")
    ordered, visiting, visited = [], set(), set()

    def visit(module):
        if module in visited:
            return
        if module in visiting:
            raise RuntimeError(f"cyclic generated import: {module}")
        visiting.add(module)
        path = files[module]
        for imported in re.findall(r"^(?:(?:public|private|meta)\s+)*import\s+(\S+)", path.read_text(), re.M):
            if imported.startswith("Crates."):
                if imported not in files:
                    raise RuntimeError(f"missing generated import {imported} from {module}")
                visit(imported)
        visiting.remove(module)
        visited.add(module)
        ordered.append(path)

    for module in sorted(files):
        visit(module)
    return ordered


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--class", dest="kind", choices=["mixed", "logical", "scalar", "not", "mul", "shift", "cast"], default="mixed")
    options = parser.parse_args()
    prefix = {"scalar": "ScalarProduction", "not": "NotProduction", "mul": "MulProduction", "shift": "ShiftProduction", "cast": "CastProduction"}.get(options.kind, options.kind.capitalize())
    view = Path(__file__).resolve().parents[1]
    output = options.output.resolve()
    if output == view or view in output.parents:
        parser.error("--output must be outside the source tree")
    output.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, OMP_NUM_THREADS="2", OMP_THREAD_LIMIT="2", LEAN_NUM_THREADS="2")
    env.setdefault("FV_MEMCAP", "8G")
    memcap = str(view / "scripts/memcap.sh")
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=view, text=True).strip()
    sources = {str(p.relative_to(view)): sha(p) for folder in ("FV", "FVTest")
               for p in (view / folder).rglob("*.lean")}
    script_hash = sha(Path(__file__).resolve())
    records = {}

    def frozen():
        assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=view, text=True).strip() == head
        current = {str(p.relative_to(view)): sha(p) for folder in ("FV", "FVTest")
                   for p in (view / folder).rglob("*.lean")}
        assert current == sources, "source changed during integration gate"
        assert sha(Path(__file__).resolve()) == script_hash, "gate script changed during validation"

    def report(state, **details):
        (output / "receipt.json").write_text(json.dumps({
            "state": state, "head": head, "pid": os.getpid(),
            "script_sha256": script_hash, "records": records, **details,
        }, indent=2) + "\n")

    def run(name, args):
        frozen()
        log = output / (name + ".log")
        report("running", phase=name)
        print(f"Stock mixed integration: {name}", flush=True)
        with log.open("w") as stream:
            result = subprocess.run([memcap, *args], cwd=view, env=env,
                                    stdout=stream, stderr=subprocess.STDOUT)
        records[name] = {"returncode": result.returncode, "log": str(log), "sha256": sha(log)}
        if result.returncode:
            raise RuntimeError(f"{name} failed ({result.returncode}); see {log}")
        frozen()
        return log.read_text()

    try:
        (output / "sources.json").write_text(json.dumps(sources, indent=2) + "\n")
        run("current-module-keys", ["lake", "build", "--no-build",
            f"FVTest.Backend.Lowering.Stock{prefix}Runtime", f"FVTest.Backend.Lowering.Stock{prefix}Linked",
            "lean-backend", "lean-link", "link-check"])
        runtime = run("runtime", ["lake", "env", "lean", "--run",
                                  f"FVTest/Backend/Lowering/Stock{prefix}Runtime.lean"])
        assert runtime.count(f"Stock {options.kind} lean ") == 6
        assert runtime.count(f"Stock {options.kind} regalloc2 ") == 6
        assert f"Stock {options.kind} missing-binary negative control passed" in runtime
        generated = output / "linked"
        run("linked-fixture", ["lake", "env", "lean", "--run",
            f"FVTest/Backend/Lowering/Stock{prefix}Linked.lean", str(generated)])
        artifact_hashes = {str(p.relative_to(generated)): sha(p)
                           for p in generated.rglob("*") if p.is_file()}
        leanpath = subprocess.check_output([memcap, "lake", "env", "printenv", "LEAN_PATH"],
                                          cwd=view, env=env, text=True).strip()
        original_leanpath = env.get("LEAN_PATH")
        env["LEAN_PATH"] = str(generated) + ":" + leanpath
        paths = proof_order(generated, prefix)
        generated_hashes = {str(p.relative_to(generated)): sha(p) for p in paths}
        audit_imports = [".".join(p.relative_to(generated).with_suffix("").parts)
                         for p in paths if p.parent == generated / "Crates"]
        for path in paths:
            run("generated-" + "-".join(path.relative_to(generated).parts), ["lean",
                "--root=" + str(generated), "-o", str(path.with_suffix(".olean")), str(path)])
        if original_leanpath is None:
            env.pop("LEAN_PATH", None)
        else:
            env["LEAN_PATH"] = original_leanpath
        # Keep every Crates module under one import root; Lean chooses the first
        # matching package directory and does not search another partial root.
        cli_hashes = {}
        for mode, flags in (("Plain", ["--no-dead-cleanup"]), ("Cleanup", [])):
            bundle = generated / f"Stock{prefix}2{mode}FallbackGlobal-bundle"
            retained = generated / f"Stock{prefix}2Retained{mode}FallbackGlobal-bundle"
            for label, source in (("current", bundle), ("retained", retained)):
                proof = generated / "Crates" / f"{prefix}CLI{label}{mode}.lean"
                proof.parent.mkdir(exist_ok=True)
                run(f"link-check-{label}-{mode}", ["lake", "env", str(view / ".lake/build/bin/link-check"),
                    str(source), "--lean", str(proof), "--module", proof.stem, *flags])
                if label == "retained" and mode == "Plain":
                    selected = re.search(r"Backend\.Stock\.Scalar\.lowerWithRoutes \[(.*?)\]", proof.read_text(), re.S)
                    assert selected and re.search(r",\s*[1-4]\)", selected.group(1)), "non-default retained reconstruction route was not exercised"
                env["LEAN_PATH"] = str(generated) + ":" + leanpath
                run(f"cli-proof-{label}-{mode}", ["lean", "--root=" + str(generated),
                    "-o", str(proof.with_suffix(".olean")), str(proof)])
                cli_hashes[str(proof.relative_to(output))] = sha(proof)
                audit_imports.append("Crates." + proof.stem)
                if original_leanpath is None:
                    env.pop("LEAN_PATH", None)
                else:
                    env["LEAN_PATH"] = original_leanpath
            linked = run("verified-link-" + mode, ["lake", "env", str(view / ".lake/build/bin/lean-link"),
                str(bundle), "--verified", *flags])
            assert "written by Link.SemanticCompilerWith.compile" in linked
            assert "attempt_correct_source_peak" in linked
        audit = output / "GeneratedAxioms.lean"
        audit.write_text("\n".join("import " + module for module in audit_imports) + r'''
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let generated := fun (name : Name) =>
    name.toString.startsWith "Crates.StockMixed" || name.toString.startsWith "Crates.MixedCLI"
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    unless generated name do continue
    for ax in ← collectAxioms name do
      if #[``propext, ``Classical.choice, ``Quot.sound].contains ax then continue
      unless generated ax && (ax.toString.splitOn "._native.native_decide.ax_").length > 1 do
        throwError "unexpected generated-proof axiom {ax} in {name}"
    count := count + 1
  unless count > 0 do throwError "empty generated-proof audit"
  logInfo m!"STOCK_MIXED_GENERATED_AXIOMS_PASS {count}"
'''.replace('StockMixed', 'Stock'+prefix).replace('MixedCLI', prefix+'CLI').replace('STOCK_MIXED', 'STOCK_'+prefix.upper()))
        env["LEAN_PATH"] = str(generated) + ":" + leanpath
        audited = run("generated-axioms", ["lean", "--root=" + str(output), str(audit)])
        assert "STOCK_" + prefix.upper() + "_GENERATED_AXIOMS_PASS " in audited
        assert all(sha(generated / path) == digest for path, digest in generated_hashes.items())
        assert all(sha(output / path) == digest for path, digest in cli_hashes.items())
        assert all(sha(generated / path) == digest for path, digest in artifact_hashes.items()), "linked inputs changed during CLI validation"
        report("passed", source_manifest_sha256=sha(output / "sources.json"),
               generated_roots=sorted(expected_roots(prefix)), generated_sources=generated_hashes,
               cli_sources=cli_hashes, generated_axiom_audit_sha256=sha(audit),
               linked_artifacts=artifact_hashes,
               regalloc_binary_sha256=sha(view / "rust/target/release/lean-regalloc"),
               runtime_cases=24, strict_missing_oracle_negative_control=True,
               limits="Integration evidence only; full corpus, native execution, trust/MCP and identity/stage gates remain required.")
    except BaseException as error:
        report("failed", error=repr(error))
        raise


if __name__ == "__main__":
    main()
