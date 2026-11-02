# Shared #513 and production gate queue

Owner: worker-O execution coordinator. The investigation delegate owns this queue and its cleanup.
No build started. No proof slot is held. The typed activation agent retains the current3GiBslot.
No worktree or cache was created. The protected12GiBvalidation and its handoff owners remain untouched.

## Concrete snapshot

The prepared base is77088aba2b9c528264aead43ab563d7ee17a102e.
The combined tree isf29ccd6477b9c1cdb4be7053058e71c1d2f34540.
`snapshot-plan.json` records the complete source tree and separate packet hashes.
The tree combines the reconciled207-file extraction, the7-file activation packet, and four typed files.
One overlap exists: the typed LinkCheckMain replaces the earlier activation LinkCheckMain.
The coordinator explicitly accepted this exact replacement. `source-overlap-acceptance-v1.json` binds both full hashes and current receipts.
The replacement matches canonical activation-v2 and passed six complete bundles with48generated roots.
The queue rejects changed packet source. Regenerate and review the queue if an implementation agent changes its packet.
The final typed compiler modes remain active. The combined preflight rejects this preparatory snapshot until a final manifest is bound.
This guard applies only to the shared integration snapshot. It does not block an independently eligible direct-review delivery.

The tree contains5255project modules,198audit files,97crate-proof source files, and46executables.
The #513 reverse closure contains2547source consumers. Activation adds10affected consumers; eight overlap.
The shared normal scheduler builds each actual module key once. The shared audit pass runs each audit file once.
Do not run separate #513 and activation importer closures over the same snapshot.

`per-pr-bindings.json` separates the #513 tree, activation tree, and combined tree.
The combined result provides integration evidence. It does not replace either PR's exact-head CI or tested/merged tree receipt.
Green comparison CI is not evidence that all tests ran.

## Preserved and reusable evidence

`preservation-and-reuse.json` hashes the original preservation receipts.
They retain372headers,203complete consumer bodies,eight moved declarations,and eight current type/axiom comparisons.
All230sources in the passed focused context remain exact in the combined tree.
Reuse that focused result. Do not schedule another separate focused proof pass.
The normal scheduler still needs normal Lake products; the temporary focused outputs were already removed.

Exactly3004project modules retain the frozen snapshot's complete source dependency closure.
This identifies potential shared-cache reuse. The upstream scheduler must validate actual Lake keys and installed outputs.
Do not treat source equality alone as an output receipt.
Do not reuse partial historical builds or old audits whose full source context differs.

## Required sequence and mutation gates

1. Preserve and remotely back up both implementation packets and all new evidence.
2. Wait for owners3477137,3478090,3478318,and1849857 to exit. Do not kill or restart them.
3. Record the accepted typed CLI replacement, final compiler-mode binding, ownership, and12GiBshared gate budget.
4. Use the already-owned source view after release. Do not create another worktree or warm cache.
5. Materialize the pinned current-main baseline there. Keep the shared cache and successful artifacts.
6. Collect current-main comparison, both cleanup identity reports, and baseline exact axiom sets before changing production source.
7. Review and freeze all packet hashes. Materialize the combined tree in the same view.
8. Run the shared normal, tool, crate, audit, E2E, comparison, runtime, encoder, and example phases.
9. Run the exact preserved runtime matrices and real generated-proof consumers on that same snapshot.
10. Compare every old axiom set, accepted identity, settings result, successful stage, and retained artifact hash.
11. Complete each PR's independent source-context, direct-review, exact-head CI, and tested/merged tree gates.
12. Preserve evidence, remove expendable outputs, and release ownership. Retain only the existing warm cache.

The coordinator owns materialization. These scripts never check out or modify source.
The coordinator must verify current main again before baseline materialization.
If main moves during the long gate, preserve the frozen result and reconcile afterward.

## Runnable guarded phases

`preflight.py` checks an already-materialized, clean source view and an explicit coordinator release file.
It refuses the primary checkout and every active protected owner. It also checks source trees and packet hashes.
The release file requires these fields:

```
owner: "worker-O execution coordinator"
view: absolute existing worktree path
allow_shared_full_gate: true
released_old_owner_pids: [3477137, 3478090, 3478318, 1849857]
resource_budget: "12G/max1; O aggregate16G"
reviewed_overlap_sha256: SHA256 of source-overlap-decision.json
backup_receipt: absolute remote-backup receipt path
backup_receipt_sha256: SHA256 of that receipt
remote_backup_verified: true
```

All phases use12GiB,max1schedulerjob,and two Lean/OMP/Cargo threads. They share the one existing cache.
The full gate can run beside an independently allocated3GiBslot under O's16GiBaggregate cap.
The upstream scheduler retains its actual module locks and duplicate-work detection.
One exclusive queue lock prevents parallel phase writers in this view.
No script widens the cap through stock-delivery-gates.py's scheduler argument rewriting.

The following command is a template. The coordinator supplies the released view and release file.

```
WORKER_O_FULL_GATE_GRANTED=513-production-shared python3 run-phase.py \
  --root RELEASED_VIEW --release RELEASE_JSON \
  --stage baseline --phase comparison --attempt baseline-comparison-v1
```

Run every job through `ai-coord watch`.
The available phases are normal,audits,tools,crates,e2e,comparison,runtime-encoder,examples,crate-parity,retained-matrices,nonmemory-matrices,and configured-tests.
Run baseline normal/tools as needed to satisfy actual current keys before baseline measurements and audits.
After materialization, run combined normal first, then the other combined phases.
All attempts preserve distinct logs and source-bound receipts. Inspect failures before retrying.

The comparison phase measures lean-backend and lean-stock-lowering-compare separately.
It preserves original requests and accepts exit10only as a finished measurement with known gaps.
It rejects missing results,harness errors,configuration overrides,and binary normalization.
It never labels a completed measurement suite equivalence.

`compare-axioms.py` compares the exact root sets from passed baseline and combined audit attempts.
It rejects every missing or changed old axiom set.
The actual captured runtime and generated-consumer bindings remain mandatory separate gates.
Do not reuse old bundle receipts after changing source without proving their complete context and tool hashes equal.
The typed activation agent owns those bindings; this queue does not run its old isolated scripts.

## Actual execution coverage

The5255/198/97/46counts describe source/build/audit inventory. They do not count runtime executions.
`run-phase.py` names the actual commands. The required executions include:

- `scripts/lean-backend-filetests.sh`, `scripts/lean-backend-encode-check.sh`, and `scripts/arm-fault-cosim.sh`.
- `scripts/clif-filetests.sh`, `scripts/clif-unwind-native.sh`, `scripts/opt-difftest.sh`, and `scripts/float-spec.sh`.
- `lean-e2e-check` with and without `--no-dead-cleanup`, each with its own identity report.
- `scripts/stock-compiler-compare.py --jobs 2` using lean-backend for actual configured production requests.
- The same full comparison using `--lean-compiler .lake/build/bin/lean-stock-lowering-compare` for raw Stock.
- `examples/compare.sh` on fv-demo,survey,and deps with `--lean-link --verified --keep-temps`; bigframe-unwind retains its original plain mode.
- `scripts/stock-crate-parity.py --json OUT DIR...` over the actual retained codegen-unit directories from those executions.
- The original52mixed load/store matrices,26retained store matrices,17load matrices,and eight retained nonmemory routes.
- The unchanged captured-copy integration, with source hash9d39c7307e7fc9b4c3f334692726fae11926683d31f27ea49d032d46e99e70ce.
- All26nonmemory integration classes. Eighteen use registered native fixtures; the other eight retain their original interpreted mode.
- The configured-provider and pipeline tests. The original eight settings rejections require exact receipt equality and exit3.
- Actual three-CLI,linker,checker,and generated-proof execution for original mixed typed/integer bundles after the final mode adapter lands.

Filetest parity and crate parity are separate required metrics. Native example outcomes do not substitute for crate byte parity.
The crate-parity phase requires actual `--keep-temps` outputs. Bind their source/tool/allocator hashes before reuse.
The final activation agent must bind all new raw/cleanup/typed attempt and nonvacuity cases before full validation can complete.

`accepted-identity-references.json` retains the1633exact accepted filetest identities as full tuples.
It also binds1302original input hashes,4501stage identities,and4455function artifacts from the prior measured inventory.
The two original E2E reports each contain1159accepted identities and their complete stage maps.
Preserve every original successful stage. Capture fresh exact-head baselines for both compiler comparison modes.
The48captured exact axiom sets and historical full-set references live in `required-axiom-references.json`.
Collect every current-main root as well. Preserve all old variants and exact sets, including the25binary,28expanded869,and16runtime sets.
Generic correctness permits only propext,Classical.choice,and Quot.sound. Fixed native roots require their existing explicit annotations.

`known-not-runnable-and-rejections.json` records the cases that cannot count as successful compilation.
Eight early nonmemory classes have no registered native fixture mode. Run their original interpreted mode.
The eight original settings rejections must stay rejected with exit3 and produce no object or allocation file.
All eight preserved original source paths currently exist and have exact hashes.
The prior official inventory also reports nonbinary tests,foreign targets,and parser-warning skips. Report those categories; do not count them as matches.
Exit10records a complete comparison with gaps. It never establishes equivalence.

## Final compiler-mode extension

`typed-compiler-modes-packet-v1` is an active implementation packet. Its current draft hashes are not selected.
The generic10-root pass is historical progress. Actual attempt/nonvacuity and final CLI source changes remain active.
The coordinator supplies a final publication manifest and an approval receipt when that work finishes.
`bind-mode-extension.py` validates both files without building or materializing source.
The approval must state finalization,final CLI sources,passed actual attempt/nonvacuity,exact replacement hashes,and required receipt hashes.
The binder rejects a changed file or an unlisted replacement.

After binding, run `prepare.py --out NEXT_QUEUE_VERSION --extension-binding FINAL_BINDING`.
The preparation checks actual GitHub main against the local main reference before reconciliation.
It creates separate #513,activation,and combined trees with an isolated temporary index,then removes that index.
It preserves this queue version and copies the guarded runner into the next version.
The next combined preflight requires the final binding. No draft hash or green comparison check can satisfy it.
The coordinator still owns each PR's independent exact-head and tested/merged tree gates.

## Cleanup

Git created immutable candidate objects. The preparation script removed its temporary index and lock files.
No additional build outputs exist yet. Keep the queue,source hashes,patches,logs,and receipts.
Do not archive hardlinked build outputs. Remove future temporary generated outputs only after preserving unique source and diagnostics.
The coordinator retains cleanup ownership of the shared view and its single warm cache.
The delegate retains cleanup ownership of this queue's temporary files.
