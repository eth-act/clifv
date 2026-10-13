# Recovery and continuation plan: test-binary-alignment

Checkpoint: 2026-10-13. Task: [#140](https://github.com/eth-act/clifv/issues/140).
The full objective remains **unfinished**: prove the preserved Stock lowering
driver and switch production while retaining accepted-input and theorem parity.
This file is the resume entry point; the smaller family plans are supporting records.

## Resume location and preservation

- Work in `/home/lee/clifv/.worktrees/driver-proof-resume`, branch
  `agent/stock-logic-not-values-pr`, HEAD `cc29aaa494ddea10a8e38b5dd5fad707dcee47b6`.
  GitHub main was independently checked at the same commit during recovery.
- `/home/lee/clifv` is the historical `test-push` checkout at `f866008`, with dirty
  October 5 diagnostic evidence. Its `main` branch and proof roadmap are stale.
  Do not reset it or copy its old compiler sources over the active worktree.
- Seven local `StockLogicalNot*.lean` files and the local family plan are
  untracked, uncommitted and unpublished. They are real saved work, not landed work.
- All 38 dirty primary-checkout files and all eight dirty active-worktree files
  were copied and SHA256 verified in
  `/home/lee/.clifv-recovery/20261013T110839Z/manifest.json`. Binary diffs accompany
  the snapshots. This backup precedes the recovery documentation additions.
  Restore individual files only after comparing the manifest and current contents.
- The interrupted session remains at
  `/home/lee/.codex/sessions/2026/10/05/rollout-2026-10-05T23-54-09-01a10f58-ef03-7df3-9d8c-c8c0e16be9be.jsonl`.
  Its last substantive updates confirm the mirrored-root/source connection; the
  final user request asks for a plan file. The disconnect does not identify a
  compiler failure or explain the account's credit display.

## Progress and evidence

| Work | State | Evidence / limitation |
| --- | --- | --- |
| Legacy dead-instruction cleanup #137 | Landed | Historical receipt/status reports default exact matches 465 → 671; original driver retained. |
| Register alignment wrapper #139 | Landed, opt-in | Status reports 671 → 959 (+288, no losses) with focused gates; wrapper alone does not complete #140 or change the production baseline below. |
| Stock alias/domain/termination, availability and fresh-write groundwork | Landed proof slices | Existing Stock modules and plans; these are prerequisites, not whole-driver correctness. |
| Logical helper/root/record/source proofs #177–178 | Landed | Commits `de405b6`, `cd324c7`; reused by current work. |
| Scalar NOT and fused LSL/NOT #179 | Landed and validated | `cc29aaa`; GitHub confirms merged PR, all three CI checks successful. |
| Current fused binary logical-NOT batch | Local, partially validated | Seven modules build together; all 17 public theorem roots freshly checked with only `propext`, `Classical.choice`, `Quot.sound`. Full batch gates and complete witnesses remain. |
| Production Stock-driver cutover | Pending | No whole-driver simulation/completeness or actual production switch demonstrated. |

The committed [#179 audit](../research/stock-bnot-values-audit.json) records full
build 1471 jobs, crate proofs 1171 jobs, runtime 4672 passes/0 failures/0 errors/0
disagreements with seven unchanged not-runnable cases, encoder 1292 identical/0
different, and E2E 1150 accepted/0 rejected with identity/stage parity against
#178. Its nine source hashes, six gate-log hashes and identity-report hash were
independently checked during recovery. These results cover the landed batch;
they are not full gates for the seven current local modules.

The [#179 CI comparison](https://github.com/eth-act/clifv/pull/179) reports
671 exact function outputs, 939 different, 432 setting rejections and 2413
unsupported-operation rejections from 4455 outputs. All 1302 official files
were inventoried; 151/484 AArch64 files had outputs compared. The change was
+0/−0 exact outputs. Full metadata agreement remains unestablished, and the
comparison job did not execute compiled functions. Proof progress has not yet
increased default byte agreement.

## Current local module map

All paths below are under `FV/Backend/Proof/` in the active worktree.

| File | What exists now |
| --- | --- |
| `StockLogicalNotReceipts.lean` | Five thin RHS/match contracts reuse landed identical helper expressions. |
| `StockLogicalNotSemantics.lean` | Register, immediate and LSL NOT machine values through final aliases, with fresh-write preservation. |
| `StockLogicalNotValues.lean` | Actual successful term-566 helper value composition, with demanded-value guards. |
| `StockLogicalNotWitness.lean` | All nine operation/helper-form executions; fused source values need not be materialized in machine registers. These are helper witnesses. |
| `StockLogicalNotLookthrough.lean` | Actual nested NOT pattern yields original source definition and complement value. |
| `StockLogicalNotRootValues.lean` | Typed RHS/output wrapper composition for the six mirrored binary roots. |
| `StockLogicalNotMatch.lean` | Successful matching derives canonical environment and hidden NOT source; `stock_not_selected_root_values` proves original binary values for all six mirrored roots. |

Fresh recovery verification: memory-capped normal build of `StockLogicalNotMatch`
and `StockLogicalNotWitness` completed successfully (368 jobs), covering all
seven modules. A normal Lean `#print axioms` audit checked all 17 public roots.
No full repository gates or new Lean MCP checks were run during recovery.
See [recovery receipt](../research/test-binary-alignment-recovery.json) for
source/log hashes. Existing family-plan claims of earlier MCP checks remain
historical evidence, separate from this fresh verification.

## Next bounded batch

1. **Start from the compiled selected-root theorem.** Read `StockLogicalNotMatch`
   and the landed `StockLogicalRecordValues` / `StockBnotRecordValues` templates.
   Do not redo the canonical-match or term-566 helper proofs.
2. **Finish the seventh fusion, `bnot(bxor)`.** Identify its actual selected rule,
   match/RHS execution and original-source value. It is not included in the six
   mirrored `notRule` cases. Reuse existing scalar NOT and XOR helper semantics.
3. **Connect actual retained records and result binding.** Reuse existing
   whole-run record origins, final resolver and allocation bounds; derive
   selection and binding internally. Preserve the original restricted-frame
   DFG, demand/availability guards and source scope. Do not introduce a caller
   match certificate or silently treat demanded later definitions as available.
4. **Compose guarded original-source transfer.** Establish value preservation
   through final aliases and fresh writes. Follow the landed record/source proof
   structure; do not infer execution value equality from alias provenance alone.
5. **Supply complete non-vacuity witnesses.** Cover the six mirrored roots and
   seventh fusion at 32/64 bits, actual retained records and source steps,
   nonempty binding, and fused constants/shifts absent from machine registers.
   Existing helper witnesses alone do not discharge these obligations.
6. **Validate one reviewable batch.** Check every new public root with Lean MCP
   and normal kernel/transitive axiom audits, preserving all 226 prior audited
   roots and final compiler axiom sets. Run full gates below and capture a compact
   incremental receipt. Update the family plan and #44 with exact evidence.

## Gates and shell setup

The recovery shell initially lacked `lake` on PATH; supplying the pinned
toolchain fixed the invocation. Use the active worktree and memory cap:

```sh
cd /home/lee/clifv/.worktrees/driver-proof-resume
export PATH=/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:/home/lee/.cargo/bin:$PATH
export LEAN_NUM_THREADS=2 FV_MEMCAP=22G
scripts/memcap.sh lake build FV.Backend.Proof.StockLogicalNotMatch FV.Backend.Proof.StockLogicalNotWitness
```

Before calling the completed batch merge-ready, run `lake build FV FVTest
lean-backend lean-e2e-check link-check`, crate-proofs `lake build`, all relevant
public-root/E2E axiom audits, `scripts/lean-backend-filetests.sh`,
`scripts/lean-backend-encode-check.sh`, and both relevant E2E modes with full
identity/stage parity. Wrap every lake/cargo invocation in `scripts/memcap.sh`.
Preserve at least the actual #179 baseline above, not just older roadmap minima.
If CLIF semantics change, add CLIF filetests and optimizer differential gates.
Require a fresh complete stock comparison before behavior/default changes.
The landed audit and `/tmp/stock-bnot-gates.sh` document existing tool paths;
capture fresh logs rather than overwriting historical receipts.

## Remaining full-goal obligations

After this batch, inventory the uncovered selected rule families and effectful
cases. Prove execution semantics for memory, calls, traps, control flow and
omitted/sunk instructions with a sound deferred-effect invariant. Compose
source/block/whole-driver simulation and completeness under the original input
conditions, then integrate the actual driver into compiler, checker, linker and
generated-proof consumers. Preserve old theorem variants, accepted identities
and successful stages; validate runtime, encoder and complete stock comparison.
Only this completed production cutover can satisfy #140. Do not estimate a
completion percentage from the number of proof slices or merged PRs.

## Coordination and stopping rules

Read current #44/#52/#71 and #140 before further implementation; stale entries
are uncertain. #140 remains the existing claim. Kev owns #42/T6; this recovery
changes no IselLcf/Cov/optimizer interface or fixed-proof migration. Flag concrete
overlaps and pause only the conflicting portion. Preserve archived driver WIP
and historical dirty reports; reuse their implementation when relevant.

Primary-checkout AGENTS/worktree rules supplied by the user take precedence over
the active checkout's stale `/home/kev/work/clifv-wt` instruction. New linked
worktrees belong under `/home/lee/clifv/.worktrees` and use the primary helper.
Repository §7 prohibits agent push, merge, rebase, stash and pattern-kill actions;
this recovery authorizes none. Any later user-authorized merge must be squash.
No commit, push, merge, process termination or compiler-source edit was performed
for recovery. Update #44 after a commit, scope change or stop.

At each stop, record HEAD, exact dirty paths/hashes, successful and outstanding
checks, next theorem and local-only/publication state in this plan or its receipt.
After another disconnect, read this file and compare the saved receipt with
current sources before continuing. Keep #140 incomplete while any full-goal
obligation remains.

## Active continuation checkpoint

Updated UTC: 2026-10-13T11:34:51.875968+00:00

- User resumed the full #140 goal; live #44/#52/#71 and #140 read, #44 updated active. No concrete shared-interface conflict; T6 boundary retained.
- Added `StockLogicalNotXor.lean`: actual rule1406 match derives hidden XOR source operands, canonical typed environment, unchanged scheduling state and original NOT-of-XOR execution value. Normal target build380jobs passes; selected root MCP audit standard3/no source warnings.
- Added `StockLogicalNotRecord.lean` and `StockLogicalNotXorRecord.lean`: actual retained-record selection/binding/code and guarded demand/availability value transfer. Both normal target builds pass; both guarded public roots pass MCP standard3/no source warnings.
- Added `StockLogicalNotXorWitness.lean`: complete actual register-form record/source witnesses at32/64; normal target build passes.
- `StockLogicalNotRecordWitness.lean` (six mirrored roots32/64) and `StockLogicalNotXorFusedWitness.lean` (unmaterialized constant/shift32/64) are under normal kernel build; do not count them complete until fresh success.
- Current processes/logs: witness build session67553 `/tmp/driver-resume_witness2-build.log`; fused witness session32248 `/tmp/driver-resume_fused-witness-build.log`. Prior XOR failures were corrected; preserve earlier logs as development evidence.
- Full batch gates, all-root MCP/kernel/transitive audit, compact receipt and complete identity/stage parity remain. All new files local/untracked/uncommitted/unpublished. HEAD remainscc29aaa; no push/merge, no runtime/compiler changes.
- Then inventory remaining rule families/effects and continue source/block/whole-driver simulation/completeness and production consumers. Goal remains active and incomplete.

## Fused-NOT batch validated

The next bounded batch above is complete locally: seventh NOT-of-XOR; all seven
retained-record/binding/source transfers; complete32/64 witnesses, including
unmaterialized constants/shifts; all full gates and public-root audits. Evidence:
[stock-logical-not-values-audit.json](../research/stock-logical-not-values-audit.json).
Full1484/crates1171/runtime4672/0fail/0disagree/7known non-runnable; encoder1292/0;
bothE2E1150/0 and exact #179/between-mode identity-stage parity. All256 normal
roots checked:226 prior trust sets unchanged,30 new roots standard-only; all30
fresh MCP roots pass. Thirteen fused-NOT modules saved; no production behavior
changed. Witness build sessions67553/21708 and full gates70706 completed.

Next: [remaining-family plan](stock-driver-remaining-families.md), backed by the
[517-root source inventory](../research/stock-driver-rule-inventory.json).
Fifteen identified guarded record bridges are evidence of local semantics, not
whole-driver completion. Classify the other roots against original LowerScope,
then prove selected execution, effects/control/omission/sinking and compose
whole-driver simulation/completeness before production consumers/cutover.
The full goal remains active and incomplete. No push or merge.

## Multiplication continuation checkpoint

Updated UTC: 2026-10-13T12:08:16.964109+00:00

The prior goal turn made verified progress: local commit a739ad5 and all256
root audits/full gates pass; goal remains active. Current base is a739ad5.
New work: actual base multiply plus three multiply-add/subtract roots, retained
records/binding and original guarded source transfer. Normal targets pass;
base32/64 full witnesses pass; fused32/64 unmaterialized-product witnesses
building in session60091. Both guarded roots MCP standard3/no warnings.
All12 modules are local/untracked/uncommitted. No runtime/compiler changes.
Resume from [stock-multiply-values.md](stock-multiply-values.md), finish witnesses,
all25 new/all256 prior audits and full gates, then continue original full goal.
No push or merge; primary/archived work preserved.

## Multiplication batch validated

Updated UTC: 2026-10-13T12:15:35.676394+00:00

Base multiply and allthree MADD/MSUB fused roots now have actual request/state,
match/source/selection, machine/final-alias, retained-record/binding and guarded
source-transfer proofs, with complete32/64 full witnesses and unmaterialized
product. All12 modules pass;25 new MCP/normal standard-only roots; all256 prior
trust sets and final compiler sets unchanged. Full1496/crates1171/runtime4672/0fail/
0disagree/7known non-runnable; encoder1292/0; bothE2E1150/0 with exact prior/#179
and between-mode identity-stage parity. Evidence:
[stock-multiply-values-audit.json](../research/stock-multiply-values-audit.json).
Witness session21610 and gates77649 completed; no compiler/runtime change.

Next: scalar shifts (all four do_shift selections and original narrow-type
extensions), then remaining families/effects and full source/block/driver
simulation/completeness/cutover. Inventory identifies19 guarded record bridges
among517 generated lower roots; this is not whole-driver coverage. Goal active
and incomplete. No push or merge; preserve current local proof stack.
