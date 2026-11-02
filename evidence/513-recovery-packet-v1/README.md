# PR #513 recovery candidate

## Reviewed focused result

The focused gate passed on actual main77088aba2b9c528264aead43ab563d7ee17a102e.
The current-main candidate tree ise0dd63039d419577544c7b3f95be14c7364a874e.
All207candidate source hashes remain exact. All228baseline sources and seven target baselines match the prepared context.
The harness compiled all seven kernels. All eight elaborated types and exact axiom sets match current main.
`focused-current-main-state-v1.json` records the result. `attempts/kernel-v1` preserves the original diagnostics and output hashes.
No retry ran. The full affected normal, audit, tool, crate, and identity gates remain pending.

The delegate removed all isolated `.lake` outputs and snapshot hardlinks after recording hashes.
The frozen source view remains clean. The delegate released the3GiBproof slot.
`focused-cleanup-v1.json` records cleanup. No publication occurred.

## Prepared candidate context

The candidate merges without textual conflicts onto main34e39ec6b12abc4fb0dd509cc9cf56281f2c4c42.
The candidate tree isbd41bb462f03e0f13233b97a6768cb3381c63da4.
The original PR head remains5aae55c32030e3e9f15ab6515a2cccf268751646.

No branch, checkout, worktree, cache, publication, or running validation changed.
No Lean process or build ran. Git created only immutable tree/blob objects and packet files.
No temporary Git index exists.

## Exact preserved source

- `source/` contains all207 candidate files. `candidate.patch` applies against the recorded main commit.
- `recovery-receipt.json` records each candidate source hash.
- `current-header-parity.json` records372 exact current-main theorem headers across the affected source.
- `consumer-body-parity.json` records203 complete source bodies that differ only in import lines.
- `moved-declaration-parity.json` records eight declarations with byte-identical text in old main, current main, and candidate providers.
- The eight declarations retain their old names. LowerSim imports LowerValueRelations, which imports LowerOutcomes.
- No equivalent providers exist on the recorded main. PrepareSound still imports LowerSim there.
- Parithosh's #769 explicitly excluded204files from#513. It did not supersede this packet.

The lexical header reader does not replace kernel type or axiom checks.

## Recovered historical evidence

`historical/` retains original scripts, partial receipts, diagnostics, and interface logs from backup385dc1fc.
The six outcome/interface roots used only propext, Quot.sound, or no axioms.
The two frame-value roots used propext and Quot.sound.
Their old and new elaborated type/axiom outputs match exactly.
The final historical normal receipt returned143. Historical full validation remains incomplete.

The recovered scripts contain old paths and old source heads. Do not execute them unchanged.
The historical controller/drain scripts are evidence only. They must not control current healthy jobs.
The old axiom-parity script references historical audit directories. Recover those baselines or collect a current-main baseline before using its comparison logic.

## Required gate inventory

`affected-gates.json` records the fresh static reverse closure. It contains:

- 206 changed project modules and one new audit file.
- 2147FV modules and78FVTest modules.
- 157affected audit files.
- 91crate-proof files and42documentation consumers.

`affected-modules.txt` contains the2225project module targets. The static inventory does not establish successful elaboration.

Use the following gates when a proof slot becomes available:

1. Compile LowerOutcomes, LowerValueRelations, LowerSim, PrepareSound, E2E.Statement, E2E.Main, and ABIReadOnlyRealize first.
2. Compare the eight moved declarations' current-main and candidate elaborated types and exact axiom sets.
3. Build the fresh affected normal keys with the current scheduler and shared cache. Use current module locks and the allocated resource cap.
4. Run the157affected audits. Compare every old root's exact axiom set against the current-main baseline.
5. Check affected public theorem types and definition values against current main. Preserve existing statement and axiom guarantees.
6. Build affected tool targets and crate-proof consumers. Run actual compiler, checker, both linkers, and generated-proof consumers.
7. Verify preserved accepted identities, settings, original input hashes, successful stages, and artifact equality.
8. Obtain one direct cheap peer review under the user's existing review alternative. Run exact-head CI and verify tested/merged tree equality.

Retain the original full-goal validation obligations. The independent broader validation owns its frozen view and must continue unchanged.
Reconcile again if main changes before publication. This packet provides no merge or correctness approval.

## Focused harness record

`focused-package-v1` owns an isolated source package. It is not a Git worktree or warm cache.
It retains the207candidate source files and the focused dependency source.
The baseline closure contains228modules. Every baseline source blob equals both current main and frozena4.
The candidate closure contains230modules. Only the seven focused targets need source overlays and new outputs.
`focused-context-v1.json` records every dependency blob separately for each target.

`focused-ownership-v1.json` records902hardlinked import outputs and their hashes.
The harness treats every import snapshot as read-only. It unlinks each owned output before Lean writes it.
All snapshot outputs live under the package's `.lake` directory. Exclude that directory from remote backups.
The ownership manifest identifies worker-O, its delegate, its purpose, and required cleanup.

The parent granted the existing3GiB proof slot for the completed gate. The delegate then released it.
The following command records the original invocation. Its snapshot outputs were removed after completion.
Prepare a new version before a new execution. Never overwrite the completed attempt.

```
WORKER_O_PROOF_SLOT_GRANTED=513 python3 /home/lee/clifv/.git/agent-evidence/stock-memory-20261029/513-recovery-packet-v1/run-focused.py --attempt kernel-v1
```

Run it through `ai-coord watch` under worker-O's existing job discipline.
The harness compiles seven modules and compares eight elaborated types and exact axiom outputs.
It stores fresh diagnostics under `attempts/kernel-v1`. A new attempt needs a new label.
It cannot write frozen outputs. Its exclusive lock prevents another harness from writing owned outputs concurrently.
After preserving diagnostics and hashes, remove `focused-package-v1/.lake` to release all snapshot hardlinks and owned outputs.
Preserve source, manifests, scripts, and receipts.
