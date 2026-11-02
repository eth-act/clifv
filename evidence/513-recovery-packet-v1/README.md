# PR #513 recovery candidate

The candidate merges without textual conflicts onto main56576d9e6dac8be24b1f094164cd8f72f78ebff6.
The candidate tree is41ba069904bb83c261abdb70ea405c66f5f228c8.
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
- 2141FV modules and78FVTest modules.
- 156affected audit files.
- 91crate-proof files and42documentation consumers.

`affected-modules.txt` contains the2219project module targets. The static inventory does not establish successful elaboration.

Use the following gates when a proof slot becomes available:

1. Compile LowerOutcomes, LowerValueRelations, LowerSim, PrepareSound, E2E.Statement, E2E.Main, and ABIReadOnlyRealize first.
2. Compare the eight moved declarations' current-main and candidate elaborated types and exact axiom sets.
3. Build the fresh affected normal keys with the current scheduler and shared cache. Use current module locks and the allocated resource cap.
4. Run the156affected audits. Compare every old root's exact axiom set against the current-main baseline.
5. Check affected public theorem types and definition values against current main. Preserve existing statement and axiom guarantees.
6. Build affected tool targets and crate-proof consumers. Run actual compiler, checker, both linkers, and generated-proof consumers.
7. Verify preserved accepted identities, settings, original input hashes, successful stages, and artifact equality.
8. Obtain one direct cheap peer review under the user's existing review alternative. Run exact-head CI and verify tested/merged tree equality.

Retain the original full-goal validation obligations. The independent broader validation owns its frozen view and must continue unchanged.
Reconcile again if main changes before publication. This packet provides no merge or correctness approval.
