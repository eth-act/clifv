# Remaining Stock-driver semantic obligations (#140)

Worktree: `/home/lee/clifv/.worktrees/driver-proof-resume`; recover from
[test-binary-alignment-recovery.md](test-binary-alignment-recovery.md).

The machine-readable [root inventory](../research/stock-driver-rule-inventory.json)
lists all 517 generated term686 `lower` rules with source locations and hashes.
It identifies 28 roots with guarded actual Stock record-value bridges: constants,
base add/subtract, three logical roots, scalar/shift NOT, six mirrored logical-NOT
roots and NOT-of-XOR, plus base multiplication, three multiply-add/subtract fusions, all six scalar shift roots base zero/sign extension and reduction. This is a source inventory, not a reachable-rule inventory,
a correctness proof or a completion percentage. Helper selection subcases have
separate obligations. Source/context/record guards still need internal composition.

## Next semantic batch

- Classify remaining roots against the original `LowerScope`, keeping the scope
  unchanged. Derive impossible matches from actual mapped contexts; otherwise
  prove the actual Stock request/state/emission semantics.
- Continue remaining extension/look-through,
  comparisons/selects and arithmetic/logical families.
  Reuse legacy machine lemmas and actual Stock selection/request receipts.
- Each batch must connect retained records, binding and original availability-
  restricted source transfer, with complete non-vacuity witnesses and fresh
  standard-only audits. Do not count a helper value theorem as driver completion.

## Effectful and control cases

- Prove memory loads/stores, atomics, stack/global/symbol addressing and call/try-
  call execution with the required world and memory relations.
- Prove branches, successor arguments, critical-edge moves, returns and traps;
  reservation terminality alone does not establish reserved-register values.
- Supply a deferred-effect invariant for omitted/sunk instructions and trapping
  paths. `StockScanSemantics` composes successful fall-through under local
  obligations; it does not discharge those obligations or trapping simulation.

## Driver and consumers

- Derive the local obligations under the original input conditions; compose
  source, block, node and whole-driver simulation and completeness.
- Preserve old theorem variants and integrate the actual Stock driver into
  compiler, checker, linker and generated-proof consumers.
- Before production/default changes, run the full recovery-plan gates and a
  fresh complete stock comparison, preserving accepted identities, successful
  stages and theorem trust sets. Only the completed production cutover satisfies
  #140. No push or merge is authorized.


## Generated family classification

[stock-driver-rule-families.json](../research/stock-driver-rule-families.json)
classifies every one of the517 generated term686 patterns by its first opcode,
all nested opcode terms, literal type constraints and instruction-data forms.
The source term files are hashed. This is static pattern evidence; none of its
entries is a scope-reachability or exclusion proof.

Next kernel obligations are scope-derived exclusion of unsupported opcodes and
non-scalar type literals, and actual execution/source transfer for the remaining
accepted integer arithmetic, rotations/counts/reversals, comparisons/selects,
loads/stores/atomics, addressing, calls/returns/traps. Branch roots and traversal
obligations are additional to this term686 inventory. Preserve the original
Compile.instE/LowerScope and derive exclusions from mapped source data.


## Ordinary-source root exclusions validated locally

Updated UTC: 2026-10-14T00:25:34.544757+00:00

Original mapped source scope proves372 of517 generated lower roots cannot match ordinary source instructions. Actual first-match and retained-record selection derives membership in the145 remaining closure roots internally. Exact partition counts are kernel-checked; concrete excluded-root and complete emitted-source witnesses pass. This is scope exclusion, not execution coverage; terminator/branch contexts remain separate.

All10 new roots normal/MCP standard-only;342 prior sets unchanged (352 total),0 source warnings. Full1528/crates1171/runtime4672 with0fail/0disagree and7known non-runnable; encoder1292/0; bothE2E1150/0 with full identity/stage parity. Receipt docs/research/stock-source-scope-audit.json; plan docs/plans/stock-source-scope.md. Inventory/family classification now links proof-backed ordinary-source exclusions. No legacy Cov/T6/IselLcf/optimizer interface or production changes. Next remaining closure execution/source transfer, effects/control/deferred semantics, full simulation/completeness and actual production integration/complete stock comparison. Full #140 active/incomplete; no push/merge.
