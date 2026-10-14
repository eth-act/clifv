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
