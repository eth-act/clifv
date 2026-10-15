# Stock ordinary-source root scope (#140)

The original source scope excludes372 of the517 generated term686 roots. Actual
Stock first-match selection of ordinary source instructions is proved to choose
one of the145 remaining closure roots. The kernel checks the counts over the
real generated list; closure membership is derived from actual source data and
the mapped source invariant, without a caller-supplied rule certificate.

`StockScopeRoots` transfers the existing `exclOk_program`/`fails_sound` argument
through the identity source view. No legacy exclusion/Cov/T6 interface changes.
`StockScopeRootsWitness` uses a real nonempty context, a concrete excluded floating
root and a complete emitted constant record. `StockScopePartition` provides exact
membership/counts and a real selected-source membership witness.

All10 new roots pass normal/MCP standard-only audits, all342 prior sets unchanged
(352 total),0 original-source warning patterns. Full1528/crates1171/runtime4672
with0fail/0disagree and7known non-runnable; encoder1292 identical/0different; both
E2E1150accepted/0rejected with full identity/stage parity. Receipt:
[stock-source-scope-audit.json](../research/stock-source-scope-audit.json).

The partition applies to ordinary source slots. Retained closure rules still need
execution/source-transfer proofs; terminator/branch contexts, deferred effects,
source/block/whole-driver simulation/completeness and actual production consumer
cutover remain. Do not interpret the partition counts as execution coverage.
Full #140 active/incomplete; production legacy; no push or merge.
