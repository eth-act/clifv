# Actual Stock multiplication values (#140)

Base: local/unpublished `a739ad525b0277f45717da92785d6ef7ccaaadea` in
`/home/lee/clifv/.worktrees/driver-proof-resume`.

## Current implementation

- `StockMulHelper`: kernel-checked pure helper scope, full scheduling-state
  preservation and actual four-register ALU/MADD/MSUB helper emission.
- `StockMulRhs/Semantics/Values`: actual guarded multiply requests, original
  typed root matching/selection, mapped final-alias execution and fresh writes.
- `StockMulRecordValues`: actual retained-record selection/binding/code and
  original demand/availability guarded source transfer.
- `StockMulWitness`: complete32/64 retained-record and source-step witnesses;
  normal capped build passes.
- `StockMulFusedRhs/Semantics/Match/Values`: all three actual multiply-add/subtract
  roots (`125`, `128`, `132`), successful request inversion, hidden multiplication
  source values via original restricted DFG, canonical environment, final-alias
  execution and fresh-only writes. Normal target builds pass.
- `StockMulFusedRecordValues`: actual retained records/binding and original
  guarded source transfer; normal build passes.
- `StockMulFusedWitness`: complete32/64 source/record witnesses with a product
  absent from machine registers. Build in progress; not yet validated.

Both guarded source-transfer public roots freshly pass Lean MCP with standard3
and no source warnings. All12 modules are local/untracked/uncommitted. No compiler,
legacy Cov/T6/IselLcf or optimizer changes. Live statuses and claim #140 reread;
#44 active, no concrete shared-interface conflict. No push or merge.

## Remaining batch checks

Finish the fusion witness build (`/tmp/driver-resume_mul-fused-witness-build.log`,
session60091), then all25 public-root MCP/kernel audits with all256 prior sets
unchanged; full FV/FVTest/tools, crates, runtime, encoder and both E2E modes with
exact identity/stage parity. Capture a compact incremental receipt and update #44.

## Full goal remains

Continue shifts, extensions, comparisons/selects and remaining families/effects,
then source/block/whole-driver simulation/completeness and actual production
consumer cutover, preserving original scope/theorem/accepted-input parity. This
batch does not satisfy #140. See [remaining obligations](stock-driver-remaining-families.md).

Updated UTC: 2026-10-13T12:08:16.964109+00:00

## Batch validated

All12 modules and both complete witness targets pass. All25 new public roots
pass fresh MCP and normal audits with only standard axioms; all256 prior sets and
final compiler sets unchanged. Full1496/crates1171/runtime4672/0fail/0disagree with
7known non-runnable; encoder1292identical/0different; bothE2E1150accepted/0rejected
and complete identity/stage parity with prior batch/#179 and between modes.

Evidence: [incremental audit](../research/stock-multiply-values-audit.json).
No runtime/compiler change, push or merge. This closes the four named
multiplication roots locally; original whole-driver obligations remain. Continue
scalar shifts with all four `do_shift` selections and original narrow-type
zero/sign extensions; avoid certifying only32/64 register shifts.

Updated UTC: 2026-10-13T12:15:35.676394+00:00
