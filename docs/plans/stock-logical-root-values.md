# Actual logical root and record value transfer

Part of #140, following merged #177; fresh-main branch
agent/stock-logical-root-values-pr.

1. Reuse actual root-to-helper execution and all-five-form value correctness.
   Transport held coverage with existing output-wrapper demand monotonicity,
   then derive exact output-vector and state from the actual wrapper execution.
2. Connect actual emitted records: derive selected root/width/typed receipts,
   mapped demand bounds and final alias size, result binding and emitted code.
3. Reuse generic fresh-record source-step/guarded-value transfer; use the original
   restricted source frame and demanded-and-available coverage without stronger
   baseline input conditions.
4. Inhabit complete logical root/record runs and audit normal/MCP theorem trust;
   run all repository gates before publication.

Steps1–3 now compile through Lean MCP in StockLogicalRootValues and
StockLogicalRecordValues. Record binding preserves demand and contributes no
physical copies for the actual singleton virtual result. Complete-run receipts
derive final alias size and mapped demand bounds. Original demanded-and-available
source transfer reuses actual allocation-interval exclusion and the helper's
fresh-register frame; no emitted-code or definition-bound premise is added.

Step4 is in progress in StockLogicalRecordWitness: complete real runs for all five
forms, actual source execution and held-value transfer. Existing fixtures have
been extracted unchanged into StockLogicalFixtures for reuse by both witnesses.
All five complete-record witnesses now pass Lean MCP and kernel checking,
including explicit transport of original source instructions/results through
the driver's changed instruction-selection metadata. The complete source-step witness also passes MCP using the original statement
frame, restricted DFG, demand/availability guard and actual source transition.
It uses existing availability lemmas rather than kernel evaluation of the
fixpoint. All new semantic/witness roots verified so far use only standard
axioms with clean source scans. All required gates pass: full1465/crates1171, runtime4672/0/0 with seven
unchanged not-runnable cases, encoder1292/0, E2E1150/0 with every identity/stage
field equal to #177. The 210-root audit preserves all197 prior axiom sets;
13 new/shared roots use standard axioms. Compact receipt:
docs/research/stock-logical-record-audit.json. Ready for one combined PR. Other instruction families/effects, whole simulation/completeness
and production cutover remain under #140.

Publication discipline: combine these root/record/source-transfer slices into
one PR. Validate locally before publication and minimize repeated pushes. Audit
receipts refer to the previous cumulative audit and record only new roots and
final compiler root hashes, rather than copying the whole inventory again.
