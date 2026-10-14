# Scalar shifts and extension helpers (#140)

Active worktree: `/home/lee/clifv/.worktrees/driver-proof-resume`.
Resume from `test-binary-alignment-recovery.md`; the full driver goal remains active.

## Current work

The new `ScalarShift` modules derive all four actual extension-helper selections
(555–558), including first-match exclusions, pass-through and fresh extension.
`ExtValueOut` accounts for final-alias execution, original source extension,
fragment definition bounds and preservation outside the fresh interval. The
extension witness covers all helpers at i8/i16/i32/i64, with dirty upper bits.
These modules build locally. The foundation batch passed all recovery gates, and all 26 new public roots are standard-only;281 prior trust sets are unchanged. See the [fresh audit](../research/stock-scalar-shift-foundations-audit.json).

The three shift machine contracts cover immediate counts, register counts at
32/64 bits and masked register counts at 8/16 bits. The narrow fragment writes a
scratch register before reading its value input, so its local semantic contract
requires separation from that scratch. The original record-availability theorem
must derive this separation; it must not become a new accepted-input condition.

Forward RHS contracts, observed request/state receipts, all-operation execution witnesses and complete machine-contract witnesses now build and are freshly audited.
The masked RHS must reserve six environment slots: four matcher inputs and two
locals. Both locals start empty in the actual matcher environment. An interpreter
proof with only four slots is malformed. Witnesses must use the actual six-slot
environment, rather than assuming a caller shape or a pre-materialized count.

## Remaining family obligations

1. Finish and kernel-check all actual shift RHS executions and observed receipts.
2. Compose all four actual `do_shift` selections, including looked-through
   immediate definitions and original count values with a different source type.
3. Connect all six scalar source roots (LSL, LSR, ASR, each narrow/wide), deriving
   extension/pass-through selections and original typed operands internally.
4. Connect retained records and result binding; derive scratch/input separation
   from original restricted source availability and final-alias bounds.
5. Add complete record/source witnesses for every width, operation, count helper
   selection and extension case, including unmaterialized looked-through counts.
6. Run fresh standard-only public-root/kernel/transitive audits and every recovery
   gate. Keep all earlier root trust sets and both identity/stage baselines.

Helper witnesses are not record/source witnesses, and these foundations do not
close any additional full-driver root in the inventory. Production is unchanged.
After this family, continue uncovered arithmetic/logical rules, comparisons and
selects, effects/control, source/block/whole-driver simulation and completeness,
and compiler/checker/linker/generated-proof integration under the original scope.
No push or merge is authorized.

## Record/source implementation checkpoint

Seven further local core modules now build: ShiftMatch, ShiftValues,
ShiftRootReceipts, ShiftPrepValues, ShiftRootValues, ShiftRootMatch and
ShiftRecordValues. The actual do_shift value theorem covers all four selected
forms and derives original looked-through constants. The demanded-frame variant
is retained alongside count-restricted coverage. Preparation, six actual source
roots and actual retained-record binding compose. Original availability supplies
both input endpoint separations; no new accepted-input certificate is used.
The guarded post-source frame transfer is proved; its fresh MCP audit is
standard-only.

The complete24-case (three operations/four widths/two count forms) witness grid
is still kernel-checking. Its compiler was confirmed live at 2026-10-13T16:03:15.918621+00:00; use /tmp/driver-resume_shift-witness-inputs3-build.log and session26361/PID2295358
lifecycle evidence before restarting. The prepared DFG/dominance/source-step tail
is /tmp/driver-resume_shift-witness-tail.lean; append after the current compilation
is terminal. New core files and the partial witness are untracked and preserved.
Full family witnesses, prior-root parity and full gates are pending. Root inventory
remains at19 guarded bridges until this batch is fully validated; full #140 remains
active, production legacy. No push or merge.

### Witness kernel-check continuation

The original aggregate24-case observed proof reached4M heartbeats and is
terminal (log `/tmp/driver-resume_shift-witness-inputs3-build.log`). Its RF count
proof also needed the supported type instantiated before kernel deciding. Both
were corrected. Observation is now split into24 separate kernel lemmas, retaining
all widths/operations/count forms. Active build session26293/PID2466601 was
confirmed live; use `/tmp/driver-resume_shift-witness-split-build.log` and
authoritative process state before further action. Do not restart solely because
an observation times out. The independent diagnostic confirmed all24 expected
root IDs, demands, context keys and source alias endpoints; it introduces no
proof axiom and does not replace kernel proof.

All13 new core public roots passed normal and fresh MCP audits with only standard
axioms and no source warnings. See `stock-scalar-shift-core-checkpoint.json` in
research for current source hashes; this is a checkpoint, not full batch gates.
Once the current build is terminal, append the complete DFG/dominance/source-step
tail `/tmp/driver-resume_shift-witness-tail.lean` before the final namespace end
in StockShiftWitness, then build and fix its elaboration, complete witnesses,
all prior trust-set checks and full gates. Do not count inventory coverage before
that validation. No further commit, push or merge; #140 remains active.


### Witness wrapper timeout diagnosed (2026-10-13T22:20:00.723516+00:00)
The split witness build terminated after 877 seconds at StockShiftWitness.lean:84:6, with a 4,000,000-heartbeat whnf timeout in the aggregate wrapper's trial proof selection. The individual ground lemmas passed that stage; the wrapper tried unrelated concrete reports and triggered expensive definitional comparison. Replaced trial selection with direct case dispatch. No theorem statement, input condition or axiom set changed. Compilation of this correction and the complete source witness tail remain pending. Goal service reports blocked; the last live-process checkpoint is historical, and PID2466601 has exited. Production remains legacy; no full-goal completion claimed.


## Scalar-shift source witnesses and normal gates complete

Updated UTC: 2026-10-13T23:10:09.019988+00:00

The witness receipt/source proof split builds383jobs. Complete24-case actual retained-record/source witnesses cover all scalar widths, three operations and literal/register counts; literal counts stay unmaterialized. Full1515/crates1171/runtime4672 with0fail/0disagree and7unchanged known non-runnable; encoder1292 identical/0different; bothE2E1150accepted/0rejected, all full identities/stages match each other and the previous foundation batch. Normal323-root audit preserves all307 prior sets and gives16 new standard-only roots.

Final MCP witness checks/source scan are pending; source-copy MCP verification is re-elaborating expensive concrete receipts, and a compact imported-root audit is prepared. Do not call this completed batch merge-ready or update inventory until those checks finish. See docs/research/stock-scalar-shift-record-checkpoint.json. Full #140 remains active and incomplete; production legacy, no push/merge. The next extension draft at /tmp/driver-resume_cast-receipts.lean kernel-checks actual base zero/sign-extension matches, requests, emissions and all six widening semantics; selected-root draft checks locally. No complete extension record/source witnesses or full family coverage claimed.


## Scalar-shift family validated locally

Updated UTC: 2026-10-13T23:14:39.055969+00:00

All four actual count selections, six scalar shift roots, retained-record/result binding and original guarded source transfer are complete locally, with24 complete source/record witnesses including unmaterialized literal counts. Scratch/input separation is derived from original availability; the prior full-demand helper variant is retained. Nine new modules build. All16 new public roots pass MCP and normal standard-only audits; all307 previous sets are unchanged (323 total). Original sources have0 MCP source-warning patterns. The expensive computational witness receipts are separated from the source witness, and MCP audits import compiled declarations to avoid redundant source elaboration.

Full1515/crates1171/runtime4672 with0fail/0disagree and7unchanged known non-runnable; encoder1292 identical/0different; bothE2E1150accepted/0rejected with exact full identity/stage parity. Durable receipt: docs/research/stock-scalar-shift-record-audit.json. Source inventory now identifies25 guarded record bridges among517 generated source roots; this is not whole-driver coverage or a completion percentage.

Full #140 remains active and incomplete. Production remains legacy. Continue extension/reduction roots, remaining families/effects/control, source/block/whole-driver simulation and completeness, and actual compiler/checker/linker/generated-proof production integration. Require fresh complete stock comparison before cutover. No push or merge.
