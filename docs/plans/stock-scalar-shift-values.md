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
