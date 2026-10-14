# Scalar Stock add/subtract: original selection, retained records and source transfer

Parent task: #140. Worktree: `/home/lee/clifv/.worktrees/driver-proof-resume`.
Parent validated local commit: `3ae4c79` (population count). No push or merge.

## Scope and preserved conditions

Cover every actual scalar Iadd/Isub candidate under the original LowerScope,
Dominated and availability-restricted DFG/value conditions. Preserve earlier
base and multiply-fusion variants, all509 prior audited roots and the exact
seven compiler trust sets. The all-rule source contract derives the original
operand getters and actual dispatch internally; no chosen rule, final rule ID
or separate match certificate is an extra caller premise.

| Form | Add roots | Subtract root |
| --- | --- | --- |
| Base (existing) | 588 | 745 |
| Positive immediate | 589,590 | 746 |
| Negative immediate | 591,592 | 747 |
| Extended register | 593,594 | 748 |
| Shifted register | 595,596 | 749 |
| Multiply fusion (existing) | 597,598 | 599 |

## Proof connection

StockAddSubPure and NegativePure establish closed base-only helper projections;
demand-changing terms381/434/439 are handled by actual Stock execution.
Semantics covers immediate, LSL and extended operands through final aliases
with dirty upper bits and fresh-only writes. Rhs/Selected/Observed derive the
actual successful requests, demand guards, output and complete scheduling state.
Match/ImmediateMatch/NegativeMatch and value modules recover original source
values and canonical environments from actual matches in the mapped context.
UnifiedValues/RecordValues establish retained result binding/code/allocation
and original guarded availability transfer. AllValues/AllSourceValues compose
all17 candidates, original source steps, unchanged memory and guarded post-frames.

## Complete witnesses and non-vacuity

Immediate/Negative/Shift:12 cases each across all four scalar widths.
Extension:36 cases, three roots × two signs × six legal target/source width
pairs16/8,32/8,32/16,64/8,64/16,64/32. ShiftEdge:12 cases, width-equal wrapped
counts at8/16/32 and zero at64. All carry actual Stock.lower/records/source
steps, nonempty result binding, dirty upper bits and unmaterialized fused values.
AuxWitness separately inhabits pure-term projection with nonzero demand/sunk
fields. Existing base/multiply complete witnesses remain preserved.

Original i8 priorities are retained: add of-5 uses the higher-priority positive
immediate root; subtract of255 uses the negative root. Positive fixtures use127.
The60-public-root premise/chain matrix is in
`docs/research/stock-addsub-witness-checklist.json`.

## Gates and current evidence

All84 complete witnesses and the auxiliary projection now pass ordinary kernel
builds. All60 public roots pass matching fresh normal/MCP audits and24 source
scans are clean. Full569-root audit preserves509 prior sets/exact seven compiler
trust sets. Full1629/crates1171/runtime4672/0 runnable failures/encoder1292/0
differences/bothE2E1150/0 and every identity-stage field match population count.
Final receipt: `docs/research/stock-addsub-audit.json`. The full goal remains
incomplete; production remains legacy.
Require fresh normal/MCP/source audits for60 new roots,509 prior/exact-seven
trust parity, full FV/crate builds, runtime4672/0 runnable failures, encoder
1292/0 differences, both E2E modes1150/0 rejections and exact identity/stage
parity with population count. Capture logs/source hashes and preservation archive
before a local commit. Production remains legacy.

## Remaining full goal

After validated local delivery, continue uncovered rule families/effects/control
and deferred invariants, source/block/whole-driver simulation and completeness,
then actual compiler/checker/linker/generated-proof-consumer integration and a
fresh complete Stock comparison. Preserve original inputs, old variants,
identities, successful stages and trust sets. This family does not complete #140.
