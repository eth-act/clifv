# Stock bmask source checkpoint — 2026-10-24

This packet closes the bmask helper, selected source, retained-record binding
and guarded value-transfer dependencies of #140. Production activation and the
full register-agreement goal remain unfinished. The production class last
landed in #623; measured real-crate byte agreement remains 887/4,543 comparisons.

The execution checkpoint is `d9ae33d15f60c0a4919b686e35e55e51682bf0c9` on
`agent/stock-bmask-production-20261024`. The subsequent source packet is on the
same branch; #44 records its exact published head and remote evidence backup.
All older theorem variants, inputs and axiom sets remain unchanged.

- `StockPureHelperTransport` proves checked pure-helper projection, full
  scheduling-state preservation and replay. `StockBmaskProjection` kernel-checks
  the actual pure child closure; the outer input-sensitive paths are separate.
- `StockBmaskHelper/Wide/Narrow/Rhs` prove actual allocating CSETM, the masked
  and unmasked helper paths, and the guarded original RHS. Input/output widths
  are independent. Successful execution derives the demand guard and mapping.
- `StockBmaskMatch` derives the source opcode, actual selected rule and original
  operand type. `StockBmaskRecord` derives exact fresh results, result binding,
  emitted code and full bound state from the actual driver record.
- `StockBmaskSemantics` executes through final aliases, proves the original
  source value, and bounds every write to the actual fresh interval.
  `StockBmaskSourceValues` reuses existing guarded record transfer to establish
  the real original source post-frame and unchanged source memory.
- Real helper/RHS witnesses cover all sixteen original width pairs. Machine
  witnesses cover all sixteen pairs and arbitrary integer inputs, including an
  operand resolving above the fresh interval. A complete successful driver and
  source-step witness uses sparse IDs, an i64 parameter and an i8 result.

Validation: normal FV/FVTest 3,966/3,966; both bmask audit files 34/34 public
roots; one bundled MCP check per execution/source packet. All use standard
axioms: 33 roots have Std3, and `stock_bmask_defs` has exactly propext/Quot.sound.
No handwritten or native witness axiom was added. Failed development attempts
remain distinct from passes in the remote evidence archive.

Next: compose bmask and general nop with the existing arbitrary scalar/division
body, add the required CSETM consumer support, enable the default production
route, and run current activation/consumer/native/retention gates before opening
a substantive PR. Then continue CFG, memory/effects, calls/unwind, whole-driver
simulation/completeness, optimizer and all remaining original #140 consumers.
Successful-run refinement and legacy fallback do not establish completeness.
