# Division and mixed-body inherited carry

Implementation `e91b7103` extends the carry proof from #628 through all existing
signed/unsigned division and remainder source cases. Production CFG activation
and the original full #140 objective remain pending.

`Inherited.record_frame_carry` reuses the outside-interval register frame already
proved by selected-rule semantics. It combines original source entry-value
preservation with the saved available-alias noninterference proof. The CFG layer
therefore need not derive each division sequence's instruction semantics again.

`division_scan_carry_fall_refines` reuses the existing complete division source
execution and frame, retaining arbitrary original narrow operands and selected
forms. `division_scan_carry_trap_refines` retains the original zero-divisor and
signed-overflow behavior under the extended invariant. No carried value needs a
positive demand count at that compiler position.

`constant_division_body_carry_refines` composes complete original bodies of
constants, divisions and nop, including arbitrary ordering, multiple divisions,
unused results and the first source trap. Real selection, omission, result
binding and write preservation are derived internally. The syntactic family is
an internal proof-coverage boundary; it changes neither compiler acceptance nor
production guards. Existing theorem variants remain unchanged.

Three witnesses reuse the old complete unsigned-division compiler/source fixture:
executable entry with7/3 produces2 and retains defined entry7; entry with a zero
divisor traps; the complete body composition inhabits both paths. No new finite
check or native axiom is introduced. All four general roots and all three
witness roots use only standard axioms.

Validation on the implementation:

- Full normal FV/FVTest: 4,004/4,004, zero remaining rebuilds.
- All85 repository audits: 3,576 reports / 3,425 distinct roots; all3,418 prior
  axiom sets exact. All3,991 previous FV/FVTest Lean files byte-exact.
- Bundled Lean MCP source/axiom checks pass without warnings. Terminal evidence:
  `/tmp/stock-cfg-div-carry-terminal-v1.json`.
- Serialized6GiB workers/8GiB scheduler, no extra worktree or build cache.
- No compiler, scope, allocator, encoding, checker, linker or production consumer
  definition changes. Runtime inputs, old theorem interfaces and stages remain.

Next prioritize actual return-block/core composition and a substantive two-block
CFG production class using these proved constant/division prefixes, emitted
jumps, actual edge copies and carry. Compose actual ABI entry, return and
prepared/physical consumers; extend successive classes afterward. Do not require
every remaining family to be finished before any CFG activation, and do not stop
at the first class. Arbitrary scalar families, whole-edge order/demand coverage,
critical edges/loops, memory/effects/calls/exceptions, whole-driver simulation and
completeness, original-domain parity and all downstream consumers remain in
scope. No new byte-agreement gain is claimed; historical887/4,543 symbol
comparisons are unchanged.
