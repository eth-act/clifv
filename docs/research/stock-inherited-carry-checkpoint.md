# Inherited values through actual bodies and jumps

Implementation `4c955f39` closes the first complete inherited-value carry
dependency after #627. Production CFG activation and full #140 remain pending.

`Inherited.source_entry_carry` and `source_steps_entry_carry` derive preservation
of original block-entry source values through actual source steps. Entry
availability excludes definitions in the current body. `record_fresh_carry`
combines that result with the saved `stock_lower_available_fresh_frame`, including
alias endpoints above or below the current record's allocation interval. Carried
values do not need a positive demand count at this compiler scan position.

`constant_record_fresh_defs` derives resolved write bounds from actual selected
constant matching, RHS execution, output binding and retained code. It assumes
no code-shape certificate or caller execution callback. The old selection,
CodeShape, alias and scan proofs are reused; no old proof source changes.

`constant_body_carry_fall_refines` composes actual constant/omitted/nop records
through an arbitrary original block. `constant_jump_carry_returns` composes its
complete emitted jump and retains the original source continuation, fuel,
callers and source register preservation. This syntax condition marks current
proof coverage; it does not change accepted inputs or production guards.

The real fixture has entry value0 holding7, emits constant9 into value1, then
jumps with value1 as the sole argument. Its next block has parameter2 and adds
inherited value0 to parameter2, returning16. The witness starts with executable
source entry and derives machine carry through the actual first core. The
successor witness then uses actual source binding, real per-edge copies and the
saved source DFG transfer to establish the next actual scan's complete
GuardedScanRel, including inherited values and the memory relation. Target
availability cases come from the existing fixed-point theorem and source syntax,
not a finite code-shape check. The virtual-register seed witness does not claim
physical ABI prelude execution.

Six general roots use only standard axioms. Three non-vacuity roots share one
labelled native fact for the fixed fixture's original-input dominance. Compiler
success and scope are checked in the kernel; there is no new native emitted-code
fact. Earlier kernel attempts at the opaque availability computation and bounded
fixture build failures remain separate failed evidence, never claimed as passes.

Validation on the implementation:

- Full normal FV/FVTest: 4,000/4,000, zero remaining rebuilds.
- All 84 repository audits: 3,569 reports / 3,418 distinct roots; all 3,409 old
  axiom sets exact. All 3,985 existing FV/FVTest Lean files byte-exact.
- Bundled Lean MCP source/axiom checks pass without warnings. Terminal evidence:
  `/tmp/stock-cfg-inherited-terminal-v1.json`.
- Final fixture kernel compilation passes in25s, cgroup peak7.7GiB under its
  serialized8GiB cap. Other new proof modules use one6GiB worker.
- No compiler, scope, allocator, encoding, linker, checker or production consumer
  definition changes; runtime inputs and successful stages remain unchanged.

Next reuse this carry relation with the existing scalar/division record write
bounds and frame results. Derive the remaining whole-edge demand/order coverage
internally, including new body definitions and backedges; extend critical-edge
nodes, conditional/table branches and loops. Compose actual ABI entry, source
returns and complete prepared/physical consumers to activate a substantive CFG
production class, then continue all original effects/calls/exceptions,
whole-driver simulation/completeness and original-domain obligations. Do not
substitute a caller certificate for a missing invariant or stop at this class.
Historical 887/4,543 symbol comparisons are unchanged; no new agreement gain is
claimed.
