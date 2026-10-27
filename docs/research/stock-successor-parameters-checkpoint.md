# Actual jump arguments and successor parameter copies

Implementation `49bf11e9` closes argument demand/value and direct successor
parameter binding after #626. It does not activate production CFG lowering or
complete original #140.

`stock_branchArgs_selected_marks` derives the exact state after ordinary outgoing
collection as the source argument mark fold. `stock_branchArgs_selected_mapping`
retains the actual source register map from the same call. Duplicate operands
remain duplicate requests; a kernel-only real context/call witness checks the
zero-to-two demand transition.

`Control.stock_collect_jump_marks` and `stock_jump_core_outgoing_marks` connect
those facts through actual singleton-original collection and the same retained
core's input scan, including its actual branch emission. The actual terminal
record, whole-run demand extent and source mapping derive every argument's
demand after the body in `stock_jump_body_arguments_demanded`. Original dominance
derives source availability; `stock_jump_body_argument_values` then obtains all
outgoing argument values from the post-body guard. Neither a separate argument
value certificate nor an argument-demand input condition is introduced.

`stock_jump_body_direct_parameter_values` composes those values with actual
per-successor `result.edgeArgs` and the existing parallel-copy semantics. Original
SSA derives target parameter availability and separation. Every target parameter
holds the corresponding original source value after successful source binding.

The actual two-block witness starts from executable source entry, executes the
compiled body and jump, extracts successful source successor binding from the
return continuation, executes the real per-edge copies and establishes both
target parameters. It reuses the two previous finite facts
`QuietBlockWitness.checked` and `MaskBlockWitness.dominated`. No new finite fact
or code-shape assumption is used. All seven general roots are standard-only.

Validation on the implementation:

- Full normal FV/FVTest: 3,994/3,994, one remaining witness rebuilt.
- All 83 repository audits: 3,560 reports / 3,409 distinct roots; all 3,399 prior
  axiom sets exact. The three new witnesses inhabit the seven general roots.
- All 3,980 previous FV/FVTest Lean files byte-exact against main `f1ce87ea`.
- Bundled Lean MCP source/axiom checks pass without warnings. Terminal evidence:
  `/tmp/stock-cfg-successor-terminal-v1.json`.
- No compiler, scope, allocator, checker, encoding, linker or production consumer
  definitions change; runtime gate inputs are unchanged.

The next value-transfer obligation is inherited nonparameter values. The existing
post-body guard covers values demanded at that scan's compiler state. Completing
loop/backedge simulation requires carrying inherited available values even when
a successor's demand was established later in the reverse compiler traversal.
Use the existing available-value fresh-write frame and source SSA/availability
proofs to establish this dynamic invariant internally. Do not turn the missing
invariant into a certificate required of accepted programs, or claim that target
parameter binding alone establishes the entire successor guard.

Continue critical-edge nodes, conditional/table branches and loops, physical and
prepared production consumers, then every original memory/effect/call/exception,
whole-driver simulation/completeness and original-domain obligation. Latest
historical 887/4,543 symbol comparisons are unchanged; no new agreement gain or
completion percentage is claimed.
