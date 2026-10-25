# Actual original-block body and jump composition

This closes the machine body/jump dependency following #625. It does not enable
production CFG lowering or complete register agreement / #140.

`StockOriginalBlockOrigin.stock_lower_original_block_scan_assembly` retains one
actual original core together with its scan membership, prepared terminator,
canonical ABI parameter widths, assembly run and returned resolved machine block.
Consumers no longer need to identify cores chosen by independent existential
origin theorems. The old origin theorems remain unchanged.

`Control.stock_jump_core_seq` executes the actual singleton jump following a
successful machine body. `Control.stock_lower_jump_body_spec` derives that body
execution from original source semantics, the unchanged LowerScope and Dominated
conditions, and the existing scalar/division/bmask/nop family proofs. Its return
case retains the actual source terminator and remaining continuation fuel. Its
trap case either traps inside the actual machine core or completes the current
body and jump while retaining the later source trap continuation. Source callers
are unrestricted; the general theorem assumes neither an empty caller stack nor
a finite compiled-code shape certificate.

The executable returning witness starts from a real `enterFunc` and a successful
two-block source run. A guarded virtual-register seed is derived for the same
canonical core; the proof executes that core through its actual emitted jump.
This witness does not claim to execute the physical ABI prelude. The source/run
fixtures reuse only `QuietBlockWitness.checked` and `MaskBlockWitness.dominated`;
the general results use only propext, Classical.choice and Quot.sound.

Validation on implementation `22d1627f`:

- Targeted witness closure: 1,078/1,078 normal modules pass.
- Full normal FV/FVTest: 3,989/3,989 pass, one remaining witness module rebuilt.
- Five new roots pass the normal axiom audit and bundled Lean MCP source/axiom
  verification, without source warnings or new finite witness facts.
- All 3,975 FV/FVTest Lean sources already on main `70220733` are byte-exact.
- All 81 repository audit files pass (3,550 reports,
  3,399 distinct roots); all 3,389 previous axiom sets match exactly,
  including the earlier 626-root retained baseline. Terminal evidence:
  `/tmp/stock-cfg-jump-body-terminal-v1.json`.

No lowering, allocator, checker, encoding, linker, scope predicate or production
consumer definition changes. Runtime inputs and successful stages are therefore
unchanged. The historical 887/4,543 symbol comparisons are not a completion
percentage and no new agreement gain is claimed.

Next: derive the actual predecessor's demanded outgoing arguments and inherited
successor values, compose source DFG transfer and per-edge parallel copies into
the guarded successor relation, and handle critical edges/loops. Continue memory,
calls/exceptions, all original-domain correspondence, whole-driver simulation
and completeness, and actual downstream production integration. Production CFG
activation must retain the real per-successor edgeArgs metadata.
