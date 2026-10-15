# Stock scalar high multiplication

Full #140 remains active. This family does not establish whole-driver simulation,
completeness or production integration. Production still uses the legacy driver.
Parent: local/unpublished `22894a14dd632b85d5900efc9d93d6094ceec0b5`.

The actual signed roots are777/778 (`rule_lower_1056/1059`); unsigned roots779/780
(`rule_lower_1068/1071`). Original accepted widths8/16/32 use two real guarded
sext64/zext64 requests,64-bit multiplication and arithmetic/logical shift. Width64
uses the actual SMulH/UMulH instruction. Original source selection derives all four
roots internally. The original typed frame/getters exclude narrow helper64-bit
pass-through; successful calls supply mappings and guards.

Narrow execution has a technical second-source non-capture condition. The actual
retained record allocates exactly four temporaries; original availability and the
existing whole-run record interval invariant discharge this condition internally.
The final record/source theorems add no such caller premise. Wide and narrow actual
records derive output binding/code/execution and preserve the demanded-and-
available post-frame. Unified original source transfer derives operand getters and
rule selection, preserves source memory, and uses the actual final alias resolver.

The complete witness matrix is signed/unsigned ×8/16/32/64. Original source IDs are
7/31, result100, machine source registers192/193; source values are-7 and5. Both
machine operands have deliberately dirty bits above the source width. Each chain
must establish actual Stock.lower success, original LowerScope/Dominated, emitted
record/rule/result, original source getters, output allocation interval, execution,
original high-product value, interval preservation, actual source step and guarded
post-frame. Kernel run checks are isolated in StockHighMulWitnessRuns so later
proof edits reuse the compiled checks.

Validation complete locally: eight complete witnesses and all34 public-root
premise/non-vacuity reviews; fresh normal/MCP audits and17 clean original-source
scans;569 prior root sets and exact seven compiler trust sets unchanged in603-root
audit; full1646/crates1171/runtime4672/0fail/0disagree/seven unchanged known non-
runnable/byte-identical report/encoder1292identical0different/both E2E1150accepted
0rejected. All1150 function identity/stage fields match both modes and the add/sub
baseline. Receipt: [stock-highmul-audit.json](../research/stock-highmul-audit.json).
A fresh complete Stock comparison remains required for the later production cutover.
All other original full-goal obligations remain; no push or merge.
