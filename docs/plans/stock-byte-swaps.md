# Scalar byte swaps and source-driven unary transfer (#140)

Actual roots2035/2038/2041 (ids932/933/934) have complete match/RHS state,
success-derived requests, final-alias execution, actual retained binding and
original guarded source transfer. Halfword REV16 uses kernel bit-index
reasoning; old byte-swap bit-blasting lemmas are not called. Machine values
permit dirty bits above the original source width.

StockUnarySourceValues derives restricted typed unary operands from successful
original source evaluation plus unchanged dominance. Negation, bit reversal
and byte swaps have new source-driven variants without a caller getter;
existing theorem variants remain unchanged. These are internal proof facts,
not additional accepted-input certificates or compiler changes.

Six complete witnesses cover16/32/64 bits, parameters and earlier producers
with unmaterialized original source registers, actual emitted root ids and
nonempty result binding. Both full witness builds pass (initial370jobs; source-driven403jobs). All14
public roots normal/MCP standard-only;374 earlier sets unchanged (388total),
including seven final compiler trust sets;0 source warnings. Full1549/crates1171,
runtime4672/0fail/0disagree/7known with identical report; encoder1292 identical/
0different; bothE2E1150accepted/0rejected with full identity/stage parity.
Receipt: [stock-bswap-audit.json](../research/stock-bswap-audit.json).

Next derive actual rule-family selection from source opcode/type data, then
remaining counts/rotation/arithmetic/comparison/select/extension/look-through,
effects/control/deferred invariants, full simulation/completeness and actual
production integration/complete stock comparison. Production legacy; full #140
active/incomplete. No push/merge.

Updated UTC: 2026-10-14T01:42:03.876677+00:00
