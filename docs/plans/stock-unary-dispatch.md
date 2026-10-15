# Actual unary rule dispatch from original source data (#140)

StockRootOpcode kernel-checks that all145 original closure roots have a
recognized primary opcode. Exact candidate lists include negation[756], bit
reversal[915,916,918] and byte swaps[932,933,934]. StockRootOpcodeMatch proves
the parser sound via actual inst_data_value/enum matching, handles the same
bind/and wrappers as the existing format parser, and transports to actual
Stock LowerSelection and retained-record candidate ids. The source scope and
actual matching supply the connection; a caller supplies no reachable-root
certificate.

StockUnaryDispatch derives the actual rules from original opcode/type data.
Bit-reversal fallback constraints reuse actual rejected-prefix proofs. New
negation/bit-reversal/byte-swap source-by-instruction variants derive both
operand getter and selected rule id internally. Existing source variants,
input conditions, production code and all shared T6 interfaces are unchanged.

Three complete witness modules cover22 actual retained source steps: negation
and bit reversal at8/16/32/64 with both operand forms, and byte swaps at16/32/64
with both forms. Earlier producers leave original source registers
unmaterialized; dirty bits include positions above the source width. Witness
statements expose actual emitted decisions, root ids, nonempty bindings,
resolved execution and original post-frame. All22 witness cases build (three407-job targets), and all16 new public roots
pass normal/MCP standard-only audits. All388 prior sets unchanged (404total),
including seven final compiler trust sets;0 source warnings. Full1555/crates1171,
runtime4672/0fail/0disagree/7known identical report; encoder1292/0; bothE2E1150/0
with complete identity/stage parity. Receipt:
[stock-unary-dispatch-audit.json](../research/stock-unary-dispatch-audit.json).

The full diagnostic opcode-family lists (60 groups/145 closure roots) are saved
in stock-root-opcode-families.json. Ordinary-source matching is proved; these
lists are not execution coverage, and branch/terminator contexts remain separate.
Next extend actual source-based dispatch to other covered families and prove
remaining count/rotation/arithmetic/comparison/select/extension/look-through,
effects/control/deferred invariants, full source/block/whole-driver simulation
and completeness, actual production integration and fresh complete stock
comparison. Full #140 active/incomplete; production legacy; no push or merge.

Updated UTC: 2026-10-14T02:18:14.895065+00:00
