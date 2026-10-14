# Scalar bit reversal (#140)

The eight modules in this batch reuse the pure legacy BitRR helper through the
Stock state projection, prove the three actual scalar matches/RHSs, derive
requests from success, and establish final-alias execution values. Byte/halfword
roots allocate two registers for rbit then lsr; word/doubleword roots allocate
one. Narrow values are proved by kernel bit-index reasoning, independent of
dirty upper machine bits. Actual rejected-prefix selection proves the wide
fallback cannot apply at8/16 bits.

Retained-record selection and result binding are derived from real lowering.
The original demand/availability, source scope and dominance premises remain;
source transfer consumes the original CLIF body and preserves memory. No
compiler/default change or new accepted-input certificate is introduced.

Complete witnesses cover8/16/32/64 bits with parameter operands and earlier
constant producers, actual emitted decisions/rule ids/nonempty bindings,
resolved execution, original source steps and demanded/available post-frames.
Earlier-producer cases leave the original mapped source vreg unmaterialized.
All eight complete witnesses build (392jobs). All14 public roots pass normal
and MCP standard-only checks; all360 prior sets remain unchanged (374total),
including seven final compiler trust sets;0 original-source warnings. Full1542/
crates1171, runtime4672/0fail/0disagree/7unchanged known not-runnable (entire
report identical), encoder1292 identical/0different; bothE2E1150accepted/0rejected,
full identity/stage parity. Receipt:
[stock-bitrev-audit.json](../research/stock-bitrev-audit.json).

Next remaining closure scalar families, effects/control and deferred invariants,
source/block/whole-driver simulation/completeness, actual production integration
and fresh complete stock comparison. Production legacy; full #140 active and
incomplete. No push or merge.

Updated UTC: 2026-10-14T01:12:20.511148+00:00
