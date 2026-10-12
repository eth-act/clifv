# Successful Stock scalar requests and ALU execution

Part of #140, based on merged demand preservation #164.

1. Invert successful actual scalar requests to derive source safety, the mapped
   register and the complete marked state. Retain the existing forward theorem.
2. Derive both operand request facts from successful actual add/subtract RHS
   execution, including rejection paths. Reuse the proved forward RHS to derive
   the exact result and complete emitted state without caller safety/map premises.
3. Reuse the real sparse-ID context/match/execution fixtures for both operations
   and both 32/64-bit widths to inhabit every new contract.
4. Run normal/MCP axiom audits and required full/crate/runtime/encoder/E2E gates;
   require baseline identity/stage and final theorem trust parity, then publish
   a bounded PR.

These contracts concern successful RHS execution at its typed matched environment;
width/data validity, selecting the rule and whole-record composition still need
separate connection. They change no compiler behavior. Other families, reserved
writes, memory/traps/deferred sinking, full simulation/completeness and the
production driver switch remain under #140.
