# Actual demand preservation

Part of #140, following merged guarded value transfer #163.

1. Prove that marking one or many source values never decreases any demand count,
   including out-of-bounds queries. Prove preservation for all actual constructors,
   including successful reserved-payload alias folds.
2. Reuse generic interpreter state preservation to lift this through nested and
   named lowering. Derive retained emitted-record count monotonicity from its
   actual normalized scan and emitter; virtual binding and copies retain demand.
3. Keep the original guarded transfer and add a variant deriving its demand
   premise from successful whole-driver record execution. Move the complete add
   execution/source-frame witness onto this variant.
4. Inhabit constructor/helper/named-root paths with real mark_value_used execution
   and retained-record paths with the existing complete Stock add run.
5. Validate normal/MCP axiom sets, full/crate/runtime/encoder/E2E gates and exact
   baseline identity/stage parity; publish a bounded PR.

Remaining: selected-family execution/fresh-def/safety obligations, other shapes,
reserved writes, memory/traps/deferred sinking and complete block/function
simulation/completeness before production cutover. Compiler behavior unchanged.
