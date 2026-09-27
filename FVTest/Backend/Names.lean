import FV.Backend

/-!
Consistency of the backend with the exported ISLE program (`FV/Isle/Generated`). Types and
enum variants the backend decodes or builds by *index* are the generated constants
`Isle.Aarch64.TyId.*` / `VIdx.*` (a Cranelift upgrade that renames one is a compile error);
the ones it still builds by *name* from CLIF (`mkVariant`: `InstructionData`, `Opcode`, `IntCC`)
are checked here, so a rename fails here instead of producing values no rule matches.
`lake build FVTest.Backend.Names`.
-/

open Backend

#guard [(tyInstData, "UnaryImm"), (tyInstData, "Unary"), (tyInstData, "Binary"),
  (tyInstData, "IntCompare"), (tyInstData, "Load"), (tyInstData, "Store"),
  (tyInstData, "StackAddr"), (tyInstData, "Call"), (tyInstData, "Jump"),
  (tyInstData, "Brif"), (tyInstData, "BranchTable"), (tyInstData, "MultiAry"),
  (tyInstData, "Trap"), (tyInstData, "Ternary"), (tyInstData, "NullAry"),
  (tyInstData, "UnaryGlobalValue")].all fun (t, n) => (variantIdx t n).isSome

#guard Clif.IntCC.all.all fun cc => (variantIdx tyIntCC (intccName cc)).isSome

-- The index tables of the typed view round-trip and agree with the variant names.
#guard Cond.all.all fun c => Cond.ofIdx? c.idx == some c && variantIdx tyCond c.name == some c.idx
#guard ExtendOp.all.all fun e =>
  ExtendOp.ofIdx? e.idx == some e && variantIdx tyExtendOp e.name == some e.idx

/-- Every opcode name the backend produces for E. -/
def eOpcodeNames : List String :=
  ([Clif.BinaryOp.iadd, .isub, .imul, .umulhi, .smulhi, .band, .bor, .bxor, .ishl, .ushr, .sshr,
    .rotl, .rotr, .smin, .smax, .umin, .umax].filterMap binaryOpcode) ++
  ([Clif.UnaryOp.ineg, .bnot, .clz, .ctz, .popcnt, .bswap, .bitrev].filterMap unaryOpcode) ++
  ([Clif.DivOp.udiv, .sdiv, .urem, .srem].map divOpcode) ++
  ([Clif.LoadOp.load, .uload8, .sload8, .uload16, .sload16, .uload32, .sload32].map loadOpcode) ++
  ([Clif.StoreOp.store, .istore8, .istore16, .istore32].map storeOpcode) ++
  ["Iconst", "Icmp", "Uextend", "Sextend", "Ireduce", "StackAddr", "Call", "Jump", "Brif",
   "BrTable", "Return", "Trap", "Select", "Nop", "SymbolValue"]

#guard eOpcodeNames.length == 54
#guard eOpcodeNames.all fun n => (variantIdx tyOpcode n).isSome
