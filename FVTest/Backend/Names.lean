import FV.Backend

/-!
Consistency of the backend with the exported ISLE program (`FV/Isle/Generated`): every ISLE
type and enum variant the backend builds values of by name exists. A Cranelift upgrade that
renames one of them fails here instead of producing values no rule matches.
`lake build FVTest.Backend.Names`.
-/

open Backend

#guard ["MInst", "ALUOp", "ALUOp3", "OperandSize", "Cond", "ExtendOp", "AMode", "CondBrKind",
  "MoveWideOp", "BfmOp", "BitOp", "ScalarSize", "VectorSize", "VecMisc2", "VecLanesOp",
  "VecALUOp", "TestBitAndBranchKind", "IntCC", "Opcode", "InstructionData", "RelocDistance",
  "TlsModel"].all fun n => (Isle.Aarch64.program.types.find? (·.name == n)).isSome

#guard [(tyMInst, "LoadAddr"), (tyAMode, "SlotOffset"), (tyCondBrKind, "Zero"),
  (tyCondBrKind, "NotZero"), (tyCondBrKind, "Cond"), (tyRelocDistance, "Near"),
  (tyRelocDistance, "Far"), (islTy "TlsModel", "None"),
  (tyInstData, "UnaryImm"), (tyInstData, "Unary"), (tyInstData, "Binary"),
  (tyInstData, "IntCompare"), (tyInstData, "Load"), (tyInstData, "Store"),
  (tyInstData, "StackAddr"), (tyInstData, "Call"), (tyInstData, "Jump"),
  (tyInstData, "Brif"), (tyInstData, "BranchTable"), (tyInstData, "MultiAry"),
  (tyInstData, "Trap")].all fun (t, n) => (variantIdx t n).isSome

#guard Cond.all.all fun c => (variantIdx tyCond c.name).isSome
#guard ExtendOp.all.all fun e => (variantIdx tyExtendOp e.name).isSome
#guard Clif.IntCC.all.all fun cc => (variantIdx tyIntCC (intccName cc)).isSome

/-- Every opcode name the backend produces for E. -/
def eOpcodeNames : List String :=
  ([Clif.BinaryOp.iadd, .isub, .imul, .umulhi, .smulhi, .band, .bor, .bxor, .ishl, .ushr, .sshr,
    .rotl, .rotr].filterMap binaryOpcode) ++
  ([Clif.UnaryOp.ineg, .bnot, .clz, .ctz, .popcnt].filterMap unaryOpcode) ++
  ([Clif.DivOp.udiv, .sdiv, .urem, .srem].map divOpcode) ++
  ([Clif.LoadOp.load, .uload8, .sload8, .uload16, .sload16, .uload32, .sload32].map loadOpcode) ++
  ([Clif.StoreOp.store, .istore8, .istore16, .istore32].map storeOpcode) ++
  ["Iconst", "Icmp", "Uextend", "Sextend", "Ireduce", "StackAddr", "Call", "Jump", "Brif",
   "BrTable", "Return", "Trap"]

#guard eOpcodeNames.length == 45
#guard eOpcodeNames.all fun n => (variantIdx tyOpcode n).isSome
