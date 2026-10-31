import FV.Backend.Proof.IselPrgExt

/-!
# Progress of the ISLE lowering (V7): the root forms

The driver calls `lower` on every statement (`[.inst ii]`), and `lower`/`lower_branch` on every
terminator at its placeholder slot. The abstract value of the argument is fixed by the form of
the instruction: its opcode, its result type, the enum immediates the rules dispatch on
(`IntCC`, `AtomicRmwOp`), and for a call the number of ABI returns of the callee. `formOf f c`
is that value for a statement `c`; `stmtForms` lists every form of an E statement, the table's
statement roots. `termRoots` lists the terminator roots (`return` with up to 8 values, `trap`,
`jump`, `brif`, `br_table`, `try_call`/`try_call_indirect` with up to `maxTryItems` exception
table items). `stmtOut` is the output the driver needs of a statement's lowering (one register
per result).
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Aarch64

/-! ## Opcode and immediate indices -/

/-- The `Opcode` variant of a unary operation (`unaryOpcode`). -/
def unaryIdx : Clif.UnaryOp → Nat
  | .ineg => VIdx.Opcode.Ineg | .bnot => VIdx.Opcode.Bnot | .clz => VIdx.Opcode.Clz
  | .ctz => VIdx.Opcode.Ctz | .popcnt => VIdx.Opcode.Popcnt | .bswap => VIdx.Opcode.Bswap
  | .bitrev => VIdx.Opcode.Bitrev | _ => 0

/-- The `Opcode` variant of a binary operation (`binaryOpcode`). -/
def binaryIdx : Clif.BinaryOp → Nat
  | .iadd => VIdx.Opcode.Iadd | .isub => VIdx.Opcode.Isub | .imul => VIdx.Opcode.Imul
  | .umulhi => VIdx.Opcode.Umulhi | .smulhi => VIdx.Opcode.Smulhi | .band => VIdx.Opcode.Band
  | .bor => VIdx.Opcode.Bor | .bxor => VIdx.Opcode.Bxor | .ishl => VIdx.Opcode.Ishl
  | .ushr => VIdx.Opcode.Ushr | .sshr => VIdx.Opcode.Sshr | .rotl => VIdx.Opcode.Rotl
  | .rotr => VIdx.Opcode.Rotr | .smin => VIdx.Opcode.Smin | .smax => VIdx.Opcode.Smax
  | .umin => VIdx.Opcode.Umin | .umax => VIdx.Opcode.Umax | _ => 0

/-- The `Opcode` variant of a division (`divOpcode`). -/
def divIdx : Clif.DivOp → Nat
  | .udiv => VIdx.Opcode.Udiv | .sdiv => VIdx.Opcode.Sdiv | .urem => VIdx.Opcode.Urem
  | .srem => VIdx.Opcode.Srem

/-- The `Opcode` variant of a load (`loadOpcode`). -/
def loadIdx : Clif.LoadOp → Nat
  | .load => VIdx.Opcode.Load | .uload8 => VIdx.Opcode.Uload8 | .sload8 => VIdx.Opcode.Sload8
  | .uload16 => VIdx.Opcode.Uload16 | .sload16 => VIdx.Opcode.Sload16
  | .uload32 => VIdx.Opcode.Uload32 | .sload32 => VIdx.Opcode.Sload32

/-- The `Opcode` variant of a store (`storeOpcode`). -/
def storeIdx : Clif.StoreOp → Nat
  | .store => VIdx.Opcode.Store | .istore8 => VIdx.Opcode.Istore8
  | .istore16 => VIdx.Opcode.Istore16 | .istore32 => VIdx.Opcode.Istore32

/-- The `IntCC` variant of a condition code (`intccName`). -/
def ccIdx : Clif.IntCC → Nat
  | .eq => VIdx.IntCC.Equal | .ne => VIdx.IntCC.NotEqual | .slt => VIdx.IntCC.SignedLessThan
  | .sge => VIdx.IntCC.SignedGreaterThanOrEqual | .sgt => VIdx.IntCC.SignedGreaterThan
  | .sle => VIdx.IntCC.SignedLessThanOrEqual | .ult => VIdx.IntCC.UnsignedLessThan
  | .uge => VIdx.IntCC.UnsignedGreaterThanOrEqual | .ugt => VIdx.IntCC.UnsignedGreaterThan
  | .ule => VIdx.IntCC.UnsignedLessThanOrEqual

/-- The `AtomicRmwOp` variant of an `atomic_rmw` operation (`rmwOpName`). -/
def rmwIdx : Clif.AtomicRmwOp → Nat
  | .add => VIdx.AtomicRmwOp.Add | .sub => VIdx.AtomicRmwOp.Sub | .and => VIdx.AtomicRmwOp.And
  | .nand => VIdx.AtomicRmwOp.Nand | .or => VIdx.AtomicRmwOp.Or | .xor => VIdx.AtomicRmwOp.Xor
  | .xchg => VIdx.AtomicRmwOp.Xchg | .umin => VIdx.AtomicRmwOp.Umin
  | .umax => VIdx.AtomicRmwOp.Umax | .smin => VIdx.AtomicRmwOp.Smin
  | .smax => VIdx.AtomicRmwOp.Smax

/-! ## Statement forms -/

/-- An `Opcode` value. -/
def opc (o : Nat) : PA := .data tyOpcode o []

/-- An `InstructionData` value of format `k`. -/
def idat (k : Nat) (fs : List PA) : PA := .data tyInstData k fs

/-- The type of a single-result instruction of type `ty`. -/
def tyOf (ty : Clif.Ty) : PA := .ty [CTy.ofClif ty]

/-- No result. -/
def tyNone : PA := .ty [.invalid]

/-- The first result type of a call: none, or an E type. -/
def tyCall : PA := .ty (.invalid :: eCTys)

/-- The number of declared returns of `f`'s callee `fn` (the call defines one result vreg per
declared return, `gen_call_output`). -/
def retsOf (f : Clif.Function) (fn : Nat) : Nat :=
  ((f.extern? fn).map fun e => e.sig.returns.length).getD 0

/-- The number of declared returns of `f`'s signature declaration `sig`. -/
def sigRetsOf (f : Clif.Function) (sig : Nat) : Nat :=
  ((f.sigDecls.lookup sig).map fun s => s.returns.length).getD 0

/-- **The root form of a statement**: the abstract value of `.inst ii` for an instruction with
CLIF instruction `c` (`instData`, its result type). -/
def formOf (f : Clif.Function) : Clif.Inst → PA
  | .iconst ty _ => .inst (tyOf ty) (idat VIdx.InstructionData.UnaryImm [opc VIdx.Opcode.Iconst, .int none none])
  | .unary op ty _ => .inst (tyOf ty) (idat VIdx.InstructionData.Unary [opc (unaryIdx op), aV])
  | .binary op ty _ _ =>
    .inst (tyOf ty) (idat VIdx.InstructionData.Binary [opc (binaryIdx op), .vals [aV, aV]])
  | .div op ty _ _ => .inst (tyOf ty) (idat VIdx.InstructionData.Binary [opc (divIdx op), .vals [aV, aV]])
  | .icmp cc _ _ _ => .inst (.ty [.int 8]) (idat VIdx.InstructionData.IntCompare
      [opc VIdx.Opcode.Icmp, .vals [aV, aV], .data tyIntCC (ccIdx cc) []])
  | .extend op ty _ => .inst (tyOf ty) (idat VIdx.InstructionData.Unary
      [opc (if op == .uextend then VIdx.Opcode.Uextend else VIdx.Opcode.Sextend), aV])
  | .ireduce ty _ => .inst (tyOf ty) (idat VIdx.InstructionData.Unary [opc VIdx.Opcode.Ireduce, aV])
  | .load op ty _ _ _ => .inst (tyOf ty) (idat VIdx.InstructionData.Load
      [opc (loadIdx op), aV, .op .memFlags none, .int none none])
  | .store op _ _ _ _ _ => .inst tyNone (idat VIdx.InstructionData.Store
      [opc (storeIdx op), .vals [aV, aV], .op .memFlags none, .int none none])
  | .select ty _ _ _ => .inst (tyOf ty) (idat VIdx.InstructionData.Ternary
      [opc VIdx.Opcode.Select, .vals [aV, aV, aV]])
  | .nop => .inst tyNone (idat VIdx.InstructionData.NullAry [opc VIdx.Opcode.Nop])
  | .symbolValue ty _ => .inst (tyOf ty) (idat VIdx.InstructionData.UnaryGlobalValue
      [opc VIdx.Opcode.SymbolValue, .op .globalValue none])
  | .stackAddr ty _ _ => .inst (tyOf ty) (idat VIdx.InstructionData.StackAddr
      [opc VIdx.Opcode.StackAddr, .op .stackSlot none, .int none none])
  | .call fn _ => .inst tyCall (idat VIdx.InstructionData.Call
      [opc VIdx.Opcode.Call, .valsMin 0, .op .funcRef (some (retsOf f fn))])
  | .callIndirect sig _ _ => .inst tyCall (idat VIdx.InstructionData.CallIndirect
      [opc VIdx.Opcode.CallIndirect, .valsMin 1, .op .sig (some (sigRetsOf f sig))])
  | .funcAddr ty _ => .inst (tyOf ty) (idat VIdx.InstructionData.FuncAddr
      [opc VIdx.Opcode.FuncAddr, .op .funcRef none])
  | .bmask ty _ => .inst (tyOf ty) (idat VIdx.InstructionData.Unary [opc VIdx.Opcode.Bmask, aV])
  | .atomicLoad ty _ _ => .inst (tyOf ty) (idat VIdx.InstructionData.LoadNoOffset
      [opc VIdx.Opcode.AtomicLoad, aV, .op .memFlags none])
  | .atomicStore _ _ _ _ => .inst tyNone (idat VIdx.InstructionData.StoreNoOffset
      [opc VIdx.Opcode.AtomicStore, .vals [aV, aV], .op .memFlags none])
  | .atomicRmw op ty _ _ _ => .inst (tyOf ty) (idat VIdx.InstructionData.AtomicRmw
      [opc VIdx.Opcode.AtomicRmw, .vals [aV, aV], .op .memFlags none, .data tyAtomicRmwOp (rmwIdx op) []])
  | .atomicCas ty _ _ _ _ => .inst (tyOf ty) (idat VIdx.InstructionData.AtomicCas
      [opc VIdx.Opcode.AtomicCas, .vals [aV, aV, aV], .op .memFlags none])
  | .fence => .inst tyNone (idat VIdx.InstructionData.NullAry [opc VIdx.Opcode.Fence])
  | .tlsValue ty _ => .inst (tyOf ty) (idat VIdx.InstructionData.UnaryGlobalValue
      [opc VIdx.Opcode.TlsValue, .op .tlsGlobalValue none])
  | _ => .bot

/-- The E integer types of CLIF. -/
def eTys : List Clif.Ty := [.i8, .i16, .i32, .i64]

/-- The unary operations of E. -/
def eUnary : List Clif.UnaryOp := [.ineg, .bnot, .clz, .ctz, .popcnt, .bitrev, .bswap]

/-- The binary operations of E. -/
def eBinary : List Clif.BinaryOp :=
  [.iadd, .isub, .imul, .umulhi, .smulhi, .band, .bor, .bxor, .ishl, .ushr, .sshr, .rotl, .rotr,
   .smin, .smax, .umin, .umax]

/-- The ABI return counts of a call (`retRegs`: at most 8). -/
def retCounts : List Nat := List.range 9

/-- **Every statement form of E** (with a placeholder function for the call forms, whose return
count ranges over `retCounts`). -/
def stmtForms : List PA :=
  let f0 : Clif.Function := default
  (eTys.map fun ty => formOf f0 (.iconst ty 0)) ++
  (eUnary.flatMap fun op => (eTys.filter fun ty => !(op == .bswap && ty == .i8)).map fun ty =>
    formOf f0 (.unary op ty 0)) ++
  (eBinary.flatMap fun op => eTys.map fun ty => formOf f0 (.binary op ty 0 0)) ++
  ([Clif.DivOp.udiv, .sdiv, .urem, .srem].flatMap fun op => eTys.map fun ty => formOf f0 (.div op ty 0 0)) ++
  ([Clif.IntCC.eq, .ne, .slt, .sge, .sgt, .sle, .ult, .uge, .ugt, .ule].map fun cc =>
    formOf f0 (.icmp cc .i8 0 0)) ++
  ([Clif.ExtendOp.uextend, .sextend].flatMap fun op => eTys.map fun ty => formOf f0 (.extend op ty 0)) ++
  (eTys.map fun ty => formOf f0 (.ireduce ty 0)) ++
  ([Clif.LoadOp.load, .uload8, .sload8, .uload16, .sload16, .uload32, .sload32].flatMap fun op =>
    eTys.map fun ty => formOf f0 (.load op ty {} 0 0)) ++
  ([Clif.StoreOp.store, .istore8, .istore16, .istore32].map fun op => formOf f0 (.store op .i8 {} 0 0 0)) ++
  (eTys.map fun ty => formOf f0 (.select ty 0 0 0)) ++
  [formOf f0 .nop, formOf f0 (.symbolValue .i64 0)] ++
  (eTys.map fun ty => formOf f0 (.stackAddr ty 0 0)) ++
  (retCounts.map fun n => .inst tyCall (idat VIdx.InstructionData.Call
      [opc VIdx.Opcode.Call, .valsMin 0, .op .funcRef (some n)])) ++
  (retCounts.map fun n => .inst tyCall (idat VIdx.InstructionData.CallIndirect
      [opc VIdx.Opcode.CallIndirect, .valsMin 1, .op .sig (some n)])) ++
  [formOf f0 (.funcAddr .i64 0)] ++
  (eTys.map fun ty => formOf f0 (.bmask ty 0)) ++
  (eTys.map fun ty => formOf f0 (.atomicLoad ty {} 0)) ++
  [formOf f0 (.atomicStore .i8 {} 0 0)] ++
  ([Clif.AtomicRmwOp.add, .sub, .and, .nand, .or, .xor, .xchg, .umin, .umax, .smin, .smax].flatMap
    fun op => eTys.map fun ty => formOf f0 (.atomicRmw op ty {} 0 0)) ++
  (eTys.map fun ty => formOf f0 (.atomicCas ty {} 0 0 0)) ++
  [formOf f0 .fence, formOf f0 (.tlsValue .i64 0)]

/-- The output the driver needs of a statement form's lowering: one single register per ABI
result (`StmtProg`). -/
def stmtOut : PA → PA
  | .inst _ (.data _ VIdx.InstructionData.Call [_, _, .op .funcRef n]) => .regsVec n
  | .inst _ (.data _ VIdx.InstructionData.CallIndirect [_, _, .op .sig n]) => .regsVec n
  | .inst (.ty [.invalid]) _ => .regsVec none
  | _ => .regsVec (some 1)

/-! ## Terminator forms -/

/-- The most exception-table items of a `try_call` the table covers. -/
def maxTryItems : Nat := 8

/-- The terminator data in its slot (`termData`, `tryCallData`): no result type. -/
def termInst (k : Nat) (fs : List PA) : PA := .inst tyNone (idat k fs)

/-- **The terminator roots**: the root term and its abstract arguments. -/
def termRoots : List (TermId × List PA) :=
  (retCounts.map fun m => (TId.lower, [termInst VIdx.InstructionData.MultiAry
      [opc VIdx.Opcode.Return, .vals (List.replicate m aV)]])) ++
  [(TId.lower, [termInst VIdx.InstructionData.Trap [opc VIdx.Opcode.Trap, .op .trapCode none]]),
   (TId.lower_branch, [termInst VIdx.InstructionData.Jump [opc VIdx.Opcode.Jump, .blockCalls 1],
      .labels 1 (some 1)]),
   (TId.lower_branch, [termInst VIdx.InstructionData.Brif
      [opc VIdx.Opcode.Brif, aV, .blockCalls 2], .labels 2 (some 2)]),
   (TId.lower_branch, [termInst VIdx.InstructionData.BranchTable
      [opc VIdx.Opcode.BrTable, aV, .op .jumpTable none], .labels 1 none])] ++
  ((List.range (maxTryItems + 1)).map fun m => (TId.lower_branch,
    [termInst VIdx.InstructionData.TryCall [opc VIdx.Opcode.TryCall, .valsMin 0,
      .op .funcRefTry none, .op .exnTry (some m)], .labels (m + 1) (some (m + 1))])) ++
  ((List.range (maxTryItems + 1)).map fun m => (TId.lower_branch,
    [termInst VIdx.InstructionData.TryCallIndirect [opc VIdx.Opcode.TryCallIndirect, .valsMin 1,
      .op .exnTry (some m)], .labels (m + 1) (some (m + 1))]))

/-! ## Hand-checked rules -/

/-- **The hand-checked rules**: `extr_32_or_64` (`lower.isle:1501`, rule 862) and
`extr_32_or_64_2` (`:1507`, rule 863). Their right-hand side builds the shift immediate with the
total helper `imm_shift_from_u8 ys`, which needs `ys < 64`; that follows from the if-lets
`xs + ys = ty_bits ty` (32 or 64) and `xs > 0`, a relation between two matched constants that the
interval domain does not keep. `IselPrgHand` proves their right-hand sides (`HandOk`) with the
forward lemmas of V2's rule proofs (`IselTermsALUAExtr`). -/
def handRules (r : RuleId) : Option (Nat × PA) :=
  if r == 862 || r == 863 then some (60, .regsVec (some 1)) else none

end Backend.Proof.Prg
