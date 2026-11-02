import FV.Backend.Proof.IselPrgExtT

/-!
# Progress of the ISLE lowering over the typed scope: the roots

The V7 progress analysis (`IselPrg*`) for the float-capable lowering context of a function of the
typed movement scope (`Compile.functionET`): value types are E's integers, `f32` and `f64`
(`mCTys`), and the instructions are `Compile.instET`'s (E's, the float constants, `load`/`store`
of a float, `select` of floats, `bitcast`). The transfer functions are `IselPrgExtT`'s.

`formOfT` is the root form of a statement (`formOf` on E), `stmtFormsT` lists every form of the
typed scope, `termRootsT` the terminator roots (a `return` of values of `mCTys`).

An `f64const` lowers through `constant_f64` (inst.isle:4263-4280), whose last rule needs the
literal pool; `Compile.f64PoolFree` excludes it, a relation the interval domain does not keep.
The `lower` rule of `f64const` (`lower.isle:68`, rule 585) is therefore hand-checked
(`handRulesT`, `IselPrgHandF64`): below `2^32` its call `constant_f64 n` is the entry of the
sub-table `f64Tab` on `aU32`; at least `2^32` (the low 32 bits are zero) `constant_f64`'s rules
are followed by hand, their calls are `f64Tab`'s (`f64Roots`).
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Aarch64

/-! ## Statement forms -/

/-- The float types. -/
def fTys : List Clif.Ty := [.f32, .f64]

/-- The `f64` bit patterns of at least `2^32`. -/
def f64Hi : PA := .int (some (2 ^ 32)) (some (2 ^ 64 - 1))

/-- **The root form of a statement of the typed scope**: `formOf` on E, else the form of the
float movement instruction. -/
def formOfT (f : Clif.Function) (c : Clif.Inst) : PA :=
  if Compile.instE c then formOf f c else
  match c with
  | .iconst ty _ =>
    if ty = .f32 then .inst (tyOf .f32) (idat VIdx.InstructionData.UnaryIeee32
      [opc VIdx.Opcode.F32const, aU32])
    else .inst (tyOf .f64) (idat VIdx.InstructionData.UnaryIeee64 [opc VIdx.Opcode.F64const, aU64])
  | .load _ ty _ _ _ => .inst (tyOf ty) (idat VIdx.InstructionData.Load
      [opc VIdx.Opcode.Load, aV, .op .memFlags none, .int none none])
  | .store _ _ _ _ _ _ => .inst tyNone (idat VIdx.InstructionData.Store
      [opc VIdx.Opcode.Store, .vals [aVM, aV], .op .memFlags none, .int none none])
  | .select ty _ _ _ => .inst (tyOf ty) (idat VIdx.InstructionData.Ternary
      [opc VIdx.Opcode.Select, .vals [aV, aVM, aVM]])
  | .bitcast ty _ _ => .inst (tyOf ty) (idat VIdx.InstructionData.LoadNoOffset
      [opc VIdx.Opcode.Bitcast, aVM, .any])
  | _ => .bot

/-- **Every statement form of the typed scope**: E's (`stmtForms`) and the float movement's. -/
def stmtFormsT : List PA :=
  let f0 : Clif.Function := default
  stmtForms ++
  [formOfT f0 (.iconst .f32 0), formOfT f0 (.iconst .f64 0)] ++
  (fTys.map fun ty => formOfT f0 (.load .load ty {} 0 0)) ++
  [formOfT f0 (.store .store .f32 {} 0 0 0)] ++
  (fTys.map fun ty => formOfT f0 (.select ty 0 0 0)) ++
  ((eTys ++ fTys).map fun ty => formOfT f0 (.bitcast ty {} 0))

/-! ## Terminator forms -/

/-- **The terminator roots of the typed scope**: `termRoots` with a `return` of typed values. -/
def termRootsT : List (TermId × List PA) :=
  (retCounts.map fun m => (TId.lower, [termInst VIdx.InstructionData.MultiAry
      [opc VIdx.Opcode.Return, .vals (List.replicate m aVM)]])) ++
  termRoots.drop retCounts.length

/-! ## Hand-checked rules -/

/-- The fuel of the hand-checked `f64const` rule's right-hand side. -/
def f64Fuel : Nat := 3000

/-- **The hand-checked rules over the typed scope**: V7's (`handRules`) and the `lower` rule of
`f64const` (`lower.isle:68`, rule 585), whose call `constant_f64 n` needs `f64PoolFree n`. -/
def handRulesT (r : RuleId) : Option (Nat × PA) :=
  if r == 585 then some (f64Fuel, .regsVec (some 1)) else handRules r

/-- The roots of the `f64const` sub-table: `constant_f64` below and at least `2^32`, and
`output_reg` of the rule's right-hand side. -/
def f64Roots : List (TermId × List PA) :=
  [(TId.constant_f64, [aU32]), (TId.constant_f64, [f64Hi]), (TId.output_reg, [.reg])]

end Backend.Proof.Prg
