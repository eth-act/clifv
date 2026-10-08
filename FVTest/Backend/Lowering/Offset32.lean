import FV.Backend.Isel

/-! Regression for the raw signed Offset32 extractor and the actual exported
ordinary-load helper pattern. Independent of the experimental stock driver. -/
open Backend Isle Isle.Interp Isle.Aarch64

private def offsetCtx (offset : Int) : Ctx := {
  func := default
  insts := #[⟨(instData default (.load .load .i8 {} 1 offset)).toOption.getD (.op .unit),
    [0], [.int 8], some (.load .load .i8 {} 1 offset)⟩]
  valTy := #[some (.int 8), some (.int 64)]
  valDef := #[some 0, none]
  valReg := #[some (.vreg 192 .int), some (.vreg 193 .int)]
  slotOff := [] }

private def input : LState := ⟨194, Array.replicate 194 .int, #[], 0⟩

private def extractOk (offset : Int) : Bool :=
  match Backend.externExtract (offsetCtx offset) T.offset32 (.int offset) input with
  | .ok [.int raw] => raw == offset
  | _ => false

private def matchOk (offset : Int) : Bool :=
  match (matchRule program (Backend.sem (offsetCtx offset)) {} 2
      rule_inst_4203 [.ty (.int 8), .inst 0]).run (input, #[]) with
  | .ok (some bound, _, _) => match bound[2]? with
    | some (some (V.int raw)) => raw == offset
    | _ => false
  | _ => false

#guard extractOk (0) && matchOk (0)
#guard extractOk (-16) && matchOk (-16)
#guard extractOk (8) && matchOk (8)
