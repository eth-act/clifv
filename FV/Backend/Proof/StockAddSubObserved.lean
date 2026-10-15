import FV.Backend.Proof.StockAddSubSelected
namespace Backend.Stock.Proof.ScalarAddSub
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Successful actual RHS execution determines requests, output, allocation
and the complete scheduling state. -/
theorem stock_addsub_imm_observed {p : Program} (hp : Data p) (ctx : Ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {w x n : Nat} (width : w ≤ 64) {imm : Imm12}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+50) (immRule subtract left).rhs
      (immEnv left w x imm)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧
      ∃ rx,ctx.valueReg? x = some rx ∧
      out = .regsVec [[(st.base.fresh .int).1]] ∧
      next = {st.mark x with base := (st.base.fresh .int).2.emit (.aluRRImm12 (if subtract then .sub else .add) (szOf w) (st.base.fresh .int).1 rx imm)} := by
  obtain ⟨safeX,rx,mapX⟩ := stock_addsub_imm_first_request hp ctx subtract left side run
  obtain ⟨actualTrace,forward⟩ := stock_addsub_imm_rhs hp ctx subtract left side width imm mapX st safeX tr n
  rw [forward] at run
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at run
  obtain ⟨outEq,stateEq,_⟩ := run
  exact ⟨safeX,rx,mapX,outEq.symm,stateEq.symm⟩
/-- Successful actual RHS execution determines requests, output, allocation
and the complete scheduling state. -/
theorem stock_addsub_neg_imm_observed {p : Program} (hp : Data p) (ctx : Ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {w x n : Nat} (width : w ≤ 64) {y : Nat} {imm : Imm12}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+50) (negImmRule subtract left).rhs
      (negImmEnv left w x y imm)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧
      ∃ rx,ctx.valueReg? x = some rx ∧
      out = .regsVec [[(st.base.fresh .int).1]] ∧
      next = {st.mark x with base := (st.base.fresh .int).2.emit (.aluRRImm12 (if subtract then .add else .sub) (szOf w) (st.base.fresh .int).1 rx imm)} := by
  obtain ⟨safeX,rx,mapX⟩ := stock_addsub_neg_imm_first_request hp ctx subtract left side run
  obtain ⟨actualTrace,forward⟩ := stock_addsub_neg_imm_rhs hp ctx subtract left side width imm mapX st safeX tr n
  rw [forward] at run
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at run
  obtain ⟨outEq,stateEq,_⟩ := run
  exact ⟨safeX,rx,mapX,outEq.symm,stateEq.symm⟩
/-- Successful actual RHS execution determines requests, output, allocation
and the complete scheduling state. -/
theorem stock_addsub_shift_observed {p : Program} (hp : Data p) (ctx : Ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {w x n : Nat} (width : w ≤ 64) {z y : Nat} {c : Int} {sh : ShiftOpAndAmt}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+60) (shiftRule subtract left).rhs
      (shiftEnv left w x z y c sh)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st z ∧
      ∃ rx rz,ctx.valueReg? x = some rx ∧ ctx.valueReg? z = some rz ∧
      out = .regsVec [[(st.base.fresh .int).1]] ∧
      next = {(st.mark x).mark z with base := (st.base.fresh .int).2.emit (.aluRRRShift (if subtract then .sub else .add) (szOf w) (st.base.fresh .int).1 rx rz sh)} := by
  obtain ⟨safeX,safeZ,rx,rz,mapX,mapZ⟩ := stock_addsub_shift_requests hp ctx subtract left side run
  obtain ⟨actualTrace,forward⟩ := stock_addsub_shift_rhs hp ctx subtract left side width c sh mapX mapZ st safeX safeZ tr n
  rw [forward] at run
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at run
  obtain ⟨outEq,stateEq,_⟩ := run
  exact ⟨safeX,safeZ,rx,rz,mapX,mapZ,outEq.symm,stateEq.symm⟩
/-- Successful actual RHS execution determines requests, output, allocation
and the complete scheduling state. -/
theorem stock_addsub_extend_observed {p : Program} (hp : Data p) (ctx : Ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {w x n : Nat} (width : w ≤ 64) {z : Nat} {e : ExtendOp}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+70) (extendRule subtract left).rhs
      (extendEnv left w x z e)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st z ∧
      ∃ rx rz,ctx.valueReg? x = some rx ∧ ctx.valueReg? z = some rz ∧
      out = .regsVec [[(st.base.fresh .int).1]] ∧
      next = {(st.mark x).mark z with base := (st.base.fresh .int).2.emit (.aluRRRExtend (if subtract then .sub else .add) (szOf w) (st.base.fresh .int).1 rx rz e)} := by
  obtain ⟨safeX,safeZ,rx,rz,mapX,mapZ⟩ := stock_addsub_extend_requests hp ctx subtract left side run
  obtain ⟨actualTrace,forward⟩ := stock_addsub_extend_rhs hp ctx subtract left side width e mapX mapZ st safeX safeZ tr n
  rw [forward] at run
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at run
  obtain ⟨outEq,stateEq,_⟩ := run
  exact ⟨safeX,safeZ,rx,rz,mapX,mapZ,outEq.symm,stateEq.symm⟩
end Backend.Stock.Proof.ScalarAddSub
