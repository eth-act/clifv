import FV.Backend.Proof.StockSelectConditions
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private theorem size_index {i : Nat} {sz : OperandSize}
    (decoded : OperandSize.ofIdx? i = some sz) : i = if sz = .size32 then 0 else 1 := by
  cases i with
  | zero => cases sz <;> simp_all [OperandSize.ofIdx?]
  | succ i =>
    cases i with
    | zero => cases sz <;> simp_all [OperandSize.ofIdx?]
    | succ i => simp [OperandSize.ofIdx?] at decoded
/-- Decoded scalar conditions and the original successful source requests
construct actual659 success, without requiring a supplied helper run. -/
theorem stock_select_decoded_condition_success (ctx : Ctx) {raw : V}
    (shape : CondShape raw (fun _ => True)) {w x y : Nat}
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (st : State) (tr : Array RuleId)
    {rx ry : Reg} (mapX : ctx.valueReg? x = some rx) (mapY : ctx.valueReg? y = some ry)
    (safeX : DemandAllowed ctx st x) (safeY : DemandAllowed ctx (st.mark x) y) :
    ∃ out next trace,ApplyInternal program (Stock.sem ctx) {} 999 22 659
      [.ty (.int w),raw,.value x,.value y] (st,tr) out (next,trace) := by
  rcases shape with ⟨k,i,sz,rfl,size,_⟩ | ⟨k,i,sz,rfl,size,_⟩ | ⟨mi,m,cc,rfl,decoded,_⟩
  · have index := size_index size
    subst i
    exact ⟨_,_,_,stock_select_zero_run data_program ctx (cfg := {}) rfl width st tr 780 false sz k mapX mapY safeX safeY⟩
  · have index := size_index size
    subst i
    exact ⟨_,_,_,stock_select_zero_run data_program ctx (cfg := {}) rfl width st tr 780 true sz k mapX mapY safeX safeY⟩
  · exact ⟨_,_,_,stock_select_flags_run data_program ctx (cfg := {}) rfl width st tr 780 cc decoded mapX mapY safeX safeY⟩
end Backend.Stock.Proof.ScalarSelect
