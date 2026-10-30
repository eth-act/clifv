import FV.Backend.Proof.StockCmpCondition
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
/-- A decoded scalar condition always supplies the actual715 proof companion.
Its success, exact producer, fresh result and unchanged scheduling fields are
constructed internally, rather than required from the accepted source program. -/
theorem stock_select_condition_boolean_companion (ctx : Ctx) {raw : V} {P : Nat → Prop}
    (shape : CondShape raw P) (st : State) (tr : Array RuleId) :
    ∃ (producer : MInst) (condition : Cond) (trace : Array RuleId),
      CondFlag cmpImm0 raw producer condition ∧ vdefs producer = [] ∧
      condition ≠ .al ∧ condition ≠ .nv ∧
      ApplyInternal program (Stock.sem ctx) {} 119 27 715 [raw] (st,tr)
        (.reg (st.base.fresh .int).1)
        ({st with base := (((st.base.fresh .int).2.emit producer).emit
          (.cset (st.base.fresh .int).1 condition))},trace) := by
  rcases shape with ⟨k,i,sz,rfl,decoded,_⟩ | ⟨k,i,sz,rfl,decoded,_⟩ |
    ⟨mi,m,cc,rfl,decoded,notAl,notNv,noDefs,_⟩
  · have index := size_index decoded
    subst i
    obtain ⟨trace,run⟩ := ScalarCmp.stock_cmp_condition_zero data_program ctx (cfg := {}) rfl false sz st tr 0 (.vreg k .int)
    have actual := run
    cases sz
    all_goals exact ⟨_,.eq,trace,Or.inl ⟨k,_,_,rfl,decoded,rfl,rfl⟩,rfl,by decide,by decide,actual⟩
  · have index := size_index decoded
    subst i
    obtain ⟨trace,run⟩ := ScalarCmp.stock_cmp_condition_zero data_program ctx (cfg := {}) rfl true sz st tr 0 (.vreg k .int)
    have actual := run
    cases sz
    all_goals exact ⟨_,.ne,trace,Or.inr (Or.inl ⟨k,_,_,rfl,decoded,rfl,rfl⟩),rfl,by decide,by decide,actual⟩
  · obtain ⟨trace,run⟩ := ScalarCmp.stock_cmp_condition_flags data_program ctx (cfg := {}) rfl st tr 0 decoded cc
    exact ⟨m,cc,trace,Or.inr (Or.inr ⟨mi,rfl,decoded⟩),noDefs,notAl,notNv,run⟩
end Backend.Stock.Proof.ScalarSelect
