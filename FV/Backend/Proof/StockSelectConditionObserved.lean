import FV.Backend.Proof.StockSelectDecodedObserved
import FV.Backend.Proof.StockSelectZeroObserved
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private theorem decoded_size_index {i : Nat} {sz : OperandSize}
    (decoded : OperandSize.ofIdx? i = some sz) : i = if sz = .size32 then 0 else 1 := by
  cases i with
  | zero => cases sz <;> simp_all [OperandSize.ofIdx?]
  | succ i =>
    cases i with
    | zero => cases sz <;> simp_all [OperandSize.ofIdx?]
    | succ i => simp [OperandSize.ofIdx?] at decoded
/-- All decoded scalar condition forms expose the actual select producer,
its proof companion producer, guarded source requests and exact complete state. -/
theorem stock_select_decoded_condition_observed (ctx : Ctx) {raw : V}
    (shape : CondShape raw (fun _ => True)) {w x y fuel : Nat}
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (enough : 319 ≤ fuel)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 22 659
      [.ty (.int w),raw,.value x,.value y] (st,tr) out (next,trace)) :
    ∃ booleanProducer actualProducer condition rx ry,
      CondFlag cmpImm0 raw booleanProducer condition ∧ CondFlag cmpXzr raw actualProducer condition ∧
      DemandAllowed ctx st x ∧ DemandAllowed ctx (st.mark x) y ∧
      ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
      out = .regs [(st.base.fresh .int).1] ∧
      next = {(st.mark x).mark y with base := (((st.base.fresh .int).2.emit actualProducer).emit
        (.csel (st.base.fresh .int).1 rx ry condition))} := by
  rcases shape with ⟨k,i,sz,rfl,size,_⟩ | ⟨k,i,sz,rfl,size,_⟩ |
    ⟨mi,m,cc,rfl,decoded,notAl,notNv,noDefs,held⟩
  · have index := decoded_size_index size
    subst i
    obtain ⟨safeX,safeY,rx,ry,mapX,mapY,output,finish⟩ :=
      stock_select_zero_observed data_program ctx rfl enough width false sz k run
    exact ⟨cmpImm0 sz k,cmpXzr sz k,.eq,rx,ry,Or.inl ⟨k,_,sz,rfl,size,rfl,rfl⟩,
      Or.inl ⟨k,_,sz,rfl,size,rfl,rfl⟩,safeX,safeY,mapX,mapY,output,finish⟩
  · have index := decoded_size_index size
    subst i
    obtain ⟨safeX,safeY,rx,ry,mapX,mapY,output,finish⟩ :=
      stock_select_zero_observed data_program ctx rfl enough width true sz k run
    exact ⟨cmpImm0 sz k,cmpXzr sz k,.ne,rx,ry,Or.inr (Or.inl ⟨k,_,sz,rfl,size,rfl,rfl⟩),
      Or.inr (Or.inl ⟨k,_,sz,rfl,size,rfl,rfl⟩),safeX,safeY,mapX,mapY,output,finish⟩
  · obtain ⟨m',decoded',safeX,safeY,rx,ry,mapX,mapY,output,finish⟩ :=
      stock_select_flags_decoded_observed data_program ctx rfl (by omega) width cc run
    have same : m' = m := Option.some.inj (decoded'.symm.trans decoded)
    subst m'
    exact ⟨m,m,cc,rx,ry,Or.inr (Or.inr ⟨mi,rfl,decoded⟩),Or.inr (Or.inr ⟨mi,rfl,decoded⟩),
      safeX,safeY,mapX,mapY,output,finish⟩
end Backend.Stock.Proof.ScalarSelect
