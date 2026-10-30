import FV.Backend.Proof.IselCmpIcmp
import FV.Backend.Proof.StockCmpZeroHelpers
import FV.Backend.Proof.StockCmpFlagInvert
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual scalar inversion preserves the decoded condition contract, including
the producer's no-definition property. The complete Stock state is unchanged. -/
theorem stock_select_condition_invert_shape {ctx : Ctx} {fuel : Nat}
    (enough : 39 ≤ fuel) {raw out : V} {P : Nat → Prop}
    (shape : CondShape raw P) {st next : State} {tr trace : Array RuleId}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 123 649 [raw]
      (st,tr) out (next,trace)) : CondShape out P ∧ next = st := by
  rcases shape with ⟨k,i,sz,rfl,size,held⟩ | ⟨k,i,sz,rfl,size,held⟩ |
    ⟨mi,m,cc,rfl,decoded,notAl,notNv,noDefs,held⟩
  · obtain ⟨rfl,rfl⟩ := ScalarCmp.stock_cmp_zero_invert_observed data_program ctx enough false
      (.vreg k .int) (.data 93 i []) run
    exact ⟨Or.inr (Or.inl ⟨k,i,sz,rfl,size,held⟩),rfl⟩
  · obtain ⟨rfl,rfl⟩ := ScalarCmp.stock_cmp_zero_invert_observed data_program ctx enough true
      (.vreg k .int) (.data 93 i []) run
    exact ⟨Or.inl ⟨k,i,sz,rfl,size,held⟩,rfl⟩
  · obtain ⟨rfl,rfl⟩ := ScalarCmp.stock_cmp_flag_invert_observed data_program ctx enough
      (.data 47 1 [mi]) cc run
    have valid := invert_ne ⟨notAl,notNv⟩
    exact ⟨Or.inr (Or.inr ⟨mi,m,cc.invert,rfl,decoded,valid.1,valid.2,noDefs,held⟩),rfl⟩
end Backend.Stock.Proof.ScalarSelect
