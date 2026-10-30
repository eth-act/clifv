import FV.Backend.Proof.StockSelectZeroReplacementResolved
import FV.Backend.Proof.StockSelectReplacementResolved
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- The two actual consumer producers are interchangeable for cset-to-csel
replacement, with the zero comparison change derived from the shared condition. -/
theorem stock_select_condition_producer_replacement {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {raw : V} {booleanProducer actualProducer : MInst} {condition : Cond}
    (booleanFlag : CondFlag cmpImm0 raw booleanProducer condition)
    (actualFlag : CondFlag cmpXzr raw actualProducer condition)
    (valid : condition ≠ .al ∧ condition ≠ .nv)
    {leading : List MInst} {aliases : Array (Option Nat)} {ρ : Nat → CV} {world : Arm.ArmState}
    {d x y : Nat} {ty : Clif.Ty} (width : ty.width ≤ 64) {u v : BitVec ty.width} {b : Bool}
    {P : Nat → Prop} (bounded : aliases.size ≤ d)
    (separateX : aliasNum aliases x ≠ d) (separateY : aliasNum aliases y ≠ d)
    (outside : ∀ k,P k → k ≠ d)
    (run : Runs F isem ((leading++[booleanProducer,.cset (.vreg d .int) condition]).map
      (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun final _ =>
        VHolds ⟨.i8,Clif.Sem.bool8 b⟩ (final d) ∧ VHolds ⟨ty,u⟩ (final (aliasNum aliases x)) ∧
        VHolds ⟨ty,v⟩ (final (aliasNum aliases y)) ∧ ∀ k,P k → final k = ρ k)) :
    Runs F isem ((leading++[actualProducer,.csel (.vreg d .int) (.vreg x .int) (.vreg y .int) condition]).map
      (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world
      (fun final _ => VHolds ⟨ty,if b then u else v⟩ (final d) ∧ ∀ k,P k → final k = ρ k) := by
  rcases booleanFlag with ⟨k,i,sz,rfl,hi,rfl,rfl⟩ | ⟨k,i,sz,rfl,hi,rfl,rfl⟩ | ⟨mi,rfl,hm⟩
  all_goals rcases actualFlag with ⟨k',i',sz',e,hi',rfl,_⟩ | ⟨k',i',sz',e,hi',rfl,_⟩ | ⟨mi',e,hm'⟩
  all_goals simp at e
  · obtain ⟨rfl,rfl⟩ := e
    rw [hi] at hi'; cases hi'
    exact stock_select_replace_zero_cset_resolved refines false sz k width bounded separateX separateY outside run
  · obtain ⟨rfl,rfl⟩ := e
    rw [hi] at hi'; cases hi'
    exact stock_select_replace_zero_cset_resolved refines true sz k width bounded separateX separateY outside run
  · rw [e] at hm
    rw [hm] at hm'
    cases hm'
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using
      stock_select_replace_cset_resolved refines valid width bounded separateX separateY outside
        (leading := leading++[booleanProducer]) (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using run)
end Backend.Stock.Proof.ScalarSelect
