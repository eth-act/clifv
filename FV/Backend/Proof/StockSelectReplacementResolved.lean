import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.StockSelectReplacement
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- The consumer replacement uses the actual final resolver. Fresh destination
identity and both mapped source operands are established explicitly; separation
is an internal availability obligation for the retained-record caller. -/
theorem stock_select_replace_cset_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {leading : List MInst} {aliases : Array (Option Nat)}
    {ρ : Nat → CV} {world : Arm.ArmState} {d x y : Nat} {condition : Cond}
    (valid : condition ≠ .al ∧ condition ≠ .nv) {ty : Clif.Ty} (width : ty.width ≤ 64)
    {u v : BitVec ty.width} {b : Bool} {P : Nat → Prop} (bounded : aliases.size ≤ d)
    (separateX : aliasNum aliases x ≠ d) (separateY : aliasNum aliases y ≠ d)
    (outside : ∀ k,P k → k ≠ d)
    (run : Runs F isem ((leading++[MInst.cset (.vreg d .int) condition]).map
      (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun final _ =>
        VHolds ⟨.i8,Clif.Sem.bool8 b⟩ (final d) ∧ VHolds ⟨ty,u⟩ (final (aliasNum aliases x)) ∧
        VHolds ⟨ty,v⟩ (final (aliasNum aliases y)) ∧ ∀ k,P k → final k = ρ k)) :
    Runs F isem ((leading++[MInst.csel (.vreg d .int) (.vreg x .int) (.vreg y .int) condition]).map
      (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world
      (fun final _ => VHolds ⟨ty,if b then u else v⟩ (final d) ∧ ∀ k,P k → final k = ρ k) := by
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]
    rfl
  have mapBool : (MInst.cset (.vreg d .int) condition).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) = .cset (.vreg d .int) condition := by
    simp only [MInst.mapRegs,resolve_vreg]
    change MInst.cset (.vreg (aliasNum aliases d) .int) condition = _
    rw [fresh]
  have mapSelect : (MInst.csel (.vreg d .int) (.vreg x .int) (.vreg y .int) condition).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .csel (.vreg d .int) (.vreg (aliasNum aliases x) .int) (.vreg (aliasNum aliases y) .int) condition := by
    simp only [MInst.mapRegs,resolve_vreg]
    change MInst.csel (.vreg (aliasNum aliases d) .int) (.vreg (aliasNum aliases x) .int)
      (.vreg (aliasNum aliases y) .int) condition = _
    rw [fresh]
  simp only [List.map_append,List.map_cons,List.map_nil,mapBool] at run
  simp only [List.map_append,List.map_cons,List.map_nil,mapSelect]
  exact stock_select_replace_cset refines valid width separateX separateY outside run
end Backend.Stock.Proof.ScalarSelect
