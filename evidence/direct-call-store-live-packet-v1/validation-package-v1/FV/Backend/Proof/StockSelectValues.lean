import FV.Backend.Proof.IselCmpSelect
import FV.Backend.Proof.StockAliasSemantics
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- A decoded flag producer and actual csel compute the selected original
scalar value through final aliases. The producer's semantic flag fact is an
internal emitter obligation; the consumer imposes no operand classification. -/
theorem stock_select_flags_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {ty : Clif.Ty} (width : ty.width ≤ 64)
    {u v : BitVec ty.width} {aliases : Array (Option Nat)} {ρ : Nat → CV}
    {m : MInst} {ps : Arm.PState} {condition : Cond} {b : Bool} {x y d : Nat}
    (bounded : aliases.size ≤ d)
    (flags : SetsFlags (m.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))) ρ ps)
    (truth : condOn condition.bits ps = b)
    (inputX : VHolds ⟨ty,u⟩ (ρ (aliasNum aliases x)))
    (inputY : VHolds ⟨ty,v⟩ (ρ (aliasNum aliases y))) (world : Arm.ArmState) :
    Runs F isem ([m,.csel (.vreg d .int) (.vreg x .int) (.vreg y .int) condition].map
      (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
        VHolds ⟨ty,if b then u else v⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = ρ k) := by
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]
    rfl
  have code : ([m,.csel (.vreg d .int) (.vreg x .int) (.vreg y .int) condition].map
      (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) =
      [m.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)),
        .csel (.vreg d .int) (.vreg (aliasNum aliases x) .int) (.vreg (aliasNum aliases y) .int) condition] := by
    simp only [List.map_cons,List.map_nil]
    apply congrArg (fun z => [m.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)),z])
    simp only [MInst.mapRegs,resolve_vreg]
    change MInst.csel (.vreg (aliasNum aliases d) .int)
      (.vreg (aliasNum aliases x) .int) (.vreg (aliasNum aliases y) .int) condition = _
    rw [fresh]
  rw [code]
  exact (runs_flags_csel refines flags truth d (aliasNum aliases x) (aliasNum aliases y) world).imp
    (fun ρ' _ _ same => by
      subst ρ'
      constructor
      · rw [upd_same]
        cases b
        · change (ofX (lo64 (ρ (aliasNum aliases y)))).setWidth ty.width = v
          exact (setWidth_ofX_lo64 width _).trans inputY
        · change (ofX (lo64 (ρ (aliasNum aliases x)))).setWidth ty.width = u
          exact (setWidth_ofX_lo64 width _).trans inputX
      · intro k different
        simp [upd,different])
end Backend.Stock.Proof.ScalarSelect
