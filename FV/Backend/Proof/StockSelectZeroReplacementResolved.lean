module

public import FV.Backend.Proof.StockSelectZeroReplacement

@[expose] public section

namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Zero producer/consumer replacement follows the actual final resolver,
including fresh destination identity and both resolved original sources. -/
theorem stock_select_replace_zero_cset_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {leading : List MInst} {aliases : Array (Option Nat)}
    {ρ : Nat → CV} {world : Arm.ArmState} {d x y : Nat} (nonzero : Bool) (size : OperandSize) (key : Nat) {ty : Clif.Ty} (width : ty.width ≤ 64)
    {u v : BitVec ty.width} {b : Bool} {P : Nat → Prop} (bounded : aliases.size ≤ d)
    (separateX : aliasNum aliases x ≠ d) (separateY : aliasNum aliases y ≠ d)
    (outside : ∀ k,P k → k ≠ d)
    (run : Runs F isem ((leading++[cmpImm0 size key,MInst.cset (.vreg d .int) (if nonzero then Cond.ne else Cond.eq)]).map
      (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun final _ =>
        VHolds ⟨.i8,Clif.Sem.bool8 b⟩ (final d) ∧ VHolds ⟨ty,u⟩ (final (aliasNum aliases x)) ∧
        VHolds ⟨ty,v⟩ (final (aliasNum aliases y)) ∧ ∀ k,P k → final k = ρ k)) :
    Runs F isem ((leading++[cmpXzr size key,MInst.csel (.vreg d .int) (.vreg x .int) (.vreg y .int) (if nonzero then Cond.ne else Cond.eq)]).map
      (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world
      (fun final _ => VHolds ⟨ty,if b then u else v⟩ (final d) ∧ ∀ k,P k → final k = ρ k) := by
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]
    rfl
  have mapBool : (MInst.cset (.vreg d .int) (if nonzero then Cond.ne else Cond.eq)).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) = .cset (.vreg d .int) (if nonzero then Cond.ne else Cond.eq) := by
    simp only [MInst.mapRegs,resolve_vreg]
    change MInst.cset (.vreg (aliasNum aliases d) .int) (if nonzero then Cond.ne else Cond.eq) = _
    rw [fresh]
  have mapSelect : (MInst.csel (.vreg d .int) (.vreg x .int) (.vreg y .int) (if nonzero then Cond.ne else Cond.eq)).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .csel (.vreg d .int) (.vreg (aliasNum aliases x) .int) (.vreg (aliasNum aliases y) .int) (if nonzero then Cond.ne else Cond.eq) := by
    simp only [MInst.mapRegs,resolve_vreg]
    change MInst.csel (.vreg (aliasNum aliases d) .int) (.vreg (aliasNum aliases x) .int)
      (.vreg (aliasNum aliases y) .int) (if nonzero then Cond.ne else Cond.eq) = _
    rw [fresh]
  have mapImmediate : (cmpImm0 size key).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) = cmpImm0 size (aliasNum aliases key) := by
    simp only [cmpImm0,MInst.mapRegs,resolve_vreg]; rfl
  have mapRegister : (cmpXzr size key).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) = cmpXzr size (aliasNum aliases key) := by
    simp only [cmpXzr,MInst.mapRegs,resolve_vreg]; rfl
  simp only [List.map_append,List.map_cons,List.map_nil,mapImmediate,mapBool] at run
  simp only [List.map_append,List.map_cons,List.map_nil,mapRegister,mapSelect]
  exact stock_select_replace_zero_cset refines nonzero size (aliasNum aliases key) width separateX separateY outside run
end Backend.Stock.Proof.ScalarSelect
