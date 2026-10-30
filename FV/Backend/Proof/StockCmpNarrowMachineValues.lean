import FV.Backend.Proof.StockCmpConditionValues
import FV.Backend.Proof.StockCmpNarrowFlags
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- A real extended compare/cset pair computes the original narrow predicate
through final aliases, retaining all registers outside its fresh result. -/
theorem stock_cmp_narrow_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {n : Nat} (width : n = 8 ∨ n = 16) (cc : Clif.IntCC)
    {a b : BitVec n} {aliases : Array (Option Nat)} {ρ : Nat → CV} {x y d : Nat}
    (bounded : aliases.size ≤ d)
    (left : DivOpnd (signedCC cc) a (ρ (aliasNum aliases x)))
    (right : (ρ (aliasNum aliases y)).setWidth n = b) (world : Arm.ArmState) :
    Runs F isem ([MInst.aluRRRExtend .subS .size32 .xzr (.vreg x .int) (.vreg y .int)
      (if signedCC cc then (if n = 8 then ExtendOp.sxtb else .sxth)
        else (if n = 8 then ExtendOp.uxtb else .uxth)),.cset (.vreg d .int) (condOf cc)].map
      (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
        VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc cc a b)⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = ρ k) := by
  let e := if signedCC cc then (if n = 8 then ExtendOp.sxtb else .sxth)
    else (if n = 8 then ExtendOp.uxtb else .uxth)
  have flags := stock_cmp_sets_flags_resolved
    (aliases := aliases) (ρ := ρ) (setsFlags_cmpExt .size32 x y e (fun key => ρ (aliasNum aliases key)))
  have truth := stock_cmp_narrow_extended_flags width cc left right
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]
    rfl
  have result : (.cset (.vreg d .int) (condOf cc) : MInst).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) = .cset (.vreg d .int) (condOf cc) := by
    simp only [MInst.mapRegs,resolve_vreg]
    change MInst.cset (.vreg (aliasNum aliases d) .int) (condOf cc) = _
    rw [fresh]
  simp only [List.map_cons,List.map_nil,result]
  exact (stock_cmp_flags_cset refines flags truth (condOf_ne_al cc) d world).imp
    (fun ρ' _ _ same => by
      subst ρ'
      refine ⟨?_,fun k different => by simp [upd,different]⟩
      rw [upd_same]
      exact vholds_bool8 _)
private def narrowAliases : Array (Option Nat) := #[some 1,none,some 3,none]
/-- Actual nonidentity final aliases inhabit both narrow widths and every
condition at the signed minimum/minus-one boundary. -/
theorem stock_cmp_narrow_resolved_witness (cc : Clif.IntCC) (n : Nat) (width : n = 8 ∨ n = 16)
    (world : Arm.ArmState) :
    ∃ ρ,Runs (fun _ => True) ispec ([MInst.aluRRRExtend .subS .size32 .xzr (.vreg 0 .int) (.vreg 2 .int)
      (if signedCC cc then (if n = 8 then ExtendOp.sxtb else .sxth)
        else (if n = 8 then ExtendOp.uxtb else .uxth)),.cset (.vreg 4 .int) (condOf cc)].map
      (·.mapRegs (Backend.lowerFunction.resolve narrowAliases (narrowAliases.size+1)))) ρ world (fun ρ' _ =>
        VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc cc (BitVec.intMin n) (-1 : BitVec n))⟩ (ρ' 4) ∧
        ∀ k,k ≠ 4 → ρ' k = ρ k) := by
  obtain ⟨A,B,left,right,_⟩ := stock_cmp_narrow_extended_flags_witness cc n width
  let ρ : Nat → CV := fun key => if key = 1 then A else if key = 3 then B else 0
  have left' : DivOpnd (signedCC cc) (BitVec.intMin n) (ρ (aliasNum narrowAliases 0)) := by
    have alias0 : aliasNum narrowAliases 0 = 1 := by decide +kernel
    rw [alias0]
    exact left
  have right' : (ρ (aliasNum narrowAliases 2)).setWidth n = (-1 : BitVec n) := by
    have alias2 : aliasNum narrowAliases 2 = 3 := by decide +kernel
    rw [alias2]
    exact right
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  exact ⟨ρ,stock_cmp_narrow_resolved self width cc (by decide) left' right' world⟩
end Backend.Stock.Proof.ScalarCmp
