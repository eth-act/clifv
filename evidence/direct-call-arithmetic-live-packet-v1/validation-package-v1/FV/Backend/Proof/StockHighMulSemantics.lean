import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.IselFamALUAMul
namespace Backend.Stock.Proof.ScalarHighMul
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private theorem fresh_reg {aliases : Array (Option Nat)} {d : Nat} (bounded : aliases.size ≤ d) :
    Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int) = .vreg d .int := by
  rw [resolve_vreg]
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]; rfl
  change Reg.vreg (aliasNum aliases d) .int = _
  rw [fresh]
/-- Actual wide high-multiply execution uses original values through final
aliases and preserves every register except the fresh destination. -/
theorem stock_highmul_wide_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (signed : Bool) {ctx : Ctx} {fr : Clif.Frame}
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {x y nx ny d : Nat}
    (bounded : aliases.size ≤ d)
    (mapX : ctx.valueReg? x = some (.vreg nx .int)) (mapY : ctx.valueReg? y = some (.vreg ny .int))
    (held : ValuesHeld (fun z => z = x ∨ z = y) ctx fr (fun k => ρ (aliasNum aliases k)))
    {u v : BitVec 64} (getX : fr.getAs x .i64 = .ok u) (getY : fr.getAs y .i64 = .ok v) :
    ∃ ρ', PRun F isem
      [(.aluRRR (if signed then .sMulH else .uMulH) .size64 (.vreg d .int) (.vreg nx .int) (.vreg ny .int) : MInst).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨.i64,Clif.Sem.binary (if signed then .smulhi else .umulhi) u v⟩ (ρ' d) ∧
      ∀ n,n ≠ d → ρ' n = ρ n := by
  have xValue := held.read (Or.inl rfl) (getAs_ok getX) mapX
  have yValue := held.read (Or.inr rfl) (getAs_ok getY) mapY
  change (ρ (aliasNum aliases nx)).setWidth 64 = u at xValue
  change (ρ (aliasNum aliases ny)).setWidth 64 = v at yValue
  let a := opnd .size64 (ρ (aliasNum aliases nx))
  let b := opnd .size64 (ρ (aliasNum aliases ny))
  let r : BitVec 64 := if signed then ((a.signExtend 128)*(b.signExtend 128)).extractLsb' 64 64
    else ((a.zeroExtend 128)*(b.zeroExtend 128)).extractLsb' 64 64
  have value : VHolds ⟨.i64,Clif.Sem.binary (if signed then .smulhi else .umulhi) u v⟩ (resX .size64 r) := by
    cases signed
    · exact umulh_holds xValue yValue
    · exact smulh_holds xValue yValue
  have code : (.aluRRR (if signed then .sMulH else .uMulH) .size64 (.vreg d .int) (.vreg nx .int) (.vreg ny .int) : MInst).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .aluRRR (if signed then .sMulH else .uMulH) .size64 (.vreg d .int)
        (.vreg (aliasNum aliases nx) .int) (.vreg (aliasNum aliases ny) .int) := by
    change MInst.aluRRR (if signed then .sMulH else .uMulH) .size64
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int))
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg nx .int))
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg ny .int)) = _
    rw [fresh_reg bounded,resolve_vreg,resolve_vreg]; rfl
  refine ⟨upd ρ d (resX .size64 r),?_,?_,?_⟩
  · intro w
    have spec : ispec (.aluRRR (if signed then .sMulH else .uMulH) .size64 (.vreg d .int)
        (.vreg (aliasNum aliases nx) .int) (.vreg (aliasNum aliases ny) .int))
        [ρ (aliasNum aliases nx),ρ (aliasNum aliases ny)] w = some ([resX .size64 r],w,.next) := by
      cases signed <;> rfl
    obtain ⟨w',executed,world⟩ := refines _ _ _ _ _ spec
    refine ⟨w',?_,world⟩
    rw [code]
    simp only [seqRun,operands_aluRRR]
    have uses : vuses #[⟨d,.int,.def,.late,.reg⟩,⟨aliasNum aliases nx,.int,.use,.early,.reg⟩,
      ⟨aliasNum aliases ny,.int,.use,.early,.reg⟩] ρ = [ρ (aliasNum aliases nx),ρ (aliasNum aliases ny)] := rfl
    rw [uses,executed]; rfl
  · rw [upd_same]; exact value
  · intro n different; simp only [upd,different,ite_false]
end Backend.Stock.Proof.ScalarHighMul
