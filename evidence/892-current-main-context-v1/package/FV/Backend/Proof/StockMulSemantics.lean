import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.IselFamALUAMul
namespace Backend.Stock.Proof.ScalarMul
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Actual multiply emission through final aliases computes the original low
bits and writes only its fresh destination, even when source IDs are sparse. -/
theorem stock_mul_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {ty : Clif.Ty} (width : ty.width ≤ 64) {ctx : Ctx} {fr : Clif.Frame}
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {x y nx ny d : Nat}
    (bounded : aliases.size ≤ d)
    (mappedX : ctx.valueReg? x = some (.vreg nx .int)) (mappedY : ctx.valueReg? y = some (.vreg ny .int))
    (held : ValuesHeld (fun z => z = x ∨ z = y) ctx fr (fun k => ρ (aliasNum aliases k)))
    {u v : BitVec ty.width} (sourceX : fr.getAs x ty = .ok u) (sourceY : fr.getAs y ty = .ok v) :
    ∃ ρ', PRun F isem
      [(MInst.aluRRRR .mAdd (szOf ty.width) (.vreg d .int) (.vreg nx .int) (.vreg ny .int) .xzr).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary .imul u v⟩ (ρ' d) ∧ ∀ n,n ≠ d → ρ' n = ρ n := by
  have xValue := held.read (Or.inl rfl) (getAs_ok sourceX) mappedX
  have yValue := held.read (Or.inr rfl) (getAs_ok sourceY) mappedY
  let r := (0 : BitVec (szOf ty.width).bits) + opnd (szOf ty.width) (ρ (aliasNum aliases nx)) *
    opnd (szOf ty.width) (ρ (aliasNum aliases ny))
  have value := holds_mul0 (szOf_bits width) xValue yValue
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]
    rfl
  have code : (MInst.aluRRRR .mAdd (szOf ty.width) (.vreg d .int) (.vreg nx .int) (.vreg ny .int) .xzr).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .aluRRRR .mAdd (szOf ty.width) (.vreg d .int) (.vreg (aliasNum aliases nx) .int)
        (.vreg (aliasNum aliases ny) .int) .xzr := by
    change MInst.aluRRRR .mAdd (szOf ty.width)
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int))
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg nx .int))
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg ny .int)) .xzr = _
    rw [resolve_vreg,resolve_vreg,resolve_vreg]
    change MInst.aluRRRR .mAdd (szOf ty.width) (.vreg (aliasNum aliases d) .int)
      (.vreg (aliasNum aliases nx) .int) (.vreg (aliasNum aliases ny) .int) .xzr = _
    rw [fresh]
  refine ⟨upd ρ d (resX (szOf ty.width) r),?_,?_,?_⟩
  · intro w
    obtain ⟨w',executed,world⟩ := refines _ _ _ _ _
      (ispec_aluRRRR_xzr (op := .mAdd) (sz := szOf ty.width) (d := d)
        (x := aliasNum aliases nx) (y := aliasNum aliases ny) (w := w) (r := r) rfl)
    refine ⟨w',?_,world⟩
    rw [code]
    simp only [seqRun,operands_aluRRRR_xzr]
    have uses : vuses #[⟨d,.int,.def,.late,.reg⟩,⟨aliasNum aliases nx,.int,.use,.early,.reg⟩,
      ⟨aliasNum aliases ny,.int,.use,.early,.reg⟩] ρ = [ρ (aliasNum aliases nx),ρ (aliasNum aliases ny)] := rfl
    rw [uses,executed]
    rfl
  · rw [upd_same]
    exact value
  · intro n different; simp only [upd,different,ite_false]
end Backend.Stock.Proof.ScalarMul
