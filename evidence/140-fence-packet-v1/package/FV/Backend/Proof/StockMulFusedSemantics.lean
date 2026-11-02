import FV.Backend.Proof.IselFamALUAMul
import FV.Backend.Proof.StockMulFusedRhs
namespace Backend.Stock.Proof.ScalarMul.Fused
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The actual resolved multiply-add/subtract template establishes the original
three-operand value and preserves every register outside its fresh destination. -/
theorem stock_mul_fused_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (fusion : Fusion) {ty : Clif.Ty} (width : ty.width ≤ 64)
    {ctx : Ctx} {fr : Clif.Frame} {aliases : Array (Option Nat)} {ρ : Nat → CV}
    {a b x na nb nx d : Nat} (bounded : aliases.size ≤ d)
    (ma : ctx.valueReg? a = some (.vreg na .int)) (mb : ctx.valueReg? b = some (.vreg nb .int))
    (mx : ctx.valueReg? x = some (.vreg nx .int))
    (held : ValuesHeld (fun z => z = a ∨ z = b ∨ z = x) ctx fr (fun k => ρ (aliasNum aliases k)))
    {u v t : BitVec ty.width} (getA : fr.getAs a ty = .ok u) (getB : fr.getAs b ty = .ok v)
    (getX : fr.getAs x ty = .ok t) :
    ∃ ρ', PRun F isem
      [(MInst.aluRRRR fusion.op (szOf ty.width) (.vreg d .int) (.vreg na .int) (.vreg nb .int) (.vreg nx .int)).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,if fusion.subtract then t-u*v else t+u*v⟩ (ρ' d) ∧ ∀ n,n ≠ d → ρ' n = ρ n := by
  have aValue := held.read (Or.inl rfl) (getAs_ok getA) ma
  have bValue := held.read (Or.inr (Or.inl rfl)) (getAs_ok getB) mb
  have xValue := held.read (Or.inr (Or.inr rfl)) (getAs_ok getX) mx
  let r := if fusion.subtract then opnd (szOf ty.width) (ρ (aliasNum aliases nx)) -
      opnd (szOf ty.width) (ρ (aliasNum aliases na)) * opnd (szOf ty.width) (ρ (aliasNum aliases nb))
    else opnd (szOf ty.width) (ρ (aliasNum aliases nx)) +
      opnd (szOf ty.width) (ρ (aliasNum aliases na)) * opnd (szOf ty.width) (ρ (aliasNum aliases nb))
  have computed : mulAddVal fusion.op (opnd (szOf ty.width) (ρ (aliasNum aliases na)))
      (opnd (szOf ty.width) (ρ (aliasNum aliases nb))) (opnd (szOf ty.width) (ρ (aliasNum aliases nx))) = some r := by
    cases fusion <;> rfl
  have value : VHolds ⟨ty,if fusion.subtract then t-u*v else t+u*v⟩ (resX (szOf ty.width) r) := by
    cases fusion
    · exact holds_madd (szOf_bits width) aValue bValue xValue
    · exact holds_madd (szOf_bits width) aValue bValue xValue
    · exact holds_msub (szOf_bits width) aValue bValue xValue
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]
    rfl
  have code : (MInst.aluRRRR fusion.op (szOf ty.width) (.vreg d .int) (.vreg na .int) (.vreg nb .int) (.vreg nx .int)).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .aluRRRR fusion.op (szOf ty.width) (.vreg d .int) (.vreg (aliasNum aliases na) .int)
        (.vreg (aliasNum aliases nb) .int) (.vreg (aliasNum aliases nx) .int) := by
    change MInst.aluRRRR fusion.op (szOf ty.width)
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int))
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg na .int))
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg nb .int))
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg nx .int)) = _
    rw [resolve_vreg,resolve_vreg,resolve_vreg,resolve_vreg]
    change MInst.aluRRRR fusion.op (szOf ty.width) (.vreg (aliasNum aliases d) .int)
      (.vreg (aliasNum aliases na) .int) (.vreg (aliasNum aliases nb) .int) (.vreg (aliasNum aliases nx) .int) = _
    rw [fresh]
  refine ⟨upd ρ d (resX (szOf ty.width) r),?_,?_,?_⟩
  · intro w
    obtain ⟨w',executed,world⟩ := refines _ _ _ _ _
      (ispec_aluRRRR (d := d) (rn := .vreg (aliasNum aliases na) .int)
        (rm := .vreg (aliasNum aliases nb) .int) (ra := .vreg (aliasNum aliases nx) .int) (w := w) computed)
    refine ⟨w',?_,world⟩
    rw [code]
    simp only [seqRun,operands_aluRRRR]
    have uses : vuses #[⟨d,.int,.def,.late,.reg⟩,⟨aliasNum aliases na,.int,.use,.early,.reg⟩,
      ⟨aliasNum aliases nb,.int,.use,.early,.reg⟩,⟨aliasNum aliases nx,.int,.use,.early,.reg⟩] ρ =
      [ρ (aliasNum aliases na),ρ (aliasNum aliases nb),ρ (aliasNum aliases nx)] := rfl
    rw [uses,executed]
    rfl
  · rw [upd_same]; exact value
  · intro n different; simp only [upd,different,ite_false]
end Backend.Stock.Proof.ScalarMul.Fused
