import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.IselFamAluBUnary
namespace Backend.Stock.Proof.Neg
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private theorem fresh_reg {aliases : Array (Option Nat)} {d : Nat} (bounded : aliases.size ≤ d) :
    Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int) = .vreg d .int := by
  rw [resolve_vreg]
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]
    rfl
  change Reg.vreg (aliasNum aliases d) .int = _
  rw [fresh]

/-- Mapped, final-alias-resolved scalar negation computes the original unary value
and preserves every register except its fresh destination. -/
theorem stock_neg_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {ty : Clif.Ty} (width : ty.width ≤ 64) {ctx : Ctx} {fr : Clif.Frame}
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {x nx d : Nat}
    (bounded : aliases.size ≤ d) (mapped : ctx.valueReg? x = some (.vreg nx .int))
    (held : ValuesHeld (fun z => z = x) ctx fr (fun k => ρ (aliasNum aliases k)))
    {u : BitVec ty.width} (source : fr.getAs x ty = .ok u) :
    ∃ ρ', PRun F isem
        [(MInst.aluRRR .sub (szOf ty.width) (.vreg d .int) .xzr (.vreg nx .int)).mapRegs
          (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .ineg u⟩ (ρ' d) ∧ ∀ n, n ≠ d → ρ' n = ρ n := by
  have input := held.read rfl (getAs_ok source) mapped
  have codeEq : (MInst.aluRRR .sub (szOf ty.width) (.vreg d .int) .xzr (.vreg nx .int)).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .aluRRR .sub (szOf ty.width) (.vreg d .int) .xzr (.vreg (aliasNum aliases nx) .int) := by
    change MInst.aluRRR .sub (szOf ty.width)
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int)) .xzr
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg nx .int)) = _
    rw [fresh_reg bounded,resolve_vreg]
    rfl
  let r := resX (szOf ty.width) (0#(szOf ty.width).bits - opnd (szOf ty.width) (ρ (aliasNum aliases nx)))
  refine ⟨upd ρ d r,?_,?_,?_⟩
  · rw [codeEq]
    exact prun_rr refines rfl (fun w => ispec_xzr_sub _ _ _ _ w) (prun_nil _)
  · rw [upd_same]
    change r.setWidth ty.width = Clif.Sem.unary .ineg u
    have small := szOf_bits width
    have target := opSize_bits_le (szOf ty.width)
    rw [resX_setWidth small target,setWidth_sub_of_le small,BitVec.setWidth_zero,
      opnd_setWidth small target,input]
    rfl
  · intro n different
    simp only [upd,different,ite_false]


end Backend.Stock.Proof.Neg
