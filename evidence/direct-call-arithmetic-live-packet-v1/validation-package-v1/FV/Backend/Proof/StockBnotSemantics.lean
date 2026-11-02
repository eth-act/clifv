import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.IselFamAluBNotShift

namespace Backend.Stock.Proof.Bnot
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

/-- Mapped, final-alias-resolved scalar NOT computes the original unary value
and preserves every register except its fresh destination. -/
theorem stock_bnot_base_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {ty : Clif.Ty} (width : ty.width ≤ 64) {ctx : Ctx} {fr : Clif.Frame}
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {x nx d : Nat}
    (bounded : aliases.size ≤ d) (mapped : ctx.valueReg? x = some (.vreg nx .int))
    (held : ValuesHeld (fun z => z = x) ctx fr (fun k => ρ (aliasNum aliases k)))
    {u : BitVec ty.width} (source : fr.getAs x ty = .ok u) :
    ∃ ρ', PRun F isem
        [(MInst.aluRRR .orrNot (szOf ty.width) (.vreg d .int) .xzr (.vreg nx .int)).mapRegs
          (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bnot u⟩ (ρ' d) ∧ ∀ n, n ≠ d → ρ' n = ρ n := by
  have input := held.read rfl (getAs_ok source) mapped
  have codeEq : (MInst.aluRRR .orrNot (szOf ty.width) (.vreg d .int) .xzr (.vreg nx .int)).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .aluRRR .orrNot (szOf ty.width) (.vreg d .int) .xzr (.vreg (aliasNum aliases nx) .int) := by
    change MInst.aluRRR .orrNot (szOf ty.width)
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int)) .xzr
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg nx .int)) = _
    rw [fresh_reg bounded,resolve_vreg]
    rfl
  let r := resX (szOf ty.width) (0#(szOf ty.width).bits ||| ~~~(opnd (szOf ty.width) (ρ (aliasNum aliases nx))))
  refine ⟨upd ρ d r,?_,?_,?_⟩
  · rw [codeEq]
    exact prun_rr refines rfl (fun w => ispec_xzr_orrNot _ _ _ _ w) (prun_nil _)
  · rw [upd_same]
    change r.setWidth ty.width = ~~~u
    simpa only [BitVec.shiftLeft_zero] using not_shl_fin (szOf ty.width) (szOf_bits width)
      (ρ (aliasNum aliases nx)) u input 0
  · intro n different
    simp only [upd,different,ite_false]

/-- The fused LSL/NOT instruction executes through the actual mapped source;
the sunk shift result itself need not be materialized in the machine file. -/
theorem stock_bnot_shift_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {ty : Clif.Ty} (width : ty.width ≤ 64) {ctx : Ctx} {fr : Clif.Frame}
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {x nx d : Nat}
    (bounded : aliases.size ≤ d) (mapped : ctx.valueReg? x = some (.vreg nx .int))
    (held : ValuesHeld (fun z => z = x) ctx fr (fun k => ρ (aliasNum aliases k)))
    {u : BitVec ty.width} (source : fr.getAs x ty = .ok u) {sh : ShiftOpAndAmt}
    (lsl : sh.op = .lsl) (amount : sh.amt < ty.width) :
    ∃ ρ', PRun F isem
        [(MInst.aluRRRShift .orrNot (szOf ty.width) (.vreg d .int) .xzr (.vreg nx .int) sh).mapRegs
          (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bnot (u <<< sh.amt)⟩ (ρ' d) ∧ ∀ n, n ≠ d → ρ' n = ρ n := by
  cases sh with
  | mk op amt =>
    change op = .lsl at lsl
    subst op
    have input := held.read rfl (getAs_ok source) mapped
    have codeEq : (MInst.aluRRRShift .orrNot (szOf ty.width) (.vreg d .int) .xzr (.vreg nx .int) ⟨.lsl,amt⟩).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
        .aluRRRShift .orrNot (szOf ty.width) (.vreg d .int) .xzr (.vreg (aliasNum aliases nx) .int) ⟨.lsl,amt⟩ := by
      change MInst.aluRRRShift .orrNot (szOf ty.width)
        (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int)) .xzr
        (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg nx .int)) ⟨.lsl,amt⟩ = _
      rw [fresh_reg bounded,resolve_vreg]
      rfl
    let r := resX (szOf ty.width) (0#(szOf ty.width).bits ||| ~~~(opnd (szOf ty.width) (ρ (aliasNum aliases nx)) <<< amt))
    refine ⟨upd ρ d r,?_,?_,?_⟩
    · rw [codeEq]
      exact prun_rr refines rfl (fun w => ispec_orn_shift_fb (Nat.lt_of_lt_of_le amount (szOf_bits width))) (prun_nil _)
    · rw [upd_same]
      change r.setWidth ty.width = ~~~(u <<< amt)
      exact not_shl_fin (szOf ty.width) (szOf_bits width) _ _ input amt
    · intro n different
      simp only [upd,different,ite_false]

end Backend.Stock.Proof.Bnot
