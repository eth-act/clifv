import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.IselCmpExt
import FV.Backend.Proof.IselFamALUAExt
namespace Backend.Stock.Proof.ScalarShift
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Low-bit preservation and zero/sign-extension are proved with ordinary
bit-vector resizing lemmas, without a new fixed-proof oracle dependency. -/
theorem stock_extend_holds (sg : Bool) {ty : Clif.Ty} (bits : BitVec ty.width)
    (width : ty.width ≤ 32) (to : Nat) (target : to = 32 ∨ to = 64) (fits : ty.width ≤ to)
    {x : CV} (held : VHolds ⟨ty,bits⟩ x) :
    ExtHolds sg to ⟨ty,bits⟩ (ofX (if sg then (((lo64 x).setWidth ty.width).signExtend to).setWidth 64
      else (((lo64 x).setWidth ty.width).setWidth to).setWidth 64)) := by
  have to64 : to ≤ 64 := by rcases target with rfl | rfl <;> decide
  have original : (lo64 x).setWidth ty.width = bits := by
    change (x.setWidth 64).setWidth ty.width = bits
    rw [BitVec.setWidth_setWidth_of_le _ (by omega)]
    exact held
  rw [original]
  constructor
  · unfold VHolds
    cases sg
    · simp only [Bool.false_eq_true,ite_false,ofX]
      rw [BitVec.setWidth_setWidth_of_le _ (by omega),BitVec.setWidth_setWidth_of_le _ (by omega),
        BitVec.setWidth_setWidth_of_le _ fits,BitVec.setWidth_eq]
    · simp only [ite_true,ofX]
      rw [BitVec.setWidth_setWidth_of_le _ (by omega),BitVec.setWidth_setWidth_of_le _ (by omega),
        setWidth_signExtend_of_le _ fits,BitVec.signExtend_eq]
  · intro _
    cases sg
    · simp only [Bool.false_eq_true,ite_false,lo64,ofX]
      rw [BitVec.setWidth_setWidth_of_le _ (by omega),BitVec.setWidth_setWidth_of_le _ (by omega),
        BitVec.setWidth_setWidth_of_le _ to64,BitVec.setWidth_eq]
    · simp only [ite_true,lo64,ofX]
      rw [BitVec.setWidth_setWidth_of_le _ (by omega),BitVec.setWidth_setWidth_of_le _ (by omega),
        BitVec.setWidth_setWidth_of_le _ to64,BitVec.setWidth_eq]

/-- Existing32/64-bit registers satisfy the exact extension guarantee of the
pass-through rules, with no assumption about unobserved upper bits. -/
theorem stock_ext_passthrough_holds (sg : Bool) {ty : Clif.Ty} {bits : BitVec ty.width} {to : Nat}
    (pass : ty = .i64 ∨ (ty = .i32 ∧ to = 32)) {x : CV} (held : VHolds ⟨ty,bits⟩ x) :
    ExtHolds sg to ⟨ty,bits⟩ x := by
  refine ⟨held,?_⟩
  rcases pass with rfl | ⟨rfl,rfl⟩
  · intro impossible
    change 64 ≤ 32 at impossible
    omega
  · intro _
    have original : (lo64 x).setWidth 32 = bits := by
      change (x.setWidth 64).setWidth 32 = bits
      rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
      exact held
    rw [original]
    cases sg
    · exact (BitVec.setWidth_eq bits).symm
    · exact (BitVec.signExtend_eq bits).symm

/-- The mapped extension instruction through final aliases establishes the
original operand's extended bits and changes only its fresh destination. -/
theorem stock_extend_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (sg : Bool) {ty : Clif.Ty} (sourceWidth : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32)
    {to : Nat} (target : to = 32 ∨ to = 64) (grows : ty.width < to)
    {ctx : Ctx} {fr : Clif.Frame} {aliases : Array (Option Nat)} {ρ : Nat → CV} {x nx d : Nat}
    (bounded : aliases.size ≤ d) (mapped : ctx.valueReg? x = some (.vreg nx .int))
    (held : ValuesHeld (fun z => z = x) ctx fr (fun k => ρ (aliasNum aliases k)))
    {bits : BitVec ty.width} (source : fr.getAs x ty = .ok bits) :
    ∃ ρ', PRun F isem
      [(MInst.extend (.vreg d .int) (.vreg nx .int) sg ty.width to).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      ExtHolds sg to ⟨ty,bits⟩ (ρ' d) ∧ ∀ n,n ≠ d → ρ' n = ρ n := by
  have input := held.read rfl (getAs_ok source) mapped
  let value := ofX (if sg then (((lo64 (ρ (aliasNum aliases nx))).setWidth ty.width).signExtend to).setWidth 64
    else (((lo64 (ρ (aliasNum aliases nx))).setWidth ty.width).setWidth to).setWidth 64)
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]
    rfl
  have code : (MInst.extend (.vreg d .int) (.vreg nx .int) sg ty.width to).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .extend (.vreg d .int) (.vreg (aliasNum aliases nx) .int) sg ty.width to := by
    change MInst.extend (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int))
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg nx .int)) sg ty.width to = _
    rw [resolve_vreg,resolve_vreg]
    change MInst.extend (.vreg (aliasNum aliases d) .int) (.vreg (aliasNum aliases nx) .int) sg ty.width to = _
    rw [fresh]
  refine ⟨upd ρ d value,?_,?_,?_⟩
  · intro w
    obtain ⟨w',executed,world⟩ := refines _ _ _ _ _
      (ispec_extend (d := d) (rn := .vreg (aliasNum aliases nx) .int) (sg := sg) (x := ρ (aliasNum aliases nx))
        (w := w) sourceWidth target grows)
    refine ⟨w',?_,world⟩
    rw [code]
    simp only [seqRun,operands_extend']
    have uses : vuses #[⟨d,.int,.def,.late,.reg⟩,⟨aliasNum aliases nx,.int,.use,.early,.reg⟩] ρ =
      [ρ (aliasNum aliases nx)] := rfl
    rw [uses,executed]
    rfl
  · rw [upd_same]
    exact stock_extend_holds sg bits (by rcases sourceWidth with h | h | h <;> omega) to target (by omega) input
  · intro n different; simp only [upd,different,ite_false]
end Backend.Stock.Proof.ScalarShift
