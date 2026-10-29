module

public import FV.Backend.Proof.StockShiftBitfieldRhs

@[expose] public section

namespace Backend.Stock.Proof.ShiftBitfield
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- A resolved fused bitfield instruction implements the original shift pair,
and writes only its fresh result. Both counts retain their full original value. -/
theorem stock_bitfield_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (signed : Bool) {ty : Clif.Ty} (width : ty.width = 32 ∨ ty.width = 64)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {a b : Int} {x d : Nat}
    (bounded : aliases.size ≤ d) :
    ∃ ρ', PRun F isem
      [(fusedCode signed ty.width (.vreg d .int) (.vreg x .int) a b).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      (ρ' d).setWidth ty.width =
        (if signed then ((ρ (aliasNum aliases x)).setWidth ty.width <<< (u64 a % ty.width)).sshiftRight (u64 b % ty.width)
         else ((ρ (aliasNum aliases x)).setWidth ty.width <<< (u64 a % ty.width)) >>> (u64 b % ty.width)) ∧
      ∀ n,n ≠ d → ρ' n = ρ n := by
  have iw : IW ty.width := by rcases width with h | h <;> simp [IW,h]
  have bits : (szOf ty.width).bits = ty.width := by rcases width with h | h <;> simp [h,szOf,OperandSize.bits]
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none; rw [Array.getElem?_eq_none bounded]; rfl
  have code : (fusedCode signed ty.width (.vreg d .int) (.vreg x .int) a b).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      fusedCode signed ty.width (.vreg d .int) (.vreg (aliasNum aliases x) .int) a b := by
    unfold fusedCode
    change MInst.bitfieldMove _ _
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int))
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg x .int)) _ _ = _
    rw [resolve_vreg,resolve_vreg]
    change MInst.bitfieldMove _ _ (.vreg (aliasNum aliases d) .int) _ _ _ = _
    rw [fresh]
    rfl
  have ha : u64 a % ty.width < ty.width := Nat.mod_lt _ (by omega)
  have hb : u64 b % ty.width < ty.width := Nat.mod_lt _ (by omega)
  let r := bfmVal (fusedOp signed) (opnd (szOf ty.width) (ρ (aliasNum aliases x)))
    (bfmImmr ty.width (u64 a) (u64 b)) (ty.width-1-Nat.land (u64 a % 256) (ty.width-1))
  refine ⟨upd ρ d (resX (szOf ty.width) r),?_,?_,?_⟩
  · rw [code]
    apply prun_rr refines rfl _ (prun_nil _)
    intro world
    apply ispec_bfm_fb
    · unfold bfmImmr
      rw [land_mod256 iw,land_mod256 iw,bits]
      exact immr_lt ha hb
    · rw [land_mod256 iw,bits]; omega
  · rw [upd_same]
    dsimp only [r]
    simp only [bfmImmr,land_mod256 iw]
    rcases width with h32 | h64
    · rw [h32]
      have ha' : u64 a % 32 < 32 := by simpa only [h32] using ha
      have hb' : u64 b % 32 < 32 := by simpa only [h32] using hb
      cases signed
      · exact bfm_fin_u .size32 _ ha' hb'
      · exact bfm_fin_s .size32 _ ha' hb'
    · rw [h64]
      have ha' : u64 a % 64 < 64 := by simpa only [h64] using ha
      have hb' : u64 b % 64 < 64 := by simpa only [h64] using hb
      cases signed
      · exact bfm_fin_u .size64 _ ha' hb'
      · exact bfm_fin_s .size64 _ ha' hb'
  · intro n different; simp only [upd,different,ite_false]
end Backend.Stock.Proof.ShiftBitfield
