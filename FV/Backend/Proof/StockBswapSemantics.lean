import FV.Backend.Proof.StockBswapRhs
namespace Backend.Stock.Proof.ScalarBit
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxHeartbeats 4000000
private theorem rev16_low (x : BitVec 32) :
    (rev16w x).setWidth 16 = Clif.Sem.bswap (x.setWidth 16) := by
  simp only [Clif.Sem.bswap,show List.range (16/8) = [0,1] from rfl,List.foldl_cons,List.foldl_nil]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i bound
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [rev16w,Clif.Sem.bswap,BitVec.getLsbD_setWidth,BitVec.getLsbD_or,BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight]
/-- REV16 computes the original source halfword byte swap independently of
all upper bits in the mapped machine register. -/
theorem stock_bswap16_bits {x : CV} {u : BitVec 16} (held : VHolds ⟨.i16,u⟩ x) :
    VHolds ⟨.i16,Clif.Sem.unary .bswap u⟩ (resX .size32 (rev16w (opnd .size32 x))) := by
  change (resX .size32 (rev16w (opnd .size32 x))).setWidth 16 = Clif.Sem.bswap u
  have original : (opnd .size32 x).setWidth 16 = u :=
    (opnd_setWidth (sz := .size32) (w := 16) (by decide) (by decide) x).trans held
  have output := resX_setWidth (sz := .size32) (w := 16) (by decide) (by decide) (rev16w (opnd .size32 x))
  exact output.trans ((rev16_low (opnd .size32 x)).trans (congrArg Clif.Sem.bswap original))
private theorem bswap_equal_width {n w : Nat} (same : n = w) (x : BitVec n) :
    (Clif.Sem.bswap x).setWidth w = Clif.Sem.bswap (x.setWidth w) := by
  cases same
  simp
/-- Word/doubleword byte-swap values use the exact original operand width. -/
theorem stock_bswap_wide_bits {ty : Clif.Ty} (width : ty.width = 32 ∨ ty.width = 64)
    {x : CV} {u : BitVec ty.width} (held : VHolds ⟨ty,u⟩ x) :
    VHolds ⟨ty,Clif.Sem.unary .bswap u⟩ (resX (szOf ty.width) (Clif.Sem.bswap (opnd (szOf ty.width) x))) := by
  have small : ty.width ≤ 64 := by rcases width with h | h <;> omega
  have same : (szOf ty.width).bits = ty.width := by rcases width with h | h <;> simp [szOf,h,OperandSize.bits]
  change (resX (szOf ty.width) (Clif.Sem.bswap (opnd (szOf ty.width) x))).setWidth ty.width = Clif.Sem.bswap u
  rw [resX_setWidth (szOf_bits small) (opSize_bits_le (szOf ty.width)),
    bswap_equal_width same,opnd_setWidth (szOf_bits small) (opSize_bits_le (szOf ty.width)),held]
private theorem fresh_reg {aliases : Array (Option Nat)} {d : Nat} (bounded : aliases.size ≤ d) :
    Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int) = .vreg d .int := by
  rw [resolve_vreg]
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]
    rfl
  change Reg.vreg (aliasNum aliases d) .int = _
  rw [fresh]

private theorem mapped_code {aliases : Array (Option Nat)} {d x : Nat} (bounded : aliases.size ≤ d)
    (op : BitOp) (sz : OperandSize) :
    (MInst.bitRR op sz (.vreg d .int) (.vreg x .int)).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .bitRR op sz (.vreg d .int) (.vreg (aliasNum aliases x) .int) := by
  change MInst.bitRR op sz
    (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int))
    (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg x .int)) = _
  rw [fresh_reg bounded,resolve_vreg]; rfl
/-- Actual scalar byte-swap templates compute original values through final
aliases and preserve every register except the fresh destination. -/
theorem stock_bswap_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {ty : Clif.Ty} (width : ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    {ctx : Ctx} {fr : Clif.Frame} {aliases : Array (Option Nat)} {ρ : Nat → CV} {x nx d : Nat}
    (bounded : aliases.size ≤ d) (mapped : ctx.valueReg? x = some (.vreg nx .int))
    (held : ValuesHeld (fun z => z = x) ctx fr (fun k => ρ (aliasNum aliases k)))
    {u : BitVec ty.width} (source : fr.getAs x ty = .ok u) :
    ∃ ρ', PRun F isem
        [(MInst.bitRR (bswapOp ty.width) (szOf ty.width) (.vreg d .int) (.vreg nx .int)).mapRegs
          (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bswap u⟩ (ρ' d) ∧ ∀ n,n ≠ d → ρ' n = ρ n := by
  have input := held.read rfl (getAs_ok source) mapped
  rcases width with half | word | double
  · obtain rfl := ty_eq_of_width (ty' := .i16) half (by decide)
    let r := resX .size32 (rev16w (opnd .size32 (ρ (aliasNum aliases nx))))
    refine ⟨upd ρ d r,?_,?_,?_⟩
    · rw [mapped_code bounded]
      simp only [bswapOp,szOf,Clif.Ty.width,Nat.reduceEqDiff,ite_true,ite_false]
      exact prun_rr refines rfl (fun _ => rfl) (prun_nil _)
    · rw [upd_same]
      exact stock_bswap16_bits input
    · intro n different
      simp only [upd,different,ite_false]
  · obtain rfl := ty_eq_of_width (ty' := .i32) word (by decide)
    let r := resX .size32 (Clif.Sem.bswap (opnd .size32 (ρ (aliasNum aliases nx))))
    refine ⟨upd ρ d r,?_,?_,?_⟩
    · rw [mapped_code bounded]
      simp only [bswapOp,szOf,Clif.Ty.width,Nat.reduceEqDiff,ite_true,ite_false]
      exact prun_rr refines rfl (fun _ => rfl) (prun_nil _)
    · rw [upd_same]
      exact stock_bswap_wide_bits (Or.inl rfl) input
    · intro n different
      simp only [upd,different,ite_false]
  · obtain rfl := ty_eq_of_width (ty' := .i64) double (by decide)
    let r := resX .size64 (Clif.Sem.bswap (opnd .size64 (ρ (aliasNum aliases nx))))
    refine ⟨upd ρ d r,?_,?_,?_⟩
    · rw [mapped_code bounded]
      simp only [bswapOp,szOf,Clif.Ty.width,Nat.reduceEqDiff,ite_true,ite_false]
      exact prun_rr refines rfl (fun _ => rfl) (prun_nil _)
    · rw [upd_same]
      exact stock_bswap_wide_bits (Or.inr rfl) input
    · intro n different
      simp only [upd,different,ite_false]
end Backend.Stock.Proof.ScalarBit
