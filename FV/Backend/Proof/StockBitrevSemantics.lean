import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.IselFamAluBShiftTerms
import FV.Backend.Proof.StockBitrevForms
namespace Backend.Stock.Proof.ScalarBit
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private theorem reverse_low {w n : Nat} (h : w ≤ n) (x : BitVec n) :
    (x.reverse >>> (n-w)).setWidth w = (x.setWidth w).reverse := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  have shifted : n-w+i < n := by omega
  have index : n-1-(n-w+i) = w-1-i := by omega
  simp only [BitVec.getLsbD_setWidth,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_reverse,
    BitVec.getMsbD_eq_getLsbD,hi,shifted,decide_true,Bool.true_and,index]
  simp only [show w-1-i < w by omega,decide_true,Bool.true_and]
/-- Reversal followed by its narrow logical shift computes the original low
source bits independently of dirty upper bits in the mapped machine register. -/
theorem stock_bitrev_narrow_bits {ty : Clif.Ty} (width : ty.width ≤ 32)
    {u : BitVec ty.width} {x : CV} (held : VHolds ⟨ty,u⟩ x) :
    VHolds ⟨ty,Clif.Sem.unary .bitrev u⟩
      (resX .size32 ((opnd .size32 x).reverse >>> (32-ty.width))) := by
  change (resX .size32 ((opnd .size32 x).reverse >>> (32-ty.width))).setWidth ty.width = u.reverse
  rw [resX_setWidth width (by decide)]
  have low := reverse_low width (opnd .size32 x)
  have original : (opnd .size32 x).setWidth ty.width = u := by
    rw [opnd_setWidth width (by decide)]
    exact held
  exact low.trans (congrArg BitVec.reverse original)
private theorem fresh_reg {aliases : Array (Option Nat)} {d : Nat} (bounded : aliases.size ≤ d) :
    Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int) = .vreg d .int := by
  rw [resolve_vreg]
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none; rw [Array.getElem?_eq_none bounded]; rfl
  change Reg.vreg (aliasNum aliases d) .int = _
  rw [fresh]
private theorem mapped_bit {aliases : Array (Option Nat)} {d x : Nat} (bounded : aliases.size ≤ d) (sz : OperandSize) :
    (MInst.bitRR .rbit sz (.vreg d .int) (.vreg x .int)).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .bitRR .rbit sz (.vreg d .int) (.vreg (aliasNum aliases x) .int) := by
  change MInst.bitRR .rbit sz
    (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int))
    (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg x .int)) = _
  rw [fresh_reg bounded,resolve_vreg]; rfl
private theorem mapped_shift {aliases : Array (Option Nat)} {d : Nat} (bounded : aliases.size ≤ d) (amount : Nat) :
    (MInst.aluRRImmShift .lsr .size32 (.vreg (d+1) .int) (.vreg d .int) amount).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .aluRRImmShift .lsr .size32 (.vreg (d+1) .int) (.vreg d .int) amount := by
  change MInst.aluRRImmShift .lsr .size32
    (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg (d+1) .int))
    (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int)) amount = _
  rw [fresh_reg (by omega : aliases.size ≤ d+1),fresh_reg bounded]

private theorem reverse_equal_width {n w : Nat} (same : n = w) (x : BitVec n) :
    x.reverse.setWidth w = (x.setWidth w).reverse := by
  cases same
  simp
private theorem narrow_machine {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {ty : Clif.Ty} (width : ty.width = 8 ∨ ty.width = 16)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {d x : Nat} (bounded : aliases.size ≤ d)
    {u : BitVec ty.width} (held : VHolds ⟨ty,u⟩ (ρ (aliasNum aliases x))) :
    ∃ ρ', PRun F isem
      ([MInst.bitRR .rbit .size32 (.vreg d .int) (.vreg x .int),
        .aluRRImmShift .lsr .size32 (.vreg (d+1) .int) (.vreg d .int) (32-ty.width)].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bitrev u⟩ (ρ' (d+1)) ∧
      ∀ n,n ≠ d → n ≠ d+1 → ρ' n = ρ n := by
  have small : ty.width ≤ 32 := by rcases width with h | h <;> omega
  have fits : 32-ty.width < OperandSize.size32.bits := by rcases width with h | h <;> simp [OperandSize.bits] <;> omega
  let r0 := resX .size32 (opnd .size32 (ρ (aliasNum aliases x))).reverse
  let mid := upd ρ d r0
  let r1 := resX .size32 (opnd .size32 (mid d) >>> (32-ty.width))
  refine ⟨upd mid (d+1) r1,?_,?_,?_⟩
  · simp only [List.map_cons,List.map_nil,mapped_bit bounded,mapped_shift bounded]
    exact prun_rr refines rfl (fun _ => rfl) (prun_rr refines rfl (fun w => ispec_imm_shift_fb (w := w) (by simp [IsShift]) fits) (prun_nil _))
  · rw [upd_same]
    have bits := stock_bitrev_narrow_bits small held
    change VHolds _ (resX .size32 (opnd .size32 (upd ρ d r0 d) >>> (32-ty.width)))
    rw [upd_same]
    dsimp only [r0]
    rw [opnd_resX]
    exact bits
  · intro n first second
    simp only [mid,upd,first,second,ite_false]
private theorem wide_machine {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {ty : Clif.Ty} (width : ty.width = 32 ∨ ty.width = 64)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {d x : Nat} (bounded : aliases.size ≤ d)
    {u : BitVec ty.width} (held : VHolds ⟨ty,u⟩ (ρ (aliasNum aliases x))) :
    ∃ ρ', PRun F isem
      [(MInst.bitRR .rbit (szOf ty.width) (.vreg d .int) (.vreg x .int)).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bitrev u⟩ (ρ' d) ∧ ∀ n,n ≠ d → ρ' n = ρ n := by
  let r := resX (szOf ty.width) (opnd (szOf ty.width) (ρ (aliasNum aliases x))).reverse
  refine ⟨upd ρ d r,?_,?_,?_⟩
  · rw [mapped_bit bounded]
    exact prun_rr refines rfl (fun _ => rfl) (prun_nil _)
  · rw [upd_same]
    have small : ty.width ≤ 64 := by rcases width with h | h <;> omega
    have same : (szOf ty.width).bits = ty.width := by rcases width with h | h <;> simp [szOf,h,OperandSize.bits]
    change r.setWidth ty.width = u.reverse
    dsimp only [r]
    rw [resX_setWidth (szOf_bits small) (opSize_bits_le (szOf ty.width)),
      reverse_equal_width same,opnd_setWidth (szOf_bits small) (opSize_bits_le (szOf ty.width)),held]
  · intro n different
    simp only [upd,different,ite_false]
/-- Every scalar bit-reversal template computes the original source value
through final aliases, preserving all registers outside its actual allocation. -/
theorem stock_bitrev_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {ty : Clif.Ty} (width : IW ty.width) {ctx : Ctx} {fr : Clif.Frame}
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {x nx d : Nat}
    (bounded : aliases.size ≤ d) (mapped : ctx.valueReg? x = some (.vreg nx .int))
    (held : ValuesHeld (fun z => z = x) ctx fr (fun k => ρ (aliasNum aliases k)))
    {u : BitVec ty.width} (source : fr.getAs x ty = .ok u) :
    ∃ ρ', PRun F isem ((bitrevCode ty.width d nx).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bitrev u⟩ (ρ' (bitrevResult ty.width d)) ∧
      ∀ n,n < d ∨ d+bitrevAlloc ty.width ≤ n → ρ' n = ρ n := by
  have input := held.read rfl (getAs_ok source) mapped
  by_cases narrow : ty.width = 8 ∨ ty.width = 16
  · obtain ⟨ρ',execution,value,kept⟩ := narrow_machine refines narrow bounded input
    refine ⟨ρ',?_,?_,?_⟩
    · simpa only [bitrevCode,narrow,ite_true] using execution
    · simpa only [bitrevResult,narrow,ite_true] using value
    · intro n outside
      simp only [bitrevAlloc,narrow,ite_true] at outside
      exact kept n (by omega) (by omega)
  · have wide : ty.width = 32 ∨ ty.width = 64 := by rcases width with h | h | h | h <;> simp_all
    obtain ⟨ρ',execution,value,kept⟩ := wide_machine refines wide bounded input
    refine ⟨ρ',?_,?_,?_⟩
    · simpa only [bitrevCode,narrow,ite_false,List.map_cons,List.map_nil] using execution
    · simpa only [bitrevResult,narrow,ite_false] using value
    · intro n outside
      simp only [bitrevAlloc,narrow,ite_false] at outside
      exact kept n (by omega)
end Backend.Stock.Proof.ScalarBit
