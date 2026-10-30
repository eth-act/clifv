import FV.Backend.Proof.IselCmpExt
import FV.Backend.Proof.IselFamALUA
import FV.Backend.Proof.StockCountMath
import FV.Backend.Proof.StockCountRhs
import FV.Backend.Proof.StockCountForms
namespace Backend.Stock.Proof.ScalarCount
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private theorem fresh_reg {aliases : Array (Option Nat)} {d : Nat} (bounded : aliases.size ≤ d) :
    Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int) = .vreg d .int := by
  rw [resolve_vreg]
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none; rw [Array.getElem?_eq_none bounded]; rfl
  change Reg.vreg (aliasNum aliases d) .int = _
  rw [fresh]
private theorem mapped_bit {aliases : Array (Option Nat)} {d x : Nat}
    (bounded : aliases.size ≤ d) (op : BitOp) (sz : OperandSize) :
    (MInst.bitRR op sz (.vreg d .int) (.vreg x .int)).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .bitRR op sz (.vreg d .int) (.vreg (aliasNum aliases x) .int) := by
  change MInst.bitRR op sz
    (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int))
    (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg x .int)) = _
  rw [fresh_reg bounded,resolve_vreg]; rfl
private theorem count_equal_width {n w : Nat} (same : n = w) (trailing : Bool) (x : BitVec n) :
    (if trailing then x.reverse.clz else x.clz).setWidth w =
      Clif.Sem.unary (countOp trailing) (x.setWidth w) := by
  cases same
  cases trailing <;> simp [countOp,Clif.Sem.unary,Clif.Sem.clz,Clif.Sem.ctz,BitVec.ctz_eq_reverse_clz]
/-- The wide count templates execute through final aliases and write only
their one or two allocated registers. -/
theorem stock_count_wide_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (trailing : Bool) {ty : Clif.Ty}
    (width : ty.width = 32 ∨ ty.width = 64)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {d x : Nat}
    (bounded : aliases.size ≤ d) {u : BitVec ty.width}
    (held : VHolds ⟨ty,u⟩ (ρ (aliasNum aliases x))) :
    ∃ ρ', PRun F isem ((countCode trailing ty.width d x).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary (countOp trailing) u⟩
        (ρ' (countResult trailing ty.width d)) ∧
      ∀ n,n < d ∨ d+countAlloc trailing ty.width ≤ n → ρ' n = ρ n := by
  have narrow : ¬ (ty.width = 8 ∨ ty.width = 16) := by rcases width with h | h <;> omega
  have small : ty.width ≤ 64 := by rcases width with h | h <;> omega
  have same : (szOf ty.width).bits = ty.width := by
    rcases width with h | h <;> simp [szOf,h,OperandSize.bits]
  have input : (opnd (szOf ty.width) (ρ (aliasNum aliases x))).setWidth ty.width = u := by
    rw [opnd_setWidth (szOf_bits small) (opSize_bits_le (szOf ty.width))]
    exact held
  cases trailing
  · let r := resX (szOf ty.width) (opnd (szOf ty.width) (ρ (aliasNum aliases x))).clz
    refine ⟨upd ρ d r,?_,?_,?_⟩
    · simp only [countCode,narrow,ite_false,Bool.false_eq_true,List.map_cons,List.map_nil,mapped_bit bounded]
      exact prun_rr refines rfl (fun _ => rfl) (prun_nil _)
    · simp only [countResult,countAlloc,narrow,ite_false,Bool.false_eq_true,Nat.add_sub_cancel,upd_same]
      change r.setWidth ty.width = _
      dsimp only [r]
      rw [resX_setWidth (szOf_bits small) (opSize_bits_le (szOf ty.width))]
      exact (count_equal_width same false _).trans (congrArg (Clif.Sem.unary (countOp false)) input)
    · intro n outside
      simp only [countAlloc,narrow,ite_false,Bool.false_eq_true] at outside
      simp only [upd,show n ≠ d by omega,ite_false]
  · let r0 := resX (szOf ty.width) (opnd (szOf ty.width) (ρ (aliasNum aliases x))).reverse
    let mid := upd ρ d r0
    let r1 := resX (szOf ty.width) (opnd (szOf ty.width) (mid d)).clz
    refine ⟨upd mid (d+1) r1,?_,?_,?_⟩
    · have alias : aliasNum aliases d = d := by
        apply chaseF_none; rw [Array.getElem?_eq_none bounded]; rfl
      simp only [countCode,narrow,ite_false,ite_true,List.map_cons,List.map_nil,
        mapped_bit bounded,mapped_bit (by omega : aliases.size ≤ d+1),alias]
      exact prun_rr refines rfl (fun _ => rfl) (prun_rr refines rfl (fun _ => rfl) (prun_nil _))
    · simp only [countResult,countAlloc,narrow,ite_false,ite_true,
        show d+2-1 = d+1 by omega,upd_same]
      change r1.setWidth ty.width = _
      dsimp only [r1,mid]
      rw [upd_same]
      dsimp only [r0]
      rw [opnd_resX,resX_setWidth (szOf_bits small) (opSize_bits_le (szOf ty.width))]
      exact (count_equal_width same true _).trans (congrArg (Clif.Sem.unary (countOp true)) input)
    · intro n outside
      simp only [countAlloc,narrow,ite_false,ite_true] at outside
      simp only [mid,upd,show n ≠ d by omega,show n ≠ d+1 by omega,ite_false]
private theorem mapped_narrow {aliases : Array (Option Nat)} {d x : Nat}
    (bounded : aliases.size ≤ d) (trailing : Bool) (w : Nat) :
    ((countCode trailing w d x).map
      (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) =
      countCode trailing w d (aliasNum aliases x) := by
  have a : aliasNum aliases d = d := by
    apply chaseF_none; rw [Array.getElem?_eq_none bounded]; rfl
  have b : aliasNum aliases (d+1) = d+1 := by
    apply chaseF_none; rw [Array.getElem?_eq_none (by omega : aliases.size ≤ d+1)]; rfl
  have c : aliasNum aliases (d+2) = d+2 := by
    apply chaseF_none; rw [Array.getElem?_eq_none (by omega : aliases.size ≤ d+2)]; rfl
  simp only [aliasNum] at a b c
  unfold countCode
  split <;> cases trailing <;>
    simp only [ite_false,ite_true,Bool.false_eq_true,List.map_cons,List.map_nil,
      MInst.mapRegs,resolve_vreg,a,b,c]
  all_goals rfl
private theorem sentinel_mask {w : Nat} (width : w = 8 ∨ w = 16) :
    BitVec.ofNat 32 (2^(32-w-1)) = (1#32 <<< (32-w-1)) := by
  rcases width with rfl | rfl <;> decide +kernel
private theorem sentinel_valid {w : Nat} (width : w = 8 ∨ w = 16) :
    ImmLogic.ofNat? (2^(32-w-1)) .size32 = some ⟨2^(32-w-1),.size32⟩ := by
  rcases width with rfl | rfl <;> decide +kernel
/-- Narrow CTZ uses its sentinel even for zero input; dirty upper source bits
cannot change the count. Registers outside the three fresh writes survive. -/
theorem stock_count_ctz_narrow_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {ty : Clif.Ty} (width : ty.width = 8 ∨ ty.width = 16)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {d x : Nat}
    (bounded : aliases.size ≤ d) {u : BitVec ty.width}
    (held : VHolds ⟨ty,u⟩ (ρ (aliasNum aliases x))) :
    ∃ ρ', PRun F isem ((countCode true ty.width d x).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .ctz u⟩ (ρ' (d+2)) ∧
      ∀ n,n ≠ d → n ≠ d+1 → n ≠ d+2 → ρ' n = ρ n := by
  have small : ty.width ≤ 32 := by rcases width with h | h <;> omega
  have fits : ty.width < 32 := by omega
  have positive : 0 < ty.width := by rcases width with h | h <;> omega
  let r0 := resX .size32 (opnd .size32 (ρ (aliasNum aliases x))).reverse
  let mid0 := upd ρ d r0
  let r1 := resX .size32 (opnd .size32 (mid0 d) ||| BitVec.ofNat OperandSize.size32.bits (2^(32-ty.width-1)))
  let mid1 := upd mid0 (d+1) r1
  let r2 := resX .size32 (opnd .size32 (mid1 (d+1))).clz
  refine ⟨upd mid1 (d+2) r2,?_,?_,?_⟩
  · rw [mapped_narrow bounded]
    simp only [countCode,width,ite_true]
    exact prun_rr refines rfl (fun _ => rfl)
      (prun_rr refines rfl (fun world => by
        simp only [ispec,sentinel_valid width,ne_eq,reduceCtorEq,not_false_eq_true,
          and_self,ite_true,aluVal,Option.map_some,defOut]
        rfl) (prun_rr refines rfl (fun _ => rfl) (prun_nil _)))
  · rw [upd_same]
    change r2.setWidth ty.width = u.ctz
    dsimp only [r2,mid1]
    rw [upd_same]
    dsimp only [r1,mid0]
    rw [upd_same]
    dsimp only [r0]
    rw [opnd_resX,opnd_resX,resX_setWidth small (by decide)]
    let raw : BitVec 32 := opnd .size32 (ρ (aliasNum aliases x))
    have result := stock_ctz_sentinel_bits positive fits raw
    rw [← sentinel_mask width] at result
    have input : (opnd .size32 (ρ (aliasNum aliases x))).setWidth ty.width = u := by
      rw [opnd_setWidth small (by decide)]
      exact held
    exact result.trans (congrArg BitVec.ctz input)
  · intro n first second third
    simp only [mid1,mid0,upd,first,second,third,ite_false]
/-- Narrow CLZ explicitly zero-extends before counting, so the correction
computes the source-width result independently of dirty physical upper bits. -/
theorem stock_count_clz_narrow_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {ty : Clif.Ty} (width : ty.width = 8 ∨ ty.width = 16)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {d x : Nat}
    (bounded : aliases.size ≤ d) {u : BitVec ty.width}
    (held : VHolds ⟨ty,u⟩ (ρ (aliasNum aliases x))) :
    ∃ ρ', PRun F isem ((countCode false ty.width d x).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .clz u⟩ (ρ' (d+2)) ∧
      ∀ n,n ≠ d → n ≠ d+1 → n ≠ d+2 → ρ' n = ρ n := by
  have small : ty.width ≤ 32 := by rcases width with h | h <;> omega
  have fits : ty.width < 32 := by omega
  have positive : 0 < ty.width := by rcases width with h | h <;> omega
  let low := (lo64 (ρ (aliasNum aliases x))).setWidth ty.width
  let r0 := resX .size32 (low.setWidth OperandSize.size32.bits)
  let mid0 := upd ρ d r0
  let r1 := resX .size32 (opnd .size32 (mid0 d)).clz
  let mid1 := upd mid0 (d+1) r1
  let r2 := resX .size32 (opnd .size32 (mid1 (d+1)) - BitVec.ofNat OperandSize.size32.bits (32-ty.width))
  refine ⟨upd mid1 (d+2) r2,?_,?_,?_⟩
  · rw [mapped_narrow bounded]
    simp only [countCode,width,ite_true,Bool.false_eq_true,ite_false]
    exact prun_rr refines rfl
      (fun world => ispec_extend (width.elim (fun h => .inl h) (fun h => .inr (.inl h))) (.inl rfl) fits)
      (prun_rr refines rfl (fun _ => rfl)
        (prun_rr refines rfl (fun world => ispec_aluRRImm12_sub (by
          change 32-ty.width < 4096; omega)) (prun_nil _)))
  · rw [upd_same]
    change r2.setWidth ty.width = u.clz
    dsimp only [r2,mid1]
    rw [upd_same]
    dsimp only [r1,mid0]
    rw [upd_same]
    dsimp only [r0]
    rw [opnd_resX,opnd_resX,resX_setWidth small (by decide)]
    change ((low.setWidth 32).clz - BitVec.ofNat 32 (32-ty.width)).setWidth ty.width = u.clz
    rw [stock_clz_zext_bits positive small]
    have input : low = u := by
      dsimp only [low]
      change (opnd .size64 (ρ (aliasNum aliases x))).setWidth ty.width = u
      rw [opnd_setWidth (by change ty.width ≤ 64; omega) (by decide)]
      exact held
    rw [input]
  · intro n first second third
    simp only [mid1,mid0,upd,first,second,third,ite_false]
/-- All scalar count templates compute the original source value through
final aliases and preserve every register outside their actual allocation. -/
theorem stock_count_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (trailing : Bool) {ty : Clif.Ty} (width : IW ty.width)
    {ctx : Ctx} {fr : Clif.Frame} {aliases : Array (Option Nat)} {ρ : Nat → CV}
    {x nx d : Nat} (bounded : aliases.size ≤ d)
    (mapped : ctx.valueReg? x = some (.vreg nx .int))
    (held : ValuesHeld (fun z => z = x) ctx fr (fun k => ρ (aliasNum aliases k)))
    {u : BitVec ty.width} (source : fr.getAs x ty = .ok u) :
    ∃ ρ', PRun F isem ((countCode trailing ty.width d nx).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary (countOp trailing) u⟩
        (ρ' (countResult trailing ty.width d)) ∧
      ∀ n,n < d ∨ d+countAlloc trailing ty.width ≤ n → ρ' n = ρ n := by
  have input := held.read rfl (getAs_ok source) mapped
  by_cases narrow : ty.width = 8 ∨ ty.width = 16
  · have result : countResult trailing ty.width d = d+2 := by
      simp only [countResult,countAlloc,narrow,ite_true]; omega
    cases trailing
    · obtain ⟨ρ',execution,value,kept⟩ := stock_count_clz_narrow_resolved refines narrow bounded input
      refine ⟨ρ',execution,?_,?_⟩
      · simpa only [result,countOp,Bool.false_eq_true,ite_false] using value
      · intro n outside
        simp only [countAlloc,narrow,ite_true] at outside
        exact kept n (by omega) (by omega) (by omega)
    · obtain ⟨ρ',execution,value,kept⟩ := stock_count_ctz_narrow_resolved refines narrow bounded input
      refine ⟨ρ',execution,?_,?_⟩
      · simpa only [result,countOp,ite_true] using value
      · intro n outside
        simp only [countAlloc,narrow,ite_true] at outside
        exact kept n (by omega) (by omega) (by omega)
  · have wide : ty.width = 32 ∨ ty.width = 64 := by
      rcases width with h | h | h | h <;> simp_all
    exact stock_count_wide_resolved refines trailing wide bounded input
end Backend.Stock.Proof.ScalarCount
