import FV.Arm.BitVec
import FV.Arm.MinTheory
import FV.Backend.Proof.IselInterp
import FV.Backend.Proof.PrepareCheck
namespace Backend.Stock.Proof.ScalarCount
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private def countAt (w : Nat) (bits : Nat → Bool) : Nat → Nat
  | 0 => if bits 0 then w-1 else w
  | n+1 => if bits (n+1) then w-1-(n+1) else countAt w bits n
private theorem aux_nat {w : Nat} (x : BitVec w) (n : Nat) :
    (x.clzAuxRec n).toNat = countAt w x.getLsbD n := by
  have bound : w < 2^w := Nat.lt_pow_self (by decide)
  induction n with
  | zero =>
    simp only [BitVec.clzAuxRec_zero,countAt]
    cases bit : x.getLsbD 0
    · simp [bit,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound]
    · simp [bit,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : w-1 < 2^w)]
  | succ n ih =>
    simp only [BitVec.clzAuxRec_succ,countAt]
    cases bit : x.getLsbD (n+1)
    · simp [bit,ih]
    · simp [bit,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : w-1-(n+1) < 2^w)]
private theorem count_offset {w N n : Nat} (positive : 0 < w) (fits : w ≤ N) (inside : n < w)
    (bits : Nat → Bool) : countAt N bits n = N-w+countAt w bits n := by
  induction n with
  | zero => unfold countAt; cases bits 0 <;> simp <;> omega
  | succ n ih =>
    simp only [countAt]
    cases bit : bits (n+1)
    · simp only [bit,ite_false,Bool.false_eq_true]
      exact ih (by omega)
    · simp only [bit,ite_true]
      omega
private theorem extend_aux {w N : Nat} (positive : 0 < w) (fits : w ≤ N) (x : BitVec w) :
    ((x.setWidth N).clzAuxRec (w-1)).toNat = N-w+(x.clzAuxRec (w-1)).toNat := by
  rw [aux_nat,aux_nat]
  have bits : (x.setWidth N).getLsbD = x.getLsbD := by
    funext i
    by_cases within : i < N
    · simp [BitVec.getLsbD_setWidth,within]
    · have outside : w ≤ i := by omega
      simp [BitVec.getLsbD_setWidth,within,BitVec.getLsbD_of_ge x i outside]
  rw [bits]
  exact count_offset positive fits (by omega) _
private theorem clz_extend_nat {w N : Nat} (positive : 0 < w) (fits : w ≤ N) (x : BitVec w) :
    (x.setWidth N).clz.toNat = N-w+x.clz.toNat := by
  have upper : ∀ i,w-1 < i → (x.setWidth N).getLsbD i = false := by
    intro i hi
    have outside : w ≤ i := by omega
    simp [BitVec.getLsbD_setWidth,BitVec.getLsbD_of_ge x i outside]
  have short := BitVec.clzAuxRec_eq_clzAuxRec_of_getLsbD_false (x := x.setWidth N) (n := w-1) (k := N-w) upper
  have endpoint : w-1+(N-w) = N-1 := by omega
  rw [endpoint] at short
  change ((x.setWidth N).clzAuxRec (N-1)).toNat = _
  rw [← short,extend_aux positive fits]
  rfl
private theorem count_hit (w : Nat) (bits : Nat → Bool) (n : Nat) (hit : bits n = true) :
    countAt w bits n = w-1-n := by
  cases n <;> simp [countAt,hit]
private theorem clz_top_sentinel {w N : Nat} (positive : 0 < w) (fits : w < N)
    (x : BitVec w) (y : BitVec N)
    (same : ∀ i,i < w → y.getLsbD (N-w+i) = x.getLsbD i)
    (sentinel : y.getLsbD (N-w-1) = true) : y.clz.toNat = x.clz.toNat := by
  have aux : ∀ n,n < w → countAt N y.getLsbD (N-w+n) = countAt w x.getLsbD n := by
    intro n inside
    induction n with
    | zero =>
      have index : N-w = (N-w-1)+1 := by omega
      simp only [Nat.add_zero]
      conv => lhs; rw [index,countAt]
      have bitEq : y.getLsbD ((N-w-1)+1) = x.getLsbD 0 := by rw [← index]; exact same 0 positive
      rw [bitEq]
      cases bit : x.getLsbD 0
      · simp only [Bool.false_eq_true,ite_false,countAt]
        rw [bit]
        simp only [Bool.false_eq_true,ite_false]
        rw [count_hit N y.getLsbD _ sentinel]
        omega
      · simp only [ite_true,countAt]
        rw [bit]
        simp only [ite_true]
        omega
    | succ n ih =>
      have index : N-w+(n+1) = (N-w+n)+1 := by omega
      conv => lhs; rw [index,countAt]
      have bitEq : y.getLsbD ((N-w+n)+1) = x.getLsbD (n+1) := by rw [← index]; exact same (n+1) inside
      rw [bitEq]
      simp only [countAt]
      cases bit : x.getLsbD (n+1)
      · simp only [Bool.false_eq_true,ite_false]
        exact ih (by omega)
      · simp only [ite_true]
        omega
  change (y.clzAuxRec (N-1)).toNat = (x.clzAuxRec (w-1)).toNat
  rw [aux_nat,aux_nat]
  have index : N-w+(w-1) = N-1 := by omega
  rw [← index]
  exact aux (w-1) (by omega)
private theorem reverse_high {w : Nat} (positive : 0 < w) (fits : w < 32) (x : BitVec 32)
    {i : Nat} (inside : i < w) :
    x.reverse.getLsbD (32-w+i) = (x.setWidth w).reverse.getLsbD i := by
  have high : 32-w+i < 32 := by omega
  have index : 32-1-(32-w+i) = w-1-i := by omega
  have low : w-1-i < w := by omega
  simp only [BitVec.getLsbD_reverse,BitVec.getMsbD_eq_getLsbD,high,inside,decide_true,
    Bool.true_and,BitVec.getLsbD_setWidth,index,low]
private theorem ctz_sentinel_nat {w : Nat} (positive : 0 < w) (fits : w < 32) (x : BitVec 32) :
    (x.reverse ||| (1#32 <<< (32-w-1))).clz.toNat = (x.setWidth w).ctz.toNat := by
  rw [BitVec.ctz_eq_reverse_clz]
  apply clz_top_sentinel positive fits (x.setWidth w).reverse
  · intro i inside
    have nonzero : (32-w+i)-(32-w-1) ≠ 0 := by omega
    simp only [BitVec.getLsbD_or,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_one,nonzero,
      decide_false,Bool.and_false,Bool.or_false]
    exact reverse_high positive fits x inside
  · have range : 32-w-1 < 32 := by omega
    simp [BitVec.getLsbD_or,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_one,range]
/-- The sentinel bounds the count for a zero narrow source and hides all lower
reversed bits originating above the source width. -/
theorem stock_ctz_sentinel_bits {w : Nat} (positive : 0 < w) (fits : w < 32) (x : BitVec 32) :
    ((x.reverse ||| (1#32 <<< (32-w-1))).clz).setWidth w = (x.setWidth w).ctz := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth,ctz_sentinel_nat positive fits]
  exact Nat.mod_eq_of_lt (x.setWidth w).ctz.isLt
/-- Narrow CLZ zero-extends first, then subtracts the extra physical leading
zeros; the resulting low bits equal the original source count. -/
theorem stock_clz_zext_bits {w : Nat} (positive : 0 < w) (fits : w ≤ 32) (x : BitVec w) :
    ((x.setWidth 32).clz - BitVec.ofNat 32 (32-w)).setWidth w = x.clz := by
  have count := clz_extend_nat positive fits x
  have immediate : (BitVec.ofNat 32 (32-w)).toNat = 32-w := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have order : BitVec.ofNat 32 (32-w) ≤ (x.setWidth 32).clz := by
    rw [BitVec.le_def,immediate,count]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth,BitVec.toNat_sub_of_le order,immediate,count]
  simp only [Nat.add_sub_cancel_left]
  exact Nat.mod_eq_of_lt x.clz.isLt
end Backend.Stock.Proof.ScalarCount
