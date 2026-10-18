import FV.Backend.Proof.IselLcf
import FV.Backend.Proof.DriverCheck
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private theorem clear_mask {n : Nat} (x mask : BitVec n) :
    x &&& ~~~mask = x - (x &&& mask) := by
  apply BitVec.eq_sub_iff_add_eq.mpr
  have disjoint : (x &&& ~~~mask) &&& (x &&& mask) = 0#n := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi₀
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_zero]
    cases x.getLsbD i <;> cases mask.getLsbD i <;> simp
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ disjoint]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi₀
  by_cases hi : i < n
  · simp only [BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,decide_false,Bool.true_and]
    cases x.getLsbD i <;> cases mask.getLsbD i <;> simp
  · exact False.elim (hi hi₀)
private theorem mask_slice {n k : Nat} (bound : k+16 ≤ n) (x : BitVec n) :
    x &&& ((BitVec.allOnes 16).setWidth n <<< k) =
      ((x >>> k).setWidth 16).setWidth n <<< k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi₀
  by_cases hi : i < n
  · by_cases hk : k ≤ i
    · have inner : i-k < n := by omega
      have index : k+(i-k) = i := by omega
      simp only [BitVec.getLsbD_and,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_setWidth,
        BitVec.getLsbD_ushiftRight,BitVec.getLsbD_allOnes,hi,show ¬ i < k by omega,
        inner,index,Bool.and_comm,decide_true,decide_false,Bool.true_and,Bool.and_true,Bool.not_false,Bool.and_false]
    · simp [BitVec.getLsbD_and,BitVec.getLsbD_shiftLeft,hi,show i < k by omega]
  · simp [BitVec.getLsbD_and,BitVec.getLsbD_shiftLeft,hi]
private theorem replacement_disjoint {n k : Nat} (bound : k+16 ≤ n) (x : BitVec n) (y : BitVec 16) :
    (x &&& ~~~((BitVec.allOnes 16).setWidth n <<< k)) &&& (y.setWidth n <<< k) = 0#n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi₀
  by_cases hi : i < n
  · by_cases hk : k ≤ i
    · have inner : i-k < n := by omega
      by_cases part : i-k < 16
      · simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_shiftLeft,
          BitVec.getLsbD_setWidth,BitVec.getLsbD_allOnes,hi,show ¬ i < k by omega,inner,part,BitVec.getLsbD_zero,decide_true,decide_false,Bool.true_and,Bool.and_true,Bool.not_false,Bool.not_true,Bool.and_false,Bool.false_and]
      · simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_shiftLeft,
          BitVec.getLsbD_setWidth,BitVec.getLsbD_allOnes,hi,show ¬ i < k by omega,inner,part,
          BitVec.getLsbD_of_ge y (i-k) (by omega : 16 ≤ i-k),BitVec.getLsbD_zero,decide_true,decide_false,Bool.true_and,Bool.and_true,Bool.not_false,Bool.and_false,Bool.false_and]
    · simp [BitVec.getLsbD_and,BitVec.getLsbD_shiftLeft,hi,show i < k by omega]
  · simp [BitVec.getLsbD_and,BitVec.getLsbD_shiftLeft,hi]
/-- Isolated standard-kernel MOVK algebra for Stock immediate values. The legacy
movK_ident variant and its callers remain unchanged. -/
theorem stock_div_movK_ident {n j : Nat} (width : Wid n) (slice : j < n/16) (x : BitVec n) (y : BitVec 16) :
    movKVal x ⟨y.toNat,j⟩ =
      x - (((x >>> (16*j)).setWidth 16).setWidth n <<< (16*j)) + (y.setWidth n <<< (16*j)) := by
  have bound : 16*j+16 ≤ n := by rcases width with rfl | rfl <;> omega
  have mask : BitVec.ofNat n 65535 = (BitVec.allOnes 16).setWidth n := by
    change BitVec.ofNat n (BitVec.allOnes 16).toNat = _
    exact BitVec.ofNat_toNat n (BitVec.allOnes 16)
  simp only [movKVal,BitVec.ofNat_toNat,mask]
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ (replacement_disjoint bound x y),clear_mask,mask_slice bound x]
end Backend.Stock.Proof.ScalarDiv
