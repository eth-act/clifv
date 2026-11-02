import FV.Backend.Proof.IselContract
namespace Backend.Stock.Proof.ScalarPopcount
open Backend.Proof
open Backend
set_option maxRecDepth 20000
/-- Each byte of the actual CNT value is its original byte's population count;
the proof uses extraction algebra rather than a bit-blasting oracle. -/
theorem stock_popcount_byte (x : BitVec 64) (i : Nat) (bounded : i < 8) :
    byteOf (cntBytes x) i = (byteOf x i).cpop := by
  have indices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases indices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [byteOf,cntBytes]
  all_goals simp (disch := omega) only [Nat.reduceMul,Nat.reduceSub,
    BitVec.extractLsb'_append_eq_right,BitVec.extractLsb'_append_eq_left,
    BitVec.extractLsb'_append_eq_of_le,BitVec.extractLsb'_eq_self]
private theorem unpack (x : BitVec 64) :
    byteOf x 7 ++ byteOf x 6 ++ byteOf x 5 ++ byteOf x 4 ++ byteOf x 3 ++ byteOf x 2 ++ byteOf x 1 ++ byteOf x 0 = x := by
  simp only [byteOf,Nat.reduceMul]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 56) (start₁ := 48) (len₁ := 8) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 48) (start₁ := 40) (len₁ := 8) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 40) (start₁ := 32) (len₁ := 8) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 32) (start₁ := 24) (len₁ := 8) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 24) (start₁ := 16) (len₁ := 8) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 16) (start₁ := 8) (len₁ := 8) (by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₂ := 8) (start₁ := 0) (len₁ := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self
/-- The actual ADDV/CNT low byte equals the original whole-word population
count, proved by byte decomposition and population-count append algebra. -/
theorem stock_popcount_sum (x : BitVec 64) :
    (addvBytes (cntBytes x)).setWidth 8 = x.cpop.setWidth 8 := by
  have whole := congrArg (fun y : BitVec 64 => y.cpop.toNat) (unpack x)
  simp only [BitVec.toNat_cpop_append] at whole
  apply BitVec.eq_of_toNat_eq
  simp only [addvBytes,stock_popcount_byte x 0 (by decide),stock_popcount_byte x 1 (by decide),
    stock_popcount_byte x 2 (by decide),stock_popcount_byte x 3 (by decide),stock_popcount_byte x 4 (by decide),
    stock_popcount_byte x 5 (by decide),stock_popcount_byte x 6 (by decide),stock_popcount_byte x 7 (by decide),
    BitVec.toNat_setWidth,BitVec.toNat_add,Nat.reducePow,Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 18446744073709551616),
    Nat.add_mod_mod,Nat.mod_add_mod]
  rw [← whole]
  have bound0 := BitVec.toNat_cpop_le (byteOf x 0)
  have bound1 := BitVec.toNat_cpop_le (byteOf x 1)
  have bound2 := BitVec.toNat_cpop_le (byteOf x 2)
  have bound3 := BitVec.toNat_cpop_le (byteOf x 3)
  have bound4 := BitVec.toNat_cpop_le (byteOf x 4)
  have bound5 := BitVec.toNat_cpop_le (byteOf x 5)
  have bound6 := BitVec.toNat_cpop_le (byteOf x 6)
  have bound7 := BitVec.toNat_cpop_le (byteOf x 7)
  have total := BitVec.toNat_cpop_le x
  omega
/-- Widening the eight-byte sum loses no population-count bits: the count
is at most64, so the actual ADDV result equals the whole-word count. -/
theorem stock_popcount_sum_full (x : BitVec 64) : addvBytes (cntBytes x) = x.cpop := by
  have low := congrArg BitVec.toNat (stock_popcount_sum x)
  have bound := BitVec.toNat_cpop_le x
  apply BitVec.eq_of_toNat_eq
  unfold addvBytes at low ⊢
  simp only [BitVec.toNat_setWidth,Nat.reducePow] at low ⊢
  have bytes := (byteOf (cntBytes x) 0 + byteOf (cntBytes x) 1 + byteOf (cntBytes x) 2 +
    byteOf (cntBytes x) 3 + byteOf (cntBytes x) 4 + byteOf (cntBytes x) 5 + byteOf (cntBytes x) 6 +
    byteOf (cntBytes x) 7).isLt
  change _ < 256 at bytes
  omega
private theorem low_extract {w n : Nat} (x : BitVec w) : x.extractLsb' 0 n = x.setWidth n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb',BitVec.toNat_setWidth]
theorem stock_popcnt8_fin (X : CV) :
    (ofX ((((cntBytes (lo64 (((lo64 X).setWidth 32).setWidth 128))).setWidth 128).extractLsb'
      (8 * 0) 8).setWidth 64)).setWidth 8 = (X.setWidth 8).cpop := by
  simp only [ofX,lo64,Nat.mul_zero,low_extract]
  simp (disch := omega) only [BitVec.setWidth_setWidth_of_le,BitVec.setWidth_eq]
  change (byteOf (cntBytes ((X.setWidth 32).setWidth 64)) 0) = (X.setWidth 8).cpop
  rw [stock_popcount_byte _ 0 (by decide)]
  simp (disch := omega) only [byteOf,Nat.mul_zero,low_extract,BitVec.setWidth_setWidth_of_le]
theorem stock_popcnt32_fin (X : CV) :
    (ofX ((((addvBytes (lo64 ((cntBytes (lo64 (((lo64 X).setWidth 32).setWidth 128))).setWidth
      128))).setWidth 128).extractLsb' (8 * 0) 8).setWidth 64)).setWidth 32 = (X.setWidth 32).cpop := by
  simp only [ofX,lo64,Nat.mul_zero,low_extract]
  simp (disch := omega) only [BitVec.setWidth_setWidth_of_le,BitVec.setWidth_eq]
  rw [stock_popcount_sum_full]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth,Nat.reducePow]
  have bound := BitVec.toNat_cpop_le (X.setWidth 32)
  rw [BitVec.toNat_cpop_setWidth_eq_of_le (by decide : 32 ≤ 64)]
  omega
theorem stock_popcnt64_fin (X : CV) :
    (ofX ((((addvBytes (lo64 ((cntBytes (lo64 ((lo64 X).setWidth 128))).setWidth 128))).setWidth
      128).extractLsb' (8 * 0) 8).setWidth 64)).setWidth 64 = (X.setWidth 64).cpop := by
  simp only [ofX,lo64,Nat.mul_zero,low_extract]
  simp (disch := omega) only [BitVec.setWidth_setWidth_of_le,BitVec.setWidth_eq]
  rw [stock_popcount_sum_full]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth,Nat.reducePow]
  have bound := BitVec.toNat_cpop_le (X.setWidth 64)
  omega
theorem stock_popcnt16_fin (X : CV) :
    (ofX ((((addpBytes (lo64 ((cntBytes (lo64 (((lo64 X).setWidth 32).setWidth 128))).setWidth 128))
      (lo64 ((cntBytes (lo64 (((lo64 X).setWidth 32).setWidth 128))).setWidth 128))).setWidth
      128).extractLsb' (8 * 0) 8).setWidth 64)).setWidth 16 = (X.setWidth 16).cpop := by
  let y := (X.setWidth 32).setWidth 64
  have pair : byteOf y 1 ++ byteOf y 0 = X.setWidth 16 := by
    simp only [byteOf,Nat.reduceMul]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 8 = 0+8),low_extract]
    simp (disch := omega) only [y,BitVec.setWidth_setWidth_of_le]
  have count := congrArg (fun v : BitVec 16 => v.cpop.toNat) pair
  simp only [BitVec.toNat_cpop_append] at count
  have bound0 := BitVec.toNat_cpop_le (byteOf y 0)
  have bound1 := BitVec.toNat_cpop_le (byteOf y 1)
  simp only [ofX,lo64,Nat.mul_zero,low_extract]
  simp (disch := omega) only [BitVec.setWidth_setWidth_of_le,BitVec.setWidth_eq]
  change ((addpBytes (cntBytes y) (cntBytes y)).setWidth 8).setWidth 16 = _
  simp only [addpBytes,BitVec.setWidth_append_eq_right]
  rw [stock_popcount_byte y 0 (by decide),stock_popcount_byte y 1 (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth,BitVec.toNat_add,Nat.reducePow]
  omega
/-- Concrete dirty-upper-bit values and every byte index inhabit all new
population-count arithmetic contracts; actual driver witnesses come with
retained/source composition in the complete family batch. -/
theorem stock_popcount_math_witness : ∃ (x : BitVec 64) (X : CV),
    (∀ i ∈ ([0,1,2,3,4,5,6,7] : List Nat),byteOf (cntBytes x) i = (byteOf x i).cpop) ∧
    (addvBytes (cntBytes x)).setWidth 8 = x.cpop.setWidth 8 ∧
    addvBytes (cntBytes x) = x.cpop ∧
    (ofX ((((cntBytes (lo64 (((lo64 X).setWidth 32).setWidth 128))).setWidth 128).extractLsb'
      0 8).setWidth 64)).setWidth 8 = (X.setWidth 8).cpop ∧
    (ofX ((((addpBytes (lo64 ((cntBytes (lo64 (((lo64 X).setWidth 32).setWidth 128))).setWidth 128))
      (lo64 ((cntBytes (lo64 (((lo64 X).setWidth 32).setWidth 128))).setWidth 128))).setWidth
      128).extractLsb' 0 8).setWidth 64)).setWidth 16 = (X.setWidth 16).cpop ∧
    (ofX ((((addvBytes (lo64 ((cntBytes (lo64 (((lo64 X).setWidth 32).setWidth 128))).setWidth
      128))).setWidth 128).extractLsb' 0 8).setWidth 64)).setWidth 32 = (X.setWidth 32).cpop ∧
    (ofX ((((addvBytes (lo64 ((cntBytes (lo64 ((lo64 X).setWidth 128))).setWidth 128))).setWidth
      128).extractLsb' 0 8).setWidth 64)).setWidth 64 = (X.setWidth 64).cpop := by
  let x : BitVec 64 := BitVec.ofNat 64 (2^63+291)
  let X : CV := BitVec.ofNat 128 (2^100+2^64+291)
  refine ⟨x,X,?_,stock_popcount_sum x,stock_popcount_sum_full x,
    stock_popcnt8_fin X,stock_popcnt16_fin X,stock_popcnt32_fin X,stock_popcnt64_fin X⟩
  intro i member
  have bound : i < 8 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact stock_popcount_byte x i bound
end Backend.Stock.Proof.ScalarPopcount
