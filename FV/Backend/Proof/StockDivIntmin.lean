import FV.Backend.Proof.IselCmpSdiv
import FV.Backend.Proof.DriverCheck
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
/-- Signed widening reflects the all-ones divisor, using its integer value. -/
theorem stock_div_signExtend_allOnes {n m : Nat} (positive : 0 < n) (width : n ≤ m) (a : BitVec n) :
    a.signExtend m = BitVec.allOnes m ↔ a = BitVec.allOnes n := by
  have targetPositive : 0 < m := by omega
  rw [← BitVec.toInt_inj,BitVec.toInt_signExtend_of_le width]
  simp only [BitVec.toInt_allOnes,positive,targetPositive,ite_true]
  rw [← BitVec.toInt_inj]
  simp only [BitVec.toInt_allOnes,positive,ite_true]

/-- The narrow shifted dividend is signed minimum exactly at its original
signed minimum. The discarded extension bits are handled bit by bit. -/
theorem stock_div_shift_intMin {n : Nat} (width : n = 8 ∨ n = 16) (a : BitVec n) :
    a.signExtend 32 <<< (32-n) = BitVec.intMin 32 ↔ a = BitVec.intMin n := by
  have same : a.signExtend 32 <<< (32-n) = a.zeroExtend 32 <<< (32-n) := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp only [BitVec.getElem_shiftLeft]
    by_cases below : i < 32-n
    · simp [below]
    · have source : i-(32-n) < n := by omega
      simp [below,BitVec.getElem_signExtend,BitVec.getElem_setWidth,source]
  rw [same,← BitVec.toNat_inj]
  have bounded := a.isLt
  have shifted : (a.zeroExtend 32 <<< (32-n)).toNat = a.toNat * 2^(32-n) := by
    rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,BitVec.toNat_setWidth]
    have small : a.toNat < 2^32 := by rcases width with rfl | rfl <;> omega
    rw [Nat.mod_eq_of_lt small]
    apply Nat.mod_eq_of_lt
    rcases width with rfl | rfl <;> omega
  rw [shifted]
  rw [← BitVec.toNat_inj]
  rcases width with rfl | rfl
  · change a.toNat * 16777216 = 2147483648 ↔ a.toNat = 128
    omega
  · change a.toNat * 65536 = 2147483648 ↔ a.toNat = 32768
    omega
theorem stock_div_operand_allOnes {n : Nat} (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) {b : BitVec n} {B : CV}
    (h : DivOpnd true b B) : opnd (szOf n) B = BitVec.allOnes _ ↔ b = BitVec.allOnes n := by
  unfold DivOpnd at h
  rcases hn with rfl | rfl | rfl | rfl
  · simp only [show (8:Nat) ≤ 32 by decide, ↓reduceIte] at h
    show ((lo64 B).setWidth 32 = BitVec.allOnes 32) ↔ _
    rw [h]; exact stock_div_signExtend_allOnes (by decide) (by decide) b
  · simp only [show (16:Nat) ≤ 32 by decide, ↓reduceIte] at h
    show ((lo64 B).setWidth 32 = BitVec.allOnes 32) ↔ _
    rw [h]; exact stock_div_signExtend_allOnes (by decide) (by decide) b
  · simp only [show (32:Nat) ≤ 32 by decide, ↓reduceIte] at h
    show ((lo64 B).setWidth 32 = BitVec.allOnes 32) ↔ _
    rw [h]; exact stock_div_signExtend_allOnes (by decide) (by decide) b
  · simp only [show ¬ (64:Nat) ≤ 32 by decide, ↓reduceIte] at h
    show ((lo64 B).setWidth 64 = BitVec.allOnes 64) ↔ _
    rw [h]; simp

theorem stock_div_intmin_code_sem (hR : Refines F isem) {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    {s2 s3 : LState} {v : V} {kx : Nat}
    (hI : (w ≤ 16 ∧ v = .reg (s2.fresh .int).1 ∧ s3 = (s2.fresh .int).2.emit
        (.aluRRImmShift .lsl .size32 (s2.fresh .int).1 (.vreg kx .int) (32 - w))) ∨
      (16 < w ∧ v = .reg (.vreg kx .int) ∧ s3 = s2)) :
    ∃ kc msC, v = .reg (.vreg kc .int) ∧ Frag s2 s3 msC ∧ (kc = kx ∨ s2.nextVreg ≤ kc) ∧
      (kc = kx ∨ kc < s3.nextVreg) ∧ (∀ m ∈ msC, ∀ u ∈ vuseNums m, u = kx) ∧
      ∀ (a : BitVec w) (ρ : Nat → CV) (wd : Arm.ArmState), DivOpnd true a (ρ kx) →
        Runs F isem msC ρ wd (fun ρ' _ => (∀ z < s2.nextVreg, ρ' z = ρ z) ∧
          (opnd (szOf w) (ρ' kc) = BitVec.intMin _ ↔ a = BitVec.intMin w)) := by
  rcases hI with ⟨hw16, rfl, rfl⟩ | ⟨hw16, rfl, rfl⟩
  · refine ⟨s2.nextVreg, [.aluRRImmShift .lsl .size32 (.vreg s2.nextVreg .int) (.vreg kx .int) (32 - w)],
      rfl, Frag.fresh_emit s2 (by rw [show (s2.fresh .int).1 = .vreg s2.nextVreg .int from rfl, vdefs_lsl']; simp),
      .inr (Nat.le_refl _),
      .inr (by simp [LState.emit, LState.fresh]), ?_, ?_⟩
    · intro m hm u hu
      simp only [List.mem_singleton] at hm; subst hm
      rw [vuseNums_lsl', List.mem_singleton] at hu; exact hu
    · intro a ρ wd ha
      refine (runs_lsl32 hR _ _ _ (by omega) ρ wd).imp fun ρ' _ _ e => ⟨fun z hz => ?_, ?_⟩
      · rw [e]; simp [upd, show z ≠ s2.nextVreg by omega]
      · rw [e, upd_same]
        unfold DivOpnd at ha
        rcases hw with rfl | rfl | rfl | rfl <;> (try omega)
        · simp only [show (8:Nat) ≤ 32 by decide, ↓reduceIte] at ha
          show (opnd .size32 (resX .size32 (opnd .size32 (ρ kx) <<< 24)) = BitVec.intMin 32) ↔ _
          rw [cmp_opnd_resX, show (opnd .size32 (ρ kx) : BitVec 32) = (lo64 (ρ kx)).setWidth 32 from rfl, ha]
          exact stock_div_shift_intMin (Or.inl rfl) a
        · simp only [show (16:Nat) ≤ 32 by decide, ↓reduceIte] at ha
          show (opnd .size32 (resX .size32 (opnd .size32 (ρ kx) <<< 16)) = BitVec.intMin 32) ↔ _
          rw [cmp_opnd_resX, show (opnd .size32 (ρ kx) : BitVec 32) = (lo64 (ρ kx)).setWidth 32 from rfl, ha]
          exact stock_div_shift_intMin (Or.inr rfl) a
  · refine ⟨kx, [], rfl, Frag.nil _, .inl rfl, .inl rfl, by simp, fun a ρ wd ha =>
      Runs.nil ⟨fun _ _ => rfl, divOpnd_intMin (by omega) ha⟩⟩
end Backend.Stock.Proof.ScalarDiv
