import FV.E2E.SretCopyResultBytes
import FV.E2E.SemanticExecBytes

namespace E2E.SretHeapBoundary
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Compact code relocations cannot hide bytes of either original live heap region. -/
theorem copied_live_not_relocated (contents : Nat → BitVec 8) (syms : String → Option Nat)
    {R : BitVec 64 → Prop} (codeBound : ∀ a,R a → a.toNat < 0x300000)
    {a : Nat} (valid : (Source.copied contents syms).valid a 1 = true) :
    ¬ R (BitVec.ofNat 64 a) := by
  rw [copied_valid] at valid
  have bounds := valid_bounds contents syms valid
  have fits : a < 2^64 := by rcases bounds with bounds | bounds <;> omega
  have above : 0x400000 ≤ a := by rcases bounds with bounds | bounds <;> omega
  intro relocated
  have low := codeBound _ relocated
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt fits] at low
  omega

/-- The actual executable result copies every symbolic byte and preserves the source bytes. -/
theorem copied_exec_return_bytes (contents : Nat → BitVec 8) (syms : String → Option Nat)
    {fb : FnBin} {base ra : BitVec 64} {astep : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState}
    {R : BitVec 64 → Prop} (codeBound : ∀ a,R a → a.toNat < 0x300000)
    (result : E2E.SemanticExecBytes.ExecRefines fb base ra astep s R
      (.returned [] (Source.copied contents syms))) :
    ∃ n,ArmRet ra s (runX astep n s) ∧
      (∀ k < 16,Arm.read_mem (BitVec.ofNat 64 (0x400000+k)) (runX astep n s) = contents k) ∧
      (∀ k < 16,Arm.read_mem (BitVec.ofNat 64 (0x500000+k)) (runX astep n s) = contents k) := by
  obtain ⟨n,returned,_,memory⟩ := result
  have agree : MemAgree (Source.copied contents syms) (runX astep n s) := by
    intro a byte valid initialized
    exact memory a byte valid initialized (copied_live_not_relocated contents syms codeBound valid)
  exact ⟨n,returned,copied_machine_bytes contents syms agree⟩

end E2E.SretHeapBoundary
