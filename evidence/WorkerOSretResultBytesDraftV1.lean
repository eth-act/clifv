import FV.E2E.SretCopyHeapBoundary

namespace E2E.SretHeapBoundary
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The complete source return retains both original live allocations. -/
theorem copied_valid (contents : Nat → BitVec 8) (syms : String → Option Nat) (a n : Nat) :
    (Source.copied contents syms).valid a n = (heap contents syms).valid a n := by
  rfl

theorem copied_destination_valid (contents : Nat → BitVec 8) (syms : String → Option Nat)
    {k : Nat} (bound : k < 16) : (Source.copied contents syms).valid (0x400000+k) 1 = true := by
  rw [copied_valid]
  simp [heap,Clif.Mem.valid,Clif.Alloc.contains]
  omega

theorem copied_source_valid (contents : Nat → BitVec 8) (syms : String → Option Nat)
    {k : Nat} (bound : k < 16) : (Source.copied contents syms).valid (0x500000+k) 1 = true := by
  rw [copied_valid]
  simp [heap,Clif.Mem.valid,Clif.Alloc.contains]
  omega

/-- The existing memory observation gives every actual destination and source byte. -/
theorem copied_machine_bytes (contents : Nat → BitVec 8) (syms : String → Option Nat)
    {s : Arm.ArmState} (agree : MemAgree (Source.copied contents syms) s) :
    (∀ k < 16,Arm.read_mem (BitVec.ofNat 64 (0x400000+k)) s = contents k) ∧
    (∀ k < 16,Arm.read_mem (BitVec.ofNat 64 (0x500000+k)) s = contents k) := by
  constructor
  · intro k bound
    exact agree _ _ (copied_destination_valid contents syms bound) (Source.copied_byte contents syms bound)
  · intro k bound
    exact agree _ _ (copied_source_valid contents syms bound) (Source.copied_source_byte contents syms bound)

/-- Extract bytes from the existing machine theorem without changing any run premise. -/
theorem copied_model_return_bytes (contents : Nat → BitVec 8) (syms : String → Option Nat)
    {fb : FnBin} {base ra : BitVec 64} {astep : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState}
    (result : ArmRefines fb base ra astep s (.returned [] (Source.copied contents syms))) :
    ∃ n,ArmRet ra s (runX astep n s) ∧
      (∀ k < 16,Arm.read_mem (BitVec.ofNat 64 (0x400000+k)) (runX astep n s) = contents k) ∧
      (∀ k < 16,Arm.read_mem (BitVec.ofNat 64 (0x500000+k)) (runX astep n s) = contents k) := by
  obtain ⟨n,returned,_,agree⟩ := result
  exact ⟨n,returned,copied_machine_bytes contents syms agree⟩

end E2E.SretHeapBoundary

#print axioms E2E.SretHeapBoundary.copied_valid
#print axioms E2E.SretHeapBoundary.copied_destination_valid
#print axioms E2E.SretHeapBoundary.copied_source_valid
#print axioms E2E.SretHeapBoundary.copied_machine_bytes
#print axioms E2E.SretHeapBoundary.copied_model_return_bytes
