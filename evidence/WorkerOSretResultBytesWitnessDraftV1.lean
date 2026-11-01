import FV.E2E.SretCopyResultBytes

namespace E2E.SretHeapBoundary
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private def resultState (contents : Nat → BitVec 8) (syms : String → Option Nat) : Arm.ArmState :=
  {Arm.ArmState.default with mem := fun a => ((Source.copied contents syms).bytes a.toNat).getD 0}

/-- Inhabit the conclusion adapters' premises; this is not an execution witness for compiled code. -/
theorem result_bytes_inhabited (contents : Nat → BitVec 8) (syms : String → Option Nat) (fb : FnBin) :
    ∃ s : Arm.ArmState,
      (Source.copied contents syms).valid (0x400000+0) 1 = true ∧
      (Source.copied contents syms).valid (0x500000+0) 1 = true ∧
      MemAgree (Source.copied contents syms) s ∧
      ArmRefines fb 0 (Arm.r .PC s) id s (.returned [] (Source.copied contents syms)) := by
  let s := resultState contents syms
  have agree : MemAgree (Source.copied contents syms) s := by
    intro a byte valid initialized
    rw [copied_valid] at valid
    have bounds := valid_bounds contents syms valid
    have fits : a < 2^64 := by rcases bounds with bounds | bounds <;> omega
    change ((Source.copied contents syms).bytes (BitVec.ofNat 64 a).toNat).getD 0 = byte
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt fits,initialized]
    rfl
  have returned : ArmRet (Arm.r .PC s) s s := by
    refine ⟨rfl,?_,rfl,fun _ _ => rfl,fun _ _ _ => rfl⟩
    simp [s,resultState,Arm.r,Arm.read_base_error,Arm.ArmState.default]
  refine ⟨s,copied_destination_valid contents syms (k := 0) (by decide),
    copied_source_valid contents syms (k := 0) (by decide),agree,?_⟩
  refine ⟨0,returned,?_,agree⟩
  intro j v present
  simp at present

end E2E.SretHeapBoundary

#print axioms E2E.SretHeapBoundary.result_bytes_inhabited
