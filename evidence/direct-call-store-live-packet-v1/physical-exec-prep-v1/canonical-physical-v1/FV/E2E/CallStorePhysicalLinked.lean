import FV.E2E.CallStorePhysicalExec

namespace E2E.CallStorePhysicalExec
open Arm _root_.BitVec Arm.BitVec
set_option autoImplicit false
set_option Elab.async false

def actualProgram (cleanup : Bool) : Arm.Program := def_program (linkedWords cleanup)

/-- The program comes from the original object bytes and linker in both modes. -/
-- witness: native_decide (fixed byte image only)
theorem actual_program_eq (cleanup : Bool) : actualProgram cleanup = literalProgram := by
  unfold actualProgram literalProgram
  rw [linked_words_exact cleanup]

def machine (cleanup : Bool) (word : BitVec 64) (initial : Arm.ArmState) : Arm.ArmState :=
  Arm.w .PC 0x200160#64
    (Arm.w (.GPR 31#5) 0x1000000#64
      (Arm.w (.GPR 0#5) 0x300000#64
        (Arm.w (.GPR 1#5) word (Arm.w .ERR .None {initial with program := actualProgram cleanup}))))

/-- The complete linked run returns and stores the arbitrary callee result.
The remaining initial registers and memory are arbitrary. -/
-- witness: native_decide (the actual image bridge only; symbolic execution is standard-only)
theorem complete_linked_run (cleanup : Bool) (word : BitVec 64) (initial : Arm.ArmState) :
    let before := machine cleanup word initial
    let after := Arm.run 15 before
    E2E.ArmRet (read_gpr 64 30#5 before) before after ∧
      read_gpr 64 0#5 after = word+13#64 ∧
      read_mem_bytes 8 0x300008#64 after = word+13#64 := by
  dsimp only
  have pc : read_pc (machine cleanup word initial) = 0x200160#64 := by
    simp (disch := decide) only [machine,state_simp_rules,Arm.r_of_w_same,Arm.r_of_w_different,BitVec.setWidth_eq]
  have prog : (machine cleanup word initial).program = literalProgram := by
    simp only [machine,Arm.w_program,actual_program_eq]
  have err : read_err (machine cleanup word initial) = .None := by
    simp (disch := decide) only [machine,state_simp_rules,Arm.r_of_w_same,Arm.r_of_w_different,BitVec.setWidth_eq]
  have stack : read_gpr 64 31#5 (machine cleanup word initial) = 0x1000000#64 := by
    simp (disch := decide) only [machine,state_simp_rules,Arm.r_of_w_same,Arm.r_of_w_different,BitVec.setWidth_eq]
  have pointer : read_gpr 64 0#5 (machine cleanup word initial) = 0x300000#64 := by
    simp (disch := decide) only [machine,state_simp_rules,Arm.r_of_w_same,Arm.r_of_w_different,BitVec.setWidth_eq]
  have argument : read_gpr 64 1#5 (machine cleanup word initial) = word := by
    simp (disch := decide) only [machine,state_simp_rules,Arm.r_of_w_same,Arm.r_of_w_different,BitVec.setWidth_eq]
  simpa only [argument] using literal_arm_ret (machine cleanup word initial)
    (Arm.run 15 (machine cleanup word initial)) pc prog err stack pointer rfl

end E2E.CallStorePhysicalExec
