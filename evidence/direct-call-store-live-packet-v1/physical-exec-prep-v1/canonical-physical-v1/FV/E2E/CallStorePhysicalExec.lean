import FV.E2E.CallStorePhysicalProgram

namespace E2E.CallStorePhysicalExec
open Arm _root_.BitVec Arm.BitVec
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- The decoded instructions consume the real call result and original retained pointer. -/
theorem literal_effects (s0 sf : Arm.ArmState)
    (h_s0_pc : read_pc s0 = 0x200160#64)
    (h_s0_program : s0.program = literalProgram)
    (h_s0_err : read_err s0 = .None)
    (h_s0_sp : read_gpr 64 31#5 s0 = 0x1000000#64)
    (h_s0_pointer : read_gpr 64 0#5 s0 = 0x300000#64)
    (h_run : sf = run 15 s0) :
    (read_gpr 64 0#5 sf = read_gpr 64 1#5 s0 + 13#64 ∧
    read_mem_bytes 8 0x300008#64 sf = read_gpr 64 1#5 s0 + 13#64 ∧
    read_pc sf = read_gpr 64 30#5 s0 ∧ read_err sf = .None ∧
    read_gpr 64 31#5 sf = read_gpr 64 31#5 s0 ∧ read_gpr 64 19#5 sf = read_gpr 64 19#5 s0 ∧
      read_gpr 64 29#5 sf = read_gpr 64 29#5 s0) ∧
    ∀ fld : Arm.StateField,fld ≠ .PC → fld ≠ .ERR → fld ≠ .GPR 0#5 →
      fld ≠ .GPR 19#5 → fld ≠ .GPR 29#5 → fld ≠ .GPR 30#5 → fld ≠ .GPR 31#5 →
      Arm.r fld sf = Arm.r fld s0 := by
  have h_s0_sp_aligned : CheckSPAlignment s0 := by
    simp only [CheckSPAlignment,h_s0_sp]
    decide
  simp_all only [state_simp_rules,-h_run]
  sym_n 11
  have sp9 : r (StateField.GPR 31#5) s9 = r (StateField.GPR 31#5) s6 + 18446744073709551600#64 := by
    rw [h_s9_non_effects _ (by decide),h_s8_non_effects _ (by decide),h_s7_x31]
  have saved_callee : read_mem_bytes 16 (r (StateField.GPR 31#5) s9) s9 =
      r (StateField.GPR 30#5) s6 ++ r (StateField.GPR 29#5) s6 := by
    rw [sp9,Arm.Memory.State.read_mem_bytes_eq_mem_read_bytes,h_s9_memory_effects,
      h_s8_memory_effects,h_s7_memory_effects]
    exact (Arm.Memory.State.read_mem_bytes_eq_mem_read_bytes _).symm.trans
      (read_mem_bytes_of_write_mem_bytes_same (by decide))
  have returned_pc : r StateField.PC s11 = 0x200178#64 := by
    rw [h_s11_pc,h_s10_x30,saved_callee]
    simpa only [Arm.BitVec.extractLsb'_append_left] using h_s6_x30
  clear h_s11_pc
  have h_s11_pc := returned_pc
  sym_n 4 at s11
  constructor
  · simp (disch := decide) only [state_simp_rules,memory_rules,bitvec_rules,minimal_theory,
      Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate',Arm.BitVec.extractLsb'_append_left,
      h_s1_non_effects,h_s2_non_effects,h_s3_non_effects,h_s4_non_effects,h_s5_non_effects,
      h_s6_non_effects,h_s7_non_effects,h_s8_non_effects,h_s9_non_effects,h_s10_non_effects,
      h_s11_non_effects,h_s12_non_effects,h_s13_non_effects,h_s14_non_effects,h_s15_non_effects,
      h_s1_memory_effects,h_s2_memory_effects,h_s3_memory_effects,h_s4_memory_effects,h_s5_memory_effects,
      h_s6_memory_effects,h_s7_memory_effects,h_s8_memory_effects,h_s9_memory_effects,h_s10_memory_effects,
      h_s11_memory_effects,h_s12_memory_effects,h_s13_memory_effects,h_s14_memory_effects,h_s15_memory_effects,
      h_s15_pc,h_s15_err,h_s0_sp,h_s0_pointer,h_s1_x31,
      h_s2_x29,h_s3_x31,h_s4_x19,h_s5_x0,h_s6_x30,
      h_s7_x31,h_s8_x29,h_s9_x0,h_s10_x31,h_s10_x29,
      h_s10_x30,h_s13_x31,h_s13_x19,h_s14_x31,h_s14_x29,
      h_s14_x30]
    exact ⟨Arm.BitVec.extractLsb'_append_left (r (StateField.GPR 30#5) s0) (r (StateField.GPR 29#5) s0),
      Arm.BitVec.extractLsb'_append_right (r (StateField.GPR 30#5) s0) (r (StateField.GPR 29#5) s0)⟩
  · intro fld pc err zero saved fp lr sp
    simp (disch := simp [pc,err,zero,saved,fp,lr,sp]) only [
      h_s1_non_effects,h_s2_non_effects,h_s3_non_effects,h_s4_non_effects,h_s5_non_effects,
      h_s6_non_effects,h_s7_non_effects,h_s8_non_effects,h_s9_non_effects,h_s10_non_effects,
      h_s11_non_effects,h_s12_non_effects,h_s13_non_effects,h_s14_non_effects,h_s15_non_effects]
  all_goals
    apply Aligned_BitVecAdd_64_4
    · change CheckSPAlignment _
      assumption
    · decide


/-- Keep the original observable from the single effects proof. -/
theorem literal_run (s0 sf : Arm.ArmState)
    (h_s0_pc : read_pc s0 = 0x200160#64)
    (h_s0_program : s0.program = literalProgram)
    (h_s0_err : read_err s0 = .None)
    (h_s0_sp : read_gpr 64 31#5 s0 = 0x1000000#64)
    (h_s0_pointer : read_gpr 64 0#5 s0 = 0x300000#64)
    (h_run : sf = run 15 s0) :
    read_gpr 64 0#5 sf = read_gpr 64 1#5 s0 + 13#64 ∧
    read_mem_bytes 8 0x300008#64 sf = read_gpr 64 1#5 s0 + 13#64 ∧
    read_pc sf = read_gpr 64 30#5 s0 ∧ read_err sf = .None ∧
    read_gpr 64 31#5 sf = read_gpr 64 31#5 s0 ∧ read_gpr 64 19#5 sf = read_gpr 64 19#5 s0 := by
  obtain ⟨value,stored,pc,err,sp,saved,fp⟩ :=
    (literal_effects s0 sf h_s0_pc h_s0_program h_s0_err h_s0_sp h_s0_pointer h_run).1
  exact ⟨value,stored,pc,err,sp,saved⟩


/-- All AAPCS64 saved registers remain intact after the complete linked run. -/
theorem literal_arm_ret (s0 sf : Arm.ArmState)
    (h_s0_pc : read_pc s0 = 0x200160#64)
    (h_s0_program : s0.program = literalProgram)
    (h_s0_err : read_err s0 = .None)
    (h_s0_sp : read_gpr 64 31#5 s0 = 0x1000000#64)
    (h_s0_pointer : read_gpr 64 0#5 s0 = 0x300000#64)
    (h_run : sf = run 15 s0) :
    E2E.ArmRet (read_gpr 64 30#5 s0) s0 sf ∧
    read_gpr 64 0#5 sf = read_gpr 64 1#5 s0 + 13#64 ∧
    read_mem_bytes 8 0x300008#64 sf = read_gpr 64 1#5 s0 + 13#64 := by
  obtain ⟨⟨value,stored,pc,err,sp,saved,fp⟩,other⟩ :=
    literal_effects s0 sf h_s0_pc h_s0_program h_s0_err h_s0_sp h_s0_pointer h_run
  refine ⟨⟨?_,?_,?_,?_,?_⟩,value,stored⟩
  · simpa only [read_pc,read_gpr,BitVec.setWidth_eq] using pc
  · exact err
  · simpa only [E2E.spv,read_gpr,BitVec.setWidth_eq] using sp
  · intro n member
    have bounds : 19 ≤ n ∧ n ≤ 29 := by
      obtain ⟨i,inside,rfl⟩ := List.mem_map.mp member
      have hi := List.mem_range.mp inside
      omega
    have cases : n=19 ∨ n=20 ∨ n=21 ∨ n=22 ∨ n=23 ∨ n=24 ∨ n=25 ∨ n=26 ∨ n=27 ∨ n=28 ∨ n=29 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
    | simpa only [E2E.xreg,read_gpr,BitVec.setWidth_eq] using saved
    | simpa only [E2E.xreg,read_gpr,BitVec.setWidth_eq] using fp
    | exact other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro n lower upper
    exact congrArg (fun v : BitVec 128 => v.setWidth 64)
      (other (.SFP (BitVec.ofNat 5 n)) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))

end E2E.CallStorePhysicalExec
