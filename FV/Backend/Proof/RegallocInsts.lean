import FV.Backend.Proof.RegallocCSem

/-!
# `OperandsSound` for the straight-line instructions (M6 proof)

Every straight-line `MInst` form the backend emits, with vreg operands, satisfies
`OperandsSound F (execMInst ctx env) (csem F ctx X)`. Each proof is `os_of_corr` plus `Corr`
by `corr_tac`, which computes the allocated run (symbolic registers) and the canonical run
(`x 0`, `x 1`, …) with the same `simp` set and matches them (`sw_tac` for the world).
-/

namespace Backend.Proof

open Backend

attribute [csimp_rules] execMInst MInst.lines execLines
  Insn.toArmInst Insn.armFields Insn.armFields.dp2 Arm.ArmInst.norm Reg.encZR
  Reg.encSP Reg.encV ALUOp.addSub? ALUOp.logic? b1 OperandSize.is64 uField sField
  placeUses useVals defVals Operand.isUse Operand.isDef Arm.exec_inst
  Arm.DPR.exec_add_sub_shifted_reg Arm.DPR.exec_logical_shifted_reg
  Arm.DPR.exec_logical_shifted_reg_op Arm.DPR.decode_op
  Arm.DPR.exec_data_processing_two_source Arm.DPR.exec_data_processing_shift
  Arm.DPR.exec_data_processing_div Arm.DPR.exec_data_processing_three_source
  Arm.DPR.exec_data_processing_mulh Arm.DPR.exec_data_processing_madd
  Arm.DPR.exec_data_processing_msub Arm.DPR.exec_add_sub_carry
  Arm.DPR.exec_add_sub_ext_reg Arm.DPR.exec_conditional_select
  Arm.DPR.exec_conditional_compare_reg Arm.DPR.exec_conditional_compare_imm
  Arm.DPR.conditional_compare Arm.DPR.exec_data_processing_one_source
  Arm.DPR.exec_data_processing_rev Arm.DPR.exec_data_processing_rbit
  Arm.DPR.exec_data_processing_clz_cls Arm.DPR.logical_shifted_reg_update_pstate
  Arm.DPI.exec_add_sub_imm Arm.DPI.exec_logical_imm Arm.DPI.exec_logical_imm_op
  Arm.DPI.decode_op Arm.DPI.update_logical_imm_pstate Arm.DPI.exec_bitfield
  Arm.DPI.exec_extract Arm.DPI.exec_move_wide_imm
  Arm.read_gpr_zr Arm.write_gpr_zr Arm.read_gpr Arm.write_gpr Arm.decode_shift
  Arm.shift_reg Arm.read_pc Arm.write_pc Arm.write_pstate Arm.read_flag rnum lo64
  regVal spOf

/-- Proves `Corr F ctx env ops mk` for a concrete instruction form whose operands are all
`reg`-constrained (no fixed / reuse). -/
syntax "corr_tac" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| corr_tac) => `(tactic| (
    intro regs s w t' ha hw hacc hex
    have hsz := ha.size
    simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz
    first
      | (obtain ⟨r0, r1, r2, r3, rfl⟩ := regs4 hsz)
      | (obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz)
      | (obtain ⟨r0, r1, rfl⟩ := regs2 hsz)
      | (obtain ⟨r0, rfl⟩ := regs1 hsz)
    have hf := ha.fits
    simp [RegFits] at hf
    first
      | (rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩, ⟨n2, rfl, hn2⟩, ⟨n3, rfl, hn3⟩⟩)
      | (rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩, ⟨n2, rfl, hn2⟩⟩)
      | (rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩⟩)
      | (rcases hf with ⟨n0, rfl, hn0⟩)
    have hfl : ∀ f, Arm.r (.FLAG f) w = Arm.r (.FLAG f) s :=
      fun f => (hw.1 (.FLAG f) (by simp [Masked])).symm
    have hsp : Arm.r (.GPR 31#5) w = Arm.r (.GPR 31#5) s :=
      (hw.1 (.GPR 31#5) (by simp [Masked])).symm
    have hx29 : Arm.r (.GPR 29#5) w = Arm.r (.GPR 29#5) s :=
      (hw.1 (.GPR 29#5) (by simp [Masked])).symm
    try have e0 := ne31_of hn0.1
    try have e1 := ne31_of hn1.1
    try have e2 := ne31_of hn2.1
    try have e3 := ne31_of hn3.1
    try have e0' := ne31_of' hn0.1
    try have e1' := ne31_of' hn1.1
    try have e2' := ne31_of' hn2.1
    try have e3' := ne31_of' hn3.1
    try have l0 := le30_of hn0.1
    try have l1 := le30_of hn1.1
    try have l2 := le30_of hn2.1
    try have l3 := le30_of hn3.1
    try have f0 := le31_of hn0
    try have f1 := le31_of hn1
    try have f2 := le31_of hn2
    simp only [canonRegs, canonReg, canonBase, List.size_toArray, List.length_cons,
      List.length_nil, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil, List.getElem?_toArray, List.getElem?_cons_zero,
      List.getElem?_cons_succ] at hex hacc ⊢
    simp (config := {decide := true}) [csimp_rules, hfl, hsp, hx29, *] at hex ⊢
    subst hex
    refine ⟨?_, ?_, ?_, ?_⟩
    · sw_tac
    · refine ⟨by simp (config := {decide := true}) [csimp_rules, *], fun a _ => by simp [csimp_rules, Arm.ArmState.mem_w_eq_mem]⟩
    · first | with_reducible rfl | simp (config := {decide := true}) [csimp_rules, *]
    · intro r hr hnd
      rcases allocatable_cases hr with ⟨k, rfl, hk⟩|⟨k, rfl, hk⟩
      · simp at hnd
        simp (config := {decide := true}) (disch := omega) [csimp_rules, ofNat5_eq_iff, Ne.symm, *]
      · simp (config := {decide := true}) [csimp_rules, *]))

/-! ## ALU, three registers -/

set_option maxHeartbeats 4000000 in
theorem corr_aluRRR (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (op : ALUOp)
    (sz : OperandSize) (d n m : Nat) :
    Corr F ctx env #[⟨d, .int, .def, .late, .reg⟩, ⟨n, .int, .use, .early, .reg⟩,
      ⟨m, .int, .use, .early, .reg⟩]
      (fun r => .aluRRR op sz (r.getD 0 .xzr) (r.getD 1 .xzr) (r.getD 2 .xzr)) := by
  cases op <;> cases sz <;> corr_tac

theorem os_aluRRR (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (X : ExtSem) (op : ALUOp)
    (sz : OperandSize) (d n m : Nat) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.aluRRR op sz (.vreg d .int) (.vreg n .int) (.vreg m .int)) :=
  os_of_corr rfl _ (fun regs h => by obtain ⟨a, b, c, rfl⟩ := regs3 (by simpa using h); rfl)
    rfl rfl (corr_aluRRR F ctx env op sz d n m)

end Backend.Proof
