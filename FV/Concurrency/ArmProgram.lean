import FV.Arm.Exec

/-!
# The Arm model never changes the program (T2, #311)

A linked Arm thread machine dispatches on the state's `program` field, so it needs that one Arm
step keeps that field: every instruction class writes only through `w`/`write_mem_bytes`, neither of
which touches `program` (`w_program`, `write_mem_bytes_program`).

* `exec_inst_program`: executing any instruction keeps `program`;
* `stepi_program`: hence so does `stepi`.
-/

namespace Concurrency.ArmFoot

open Arm

section updaters

variable (s : ArmState)

@[local simp] theorem write_gpr_program (n idx v) : (write_gpr n idx v s).program = s.program := by
  simp only [write_gpr, w_program]
@[local simp] theorem write_gpr_zr_program (n idx v) : (write_gpr_zr n idx v s).program = s.program := by
  unfold write_gpr_zr; split <;> simp only [write_gpr, w_program]
@[local simp] theorem write_sfp_program (n idx v) : (write_sfp n idx v s).program = s.program := by
  simp only [write_sfp, w_program]
@[local simp] theorem write_pc_program (v) : (write_pc v s).program = s.program := by
  simp only [write_pc, w_program]
@[local simp] theorem write_flag_program (f v) : (write_flag f v s).program = s.program := by
  simp only [write_flag, w_program]
@[local simp] theorem write_pstate_program (p) : (write_pstate p s).program = s.program := by
  simp only [write_pstate, w_program]
@[local simp] theorem write_err_program (v) : (write_err v s).program = s.program := by
  simp only [write_err, w_program]
@[local simp] theorem ldst_write_program (b n idx v) : (ldst_write b n idx v s).program = s.program := by
  unfold ldst_write; split <;> simp only [write_sfp_program, write_gpr_zr_program]

theorem ite_program {c : Prop} [Decidable c] (a b : ArmState) :
    (if c then a else b).program = if c then a.program else b.program := by split <;> rfl
theorem dite_program {c : Prop} [Decidable c] (a : c → ArmState) (b : ¬ c → ArmState) :
    (if h : c then a h else b h).program = if h : c then (a h).program else (b h).program := by
  split <;> rfl

/-- `program` is kept: push the projection through the updaters and conditionals, splitting the
matches on the way. -/
macro "progkeep" : tactic => `(tactic|
  ((try simp only [write_gpr_program, write_gpr_zr_program, write_sfp_program, write_pc_program,
      write_flag_program, write_pstate_program, write_err_program, ldst_write_program,
      w_program, write_mem_bytes_program,
      ite_program, dite_program, ite_self,
      DPR.conditional_compare, DPR.exec_data_processing_clz_cls, DPR.exec_data_processing_div,
      DPR.exec_data_processing_rbit, DPR.exec_data_processing_rev, DPR.exec_data_processing_shift,
      DPSFP.exec_addp_vector, DPSFP.exec_addv, DPSFP.exec_binary_vector, DPSFP.exec_dup_element,
      DPSFP.exec_dup_general, DPSFP.exec_fmov_general, DPSFP.fmov_general_aux, DPSFP.exec_fp_int_cvt,
      DPSFP.exec_ins_element, DPSFP.exec_ins_general, DPSFP.exec_logic_vector,
      DPSFP.exec_smov_umov, DPSFP.exec_uaddlv, DPSFP.fp_write_result, LDST.reg_imm_operation,
      LDST.reg_pair_operation, Reserved.exec_udf, Vpart_write]) <;> (repeat' (split <;> (try simp only [write_gpr_program, write_gpr_zr_program, write_sfp_program, write_pc_program,
      write_flag_program, write_pstate_program, write_err_program, ldst_write_program,
      w_program, write_mem_bytes_program,
      ite_program, dite_program, ite_self,
      DPR.conditional_compare, DPR.exec_data_processing_clz_cls, DPR.exec_data_processing_div,
      DPR.exec_data_processing_rbit, DPR.exec_data_processing_rev, DPR.exec_data_processing_shift,
      DPSFP.exec_addp_vector, DPSFP.exec_addv, DPSFP.exec_binary_vector, DPSFP.exec_dup_element,
      DPSFP.exec_dup_general, DPSFP.exec_fmov_general, DPSFP.fmov_general_aux, DPSFP.exec_fp_int_cvt,
      DPSFP.exec_ins_element, DPSFP.exec_ins_general, DPSFP.exec_logic_vector,
      DPSFP.exec_smov_umov, DPSFP.exec_uaddlv, DPSFP.fp_write_result, LDST.reg_imm_operation,
      LDST.reg_pair_operation, Reserved.exec_udf, Vpart_write]))) <;>
    (try simp only [write_gpr_program, write_gpr_zr_program, write_sfp_program, write_pc_program,
      write_flag_program, write_pstate_program, write_err_program, ldst_write_program,
      w_program, write_mem_bytes_program,
      ite_program, dite_program, ite_self,
      DPR.conditional_compare, DPR.exec_data_processing_clz_cls, DPR.exec_data_processing_div,
      DPR.exec_data_processing_rbit, DPR.exec_data_processing_rev, DPR.exec_data_processing_shift,
      DPSFP.exec_addp_vector, DPSFP.exec_addv, DPSFP.exec_binary_vector, DPSFP.exec_dup_element,
      DPSFP.exec_dup_general, DPSFP.exec_fmov_general, DPSFP.fmov_general_aux, DPSFP.exec_fp_int_cvt,
      DPSFP.exec_ins_element, DPSFP.exec_ins_general, DPSFP.exec_logic_vector,
      DPSFP.exec_smov_umov, DPSFP.exec_uaddlv, DPSFP.fp_write_result, LDST.reg_imm_operation,
      LDST.reg_pair_operation, Reserved.exec_udf, Vpart_write, dite_eq_ite]) <;> (try rfl) <;> (try simp_all [write_gpr_program, write_gpr_zr_program, write_sfp_program, write_pc_program,
      write_flag_program, write_pstate_program, write_err_program, ldst_write_program,
      w_program, write_mem_bytes_program,
      ite_program, dite_program, ite_self,
      DPR.conditional_compare, DPR.exec_data_processing_clz_cls, DPR.exec_data_processing_div,
      DPR.exec_data_processing_rbit, DPR.exec_data_processing_rev, DPR.exec_data_processing_shift,
      DPSFP.exec_addp_vector, DPSFP.exec_addv, DPSFP.exec_binary_vector, DPSFP.exec_dup_element,
      DPSFP.exec_dup_general, DPSFP.exec_fmov_general, DPSFP.fmov_general_aux, DPSFP.exec_fp_int_cvt,
      DPSFP.exec_ins_element, DPSFP.exec_ins_general, DPSFP.exec_logic_vector,
      DPSFP.exec_smov_umov, DPSFP.exec_uaddlv, DPSFP.fp_write_result, LDST.reg_imm_operation,
      LDST.reg_pair_operation, Reserved.exec_udf, Vpart_write])) <;> done)

@[local simp] theorem dpi_add_sub_imm_program (i) (s : ArmState) :
    (DPI.exec_add_sub_imm i s).program = s.program := by
  unfold DPI.exec_add_sub_imm; progkeep

@[local simp] theorem dpi_pc_rel_addressing_program (i) (s : ArmState) :
    (DPI.exec_pc_rel_addressing i s).program = s.program := by
  unfold DPI.exec_pc_rel_addressing; progkeep

@[local simp] theorem dpi_logical_imm_program (i) (s : ArmState) :
    (DPI.exec_logical_imm i s).program = s.program := by
  unfold DPI.exec_logical_imm; progkeep

@[local simp] theorem dpi_bitfield_program (i) (s : ArmState) :
    (DPI.exec_bitfield i s).program = s.program := by
  unfold DPI.exec_bitfield; progkeep

@[local simp] theorem dpi_move_wide_imm_program (i) (s : ArmState) :
    (DPI.exec_move_wide_imm i s).program = s.program := by
  unfold DPI.exec_move_wide_imm; progkeep

@[local simp] theorem dpi_extract_program (i) (s : ArmState) :
    (DPI.exec_extract i s).program = s.program := by
  unfold DPI.exec_extract; progkeep

@[local simp] theorem br_compare_branch_program (i) (s : ArmState) :
    (BR.exec_compare_branch i s).program = s.program := by
  unfold BR.exec_compare_branch; progkeep

@[local simp] theorem br_uncond_branch_imm_program (i) (s : ArmState) :
    (BR.exec_uncond_branch_imm i s).program = s.program := by
  unfold BR.exec_uncond_branch_imm; progkeep

@[local simp] theorem br_uncond_branch_reg_program (i) (s : ArmState) :
    (BR.exec_uncond_branch_reg i s).program = s.program := by
  unfold BR.exec_uncond_branch_reg; progkeep

@[local simp] theorem br_cond_branch_imm_program (i) (s : ArmState) :
    (BR.exec_cond_branch_imm i s).program = s.program := by
  unfold BR.exec_cond_branch_imm; progkeep

@[local simp] theorem br_hints_program (i) (s : ArmState) :
    (BR.exec_hints i s).program = s.program := by
  unfold BR.exec_hints; progkeep

@[local simp] theorem br_barrier_program (i) (s : ArmState) :
    (BR.exec_barrier i s).program = s.program := by
  unfold BR.exec_barrier; progkeep

@[local simp] theorem br_test_branch_program (i) (s : ArmState) :
    (BR.exec_test_branch i s).program = s.program := by
  unfold BR.exec_test_branch; progkeep

@[local simp] theorem br_mrs_program (i) (s : ArmState) :
    (BR.exec_mrs i s).program = s.program := by
  unfold BR.exec_mrs; progkeep

@[local simp] theorem dpr_add_sub_carry_program (i) (s : ArmState) :
    (DPR.exec_add_sub_carry i s).program = s.program := by
  unfold DPR.exec_add_sub_carry; progkeep

@[local simp] theorem dpr_add_sub_shifted_reg_program (i) (s : ArmState) :
    (DPR.exec_add_sub_shifted_reg i s).program = s.program := by
  unfold DPR.exec_add_sub_shifted_reg; progkeep

@[local simp] theorem dpr_conditional_select_program (i) (s : ArmState) :
    (DPR.exec_conditional_select i s).program = s.program := by
  unfold DPR.exec_conditional_select; progkeep

@[local simp] theorem dpr_data_processing_one_source_program (i) (s : ArmState) :
    (DPR.exec_data_processing_one_source i s).program = s.program := by
  unfold DPR.exec_data_processing_one_source; progkeep

@[local simp] theorem dpr_data_processing_two_source_program (i) (s : ArmState) :
    (DPR.exec_data_processing_two_source i s).program = s.program := by
  unfold DPR.exec_data_processing_two_source; progkeep

@[local simp] theorem dpr_logical_shifted_reg_program (i) (s : ArmState) :
    (DPR.exec_logical_shifted_reg i s).program = s.program := by
  unfold DPR.exec_logical_shifted_reg; progkeep

@[local simp] theorem dpr_data_processing_madd_program (i) (s : ArmState) :
    (DPR.exec_data_processing_madd i s).program = s.program := by
  unfold DPR.exec_data_processing_madd; progkeep

@[local simp] theorem dpr_data_processing_msub_program (i) (s : ArmState) :
    (DPR.exec_data_processing_msub i s).program = s.program := by
  unfold DPR.exec_data_processing_msub; progkeep

@[local simp] theorem dpr_data_processing_mulh_program (u i) (s : ArmState) :
    (DPR.exec_data_processing_mulh u i s).program = s.program := by
  unfold DPR.exec_data_processing_mulh; progkeep

@[local simp] theorem dpr_data_processing_maddl_program (u o i) (s : ArmState) :
    (DPR.exec_data_processing_maddl u o i s).program = s.program := by
  unfold DPR.exec_data_processing_maddl; progkeep

@[local simp] theorem dpr_data_processing_three_source_program (i) (s : ArmState) :
    (DPR.exec_data_processing_three_source i s).program = s.program := by
  unfold DPR.exec_data_processing_three_source; progkeep

@[local simp] theorem dpr_add_sub_ext_reg_program (i) (s : ArmState) :
    (DPR.exec_add_sub_ext_reg i s).program = s.program := by
  unfold DPR.exec_add_sub_ext_reg; progkeep

@[local simp] theorem dpr_conditional_compare_imm_program (i) (s : ArmState) :
    (DPR.exec_conditional_compare_imm i s).program = s.program := by
  unfold DPR.exec_conditional_compare_imm; progkeep

@[local simp] theorem dpr_conditional_compare_reg_program (i) (s : ArmState) :
    (DPR.exec_conditional_compare_reg i s).program = s.program := by
  unfold DPR.exec_conditional_compare_reg; progkeep

@[local simp] theorem dpsfp_advanced_simd_copy_program (i) (s : ArmState) :
    (DPSFP.exec_advanced_simd_copy i s).program = s.program := by
  unfold DPSFP.exec_advanced_simd_copy; progkeep

@[local simp] theorem dpsfp_rev_vector_program (i) (s : ArmState) :
    (DPSFP.exec_rev_vector i s).program = s.program := by
  unfold DPSFP.exec_rev_vector; progkeep

@[local simp] theorem dpsfp_cnt_program (i) (s : ArmState) :
    (DPSFP.exec_cnt i s).program = s.program := by
  unfold DPSFP.exec_cnt; progkeep

@[local simp] theorem dpsfp_advanced_simd_two_reg_misc_program (i) (s : ArmState) :
    (DPSFP.exec_advanced_simd_two_reg_misc i s).program = s.program := by
  unfold DPSFP.exec_advanced_simd_two_reg_misc; progkeep

@[local simp] theorem dpsfp_advanced_simd_three_same_program (i) (s : ArmState) :
    (DPSFP.exec_advanced_simd_three_same i s).program = s.program := by
  unfold DPSFP.exec_advanced_simd_three_same; progkeep

@[local simp] theorem dpsfp_conversion_between_FP_and_Int_program (i) (s : ArmState) :
    (DPSFP.exec_conversion_between_FP_and_Int i s).program = s.program := by
  unfold DPSFP.exec_conversion_between_FP_and_Int; progkeep

@[local simp] theorem dpsfp_advanced_simd_across_lanes_program (i) (s : ArmState) :
    (DPSFP.exec_advanced_simd_across_lanes i s).program = s.program := by
  unfold DPSFP.exec_advanced_simd_across_lanes; progkeep

@[local simp] theorem dpsfp_fp_data_processing_one_source_program (i) (s : ArmState) :
    (DPSFP.exec_fp_data_processing_one_source i s).program = s.program := by
  unfold DPSFP.exec_fp_data_processing_one_source; progkeep

@[local simp] theorem dpsfp_fp_immediate_program (i) (s : ArmState) :
    (DPSFP.exec_fp_immediate i s).program = s.program := by
  unfold DPSFP.exec_fp_immediate; progkeep

@[local simp] theorem dpsfp_fp_conditional_select_program (i) (s : ArmState) :
    (DPSFP.exec_fp_conditional_select i s).program = s.program := by
  unfold DPSFP.exec_fp_conditional_select; progkeep

@[local simp] theorem dpsfp_advanced_simd_modified_immediate_program (i) (s : ArmState) :
    (DPSFP.exec_advanced_simd_modified_immediate i s).program = s.program := by
  unfold DPSFP.exec_advanced_simd_modified_immediate; progkeep

@[local simp] theorem dpsfp_fp_data_processing_two_source_program (i) (s : ArmState) :
    (DPSFP.exec_fp_data_processing_two_source i s).program = s.program := by
  unfold DPSFP.exec_fp_data_processing_two_source; progkeep

@[local simp] theorem dpsfp_fp_data_processing_three_source_program (i) (s : ArmState) :
    (DPSFP.exec_fp_data_processing_three_source i s).program = s.program := by
  unfold DPSFP.exec_fp_data_processing_three_source; progkeep

@[local simp] theorem dpsfp_fp_compare_program (i) (s : ArmState) :
    (DPSFP.exec_fp_compare i s).program = s.program := by
  unfold DPSFP.exec_fp_compare; progkeep

@[local simp] theorem ldst_reg_imm_common_program (i inst_str) (s : ArmState) :
    (LDST.exec_reg_imm_common i inst_str s).program = s.program := by
  unfold LDST.exec_reg_imm_common; progkeep

@[local simp] theorem ldst_reg_imm_unsigned_offset_program (i) (s : ArmState) :
    (LDST.exec_reg_imm_unsigned_offset i s).program = s.program := by
  unfold LDST.exec_reg_imm_unsigned_offset; progkeep

@[local simp] theorem ldst_reg_imm_post_indexed_program (i) (s : ArmState) :
    (LDST.exec_reg_imm_post_indexed i s).program = s.program := by
  unfold LDST.exec_reg_imm_post_indexed; progkeep

@[local simp] theorem ldst_reg_imm_pre_indexed_program (i) (s : ArmState) :
    (LDST.exec_reg_imm_pre_indexed i s).program = s.program := by
  unfold LDST.exec_reg_imm_pre_indexed; progkeep

@[local simp] theorem ldst_reg_unscaled_imm_gpr_program (i) (s : ArmState) :
    (LDST.exec_reg_unscaled_imm_gpr i s).program = s.program := by
  unfold LDST.exec_reg_unscaled_imm_gpr; progkeep

@[local simp] theorem ldst_ldstur_program (i) (s : ArmState) :
    (LDST.exec_ldstur i s).program = s.program := by
  unfold LDST.exec_ldstur; progkeep

@[local simp] theorem ldst_reg_unscaled_imm_program (i) (s : ArmState) :
    (LDST.exec_reg_unscaled_imm i s).program = s.program := by
  unfold LDST.exec_reg_unscaled_imm; progkeep

@[local simp] theorem ldst_reg_pair_common_program (i inst_str) (s : ArmState) :
    (LDST.exec_reg_pair_common i inst_str s).program = s.program := by
  unfold LDST.exec_reg_pair_common; progkeep

@[local simp] theorem ldst_reg_pair_pre_indexed_program (i) (s : ArmState) :
    (LDST.exec_reg_pair_pre_indexed i s).program = s.program := by
  unfold LDST.exec_reg_pair_pre_indexed; progkeep

@[local simp] theorem ldst_reg_pair_post_indexed_program (i) (s : ArmState) :
    (LDST.exec_reg_pair_post_indexed i s).program = s.program := by
  unfold LDST.exec_reg_pair_post_indexed; progkeep

@[local simp] theorem ldst_reg_pair_signed_offset_program (i) (s : ArmState) :
    (LDST.exec_reg_pair_signed_offset i s).program = s.program := by
  unfold LDST.exec_reg_pair_signed_offset; progkeep

@[local simp] theorem ldst_reg_reg_offset_program (i) (s : ArmState) :
    (LDST.exec_reg_reg_offset i s).program = s.program := by
  unfold LDST.exec_reg_reg_offset; progkeep

@[local simp] theorem ldst_reg_exclusive_program (i) (s : ArmState) :
    (LDST.exec_reg_exclusive i s).program = s.program := by
  unfold LDST.exec_reg_exclusive; progkeep

@[local simp] theorem ldst_reg_literal_program (i) (s : ArmState) :
    (LDST.exec_reg_literal i s).program = s.program := by
  unfold LDST.exec_reg_literal; progkeep

@[local simp] theorem reserved_reserved_program (i) (s : ArmState) :
    (Reserved.exec_reserved i s).program = s.program := by
  unfold Reserved.exec_reserved; progkeep

/-- **One instruction never changes the program.** -/
theorem exec_inst_program (a : ArmInst) (s : ArmState) : (exec_inst a s).program = s.program := by
  cases a with
  | RES i => simp only [exec_inst]; simp
  | _ i => cases i <;> simp only [exec_inst] <;> simp

/-- **One step never changes the program.** -/
theorem stepi_program (s : ArmState) : (stepi s).program = s.program := by
  unfold stepi
  dsimp only
  repeat' split
  all_goals first
    | rfl
    | exact exec_inst_program _ _
    | exact write_err_program _ _

end updaters

end Concurrency.ArmFoot
