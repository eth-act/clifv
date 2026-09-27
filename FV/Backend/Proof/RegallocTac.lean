import FV.Backend.Proof.RegallocCSem

/-!
# Tactics for the per-instruction proofs (M6 proof)

`csimp_rules`: the unfolding set for runs of emitted code. `corr_tac` proves `Corr` for a
concrete instruction form: it destructures the allocation (`AllocOk`), computes the allocated
run (symbolic registers) and the canonical run (`x 0`, `x 1`, …) with the same `simp` set and
matches them (`sw_tac` for the world, `FrameKeep`, def values, untouched registers).
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
  regVal spOf Arm.ConditionHolds Cond.invert Cond.bits Arm.write_err Arm.read_err beq_eq_decide'
  bitmaskEnc_false_one

/-- Close an equality of two values computed by the two runs. -/
syntax "veq_tac" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| veq_tac) => `(tactic| first
    | with_reducible rfl
    | (simp (config := {decide := true}) [csimp_rules, *]; done)
    | (rcases bv1_cases (Arm.r (.FLAG .N) s) with hN | hN <;>
        rcases bv1_cases (Arm.r (.FLAG .Z) s) with hZ | hZ <;>
        rcases bv1_cases (Arm.r (.FLAG .C) s) with hC | hC <;>
        rcases bv1_cases (Arm.r (.FLAG .V) s) with hV | hV <;>
        simp (config := {decide := true}) [csimp_rules, hN, hZ, hC, hV]))

/-- The world of the canonical run: strip masked register/pc writes from either side, match
equal writes of unmasked fields. -/
syntax "sw_tac" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| sw_tac) => `(tactic| repeat (first
    | assumption
    | contradiction
    | (refine SameWorld.ite_both (fun _ => ?_) (fun _ => ?_))
    | (refine SameWorld.w_left ?_ ?_; · (simp [Masked]; try omega))
    | (refine SameWorld.w_right ?_ ?_; · (simp [Masked]; try omega))
    | (refine SameWorld.w_both' ?_ ?_; · veq_tac)
    | (refine SameWorld.write_mem_bytes' ?_ ?_ ?_; · veq_tac
       · veq_tac)
    | simp only [*]))

/-- Proves `Corr F ctx env ops mk` for a concrete instruction form whose operands are all
`reg`-constrained (no fixed / reuse). -/
syntax "corr_tac" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| corr_tac) => `(tactic| (
    intro regs s w t' ha hw hacc hex herr
    have hsz := ha.size
    simp only [List.size_toArray, List.length_cons, List.length_nil] at hsz
    have hf := ha.fits
    first
      | (obtain ⟨r0, r1, r2, r3, rfl⟩ := regs4 hsz
         simp [RegFits] at hf
         rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩, ⟨n2, rfl, hn2⟩, ⟨n3, rfl, hn3⟩⟩)
      | (obtain ⟨r0, r1, r2, rfl⟩ := regs3 hsz
         simp [RegFits] at hf
         rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩, ⟨n2, rfl, hn2⟩⟩)
      | (obtain ⟨r0, r1, rfl⟩ := regs2 hsz
         simp [RegFits] at hf
         rcases hf with ⟨⟨n0, rfl, hn0⟩, ⟨n1, rfl, hn1⟩⟩)
      | (obtain ⟨r0, rfl⟩ := regs1 hsz
         simp [RegFits] at hf
         rcases hf with ⟨n0, rfl, hn0⟩)
    try (have hre := ha.reuse 1 0 rfl; simp at hre; subst hre)
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
    generalize hA : execMInst ctx env _ s = oa
    simp (config := {decide := true}) [csimp_rules, hfl, hsp, hx29, *] at hex hA
    all_goals (repeat' (first
      | subst hex
      | (split at hex <;> try simp (config := {decide := true}) [csimp_rules, *] at hex hA)))
    all_goals subst hA
    all_goals (try simp (config := {decide := true}) [csimp_rules] at herr)
    all_goals (repeat' (split at herr <;> try simp (config := {decide := true}) [csimp_rules, *] at herr))
    all_goals (
      refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
      · sw_tac
      · refine ⟨?_, fun a _ => ?_⟩
        · simp (config := {decide := true}) [csimp_rules, *]
        · first
            | (simp [csimp_rules, Arm.ArmState.mem_w_eq_mem, *]; done)
            | ((repeat' split) <;> simp [csimp_rules, Arm.ArmState.mem_w_eq_mem, *])
      · veq_tac
      · intro r hr hnd
        rcases allocatable_cases hr with ⟨k, rfl, hk⟩|⟨k, rfl, hk⟩
        · try simp [Operand.isDef] at hnd
          try have hnd' := Ne.symm hnd
          simp (config := {decide := true}) (disch := omega) [csimp_rules, ofNat5_eq_iff, *]
        · try simp [Operand.isDef] at hnd
          try have hnd' := Ne.symm hnd
          simp (config := {decide := true}) (disch := omega) [csimp_rules, ofNat5_eq_iff, *])))

end Backend.Proof
