import FV.Backend.Proof.EncodeBase
/-!
# M5: `decode_raw_inst (armBits a) = some a.norm` for the `DPR` encoding classes

One theorem per class (C4.1 encoding diagram), generic in every field; proof: the
uniform `decode_class` tactic (`FV/Backend/Proof/EncodeBase.lean`).
-/

namespace Backend

open Arm

theorem decode_armBits_Add_sub_carry (x : Add_sub_carry_cls) :
    decode_raw_inst (armBits (.DPR (.Add_sub_carry x))) = some (ArmInst.DPR (.Add_sub_carry x)).norm := by
  decode_class decode_raw_inst_of_dpr decode_data_proc_reg

theorem decode_armBits_Add_sub_shifted_reg (x : Add_sub_shifted_reg_cls) :
    decode_raw_inst (armBits (.DPR (.Add_sub_shifted_reg x))) = some (ArmInst.DPR (.Add_sub_shifted_reg x)).norm := by
  decode_class decode_raw_inst_of_dpr decode_data_proc_reg

theorem decode_armBits_Add_sub_ext_reg (x : Add_sub_ext_reg_cls) :
    decode_raw_inst (armBits (.DPR (.Add_sub_ext_reg x))) = some (ArmInst.DPR (.Add_sub_ext_reg x)).norm := by
  decode_class decode_raw_inst_of_dpr decode_data_proc_reg

theorem decode_armBits_Conditional_compare_imm (x : Conditional_compare_imm_cls) :
    decode_raw_inst (armBits (.DPR (.Conditional_compare_imm x))) = some (ArmInst.DPR (.Conditional_compare_imm x)).norm := by
  decode_class decode_raw_inst_of_dpr decode_data_proc_reg

theorem decode_armBits_Conditional_compare_reg (x : Conditional_compare_reg_cls) :
    decode_raw_inst (armBits (.DPR (.Conditional_compare_reg x))) = some (ArmInst.DPR (.Conditional_compare_reg x)).norm := by
  decode_class decode_raw_inst_of_dpr decode_data_proc_reg

theorem decode_armBits_Conditional_select (x : Conditional_select_cls) :
    decode_raw_inst (armBits (.DPR (.Conditional_select x))) = some (ArmInst.DPR (.Conditional_select x)).norm := by
  decode_class decode_raw_inst_of_dpr decode_data_proc_reg

theorem decode_armBits_Barrier (x : Barrier_cls) :
    decode_raw_inst (armBits (.DPR (.Barrier x))) = some (ArmInst.DPR (.Barrier x)).norm := by
  decode_class decode_raw_inst_of_dpr decode_data_proc_reg

theorem decode_armBits_Data_processing_one_source (x : Data_processing_one_source_cls) :
    decode_raw_inst (armBits (.DPR (.Data_processing_one_source x))) = some (ArmInst.DPR (.Data_processing_one_source x)).norm := by
  decode_class decode_raw_inst_of_dpr decode_data_proc_reg

theorem decode_armBits_Data_processing_two_source (x : Data_processing_two_source_cls) :
    decode_raw_inst (armBits (.DPR (.Data_processing_two_source x))) = some (ArmInst.DPR (.Data_processing_two_source x)).norm := by
  decode_class decode_raw_inst_of_dpr decode_data_proc_reg

theorem decode_armBits_Logical_shifted_reg (x : Logical_shifted_reg_cls) :
    decode_raw_inst (armBits (.DPR (.Logical_shifted_reg x))) = some (ArmInst.DPR (.Logical_shifted_reg x)).norm := by
  decode_class decode_raw_inst_of_dpr decode_data_proc_reg

theorem decode_armBits_Data_processing_three_source (x : Data_processing_three_source_cls) :
    decode_raw_inst (armBits (.DPR (.Data_processing_three_source x))) = some (ArmInst.DPR (.Data_processing_three_source x)).norm := by
  decode_class decode_raw_inst_of_dpr decode_data_proc_reg

theorem decode_armBits_DPR (x : DataProcRegInst) :
    decode_raw_inst (armBits (.DPR x)) = some (ArmInst.DPR x).norm := by
  cases x with
  | Add_sub_carry x => exact decode_armBits_Add_sub_carry x
  | Add_sub_shifted_reg x => exact decode_armBits_Add_sub_shifted_reg x
  | Add_sub_ext_reg x => exact decode_armBits_Add_sub_ext_reg x
  | Conditional_compare_imm x => exact decode_armBits_Conditional_compare_imm x
  | Conditional_compare_reg x => exact decode_armBits_Conditional_compare_reg x
  | Conditional_select x => exact decode_armBits_Conditional_select x
  | Data_processing_one_source x => exact decode_armBits_Data_processing_one_source x
  | Data_processing_two_source x => exact decode_armBits_Data_processing_two_source x
  | Logical_shifted_reg x => exact decode_armBits_Logical_shifted_reg x
  | Data_processing_three_source x => exact decode_armBits_Data_processing_three_source x

end Backend
