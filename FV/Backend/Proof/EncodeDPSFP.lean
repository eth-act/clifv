module

import FV.Backend.Proof.EncodeBase
public import FV.Backend.Encode
import Std.Tactic.BVDecide.Normalize.Prop
import Std.Data.DTreeMap.Internal.Operations

@[expose] public section

/-!
# M5: `decode_raw_inst (armBits a) = some a.norm` for the `DPSFP` encoding classes

One theorem per class (C4.1 encoding diagram), generic in every field; proof: the
uniform `decode_class` tactic (`FV/Backend/Proof/EncodeBase.lean`).
-/

namespace Backend

open Arm

theorem decode_armBits_Advanced_simd_two_reg_misc (x : Advanced_simd_two_reg_misc_cls) :
    decode_raw_inst (armBits (.DPSFP (.Advanced_simd_two_reg_misc x))) = some (ArmInst.DPSFP (.Advanced_simd_two_reg_misc x)).norm := by
  decode_class decode_raw_inst_of_dpsfp decode_data_proc_sfp

theorem decode_armBits_Advanced_simd_copy (x : Advanced_simd_copy_cls) :
    decode_raw_inst (armBits (.DPSFP (.Advanced_simd_copy x))) = some (ArmInst.DPSFP (.Advanced_simd_copy x)).norm := by
  decode_class decode_raw_inst_of_dpsfp decode_data_proc_sfp

theorem decode_armBits_Advanced_simd_three_same (x : Advanced_simd_three_same_cls) :
    decode_raw_inst (armBits (.DPSFP (.Advanced_simd_three_same x))) = some (ArmInst.DPSFP (.Advanced_simd_three_same x)).norm := by
  decode_class decode_raw_inst_of_dpsfp decode_data_proc_sfp

theorem decode_armBits_Conversion_between_FP_and_Int (x : Conversion_between_FP_and_Int_cls) :
    decode_raw_inst (armBits (.DPSFP (.Conversion_between_FP_and_Int x))) = some (ArmInst.DPSFP (.Conversion_between_FP_and_Int x)).norm := by
  decode_class decode_raw_inst_of_dpsfp decode_data_proc_sfp

theorem decode_armBits_Advanced_simd_across_lanes (x : Advanced_simd_across_lanes_cls) :
    decode_raw_inst (armBits (.DPSFP (.Advanced_simd_across_lanes x))) = some (ArmInst.DPSFP (.Advanced_simd_across_lanes x)).norm := by
  decode_class decode_raw_inst_of_dpsfp decode_data_proc_sfp

theorem decode_armBits_FP_data_processing_one_source (x : FP_data_processing_one_source_cls) :
    decode_raw_inst (armBits (.DPSFP (.FP_data_processing_one_source x))) = some (ArmInst.DPSFP (.FP_data_processing_one_source x)).norm := by
  decode_class decode_raw_inst_of_dpsfp decode_data_proc_sfp

theorem decode_armBits_FP_immediate (x : FP_immediate_cls) :
    decode_raw_inst (armBits (.DPSFP (.FP_immediate x))) = some (ArmInst.DPSFP (.FP_immediate x)).norm := by
  decode_class decode_raw_inst_of_dpsfp decode_data_proc_sfp

theorem decode_armBits_FP_conditional_select (x : FP_conditional_select_cls) :
    decode_raw_inst (armBits (.DPSFP (.FP_conditional_select x))) = some (ArmInst.DPSFP (.FP_conditional_select x)).norm := by
  decode_class decode_raw_inst_of_dpsfp decode_data_proc_sfp

theorem decode_armBits_Advanced_simd_modified_immediate (x : Advanced_simd_modified_immediate_cls) :
    decode_raw_inst (armBits (.DPSFP (.Advanced_simd_modified_immediate x))) = some (ArmInst.DPSFP (.Advanced_simd_modified_immediate x)).norm := by
  decode_class decode_raw_inst_of_dpsfp decode_data_proc_sfp

theorem decode_armBits_FP_data_processing_two_source (x : FP_data_processing_two_source_cls) :
    decode_raw_inst (armBits (.DPSFP (.FP_data_processing_two_source x))) = some (ArmInst.DPSFP (.FP_data_processing_two_source x)).norm := by
  decode_class decode_raw_inst_of_dpsfp decode_data_proc_sfp

theorem decode_armBits_FP_data_processing_three_source (x : FP_data_processing_three_source_cls) :
    decode_raw_inst (armBits (.DPSFP (.FP_data_processing_three_source x))) = some (ArmInst.DPSFP (.FP_data_processing_three_source x)).norm := by
  decode_class decode_raw_inst_of_dpsfp decode_data_proc_sfp

theorem decode_armBits_FP_compare (x : FP_compare_cls) :
    decode_raw_inst (armBits (.DPSFP (.FP_compare x))) = some (ArmInst.DPSFP (.FP_compare x)).norm := by
  decode_class decode_raw_inst_of_dpsfp decode_data_proc_sfp

theorem decode_armBits_DPSFP (x : DataProcSFPInst) :
    decode_raw_inst (armBits (.DPSFP x)) = some (ArmInst.DPSFP x).norm := by
  cases x with
  | Advanced_simd_two_reg_misc x => exact decode_armBits_Advanced_simd_two_reg_misc x
  | Advanced_simd_copy x => exact decode_armBits_Advanced_simd_copy x
  | Advanced_simd_three_same x => exact decode_armBits_Advanced_simd_three_same x
  | Conversion_between_FP_and_Int x => exact decode_armBits_Conversion_between_FP_and_Int x
  | Advanced_simd_across_lanes x => exact decode_armBits_Advanced_simd_across_lanes x
  | FP_data_processing_one_source x => exact decode_armBits_FP_data_processing_one_source x
  | FP_immediate x => exact decode_armBits_FP_immediate x
  | FP_conditional_select x => exact decode_armBits_FP_conditional_select x
  | Advanced_simd_modified_immediate x => exact decode_armBits_Advanced_simd_modified_immediate x
  | FP_data_processing_two_source x => exact decode_armBits_FP_data_processing_two_source x
  | FP_data_processing_three_source x => exact decode_armBits_FP_data_processing_three_source x
  | FP_compare x => exact decode_armBits_FP_compare x

end Backend
