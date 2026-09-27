import FV.Backend.Proof.EncodeBase
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

theorem decode_armBits_DPSFP (x : DataProcSFPInst) :
    decode_raw_inst (armBits (.DPSFP x)) = some (ArmInst.DPSFP x).norm := by
  cases x with
  | Advanced_simd_two_reg_misc x => exact decode_armBits_Advanced_simd_two_reg_misc x
  | Advanced_simd_copy x => exact decode_armBits_Advanced_simd_copy x
  | Advanced_simd_three_same x => exact decode_armBits_Advanced_simd_three_same x
  | Conversion_between_FP_and_Int x => exact decode_armBits_Conversion_between_FP_and_Int x
  | Advanced_simd_across_lanes x => exact decode_armBits_Advanced_simd_across_lanes x

end Backend
