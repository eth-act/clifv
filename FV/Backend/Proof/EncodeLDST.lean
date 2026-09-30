import FV.Backend.Proof.EncodeBase
/-!
# M5: `decode_raw_inst (armBits a) = some a.norm` for the `LDST` encoding classes

One theorem per class (C4.1 encoding diagram), generic in every field; proof: the
uniform `decode_class` tactic (`FV/Backend/Proof/EncodeBase.lean`).
-/

namespace Backend

open Arm

theorem decode_armBits_Reg_imm_post_indexed (x : Reg_imm_post_indexed_cls) :
    decode_raw_inst (armBits (.LDST (.Reg_imm_post_indexed x))) = some (ArmInst.LDST (.Reg_imm_post_indexed x)).norm := by
  decode_class decode_raw_inst_of_ldst decode_ldst_inst

theorem decode_armBits_Reg_unsigned_imm (x : Reg_unsigned_imm_cls) :
    decode_raw_inst (armBits (.LDST (.Reg_unsigned_imm x))) = some (ArmInst.LDST (.Reg_unsigned_imm x)).norm := by
  decode_class decode_raw_inst_of_ldst decode_ldst_inst

theorem decode_armBits_Reg_unscaled_imm (x : Reg_unscaled_imm_cls) :
    decode_raw_inst (armBits (.LDST (.Reg_unscaled_imm x))) = some (ArmInst.LDST (.Reg_unscaled_imm x)).norm := by
  decode_class decode_raw_inst_of_ldst decode_ldst_inst

theorem decode_armBits_Reg_pair_pre_indexed (x : Reg_pair_pre_indexed_cls) :
    decode_raw_inst (armBits (.LDST (.Reg_pair_pre_indexed x))) = some (ArmInst.LDST (.Reg_pair_pre_indexed x)).norm := by
  decode_class decode_raw_inst_of_ldst decode_ldst_inst

theorem decode_armBits_Reg_pair_post_indexed (x : Reg_pair_post_indexed_cls) :
    decode_raw_inst (armBits (.LDST (.Reg_pair_post_indexed x))) = some (ArmInst.LDST (.Reg_pair_post_indexed x)).norm := by
  decode_class decode_raw_inst_of_ldst decode_ldst_inst

theorem decode_armBits_Reg_pair_signed_offset (x : Reg_pair_signed_offset_cls) :
    decode_raw_inst (armBits (.LDST (.Reg_pair_signed_offset x))) = some (ArmInst.LDST (.Reg_pair_signed_offset x)).norm := by
  decode_class decode_raw_inst_of_ldst decode_ldst_inst

theorem decode_armBits_Reg_imm_pre_indexed (x : Reg_imm_pre_indexed_cls) :
    decode_raw_inst (armBits (.LDST (.Reg_imm_pre_indexed x))) = some (ArmInst.LDST (.Reg_imm_pre_indexed x)).norm := by
  decode_class decode_raw_inst_of_ldst decode_ldst_inst

theorem decode_armBits_Reg_reg_offset (x : Reg_reg_offset_cls) :
    decode_raw_inst (armBits (.LDST (.Reg_reg_offset x))) = some (ArmInst.LDST (.Reg_reg_offset x)).norm := by
  decode_class decode_raw_inst_of_ldst decode_ldst_inst

theorem decode_armBits_Reg_exclusive (x : Reg_exclusive_cls) :
    decode_raw_inst (armBits (.LDST (.Reg_exclusive x))) = some (ArmInst.LDST (.Reg_exclusive x)).norm := by
  decode_class decode_raw_inst_of_ldst decode_ldst_inst

theorem decode_armBits_LDST (x : LDSTInst) :
    decode_raw_inst (armBits (.LDST x)) = some (ArmInst.LDST x).norm := by
  cases x with
  | Reg_imm_post_indexed x => exact decode_armBits_Reg_imm_post_indexed x
  | Reg_unsigned_imm x => exact decode_armBits_Reg_unsigned_imm x
  | Reg_unscaled_imm x => exact decode_armBits_Reg_unscaled_imm x
  | Reg_pair_pre_indexed x => exact decode_armBits_Reg_pair_pre_indexed x
  | Reg_pair_post_indexed x => exact decode_armBits_Reg_pair_post_indexed x
  | Reg_pair_signed_offset x => exact decode_armBits_Reg_pair_signed_offset x
  | Reg_imm_pre_indexed x => exact decode_armBits_Reg_imm_pre_indexed x
  | Reg_reg_offset x => exact decode_armBits_Reg_reg_offset x

end Backend
