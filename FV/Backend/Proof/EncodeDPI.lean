import FV.Backend.Proof.EncodeBase
/-!
# M5: `decode_raw_inst (armBits a) = some a.norm` for the `DPI` encoding classes

One theorem per class (C4.1 encoding diagram), generic in every field; proof: the
uniform `decode_class` tactic (`FV/Backend/Proof/EncodeBase.lean`).
-/

namespace Backend

open Arm

theorem decode_armBits_Add_sub_imm (x : Add_sub_imm_cls) :
    decode_raw_inst (armBits (.DPI (.Add_sub_imm x))) = some (ArmInst.DPI (.Add_sub_imm x)).norm := by
  decode_class decode_raw_inst_of_dpi decode_data_proc_imm

theorem decode_armBits_Logical_imm (x : Logical_imm_cls) :
    decode_raw_inst (armBits (.DPI (.Logical_imm x))) = some (ArmInst.DPI (.Logical_imm x)).norm := by
  decode_class decode_raw_inst_of_dpi decode_data_proc_imm

theorem decode_armBits_PC_rel_addressing (x : PC_rel_addressing_cls) :
    decode_raw_inst (armBits (.DPI (.PC_rel_addressing x))) = some (ArmInst.DPI (.PC_rel_addressing x)).norm := by
  decode_class decode_raw_inst_of_dpi decode_data_proc_imm

theorem decode_armBits_Bitfield (x : Bitfield_cls) :
    decode_raw_inst (armBits (.DPI (.Bitfield x))) = some (ArmInst.DPI (.Bitfield x)).norm := by
  decode_class decode_raw_inst_of_dpi decode_data_proc_imm

theorem decode_armBits_Move_wide_imm (x : Move_wide_imm_cls) :
    decode_raw_inst (armBits (.DPI (.Move_wide_imm x))) = some (ArmInst.DPI (.Move_wide_imm x)).norm := by
  decode_class decode_raw_inst_of_dpi decode_data_proc_imm

theorem decode_armBits_Extract (x : Extract_cls) :
    decode_raw_inst (armBits (.DPI (.Extract x))) = some (ArmInst.DPI (.Extract x)).norm := by
  decode_class decode_raw_inst_of_dpi decode_data_proc_imm

theorem decode_armBits_DPI (x : DataProcImmInst) :
    decode_raw_inst (armBits (.DPI x)) = some (ArmInst.DPI x).norm := by
  cases x with
  | Add_sub_imm x => exact decode_armBits_Add_sub_imm x
  | Logical_imm x => exact decode_armBits_Logical_imm x
  | PC_rel_addressing x => exact decode_armBits_PC_rel_addressing x
  | Bitfield x => exact decode_armBits_Bitfield x
  | Move_wide_imm x => exact decode_armBits_Move_wide_imm x
  | Extract x => exact decode_armBits_Extract x

end Backend
