import FV.Backend.Proof.EncodeBase
/-!
# M5: `decode_raw_inst (armBits a) = some a.norm` for the `BR` encoding classes

One theorem per class (C4.1 encoding diagram), generic in every field; proof: the
uniform `decode_class` tactic (`FV/Backend/Proof/EncodeBase.lean`).
-/

namespace Backend

open Arm

theorem decode_armBits_Compare_branch (x : Compare_branch_cls) :
    decode_raw_inst (armBits (.BR (.Compare_branch x))) = some (ArmInst.BR (.Compare_branch x)).norm := by
  decode_class decode_raw_inst_of_br decode_branch

theorem decode_armBits_Uncond_branch_imm (x : Uncond_branch_imm_cls) :
    decode_raw_inst (armBits (.BR (.Uncond_branch_imm x))) = some (ArmInst.BR (.Uncond_branch_imm x)).norm := by
  decode_class decode_raw_inst_of_br decode_branch

theorem decode_armBits_Uncond_branch_reg (x : Uncond_branch_reg_cls) :
    decode_raw_inst (armBits (.BR (.Uncond_branch_reg x))) = some (ArmInst.BR (.Uncond_branch_reg x)).norm := by
  decode_class decode_raw_inst_of_br decode_branch

theorem decode_armBits_Cond_branch_imm (x : Cond_branch_imm_cls) :
    decode_raw_inst (armBits (.BR (.Cond_branch_imm x))) = some (ArmInst.BR (.Cond_branch_imm x)).norm := by
  decode_class decode_raw_inst_of_br decode_branch

theorem decode_armBits_Hints (x : Hints_cls) :
    decode_raw_inst (armBits (.BR (.Hints x))) = some (ArmInst.BR (.Hints x)).norm := by
  decode_class decode_raw_inst_of_br decode_branch

theorem decode_armBits_Test_branch (x : Test_branch_cls) :
    decode_raw_inst (armBits (.BR (.Test_branch x))) = some (ArmInst.BR (.Test_branch x)).norm := by
  decode_class decode_raw_inst_of_br decode_branch

theorem decode_armBits_BR (x : BranchInst) :
    decode_raw_inst (armBits (.BR x)) = some (ArmInst.BR x).norm := by
  cases x with
  | Compare_branch x => exact decode_armBits_Compare_branch x
  | Uncond_branch_imm x => exact decode_armBits_Uncond_branch_imm x
  | Uncond_branch_reg x => exact decode_armBits_Uncond_branch_reg x
  | Cond_branch_imm x => exact decode_armBits_Cond_branch_imm x
  | Hints x => exact decode_armBits_Hints x
  | Test_branch x => exact decode_armBits_Test_branch x

end Backend
