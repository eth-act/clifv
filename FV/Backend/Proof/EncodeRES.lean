import FV.Backend.Proof.EncodeBase
/-!
# M5: `decode_raw_inst (armBits a) = some a.norm` for the `RES` encoding classes

One theorem per class (C4.1 encoding diagram), generic in every field; proof: the
uniform `decode_class` tactic (`FV/Backend/Proof/EncodeBase.lean`).
-/

namespace Backend

open Arm

theorem decode_armBits_Udf (x : Udf_cls) :
    decode_raw_inst (armBits (.RES (.Udf x))) = some (ArmInst.RES (.Udf x)).norm := by
  decode_class decode_raw_inst_of_reserved decode_reserved

theorem decode_armBits_RES (x : ReservedInst) :
    decode_raw_inst (armBits (.RES x)) = some (ArmInst.RES x).norm := by
  cases x with
  | Udf x => exact decode_armBits_Udf x

end Backend
