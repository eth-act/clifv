import FV.Backend.Proof.IselFloatCvt
import FV.Backend.Proof.LowerContractTF

/-!
# The conversion roots over float-capable contexts (S11f-cvt, #410)

`lowerRulesCorrectCvtT_program : LowerRulesCorrectCvtT program`: the sixteen conversion roots
of `lower` (`floatCvtRootRule`) are correct over float-capable contexts, from
`IselFloatCvt`'s `fcvt_from_uint_f32_le32_okT` … `fcvt_to_sint_sat_i64_f64_okT` (the integer
`lowerRulesCorrect_program` dispatches the same lemmas through `.toOk`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 100000

/-- The conversion roots of `lower`, in order. -/
theorem lower_floatCvtRoot_filter : (program.rulesOf TId.lower).filter floatCvtRootRule =
    [rule_lower_730, rule_lower_733, rule_lower_750, rule_lower_753, rule_lower_767,
      rule_lower_773, rule_lower_787, rule_lower_793, rule_lower_724, rule_lower_727,
      rule_lower_744, rule_lower_747, rule_lower_764, rule_lower_770, rule_lower_784,
      rule_lower_790] := by
  rw [program_rulesOf_686]
  rfl

/-- **S11f-cvt's target**: over float-capable contexts (`CtxInvT`), the `fcvt_from_{u,s}int`
and `fcvt_to_{u,s}int_sat` roots are correct. -/
theorem lowerRulesCorrectCvtT_program : LowerRulesCorrectCvtT program := by
  intro F isem MR env cp hR hMR r hr hfc
  have hp := data_program
  have hsub : r ∈ (program.rulesOf TId.lower).filter floatCvtRootRule :=
    List.mem_filter.2 ⟨hr, hfc⟩
  rw [lower_floatCvtRoot_filter] at hsub
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsub
  rcases hsub with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact fcvt_from_uint_f32_i64_okT hp MR env cp hR hMR
  · exact fcvt_from_uint_f64_i64_okT hp MR env cp hR hMR
  · exact fcvt_from_sint_f32_i64_okT hp MR env cp hR hMR
  · exact fcvt_from_sint_f64_i64_okT hp MR env cp hR hMR
  · exact fcvt_to_uint_sat_i64_f32_okT hp MR env cp hR hMR
  · exact fcvt_to_uint_sat_i64_f64_okT hp MR env cp hR hMR
  · exact fcvt_to_sint_sat_i64_f32_okT hp MR env cp hR hMR
  · exact fcvt_to_sint_sat_i64_f64_okT hp MR env cp hR hMR
  · exact fcvt_from_uint_f32_le32_okT hp MR env cp hR hMR
  · exact fcvt_from_uint_f64_le32_okT hp MR env cp hR hMR
  · exact fcvt_from_sint_f32_le32_okT hp MR env cp hR hMR
  · exact fcvt_from_sint_f64_le32_okT hp MR env cp hR hMR
  · exact fcvt_to_uint_sat_i32_f32_okT hp MR env cp hR hMR
  · exact fcvt_to_uint_sat_i32_f64_okT hp MR env cp hR hMR
  · exact fcvt_to_sint_sat_i32_f32_okT hp MR env cp hR hMR
  · exact fcvt_to_sint_sat_i32_f64_okT hp MR env cp hR hMR

end Backend.Proof
