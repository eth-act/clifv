import FV.Backend.Proof.IselLowerAll
import FV.Backend.Proof.IselBaseTI
import FV.Backend.Proof.IselAtomicTI
import FV.Backend.Proof.IselCmpDivRemTI
import FV.Backend.Proof.IselCmpDivRootTI
import FV.Backend.Proof.IselCmpDivTI
import FV.Backend.Proof.IselCmpEmitTI
import FV.Backend.Proof.IselCmpMinMaxTI
import FV.Backend.Proof.IselCmpRootTI
import FV.Backend.Proof.IselCmpSdivTI
import FV.Backend.Proof.IselCmpSelectTI
import FV.Backend.Proof.IselCmpVecTI
import FV.Backend.Proof.IselFamALUAExtTI
import FV.Backend.Proof.IselFamALUAExtrTI
import FV.Backend.Proof.IselFamALUALogicNotTI
import FV.Backend.Proof.IselFamALUALogicTI
import FV.Backend.Proof.IselFamALUAMulNTI
import FV.Backend.Proof.IselFamALUAMulTI
import FV.Backend.Proof.IselFamALUARulesTI
import FV.Backend.Proof.IselFamALUATI
import FV.Backend.Proof.IselFamAluBBaseTI
import FV.Backend.Proof.IselFamAluBBfmTI
import FV.Backend.Proof.IselFamAluBBitrevTI
import FV.Backend.Proof.IselFamAluBBswapTI
import FV.Backend.Proof.IselFamAluBClzTI
import FV.Backend.Proof.IselFamAluBExtendTI
import FV.Backend.Proof.IselFamAluBIconstTI
import FV.Backend.Proof.IselFamAluBMiscTI
import FV.Backend.Proof.IselFamAluBNotShiftTI
import FV.Backend.Proof.IselFamAluBPopcntTI
import FV.Backend.Proof.IselFamAluBRotTI
import FV.Backend.Proof.IselFamAluBShiftBaseTI
import FV.Backend.Proof.IselFamAluBShiftTI
import FV.Backend.Proof.IselFamAluBShiftTermsTI
import FV.Backend.Proof.IselFamAluBUnaryTI
import FV.Backend.Proof.IselFamilyALUTI
import FV.Backend.Proof.IselFamilyTI
import FV.Backend.Proof.IselTermsShiftTI

/-!
# `IselLowerAll` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselLowerAll`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 100000
/-- A root proven over every instruction of a float-capable context (`LowerRuleOkT`) is proven
over its subset-E instructions (`LowerRuleOkTX P`). -/
theorem LowerRuleOkT.toTX {P : Clif.Inst → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {p : Program} {r : Rule} (h : LowerRuleOkT isem MR env cp p r) :
    LowerRuleOkTX P isem MR env cp p r :=
  fun f ctx hc ii info inst hi hic _ => h f ctx hc.inv ii info inst hi hic trivial

/-- A rule of `lower` whose root format is `Trap`/`MultiAry` never matches an E instruction. -/
theorem lowerRuleOk_of_fmtTI {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {r : Rule} {fT : Nat} (hq : ruleFmt r = some fT)
    (hf : fT = 2447 + 26 ∨ fT = 2447 + 18) : LowerRuleOkTI isem MR env cp program r := by
  intro f ctx hctxT ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch _
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  exfalso
  obtain ⟨info', fs, hinfo, hdat⟩ :=
    ruleFmt_match (vs := []) data_program fmtKinds_program hq (by omega) (by omega) hmatch
  rw [hi] at hinfo
  cases hinfo
  have hd := hctx.data ii _ inst hi hic
  rw [hdat] at hd
  have := instData_fmt_ne hE hd
  omega

/-- **The integer `lower` roots over typed contexts** (`LowerRulesCorrectTI`): every closure
root of `lower` other than the call, indirect-call, memory, float-movement and float-arithmetic
roots is correct on the subset-E instructions of a float-capable context (`CtxT`). The per-id
dispatch is `lowerRulesCorrect_program`'s with each rule's `…TI` theorem. -/
theorem lowerRulesCorrectTI_program : LowerRulesCorrectTI program := by
  intro F isem MR env cp hR hMR r hr hroot hcall hind hmem hfm hfa
  have hp := data_program
  rw [closureRoot_eq] at hroot
  have hnb := List.all_eq_true.mp lower_ids_not_branch r hr
  simp only [closureRootIds, List.contains_cons, List.contains_nil, Bool.or_false,
    Bool.or_eq_true, beq_iff_eq] at hroot

  rcases hroot with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rw [lower_rule_eq hr (k := 172) (r0 := rule_lower_53) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply iconst_okTI <;> assumption
  · exfalso; simp [floatMoveRootRule, h] at hfm
  · exfalso; simp [floatMoveRootRule, h] at hfm
  · rw [lower_rule_eq hr (k := 177) (r0 := rule_lower_78) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply nop_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 396) (r0 := rule_lower_86) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply iadd_base_case_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 24) (r0 := rule_lower_90) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply iadd_imm12_right_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 15) (r0 := rule_lower_93) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply iadd_imm12_left_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 46) (r0 := rule_lower_98) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply iadd_imm12_neg_right_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 33) (r0 := rule_lower_102) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply iadd_imm12_neg_left_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 178) (r0 := rule_lower_108) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply iadd_extend_right_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 77) (r0 := rule_lower_111) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply iadd_extend_left_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 4) (r0 := rule_lower_116) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply iadd_ishl_right_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 9) (r0 := rule_lower_120) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply iadd_ishl_left_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 5) (r0 := rule_lower_125) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply iadd_imul_right_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 10) (r0 := rule_lower_128) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply iadd_imul_left_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 179) (r0 := rule_lower_132) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply isub_imul_okTI <;> assumption
  · exfalso; simp [floatArithRootRule, h] at hfa
  · exfalso; simp [floatArithRootRule, h] at hfa
  · exfalso; simp [floatArithRootRule, h] at hfa
  · exfalso; simp [floatArithRootRule, h] at hfa
  · exfalso; simp [floatArithRootRule, h] at hfa
  · exfalso; simp [floatArithRootRule, h] at hfa
  · exfalso; simp [floatArithRootRule, h] at hfa
  · exfalso; simp [floatArithRootRule, h] at hfa
  · exfalso; simp [floatArithRootRule, h] at hfa
  · exfalso; simp [floatArithRootRule, h] at hfa
  · exfalso; simp [floatArithRootRule, h] at hfa
  · exfalso; simp [floatArithRootRule, h] at hfa
  · exfalso; simp [floatArithRootRule, h] at hfa
  · exfalso; simp [floatArithRootRule, h] at hfa
  · exfalso; simp [floatArithRootRule, h] at hfa
  · exfalso; simp [floatArithRootRule, h] at hfa
  · exfalso; simp [floatArithRootRule, h] at hfa
  · exfalso; simp [floatArithRootRule, h] at hfa
  · exfalso; simp [floatArithRootRule, h] at hfa
  · rw [lower_rule_eq hr (k := 220) (r0 := rule_lower_724) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    exact (fcvt_from_uint_f32_le32_okT hp MR env cp hR hMR).toTX
  · rw [lower_rule_eq hr (k := 221) (r0 := rule_lower_727) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    exact (fcvt_from_uint_f64_le32_okT hp MR env cp hR hMR).toTX
  · rw [lower_rule_eq hr (k := 112) (r0 := rule_lower_730) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    exact (fcvt_from_uint_f32_i64_okT hp MR env cp hR hMR).toTX
  · rw [lower_rule_eq hr (k := 113) (r0 := rule_lower_733) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    exact (fcvt_from_uint_f64_i64_okT hp MR env cp hR hMR).toTX
  · rw [lower_rule_eq hr (k := 222) (r0 := rule_lower_744) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    exact (fcvt_from_sint_f32_le32_okT hp MR env cp hR hMR).toTX
  · rw [lower_rule_eq hr (k := 223) (r0 := rule_lower_747) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    exact (fcvt_from_sint_f64_le32_okT hp MR env cp hR hMR).toTX
  · rw [lower_rule_eq hr (k := 114) (r0 := rule_lower_750) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    exact (fcvt_from_sint_f32_i64_okT hp MR env cp hR hMR).toTX
  · rw [lower_rule_eq hr (k := 115) (r0 := rule_lower_753) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    exact (fcvt_from_sint_f64_i64_okT hp MR env cp hR hMR).toTX
  · rw [lower_rule_eq hr (k := 224) (r0 := rule_lower_764) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    exact (fcvt_to_uint_sat_i32_f32_okT hp MR env cp hR hMR).toTX
  · rw [lower_rule_eq hr (k := 116) (r0 := rule_lower_767) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    exact (fcvt_to_uint_sat_i64_f32_okT hp MR env cp hR hMR).toTX
  · rw [lower_rule_eq hr (k := 225) (r0 := rule_lower_770) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    exact (fcvt_to_uint_sat_i32_f64_okT hp MR env cp hR hMR).toTX
  · rw [lower_rule_eq hr (k := 117) (r0 := rule_lower_773) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    exact (fcvt_to_uint_sat_i64_f64_okT hp MR env cp hR hMR).toTX
  · rw [lower_rule_eq hr (k := 226) (r0 := rule_lower_784) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    exact (fcvt_to_sint_sat_i32_f32_okT hp MR env cp hR hMR).toTX
  · rw [lower_rule_eq hr (k := 118) (r0 := rule_lower_787) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    exact (fcvt_to_sint_sat_i64_f32_okT hp MR env cp hR hMR).toTX
  · rw [lower_rule_eq hr (k := 227) (r0 := rule_lower_790) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    exact (fcvt_to_sint_sat_i32_f64_okT hp MR env cp hR hMR).toTX
  · rw [lower_rule_eq hr (k := 119) (r0 := rule_lower_793) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    exact (fcvt_to_sint_sat_i64_f64_okT hp MR env cp hR hMR).toTX
  · rw [lower_rule_eq hr (k := 499) (r0 := rule_lower_801) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply isub_base_case_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 228) (r0 := rule_lower_805) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply isub_imm12_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 50) (r0 := rule_lower_810) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply isub_imm12_neg_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 120) (r0 := rule_lower_816) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply isub_extend_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 484) (r0 := rule_lower_821) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply isub_ishl_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 121) (r0 := rule_lower_857) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply ineg_base_case_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 485) (r0 := rule_lower_871) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply imul_base_case_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 122) (r0 := rule_lower_1056) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply smulhi_64_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 248) (r0 := rule_lower_1059) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply smulhi_fits_in_32_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 123) (r0 := rule_lower_1068) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply umulhi_64_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 249) (r0 := rule_lower_1071) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply umulhi_fits_in_32_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 124) (r0 := rule_lower_1116) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply udiv64_ruleOkTI <;> assumption
  · rw [lower_rule_eq hr (k := 250) (r0 := rule_lower_1119) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply udiv32_ruleOkTI <;> assumption
  · rw [lower_rule_eq hr (k := 251) (r0 := rule_lower_1145) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply sdiv64_ruleOkTI <;> assumption
  · rw [lower_rule_eq hr (k := 426) (r0 := rule_lower_1153) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply sdiv32_ruleOkTI <;> assumption
  · rw [lower_rule_eq hr (k := 52) (r0 := rule_lower_1163) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply sdiv_safe64_ruleOkTI <;> assumption
  · rw [lower_rule_eq hr (k := 125) (r0 := rule_lower_1167) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply sdiv_safe32_ruleOkTI <;> assumption
  · rw [lower_rule_eq hr (k := 252) (r0 := rule_lower_1190) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply urem64_ruleOkTI <;> assumption
  · rw [lower_rule_eq hr (k := 427) (r0 := rule_lower_1197) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply urem32_ruleOkTI <;> assumption
  · rw [lower_rule_eq hr (k := 253) (r0 := rule_lower_1204) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply srem64_ruleOkTI <;> assumption
  · rw [lower_rule_eq hr (k := 428) (r0 := rule_lower_1211) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply srem32_ruleOkTI <;> assumption
  · rw [lower_rule_eq hr (k := 53) (r0 := rule_lower_1222) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply umin_ruleOkTI <;> assumption
  · rw [lower_rule_eq hr (k := 54) (r0 := rule_lower_1224) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply smin_ruleOkTI <;> assumption
  · rw [lower_rule_eq hr (k := 55) (r0 := rule_lower_1226) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply umax_ruleOkTI <;> assumption
  · rw [lower_rule_eq hr (k := 56) (r0 := rule_lower_1228) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply smax_ruleOkTI <;> assumption
  · rw [lower_rule_eq hr (k := 254) (r0 := rule_lower_1233) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply vec_smin_ruleOkTI <;> assumption
  · rw [lower_rule_eq hr (k := 255) (r0 := rule_lower_1239) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply vec_umin_ruleOkTI <;> assumption
  · rw [lower_rule_eq hr (k := 256) (r0 := rule_lower_1245) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply vec_smax_ruleOkTI <;> assumption
  · rw [lower_rule_eq hr (k := 257) (r0 := rule_lower_1251) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply vec_umax_ruleOkTI <;> assumption
  · rw [lower_rule_eq hr (k := 459) (r0 := rule_lower_1261) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply uextend_okTI <;> assumption
  · exfalso; simp [memRootRule, h] at hmem
  · rw [lower_rule_eq hr (k := 132) (r0 := rule_lower_1281) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply uextend_icmp_ruleOkTI <;> assumption
  · exfalso; simp [memRootRule, h] at hmem
  · rw [lower_rule_eq hr (k := 500) (r0 := rule_lower_1315) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply sextend_okTI <;> assumption
  · exfalso; simp [memRootRule, h] at hmem
  · rw [lower_rule_eq hr (k := 501) (r0 := rule_lower_1377) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply bnot_base_case_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 134) (r0 := rule_lower_1401) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply bnot_ishl_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 57) (r0 := rule_lower_1406) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply bnot_bxor_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 511) (r0 := rule_lower_1412) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply band_fits_in_64_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 135) (r0 := rule_lower_1429) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply band_not_right_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 58) (r0 := rule_lower_1431) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply band_not_left_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 503) (r0 := rule_lower_1449) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply bor_fits_in_64_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 136) (r0 := rule_lower_1466) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply bor_not_right_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 59) (r0 := rule_lower_1468) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply bor_not_left_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 19) (r0 := rule_lower_1501) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply extr_32_or_64_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 20) (r0 := rule_lower_1507) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply extr_32_or_64_2_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 504) (r0 := rule_lower_1516) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply bxor_fits_in_64_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 137) (r0 := rule_lower_1534) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply bxor_not_right_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 60) (r0 := rule_lower_1536) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply bxor_not_left_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 435) (r0 := rule_lower_1545) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply ishl_fits_in_32_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 266) (r0 := rule_lower_1549) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply ishl_64_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 436) (r0 := rule_lower_1638) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply ushr_fits_in_32_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 268) (r0 := rule_lower_1642) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply ushr_64_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 506) (r0 := rule_lower_1695) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply sshr_fits_in_32_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 270) (r0 := rule_lower_1699) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply sshr_64_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 138) (r0 := rule_lower_1704) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply sbfm_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 139) (r0 := rule_lower_1707) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply ubfm_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 468) (r0 := rule_lower_1772) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply rotl_fits_in_16_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 438) (r0 := rule_lower_1778) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply rotl_fits_in_16_imm_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 272) (r0 := rule_lower_1791) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply rotl_32_base_case_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 273) (r0 := rule_lower_1797) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply rotl_64_base_case_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 140) (r0 := rule_lower_1803) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply rotl_32_imm_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 141) (r0 := rule_lower_1808) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply rotl_64_imm_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 493) (r0 := rule_lower_1840) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply rotr_fits_in_16_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 439) (r0 := rule_lower_1844) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply rotr_32_base_case_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 440) (r0 := rule_lower_1848) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply rotr_64_base_case_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 469) (r0 := rule_lower_1852) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply rotr_fits_in_16_imm_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 275) (r0 := rule_lower_1857) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply rotr_32_imm_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 276) (r0 := rule_lower_1862) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply rotr_64_imm_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 278) (r0 := rule_lower_1931) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply bitrev_i8_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 279) (r0 := rule_lower_1937) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply bitrev_i16_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 441) (r0 := rule_lower_1946) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply bitrev_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 281) (r0 := rule_lower_1951) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply clz_i8_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 282) (r0 := rule_lower_1955) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply clz_i16_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 442) (r0 := rule_lower_1961) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply clz_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 284) (r0 := rule_lower_1982) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply ctz_i8_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 285) (r0 := rule_lower_1986) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply ctz_i16_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 443) (r0 := rule_lower_1995) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply ctz_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 290) (r0 := rule_lower_2035) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply bswap_i16_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 291) (r0 := rule_lower_2038) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply bswap_i32_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 292) (r0 := rule_lower_2041) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply bswap_i64_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 294) (r0 := rule_lower_2052) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply bmask_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 295) (r0 := rule_lower_2074) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply popcnt_8_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 296) (r0 := rule_lower_2080) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply popcnt_16_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 297) (r0 := rule_lower_2086) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply popcnt_32_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 298) (r0 := rule_lower_2092) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply popcnt_64_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 302) (r0 := rule_lower_2146) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply ireduce_okTI <;> assumption
  · rw [lower_rule_eq hr (k := 470) (r0 := rule_lower_2215) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply icmp_ruleOkTI <;> assumption
  · rw [lower_rule_eq hr (k := 305) (r0 := rule_lower_2237) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    exact lowerRuleOk_of_fmtTI rfl (.inl rfl)
  · rw [lower_rule_eq hr (k := 308) (r0 := rule_lower_2267) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply select_ruleOkTI <;> assumption
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · rw [lower_rule_eq hr (k := 337) (r0 := rule_lower_2476) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    apply fence_okTI <;> assumption
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [callRootRule, h] at hcall
  · exfalso; simp [callRootRule, h] at hcall
  · exfalso; simp [indRootRule, h] at hind
  · rw [lower_rule_eq hr (k := 346) (r0 := rule_lower_2574) (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [h]; rfl)]
    exact lowerRuleOk_of_fmtTI rfl (.inr rfl)
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [floatMoveRootRule, h] at hfm
  · exfalso; simp [floatMoveRootRule, h] at hfm
  · exfalso; simp [floatMoveRootRule, h] at hfm
  · exfalso; simp [floatMoveRootRule, h] at hfm
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [memRootRule, h] at hmem
  · exfalso; simp [h] at hnb
  · exfalso; simp [h] at hnb
  · exfalso; simp [h] at hnb
  · exfalso; simp [h] at hnb
  · exfalso; simp [h] at hnb

end Backend.Proof
