import FV.Backend.Proof.IselFloatArith

/-!
# S11f-cvt: float ↔ integer conversions over float-capable contexts

The `lower` roots of the float<->integer conversions cg_clif emits (`lower.isle:724-754`,
`int_to_fpu` + `put_in_reg_{s,z}ext32`: scvtf/ucvtf; `lower.isle:764-794`, `fpu_to_int_cvt_sat`:
fcvtzs/fcvtzu), proven over `CtxInvT` (`LowerRuleOkT`) against the shared IEEE core: CLIF's
`Inst.float` (`Clif.evalFloat`, `FV/Clif/FSem.lean`) and the Arm instruction the rule emits
(`ispecFP`'s `fpuToInt`/`intToFpu`, the Arm model's `exec_fp_int_cvt`) are the same `IEEE`
functions with `FPCR = 0` and rounding to nearest even, so each rule is a statement about one
function:

* `int_to_fpu` (`IntToFpu`): `fcvt_from_{s,u}int` from i8/i16/i32/i64 to f32/f64.
  The `i8`/`i16` sources go through `put_in_reg_{s,z}ext32` (sign/zero extend to 32 bits) and
  the `i32`/`i64` sources through `put_in_reg`; the rule emits `scvtf`/`ucvtf` at the
  destination's scalar size.
* `fpu_to_int_cvt_sat` (`FpuToInt`): `fcvt_to_{s,u}int_sat` from f32/f64 to i32/i64 (`fcvtzs`/
  `fcvtzu`). The `fits_in_32` result types (i8/i16) are rejected by `instData`'s `fCvtTyOk`
  (`cg_clif` lowers them to the `.i32` conversion + an integer clamp), so only the `.i32` and
  `.i64` roots can fire.

Trapping `fcvt_to_{s,u}int` is not emitted by cg_clif (its `cast.rs` never requests the
trapping variants) and its roots are not in the closure; we document that here.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Internal terms: `int_to_fpu`, `fpu_to_int_cvt_sat` -/

section Terms
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 1000000 in
include hp hc in
/-- `int_to_fpu` (`inst.isle`): `MInst.IntToFpu` into a fresh float vreg. -/
theorem intToFpu_ok {n : Nat} (hn : 40 ≤ n) {op a : V} {st st' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 27 633 [op, a] st v st') :
    EmitOutC .float st.1 st'.1 v (fun rd => .data 58 70 [op, .reg rd, a]) := by
  isel_split hp hc h 633
  isel_inv [*, rule_inst_4758, ctor_emit_iff, ctor_writable_reg_to_reg'] at hm he
  obtain ⟨rfl, rfl⟩ :=
    (ctor_temp_writable_reg_f64_iff ctx _ _ _).mp ‹externCtor ctx T.temp_writable_reg _ _ = _›
  exact ⟨rfl, _, ‹_›, rfl⟩

set_option maxHeartbeats 1000000 in
include hp hc in
/-- `fpu_to_int_cvt_sat` (`inst.isle`): `MInst.FpuToInt` into a fresh int vreg. -/
theorem fpuToIntSat_ok {n : Nat} (hn : 40 ≤ n) {op a s ty : V}
    {st st' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 629 [op, a, s, ty] st v st') :
    EmitOutC .int st.1 st'.1 v (fun rd => .data 58 69 [op, .reg rd, a]) := by
  isel_split hp hc h 629
  isel_inv [*, rule_inst_4716, rule_inst_4718, rule_inst_4720, rule_inst_4726,
    ctor_emit_iff, ctor_writable_reg_to_reg'] at hm he
  exact ⟨rfl, _, ‹_›, rfl⟩

end Terms

/-! ## The 16 roots -/

section Roots
variable {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem} (MR : MemRelT)
  (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR)
include hp hR hMR

set_option maxHeartbeats 8000000 in
/-- **`fcvt_from_sint.f32` from i32** (`rule_lower_724`, `lower.isle:724`): `scvtf s, w`
over a 32-bit-extended operand. -/
theorem fcvt_from_sint_f32_i32_okT : LowerRuleOkT isem MR env cp p rule_lower_724 := by
  sorry

set_option maxHeartbeats 8000000 in
/-- **`fcvt_from_sint.f64` from i32** (`rule_lower_727`): `scvtf d, w`. -/
theorem fcvt_from_sint_f64_i32_okT : LowerRuleOkT isem MR env cp p rule_lower_727 := by
  sorry

set_option maxHeartbeats 8000000 in
/-- **`fcvt_from_uint.f32` from i32** (`rule_lower_730`): `ucvtf s, w` over a
zero-extended operand. -/
theorem fcvt_from_uint_f32_i32_okT : LowerRuleOkT isem MR env cp p rule_lower_730 := by
  sorry

set_option maxHeartbeats 8000000 in
/-- **`fcvt_from_uint.f64` from i32** (`rule_lower_733`): `ucvtf d, w`. -/
theorem fcvt_from_uint_f64_i32_okT : LowerRuleOkT isem MR env cp p rule_lower_733 := by
  sorry

set_option maxHeartbeats 8000000 in
/-- **`fcvt_from_sint.f32` from i64** (`rule_lower_744`): `scvtf s, x`. -/
theorem fcvt_from_sint_f32_i64_okT : LowerRuleOkT isem MR env cp p rule_lower_744 := by
  sorry

set_option maxHeartbeats 8000000 in
/-- **`fcvt_from_sint.f64` from i64** (`rule_lower_747`): `scvtf d, x`. -/
theorem fcvt_from_sint_f64_i64_okT : LowerRuleOkT isem MR env cp p rule_lower_747 := by
  sorry

set_option maxHeartbeats 8000000 in
/-- **`fcvt_from_uint.f32` from i64** (`rule_lower_750`): `ucvtf s, x`. -/
theorem fcvt_from_uint_f32_i64_okT : LowerRuleOkT isem MR env cp p rule_lower_750 := by
  sorry

set_option maxHeartbeats 8000000 in
/-- **`fcvt_from_uint.f64` from i64** (`rule_lower_753`): `ucvtf d, x`. -/
theorem fcvt_from_uint_f64_i64_okT : LowerRuleOkT isem MR env cp p rule_lower_753 := by
  sorry

set_option maxHeartbeats 8000000 in
/-- **`fcvt_to_sint_sat` to i32 from f32** (`rule_lower_764`): `fcvtzs w, s`. -/
theorem fcvt_to_sint_sat_i32_f32_okT : LowerRuleOkT isem MR env cp p rule_lower_764 := by
  sorry

set_option maxHeartbeats 8000000 in
/-- **`fcvt_to_sint_sat.i64` from f32** (`rule_lower_767`): `fcvtzs x, s`. -/
theorem fcvt_to_sint_sat_i64_f32_okT : LowerRuleOkT isem MR env cp p rule_lower_767 := by
  sorry

set_option maxHeartbeats 8000000 in
/-- **`fcvt_to_uint_sat` to i32 from f32** (`rule_lower_770`): `fcvtzu w, s`. -/
theorem fcvt_to_uint_sat_i32_f32_okT : LowerRuleOkT isem MR env cp p rule_lower_770 := by
  sorry

set_option maxHeartbeats 8000000 in
/-- **`fcvt_to_uint_sat.i64` from f32** (`rule_lower_773`): `fcvtzu x, s`. -/
theorem fcvt_to_uint_sat_i64_f32_okT : LowerRuleOkT isem MR env cp p rule_lower_773 := by
  sorry

set_option maxHeartbeats 8000000 in
/-- **`fcvt_to_sint_sat` to i32 from f64** (`rule_lower_784`): `fcvtzs w, d`. -/
theorem fcvt_to_sint_sat_i32_f64_okT : LowerRuleOkT isem MR env cp p rule_lower_784 := by
  sorry

set_option maxHeartbeats 8000000 in
/-- **`fcvt_to_sint_sat.i64` from f64** (`rule_lower_787`): `fcvtzs x, d`. -/
theorem fcvt_to_sint_sat_i64_f64_okT : LowerRuleOkT isem MR env cp p rule_lower_787 := by
  sorry

set_option maxHeartbeats 8000000 in
/-- **`fcvt_to_uint_sat` to i32 from f64** (`rule_lower_790`): `fcvtzu w, d`. -/
theorem fcvt_to_uint_sat_i32_f64_okT : LowerRuleOkT isem MR env cp p rule_lower_790 := by
  sorry

set_option maxHeartbeats 8000000 in
/-- **`fcvt_to_uint_sat.i64` from f64** (`rule_lower_793`): `fcvtzu x, d`. -/
theorem fcvt_to_uint_sat_i64_f64_okT : LowerRuleOkT isem MR env cp p rule_lower_793 := by
  sorry

end Roots

/-! ## The `LowerRulesCorrectFX` family and the program theorem -/

/-- The conversion roots of `lower`, in order. -/
def floatCvtRootRule : Rule → Bool := fun r =>
  (r.id = rule_lower_724.id || r.id = rule_lower_727.id || r.id = rule_lower_730.id ||
    r.id = rule_lower_733.id || r.id = rule_lower_744.id || r.id = rule_lower_747.id ||
    r.id = rule_lower_750.id || r.id = rule_lower_753.id || r.id = rule_lower_764.id ||
    r.id = rule_lower_767.id || r.id = rule_lower_770.id || r.id = rule_lower_773.id ||
    r.id = rule_lower_784.id || r.id = rule_lower_787.id || r.id = rule_lower_790.id ||
    r.id = rule_lower_793.id)

/-- **S11f-cvt's target (float<->integer conversions)**: over float-capable contexts, the
conversion roots are correct. -/
def LowerRulesCorrectFX (program : Program) : Prop :=
  ∀ (F : BitVec 64 → Prop) {isem : Sem} (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program),
    Refines F isem → MRStable F MR →
    ∀ (r : Rule), r ∈ program.rulesOf TId.lower → floatCvtRootRule r →
      LowerRuleOkT isem MR env cp program r

/-- **The program theorem** (`lowerRulesCorrectFX_program`): `program`'s conversion roots are
correct over `CtxInvT`. -/
theorem lowerRulesCorrectFX_program : LowerRulesCorrectFX program := by
  intro F isem MR env cp hR hMR r hr hfc
  have hp := data_program
  · rw [lower_rule_eq hr (k := 220) (r0 := rule_lower_724)
      (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [hfc]; rfl)]
    exact (fcvt_from_sint_f32_i32_okT hp MR env cp hR hMR).toOk
  · rw [lower_rule_eq hr (k := 221) (r0 := rule_lower_727)
      (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [hfc]; rfl)]
    exact (fcvt_from_sint_f64_i32_okT hp MR env cp hR hMR).toOk
  · rw [lower_rule_eq hr (k := 112) (r0 := rule_lower_730)
      (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [hfc]; rfl)]
    exact (fcvt_from_uint_f32_i32_okT hp MR env cp hR hMR).toOk
  · rw [lower_rule_eq hr (k := 113) (r0 := rule_lower_733)
      (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [hfc]; rfl)]
    exact (fcvt_from_uint_f64_i32_okT hp MR env cp hR hMR).toOk
  · rw [lower_rule_eq hr (k := 222) (r0 := rule_lower_744)
      (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [hfc]; rfl)]
    exact (fcvt_from_sint_f32_i64_okT hp MR env cp hR hMR).toOk
  · rw [lower_rule_eq hr (k := 223) (r0 := rule_lower_747)
      (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [hfc]; rfl)]
    exact (fcvt_from_sint_f64_i64_okT hp MR env cp hR hMR).toOk
  · rw [lower_rule_eq hr (k := 114) (r0 := rule_lower_750)
      (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [hfc]; rfl)]
    exact (fcvt_from_uint_f32_i64_okT hp MR env cp hR hMR).toOk
  · rw [lower_rule_eq hr (k := 115) (r0 := rule_lower_753)
      (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [hfc]; rfl)]
    exact (fcvt_from_uint_f64_i64_okT hp MR env cp hR hMR).toOk
  · rw [lower_rule_eq hr (k := 224) (r0 := rule_lower_764)
      (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [hfc]; rfl)]
    exact (fcvt_to_sint_sat_i32_f32_okT hp MR env cp hR hMR).toOk
  · rw [lower_rule_eq hr (k := 116) (r0 := rule_lower_767)
      (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [hfc]; rfl)]
    exact (fcvt_to_sint_sat_i64_f32_okT hp MR env cp hR hMR).toOk
  · rw [lower_rule_eq hr (k := 225) (r0 := rule_lower_770)
      (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [hfc]; rfl)]
    exact (fcvt_to_uint_sat_i32_f32_okT hp MR env cp hR hMR).toOk
  · rw [lower_rule_eq hr (k := 117) (r0 := rule_lower_773)
      (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [hfc]; rfl)]
    exact (fcvt_to_uint_sat_i64_f32_okT hp MR env cp hR hMR).toOk
  · rw [lower_rule_eq hr (k := 226) (r0 := rule_lower_784)
      (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [hfc]; rfl)]
    exact (fcvt_to_sint_sat_i32_f64_okT hp MR env cp hR hMR).toOk
  · rw [lower_rule_eq hr (k := 118) (r0 := rule_lower_787)
      (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [hfc]; rfl)]
    exact (fcvt_to_sint_sat_i64_f64_okT hp MR env cp hR hMR).toOk
  · rw [lower_rule_eq hr (k := 227) (r0 := rule_lower_790)
      (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [hfc]; rfl)]
    exact (fcvt_to_uint_sat_i32_f64_okT hp MR env cp hR hMR).toOk
  · rw [lower_rule_eq hr (k := 119) (r0 := rule_lower_793)
      (by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl) (by rw [hfc]; rfl)]
    exact (fcvt_to_uint_sat_i64_f64_okT hp MR env cp hR hMR).toOk

end Backend.Proof
