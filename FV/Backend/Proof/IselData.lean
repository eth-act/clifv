import FV.Backend
import FV.Backend.Proof.IselAttr

/-!
# ISLE data facts for the isel proofs (generated, do not edit)

Regenerate: `lake env lean --run FVTest/Backend/Proof/Probe/GenData.lean > FV/Backend/Proof/IselData.lean`.

For every term reachable from the root rules [rule_lower_86, rule_lower_90, rule_lower_2215, rule_lower_1638] (patterns, if-lets, right-hand sides,
and the rules of every internal constructor they call, transitively) plus terms [686]:
`program.term? t = some term_t` and, for internal constructors, `program.rulesOf t = [...]`,
each by `native_decide` on one small equality; `term_t.kind` / `term_t.name` by `rfl`.

`Isle.Aarch64.program` is never reduced by the kernel (it is built by `Program.build`, a fold
over all 1165 rules and a sort per term; kernel reduction of it exhausted memory before).
-/

namespace Backend.Proof

open Isle Isle.Aarch64

-- terms: 155, internal-constructor rules: 101

/-- `def_inst` -/
def term_1 : Isle.Term :=
  ⟨1, "def_inst", [18], 15, (.decl ⟨false, false, false, false⟩ none (some (.external "def_inst" false))), ⟨"src/prelude.isle", 29⟩⟩
theorem program_term_1 : program.term? 1 = some term_1 := by native_decide
@[isel_data] theorem term_1_kind : term_1.kind = (.decl ⟨false, false, false, false⟩ none (some (.external "def_inst" false))) := rfl
@[isel_data] theorem term_1_name : term_1.name = "def_inst" := rfl

/-- `value_type` -/
def term_2 : Isle.Term :=
  ⟨2, "value_type", [14], 15, (.decl ⟨false, false, false, false⟩ none (some (.external "value_type" true))), ⟨"src/prelude.isle", 37⟩⟩
theorem program_term_2 : program.term? 2 = some term_2 := by native_decide
@[isel_data] theorem term_2_kind : term_2.kind = (.decl ⟨false, false, false, false⟩ none (some (.external "value_type" true))) := rfl
@[isel_data] theorem term_2_name : term_2.name = "value_type" := rfl

/-- `ty_bits` -/
def term_87 : Isle.Term :=
  ⟨87, "ty_bits", [14], 1, (.decl ⟨true, false, false, false⟩ (some (.external "ty_bits")) none), ⟨"src/prelude.isle", 297⟩⟩
theorem program_term_87 : program.term? 87 = some term_87 := by native_decide
@[isel_data] theorem term_87_kind : term_87.kind = (.decl ⟨true, false, false, false⟩ (some (.external "ty_bits")) none) := rfl
@[isel_data] theorem term_87_name : term_87.name = "ty_bits" := rfl

/-- `fits_in_16` -/
def term_110 : Isle.Term :=
  ⟨110, "fits_in_16", [14], 14, (.decl ⟨false, false, false, false⟩ none (some (.external "fits_in_16" false))), ⟨"src/prelude.isle", 413⟩⟩
theorem program_term_110 : program.term? 110 = some term_110 := by native_decide
@[isel_data] theorem term_110_kind : term_110.kind = (.decl ⟨false, false, false, false⟩ none (some (.external "fits_in_16" false))) := rfl
@[isel_data] theorem term_110_name : term_110.name = "fits_in_16" := rfl

/-- `fits_in_32` -/
def term_111 : Isle.Term :=
  ⟨111, "fits_in_32", [14], 14, (.decl ⟨false, false, false, false⟩ none (some (.external "fits_in_32" false))), ⟨"src/prelude.isle", 420⟩⟩
theorem program_term_111 : program.term? 111 = some term_111 := by native_decide
@[isel_data] theorem term_111_kind : term_111.kind = (.decl ⟨false, false, false, false⟩ none (some (.external "fits_in_32" false))) := rfl
@[isel_data] theorem term_111_name : term_111.name = "fits_in_32" := rfl

/-- `fits_in_64` -/
def term_113 : Isle.Term :=
  ⟨113, "fits_in_64", [14], 14, (.decl ⟨false, false, false, false⟩ none (some (.external "fits_in_64" false))), ⟨"src/prelude.isle", 431⟩⟩
theorem program_term_113 : program.term? 113 = some term_113 := by native_decide
@[isel_data] theorem term_113_kind : term_113.kind = (.decl ⟨false, false, false, false⟩ none (some (.external "fits_in_64" false))) := rfl
@[isel_data] theorem term_113_name : term_113.name = "fits_in_64" := rfl

/-- `ty_int_ref_scalar_64_extract` -/
def term_119 : Isle.Term :=
  ⟨119, "ty_int_ref_scalar_64_extract", [14], 14, (.decl ⟨true, false, true, false⟩ none (some (.external "ty_int_ref_scalar_64_extract" false))), ⟨"src/prelude.isle", 477⟩⟩
theorem program_term_119 : program.term? 119 = some term_119 := by native_decide
@[isel_data] theorem term_119_kind : term_119.kind = (.decl ⟨true, false, true, false⟩ none (some (.external "ty_int_ref_scalar_64_extract" false))) := rfl
@[isel_data] theorem term_119_name : term_119.name = "ty_int_ref_scalar_64_extract" := rfl

/-- `ty_32_or_64` -/
def term_120 : Isle.Term :=
  ⟨120, "ty_32_or_64", [14], 14, (.decl ⟨false, false, false, false⟩ none (some (.external "ty_32_or_64" false))), ⟨"src/prelude.isle", 484⟩⟩
theorem program_term_120 : program.term? 120 = some term_120 := by native_decide
@[isel_data] theorem term_120_kind : term_120.kind = (.decl ⟨false, false, false, false⟩ none (some (.external "ty_32_or_64" false))) := rfl
@[isel_data] theorem term_120_name : term_120.name = "ty_32_or_64" := rfl

/-- `ty_int` -/
def term_126 : Isle.Term :=
  ⟨126, "ty_int", [14], 14, (.decl ⟨false, false, false, false⟩ none (some (.external "ty_int" false))), ⟨"src/prelude.isle", 509⟩⟩
theorem program_term_126 : program.term? 126 = some term_126 := by native_decide
@[isel_data] theorem term_126_kind : term_126.kind = (.decl ⟨false, false, false, false⟩ none (some (.external "ty_int" false))) := rfl
@[isel_data] theorem term_126_name : term_126.name = "ty_int" := rfl

/-- `u64_from_imm64` -/
def term_144 : Isle.Term :=
  ⟨144, "u64_from_imm64", [4], 134, (.decl ⟨false, false, false, false⟩ none (some (.external "u64_from_imm64" true))), ⟨"src/prelude.isle", 597⟩⟩
theorem program_term_144 : program.term? 144 = some term_144 := by native_decide
@[isel_data] theorem term_144_kind : term_144.kind = (.decl ⟨false, false, false, false⟩ none (some (.external "u64_from_imm64" true))) := rfl
@[isel_data] theorem term_144_name : term_144.name = "u64_from_imm64" := rfl

/-- `signed_cond_code` -/
def term_159 : Isle.Term :=
  ⟨159, "signed_cond_code", [145], 145, (.decl ⟨true, false, true, false⟩ (some (.external "signed_cond_code")) none), ⟨"src/prelude.isle", 705⟩⟩
theorem program_term_159 : program.term? 159 = some term_159 := by native_decide
@[isel_data] theorem term_159_kind : term_159.kind = (.decl ⟨true, false, true, false⟩ (some (.external "signed_cond_code")) none) := rfl
@[isel_data] theorem term_159_name : term_159.name = "signed_cond_code" := rfl

/-- `unsigned_cond_code` -/
def term_160 : Isle.Term :=
  ⟨160, "unsigned_cond_code", [145], 145, (.decl ⟨true, false, true, false⟩ (some (.external "unsigned_cond_code")) none), ⟨"src/prelude.isle", 725⟩⟩
theorem program_term_160 : program.term? 160 = some term_160 := by native_decide
@[isel_data] theorem term_160_kind : term_160.kind = (.decl ⟨true, false, true, false⟩ (some (.external "unsigned_cond_code")) none) := rfl
@[isel_data] theorem term_160_name : term_160.name = "unsigned_cond_code" := rfl

/-- `value_reg` -/
def term_164 : Isle.Term :=
  ⟨164, "value_reg", [27], 22, (.decl ⟨false, false, false, false⟩ (some (.external "value_reg")) none), ⟨"src/prelude_lower.isle", 48⟩⟩
theorem program_term_164 : program.term? 164 = some term_164 := by native_decide
@[isel_data] theorem term_164_kind : term_164.kind = (.decl ⟨false, false, false, false⟩ (some (.external "value_reg")) none) := rfl
@[isel_data] theorem term_164_name : term_164.name = "value_reg" := rfl

/-- `value_regs` -/
def term_166 : Isle.Term :=
  ⟨166, "value_regs", [27, 27], 22, (.decl ⟨false, false, false, false⟩ (some (.external "value_regs")) none), ⟨"src/prelude_lower.isle", 59⟩⟩
theorem program_term_166 : program.term? 166 = some term_166 := by native_decide
@[isel_data] theorem term_166_kind : term_166.kind = (.decl ⟨false, false, false, false⟩ (some (.external "value_regs")) none) := rfl
@[isel_data] theorem term_166_name : term_166.name = "value_regs" := rfl

/-- `output` -/
def term_170 : Isle.Term :=
  ⟨170, "output", [22], 25, (.decl ⟨false, false, false, false⟩ (some (.external "output")) none), ⟨"src/prelude_lower.isle", 86⟩⟩
theorem program_term_170 : program.term? 170 = some term_170 := by native_decide
@[isel_data] theorem term_170_kind : term_170.kind = (.decl ⟨false, false, false, false⟩ (some (.external "output")) none) := rfl
@[isel_data] theorem term_170_name : term_170.name = "output" := rfl

/-- `output_reg` -/
def term_172 : Isle.Term :=
  ⟨172, "output_reg", [27], 25, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/prelude_lower.isle", 104⟩⟩
theorem program_term_172 : program.term? 172 = some term_172 := by native_decide
@[isel_data] theorem term_172_kind : term_172.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_172_name : term_172.name = "output_reg" := rfl

theorem program_rulesOf_172 : program.rulesOf 172 =
    [rule_prelude_lower_105] := by
  native_decide

/-- `temp_writable_reg` -/
def term_175 : Isle.Term :=
  ⟨175, "temp_writable_reg", [14], 28, (.decl ⟨false, false, false, false⟩ (some (.external "temp_writable_reg")) none), ⟨"src/prelude_lower.isle", 117⟩⟩
theorem program_term_175 : program.term? 175 = some term_175 := by native_decide
@[isel_data] theorem term_175_kind : term_175.kind = (.decl ⟨false, false, false, false⟩ (some (.external "temp_writable_reg")) none) := rfl
@[isel_data] theorem term_175_name : term_175.name = "temp_writable_reg" := rfl

/-- `opportunistic_def` -/
def term_181 : Isle.Term :=
  ⟨181, "opportunistic_def", [15, 22], 13, (.decl ⟨false, false, false, false⟩ (some (.external "opportunistic_def")) none), ⟨"src/prelude_lower.isle", 147⟩⟩
theorem program_term_181 : program.term? 181 = some term_181 := by native_decide
@[isel_data] theorem term_181_kind : term_181.kind = (.decl ⟨false, false, false, false⟩ (some (.external "opportunistic_def")) none) := rfl
@[isel_data] theorem term_181_name : term_181.name = "opportunistic_def" := rfl

/-- `put_in_reg` -/
def term_182 : Isle.Term :=
  ⟨182, "put_in_reg", [15], 27, (.decl ⟨false, false, false, false⟩ (some (.external "put_in_reg")) none), ⟨"src/prelude_lower.isle", 159⟩⟩
theorem program_term_182 : program.term? 182 = some term_182 := by native_decide
@[isel_data] theorem term_182_kind : term_182.kind = (.decl ⟨false, false, false, false⟩ (some (.external "put_in_reg")) none) := rfl
@[isel_data] theorem term_182_name : term_182.name = "put_in_reg" := rfl

/-- `put_in_regs` -/
def term_183 : Isle.Term :=
  ⟨183, "put_in_regs", [15], 22, (.decl ⟨false, false, false, false⟩ (some (.external "put_in_regs")) none), ⟨"src/prelude_lower.isle", 169⟩⟩
theorem program_term_183 : program.term? 183 = some term_183 := by native_decide
@[isel_data] theorem term_183_kind : term_183.kind = (.decl ⟨false, false, false, false⟩ (some (.external "put_in_regs")) none) := rfl
@[isel_data] theorem term_183_name : term_183.name = "put_in_regs" := rfl

/-- `value_regs_get` -/
def term_185 : Isle.Term :=
  ⟨185, "value_regs_get", [22, 6], 27, (.decl ⟨false, false, false, false⟩ (some (.external "value_regs_get")) none), ⟨"src/prelude_lower.isle", 182⟩⟩
theorem program_term_185 : program.term? 185 = some term_185 := by native_decide
@[isel_data] theorem term_185_kind : term_185.kind = (.decl ⟨false, false, false, false⟩ (some (.external "value_regs_get")) none) := rfl
@[isel_data] theorem term_185_name : term_185.name = "value_regs_get" := rfl

/-- `writable_reg_to_reg` -/
def term_201 : Isle.Term :=
  ⟨201, "writable_reg_to_reg", [28], 27, (.decl ⟨true, false, false, false⟩ (some (.external "writable_reg_to_reg")) none), ⟨"src/prelude_lower.isle", 280⟩⟩
theorem program_term_201 : program.term? 201 = some term_201 := by native_decide
@[isel_data] theorem term_201_kind : term_201.kind = (.decl ⟨true, false, false, false⟩ (some (.external "writable_reg_to_reg")) none) := rfl
@[isel_data] theorem term_201_name : term_201.name = "writable_reg_to_reg" := rfl

/-- `first_result` -/
def term_205 : Isle.Term :=
  ⟨205, "first_result", [15], 18, (.decl ⟨false, false, false, false⟩ none (some (.external "first_result" false))), ⟨"src/prelude_lower.isle", 300⟩⟩
theorem program_term_205 : program.term? 205 = some term_205 := by native_decide
@[isel_data] theorem term_205_kind : term_205.kind = (.decl ⟨false, false, false, false⟩ none (some (.external "first_result" false))) := rfl
@[isel_data] theorem term_205_name : term_205.name = "first_result" := rfl

/-- `is_second_result` -/
def term_207 : Isle.Term :=
  ⟨207, "is_second_result", [15], 15, (.decl ⟨false, false, false, false⟩ none (some (.external "is_second_result" false))), ⟨"src/prelude_lower.isle", 318⟩⟩
theorem program_term_207 : program.term? 207 = some term_207 := by native_decide
@[isel_data] theorem term_207_kind : term_207.kind = (.decl ⟨false, false, false, false⟩ none (some (.external "is_second_result" false))) := rfl
@[isel_data] theorem term_207_name : term_207.name = "is_second_result" := rfl

/-- `inst_data_value` -/
def term_209 : Isle.Term :=
  ⟨209, "inst_data_value", [14, 152], 18, (.decl ⟨false, false, false, false⟩ none (some (.external "inst_data_value" true))), ⟨"src/prelude_lower.isle", 330⟩⟩
theorem program_term_209 : program.term? 209 = some term_209 := by native_decide
@[isel_data] theorem term_209_kind : term_209.kind = (.decl ⟨false, false, false, false⟩ none (some (.external "inst_data_value" true))) := rfl
@[isel_data] theorem term_209_name : term_209.name = "inst_data_value" := rfl

/-- `emit` -/
def term_235 : Isle.Term :=
  ⟨235, "emit", [58], 13, (.decl ⟨false, false, false, false⟩ (some (.external "emit")) none), ⟨"src/prelude_lower.isle", 465⟩⟩
theorem program_term_235 : program.term? 235 = some term_235 := by native_decide
@[isel_data] theorem term_235_kind : term_235.kind = (.decl ⟨false, false, false, false⟩ (some (.external "emit")) none) := rfl
@[isel_data] theorem term_235_name : term_235.name = "emit" := rfl

/-- `produces_flags_concat` -/
def term_246 : Isle.Term :=
  ⟨246, "produces_flags_concat", [47, 47], 47, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/prelude_lower.isle", 643⟩⟩
theorem program_term_246 : program.term? 246 = some term_246 := by native_decide
@[isel_data] theorem term_246_kind : term_246.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_246_name : term_246.name = "produces_flags_concat" := rfl

theorem program_rulesOf_246 : program.rulesOf 246 =
    [rule_prelude_lower_644] := by
  native_decide

/-- `produces_flags_opportunistic_def` -/
def term_249 : Isle.Term :=
  ⟨249, "produces_flags_opportunistic_def", [47, 15], 47, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/prelude_lower.isle", 714⟩⟩
theorem program_term_249 : program.term? 249 = some term_249 := by native_decide
@[isel_data] theorem term_249_kind : term_249.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_249_name : term_249.name = "produces_flags_opportunistic_def" := rfl

theorem program_rulesOf_249 : program.rulesOf 249 =
    [rule_prelude_lower_715] := by
  native_decide

/-- `produces_flags_opportunistic_def2` -/
def term_250 : Isle.Term :=
  ⟨250, "produces_flags_opportunistic_def2", [58, 27, 15, 58], 47, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/prelude_lower.isle", 724⟩⟩
theorem program_term_250 : program.term? 250 = some term_250 := by native_decide
@[isel_data] theorem term_250_kind : term_250.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_250_name : term_250.name = "produces_flags_opportunistic_def2" := rfl

theorem program_rulesOf_250 : program.rulesOf 250 =
    [rule_prelude_lower_725] := by
  native_decide

/-- `consumes_flags_concat` -/
def term_251 : Isle.Term :=
  ⟨251, "consumes_flags_concat", [49, 49], 49, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/prelude_lower.isle", 731⟩⟩
theorem program_term_251 : program.term? 251 = some term_251 := by native_decide
@[isel_data] theorem term_251_kind : term_251.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_251_name : term_251.name = "consumes_flags_concat" := rfl

theorem program_rulesOf_251 : program.rulesOf 251 =
    [rule_prelude_lower_744, rule_prelude_lower_750] := by
  native_decide

/-- `with_flags` -/
def term_254 : Isle.Term :=
  ⟨254, "with_flags", [47, 49], 22, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/prelude_lower.isle", 787⟩⟩
theorem program_term_254 : program.term? 254 = some term_254 := by native_decide
@[isel_data] theorem term_254_kind : term_254.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_254_name : term_254.name = "with_flags" := rfl

theorem program_rulesOf_254 : program.rulesOf 254 =
    [rule_prelude_lower_789, rule_prelude_lower_798, rule_prelude_lower_807, rule_prelude_lower_812, rule_prelude_lower_818, rule_prelude_lower_829, rule_prelude_lower_837, rule_prelude_lower_850, rule_prelude_lower_864, rule_prelude_lower_881, rule_prelude_lower_903, rule_prelude_lower_912, rule_prelude_lower_927, rule_prelude_lower_943, rule_prelude_lower_951, rule_prelude_lower_965] := by
  native_decide

/-- `operand_size` -/
def term_305 : Isle.Term :=
  ⟨305, "operand_size", [14], 93, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 1589⟩⟩
theorem program_term_305 : program.term? 305 = some term_305 := by native_decide
@[isel_data] theorem term_305_kind : term_305.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_305_name : term_305.name = "operand_size" := rfl

theorem program_rulesOf_305 : program.rulesOf 305 =
    [rule_inst_1592, rule_inst_1593] := by
  native_decide

/-- `imm_shift_from_imm64` -/
def term_323 : Isle.Term :=
  ⟨323, "imm_shift_from_imm64", [14, 134], 66, (.decl ⟨true, false, true, false⟩ (some (.external "imm_shift_from_imm64")) none), ⟨"src/isa/aarch64/inst.isle", 2220⟩⟩
theorem program_term_323 : program.term? 323 = some term_323 := by native_decide
@[isel_data] theorem term_323_kind : term_323.kind = (.decl ⟨true, false, true, false⟩ (some (.external "imm_shift_from_imm64")) none) := rfl
@[isel_data] theorem term_323_name : term_323.name = "imm_shift_from_imm64" := rfl

/-- `imm12_from_u64` -/
def term_325 : Isle.Term :=
  ⟨325, "imm12_from_u64", [64], 4, (.decl ⟨false, false, false, false⟩ none (some (.external "imm12_from_u64" false))), ⟨"src/isa/aarch64/inst.isle", 2248⟩⟩
theorem program_term_325 : program.term? 325 = some term_325 := by native_decide
@[isel_data] theorem term_325_kind : term_325.kind = (.decl ⟨false, false, false, false⟩ none (some (.external "imm12_from_u64" false))) := rfl
@[isel_data] theorem term_325_name : term_325.name = "imm12_from_u64" := rfl

/-- `u8_into_imm12` -/
def term_327 : Isle.Term :=
  ⟨327, "u8_into_imm12", [1], 64, (.decl ⟨false, false, false, false⟩ (some (.external "u8_into_imm12")) none), ⟨"src/isa/aarch64/inst.isle", 2264⟩⟩
theorem program_term_327 : program.term? 327 = some term_327 := by native_decide
@[isel_data] theorem term_327_kind : term_327.kind = (.decl ⟨false, false, false, false⟩ (some (.external "u8_into_imm12")) none) := rfl
@[isel_data] theorem term_327_name : term_327.name = "u8_into_imm12" := rfl

/-- `u64_into_imm_logic` -/
def term_328 : Isle.Term :=
  ⟨328, "u64_into_imm_logic", [14, 4], 65, (.decl ⟨false, false, false, false⟩ (some (.external "u64_into_imm_logic")) none), ⟨"src/isa/aarch64/inst.isle", 2270⟩⟩
theorem program_term_328 : program.term? 328 = some term_328 := by native_decide
@[isel_data] theorem term_328_kind : term_328.kind = (.decl ⟨false, false, false, false⟩ (some (.external "u64_into_imm_logic")) none) := rfl
@[isel_data] theorem term_328_name : term_328.name = "u64_into_imm_logic" := rfl

/-- `ashr_from_u64` -/
def term_338 : Isle.Term :=
  ⟨338, "ashr_from_u64", [14, 4], 68, (.decl ⟨true, false, true, false⟩ (some (.external "ashr_from_u64")) none), ⟨"src/isa/aarch64/inst.isle", 2347⟩⟩
theorem program_term_338 : program.term? 338 = some term_338 := by native_decide
@[isel_data] theorem term_338_kind : term_338.kind = (.decl ⟨true, false, true, false⟩ (some (.external "ashr_from_u64")) none) := rfl
@[isel_data] theorem term_338_name : term_338.name = "ashr_from_u64" := rfl

/-- `nzcv` -/
def term_348 : Isle.Term :=
  ⟨348, "nzcv", [0, 0, 0, 0], 70, (.decl ⟨false, false, false, false⟩ (some (.external "nzcv")) none), ⟨"src/isa/aarch64/inst.isle", 2469⟩⟩
theorem program_term_348 : program.term? 348 = some term_348 := by native_decide
@[isel_data] theorem term_348_kind : term_348.kind = (.decl ⟨false, false, false, false⟩ (some (.external "nzcv")) none) := rfl
@[isel_data] theorem term_348_name : term_348.name = "nzcv" := rfl

/-- `zero_reg` -/
def term_352 : Isle.Term :=
  ⟨352, "zero_reg", [], 27, (.decl ⟨false, false, false, false⟩ (some (.external "zero_reg")) none), ⟨"src/isa/aarch64/inst.isle", 2487⟩⟩
theorem program_term_352 : program.term? 352 = some term_352 := by native_decide
@[isel_data] theorem term_352_kind : term_352.kind = (.decl ⟨false, false, false, false⟩ (some (.external "zero_reg")) none) := rfl
@[isel_data] theorem term_352_name : term_352.name = "zero_reg" := rfl

/-- `writable_zero_reg` -/
def term_356 : Isle.Term :=
  ⟨356, "writable_zero_reg", [], 28, (.decl ⟨false, false, false, false⟩ (some (.external "writable_zero_reg")) none), ⟨"src/isa/aarch64/inst.isle", 2500⟩⟩
theorem program_term_356 : program.term? 356 = some term_356 := by native_decide
@[isel_data] theorem term_356_kind : term_356.kind = (.decl ⟨false, false, false, false⟩ (some (.external "writable_zero_reg")) none) := rfl
@[isel_data] theorem term_356_name : term_356.name = "writable_zero_reg" := rfl

/-- `alu_rr_imm_logic` -/
def term_360 : Isle.Term :=
  ⟨360, "alu_rr_imm_logic", [59, 14, 27, 65], 27, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 2528⟩⟩
theorem program_term_360 : program.term? 360 = some term_360 := by native_decide
@[isel_data] theorem term_360_kind : term_360.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_360_name : term_360.name = "alu_rr_imm_logic" := rfl

theorem program_rulesOf_360 : program.rulesOf 360 =
    [rule_inst_2529] := by
  native_decide

/-- `alu_rr_imm_shift` -/
def term_361 : Isle.Term :=
  ⟨361, "alu_rr_imm_shift", [59, 14, 27, 66], 27, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 2536⟩⟩
theorem program_term_361 : program.term? 361 = some term_361 := by native_decide
@[isel_data] theorem term_361_kind : term_361.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_361_name : term_361.name = "alu_rr_imm_shift" := rfl

theorem program_rulesOf_361 : program.rulesOf 361 =
    [rule_inst_2537] := by
  native_decide

/-- `alu_rrr` -/
def term_362 : Isle.Term :=
  ⟨362, "alu_rrr", [59, 14, 27, 27], 27, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 2544⟩⟩
theorem program_term_362 : program.term? 362 = some term_362 := by native_decide
@[isel_data] theorem term_362_kind : term_362.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_362_name : term_362.name = "alu_rrr" := rfl

theorem program_rulesOf_362 : program.rulesOf 362 =
    [rule_inst_2545] := by
  native_decide

/-- `alu_rr_imm12` -/
def term_376 : Isle.Term :=
  ⟨376, "alu_rr_imm12", [59, 14, 27, 64], 27, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 2647⟩⟩
theorem program_term_376 : program.term? 376 = some term_376 := by native_decide
@[isel_data] theorem term_376_kind : term_376.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_376_name : term_376.name = "alu_rr_imm12" := rfl

theorem program_rulesOf_376 : program.rulesOf 376 =
    [rule_inst_2648] := by
  native_decide

/-- `cmp_rr_shift_asr` -/
def term_379 : Isle.Term :=
  ⟨379, "cmp_rr_shift_asr", [93, 27, 27, 4], 47, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 2674⟩⟩
theorem program_term_379 : program.term? 379 = some term_379 := by native_decide
@[isel_data] theorem term_379_kind : term_379.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_379_name : term_379.name = "cmp_rr_shift_asr" := rfl

theorem program_rulesOf_379 : program.rulesOf 379 =
    [rule_inst_2675] := by
  native_decide

/-- `alu_rrr_with_flags_paired` -/
def term_383 : Isle.Term :=
  ⟨383, "alu_rrr_with_flags_paired", [14, 27, 27, 59], 47, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 2708⟩⟩
theorem program_term_383 : program.term? 383 = some term_383 := by native_decide
@[isel_data] theorem term_383_kind : term_383.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_383_name : term_383.name = "alu_rrr_with_flags_paired" := rfl

theorem program_rulesOf_383 : program.rulesOf 383 =
    [rule_inst_2709] := by
  native_decide

/-- `sbcs_side_effect` -/
def term_385 : Isle.Term :=
  ⟨385, "sbcs_side_effect", [14, 27, 27], 47, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 2725⟩⟩
theorem program_term_385 : program.term? 385 = some term_385 := by native_decide
@[isel_data] theorem term_385_kind : term_385.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_385_name : term_385.name = "sbcs_side_effect" := rfl

theorem program_rulesOf_385 : program.rulesOf 385 =
    [rule_inst_2726] := by
  native_decide

/-- `cmp` -/
def term_390 : Isle.Term :=
  ⟨390, "cmp", [93, 27, 27], 47, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 2766⟩⟩
theorem program_term_390 : program.term? 390 = some term_390 := by native_decide
@[isel_data] theorem term_390_kind : term_390.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_390_name : term_390.name = "cmp" := rfl

theorem program_rulesOf_390 : program.rulesOf 390 =
    [rule_inst_2767] := by
  native_decide

/-- `cmp_imm` -/
def term_391 : Isle.Term :=
  ⟨391, "cmp_imm", [93, 27, 64], 47, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 2773⟩⟩
theorem program_term_391 : program.term? 391 = some term_391 := by native_decide
@[isel_data] theorem term_391_kind : term_391.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_391_name : term_391.name = "cmp_imm" := rfl

theorem program_rulesOf_391 : program.rulesOf 391 =
    [rule_inst_2774] := by
  native_decide

/-- `cmp64_imm` -/
def term_392 : Isle.Term :=
  ⟨392, "cmp64_imm", [27, 64], 47, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 2780⟩⟩
theorem program_term_392 : program.term? 392 = some term_392 := by native_decide
@[isel_data] theorem term_392_kind : term_392.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_392_name : term_392.name = "cmp64_imm" := rfl

theorem program_rulesOf_392 : program.rulesOf 392 =
    [rule_inst_2781] := by
  native_decide

/-- `cmp_extend` -/
def term_393 : Isle.Term :=
  ⟨393, "cmp_extend", [93, 27, 27, 84], 47, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 2785⟩⟩
theorem program_term_393 : program.term? 393 = some term_393 := by native_decide
@[isel_data] theorem term_393_kind : term_393.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_393_name : term_393.name = "cmp_extend" := rfl

theorem program_rulesOf_393 : program.rulesOf 393 =
    [rule_inst_2786] := by
  native_decide

/-- `extend` -/
def term_417 : Isle.Term :=
  ⟨417, "extend", [27, 0, 1, 1], 27, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 2990⟩⟩
theorem program_term_417 : program.term? 417 = some term_417 := by native_decide
@[isel_data] theorem term_417_kind : term_417.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_417_name : term_417.name = "extend" := rfl

theorem program_rulesOf_417 : program.rulesOf 417 =
    [rule_inst_2991] := by
  native_decide

/-- `tst_imm` -/
def term_424 : Isle.Term :=
  ⟨424, "tst_imm", [14, 27, 65], 47, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 3043⟩⟩
theorem program_term_424 : program.term? 424 = some term_424 := by native_decide
@[isel_data] theorem term_424_kind : term_424.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_424_name : term_424.name = "tst_imm" := rfl

theorem program_rulesOf_424 : program.rulesOf 424 =
    [rule_inst_3044] := by
  native_decide

/-- `cset` -/
def term_426 : Isle.Term :=
  ⟨426, "cset", [96], 49, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 3067⟩⟩
theorem program_term_426 : program.term? 426 = some term_426 := by native_decide
@[isel_data] theorem term_426_kind : term_426.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_426_name : term_426.name = "cset" := rfl

theorem program_rulesOf_426 : program.rulesOf 426 =
    [rule_inst_3068] := by
  native_decide

/-- `ccmp` -/
def term_430 : Isle.Term :=
  ⟨430, "ccmp", [93, 27, 27, 70, 96, 47], 47, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 3102⟩⟩
theorem program_term_430 : program.term? 430 = some term_430 := by native_decide
@[isel_data] theorem term_430_kind : term_430.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_430_name : term_430.name = "ccmp" := rfl

theorem program_rulesOf_430 : program.rulesOf 430 =
    [rule_inst_3103] := by
  native_decide

/-- `add` -/
def term_432 : Isle.Term :=
  ⟨432, "add", [14, 27, 27], 27, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 3117⟩⟩
theorem program_term_432 : program.term? 432 = some term_432 := by native_decide
@[isel_data] theorem term_432_kind : term_432.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_432_name : term_432.name = "add" := rfl

theorem program_rulesOf_432 : program.rulesOf 432 =
    [rule_inst_3118] := by
  native_decide

/-- `add_imm` -/
def term_433 : Isle.Term :=
  ⟨433, "add_imm", [14, 27, 64], 27, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 3121⟩⟩
theorem program_term_433 : program.term? 433 = some term_433 := by native_decide
@[isel_data] theorem term_433_kind : term_433.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_433_name : term_433.name = "add_imm" := rfl

theorem program_rulesOf_433 : program.rulesOf 433 =
    [rule_inst_3122] := by
  native_decide

/-- `umulh` -/
def term_451 : Isle.Term :=
  ⟨451, "umulh", [14, 27, 27], 27, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 3212⟩⟩
theorem program_term_451 : program.term? 451 = some term_451 := by native_decide
@[isel_data] theorem term_451_kind : term_451.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_451_name : term_451.name = "umulh" := rfl

theorem program_rulesOf_451 : program.rulesOf 451 =
    [rule_inst_3213] := by
  native_decide

/-- `smulh` -/
def term_452 : Isle.Term :=
  ⟨452, "smulh", [14, 27, 27], 27, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 3217⟩⟩
theorem program_term_452 : program.term? 452 = some term_452 := by native_decide
@[isel_data] theorem term_452_kind : term_452.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_452_name : term_452.name = "smulh" := rfl

theorem program_rulesOf_452 : program.rulesOf 452 =
    [rule_inst_3218] := by
  native_decide

/-- `orr` -/
def term_497 : Isle.Term :=
  ⟨497, "orr", [14, 27, 27], 27, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 3411⟩⟩
theorem program_term_497 : program.term? 497 = some term_497 := by native_decide
@[isel_data] theorem term_497_kind : term_497.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_497_name : term_497.name = "orr" := rfl

theorem program_rulesOf_497 : program.rulesOf 497 =
    [rule_inst_3412] := by
  native_decide

/-- `and_reg` -/
def term_501 : Isle.Term :=
  ⟨501, "and_reg", [14, 27, 27], 27, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 3426⟩⟩
theorem program_term_501 : program.term? 501 = some term_501 := by native_decide
@[isel_data] theorem term_501_kind : term_501.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_501_name : term_501.name = "and_reg" := rfl

theorem program_rulesOf_501 : program.rulesOf 501 =
    [rule_inst_3427] := by
  native_decide

/-- `and_imm` -/
def term_502 : Isle.Term :=
  ⟨502, "and_imm", [14, 27, 65], 27, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 3430⟩⟩
theorem program_term_502 : program.term? 502 = some term_502 := by native_decide
@[isel_data] theorem term_502_kind : term_502.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_502_name : term_502.name = "and_imm" := rfl

theorem program_rulesOf_502 : program.rulesOf 502 =
    [rule_inst_3431] := by
  native_decide

/-- `put_in_reg_sext32` -/
def term_555 : Isle.Term :=
  ⟨555, "put_in_reg_sext32", [15], 27, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 3798⟩⟩
theorem program_term_555 : program.term? 555 = some term_555 := by native_decide
@[isel_data] theorem term_555_kind : term_555.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_555_name : term_555.name = "put_in_reg_sext32" := rfl

theorem program_rulesOf_555 : program.rulesOf 555 =
    [rule_inst_3803, rule_inst_3804, rule_inst_3799] := by
  native_decide

/-- `put_in_reg_zext32` -/
def term_556 : Isle.Term :=
  ⟨556, "put_in_reg_zext32", [15], 27, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 3808⟩⟩
theorem program_term_556 : program.term? 556 = some term_556 := by native_decide
@[isel_data] theorem term_556_kind : term_556.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_556_name : term_556.name = "put_in_reg_zext32" := rfl

theorem program_rulesOf_556 : program.rulesOf 556 =
    [rule_inst_3813, rule_inst_3814, rule_inst_3809] := by
  native_decide

/-- `cond_code` -/
def term_592 : Isle.Term :=
  ⟨592, "cond_code", [145], 96, (.decl ⟨false, false, false, false⟩ (some (.external "cond_code")) none), ⟨"src/isa/aarch64/inst.isle", 4379⟩⟩
theorem program_term_592 : program.term? 592 = some term_592 := by native_decide
@[isel_data] theorem term_592_kind : term_592.kind = (.decl ⟨false, false, false, false⟩ (some (.external "cond_code")) none) := rfl
@[isel_data] theorem term_592_name : term_592.name = "cond_code" := rfl

/-- `invert_cond` -/
def term_593 : Isle.Term :=
  ⟨593, "invert_cond", [96], 96, (.decl ⟨false, false, false, false⟩ (some (.external "invert_cond")) none), ⟨"src/isa/aarch64/inst.isle", 4384⟩⟩
theorem program_term_593 : program.term? 593 = some term_593 := by native_decide
@[isel_data] theorem term_593_kind : term_593.kind = (.decl ⟨false, false, false, false⟩ (some (.external "invert_cond")) none) := rfl
@[isel_data] theorem term_593_name : term_593.name = "invert_cond" := rfl

/-- `cond_result_invert` -/
def term_649 : Isle.Term :=
  ⟨649, "cond_result_invert", [123], 123, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 4953⟩⟩
theorem program_term_649 : program.term? 649 = some term_649 := by native_decide
@[isel_data] theorem term_649_kind : term_649.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_649_name : term_649.name = "cond_result_invert" := rfl

theorem program_rulesOf_649 : program.rulesOf 649 =
    [rule_inst_4954, rule_inst_4955, rule_inst_4956, rule_inst_4957, rule_inst_4959] := by
  native_decide

/-- `is_nonzero` -/
def term_651 : Isle.Term :=
  ⟨651, "is_nonzero", [15], 123, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 4976⟩⟩
theorem program_term_651 : program.term? 651 = some term_651 := by native_decide
@[isel_data] theorem term_651_kind : term_651.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_651_name : term_651.name = "is_nonzero" := rfl

theorem program_rulesOf_651 : program.rulesOf 651 =
    [rule_inst_5094, rule_inst_5077, rule_inst_5058, rule_inst_5049, rule_inst_5032, rule_inst_5013, rule_inst_4993, rule_inst_4988, rule_inst_4983, rule_inst_4979, rule_inst_4977] := by
  native_decide

/-- `emit_icmp` -/
def term_652 : Isle.Term :=
  ⟨652, "emit_icmp", [145, 15, 15], 123, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 5105⟩⟩
theorem program_term_652 : program.term? 652 = some term_652 := by native_decide
@[isel_data] theorem term_652_kind : term_652.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_652_name : term_652.name = "emit_icmp" := rfl

theorem program_rulesOf_652 : program.rulesOf 652 =
    [rule_inst_5171, rule_inst_5173, rule_inst_5170, rule_inst_5172, rule_inst_5165, rule_inst_5155, rule_inst_5160, rule_inst_5142, rule_inst_5134, rule_inst_5128, rule_inst_5117, rule_inst_5108] := by
  native_decide

/-- `emit_icmp_i128` -/
def term_653 : Isle.Term :=
  ⟨653, "emit_icmp_i128", [145, 27, 27, 27, 27], 123, (.decl ⟨false, false, false, true⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 5176⟩⟩
theorem program_term_653 : program.term? 653 = some term_653 := by native_decide
@[isel_data] theorem term_653_kind : term_653.kind = (.decl ⟨false, false, false, true⟩ (some .internal) none) := rfl
@[isel_data] theorem term_653_name : term_653.name = "emit_icmp_i128" := rfl

theorem program_rulesOf_653 : program.rulesOf 653 =
    [rule_inst_5179, rule_inst_5181, rule_inst_5183, rule_inst_5185, rule_inst_5189, rule_inst_5191, rule_inst_5201] := by
  native_decide

/-- `emit_icmp_i128_eq_ne` -/
def term_654 : Isle.Term :=
  ⟨654, "emit_icmp_i128_eq_ne", [27, 27, 27, 27], 47, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 5194⟩⟩
theorem program_term_654 : program.term? 654 = some term_654 := by native_decide
@[isel_data] theorem term_654_kind : term_654.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_654_name : term_654.name = "emit_icmp_i128_eq_ne" := rfl

theorem program_rulesOf_654 : program.rulesOf 654 =
    [rule_inst_5195] := by
  native_decide

/-- `lower_extend_op` -/
def term_657 : Isle.Term :=
  ⟨657, "lower_extend_op", [14, 56], 84, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/inst.isle", 5263⟩⟩
theorem program_term_657 : program.term? 657 = some term_657 := by native_decide
@[isel_data] theorem term_657_kind : term_657.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_657_name : term_657.name = "lower_extend_op" := rfl

theorem program_rulesOf_657 : program.rulesOf 657 =
    [rule_inst_5264, rule_inst_5265, rule_inst_5266, rule_inst_5267] := by
  native_decide

/-- `lower` -/
def term_686 : Isle.Term :=
  ⟨686, "lower", [18], 25, (.decl ⟨false, false, true, false⟩ (some .internal) none), ⟨"src/isa/aarch64/lower.isle", 38⟩⟩
theorem program_term_686 : program.term? 686 = some term_686 := by native_decide
@[isel_data] theorem term_686_kind : term_686.kind = (.decl ⟨false, false, true, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_686_name : term_686.name = "lower" := rfl

theorem program_rulesOf_686 : program.rulesOf 686 =
    [rule_lower_419, rule_lower_402, rule_lower_1444, rule_lower_1481, rule_lower_116, rule_lower_125, rule_lower_1442, rule_lower_1479, rule_lower_2779, rule_lower_120, rule_lower_128, rule_lower_165, rule_lower_1439, rule_lower_1476, rule_lower_2784, rule_lower_93, rule_lower_167, rule_lower_1437, rule_lower_1474, rule_lower_1501, rule_lower_1507, rule_lower_2789, rule_lower_3091, rule_lower_3155, rule_lower_90, rule_lower_169, rule_lower_1435, rule_lower_1472, rule_lower_1540, rule_lower_2152, rule_lower_2793, rule_lower_3097, rule_lower_3161, rule_lower_102, rule_lower_171, rule_lower_1408, rule_lower_1434, rule_lower_1471, rule_lower_1539, rule_lower_2158, rule_lower_2185, rule_lower_2798, rule_lower_2828, rule_lower_3008, rule_lower_3101, rule_lower_3165, rule_lower_98, rule_lower_190, rule_lower_437, rule_lower_609, rule_lower_810, rule_lower_861, rule_lower_1163, rule_lower_1222, rule_lower_1224, rule_lower_1226, rule_lower_1228, rule_lower_1406, rule_lower_1431, rule_lower_1468, rule_lower_1536, rule_lower_2120, rule_lower_2164, rule_lower_2191, rule_lower_2386, rule_lower_2404, rule_lower_2419, rule_lower_2435, rule_lower_2815, rule_lower_3018, rule_lower_3036, rule_lower_3056, rule_lower_3076, rule_lower_3126, rule_lower_3140, rule_lower_3190, rule_lower_3204, rule_lower_111, rule_lower_203, rule_lower_205, rule_lower_207, rule_lower_209, rule_lower_211, rule_lower_213, rule_lower_215, rule_lower_217, rule_lower_222, rule_lower_224, rule_lower_226, rule_lower_228, rule_lower_230, rule_lower_232, rule_lower_240, rule_lower_242, rule_lower_244, rule_lower_246, rule_lower_248, rule_lower_250, rule_lower_260, rule_lower_262, rule_lower_264, rule_lower_266, rule_lower_268, rule_lower_270, rule_lower_294, rule_lower_300, rule_lower_440, rule_lower_608, rule_lower_693, rule_lower_699, rule_lower_707, rule_lower_713, rule_lower_730, rule_lower_733, rule_lower_750, rule_lower_753, rule_lower_767, rule_lower_773, rule_lower_787, rule_lower_793, rule_lower_816, rule_lower_857, rule_lower_1056, rule_lower_1068, rule_lower_1116, rule_lower_1167, rule_lower_1236, rule_lower_1242, rule_lower_1248, rule_lower_1254, rule_lower_1266, rule_lower_1272, rule_lower_1281, rule_lower_1283, rule_lower_1401, rule_lower_1429, rule_lower_1466, rule_lower_1534, rule_lower_1704, rule_lower_1707, rule_lower_1803, rule_lower_1808, rule_lower_2138, rule_lower_2170, rule_lower_2197, rule_lower_2288, rule_lower_2328, rule_lower_2331, rule_lower_2334, rule_lower_2337, rule_lower_2340, rule_lower_2343, rule_lower_2346, rule_lower_2349, rule_lower_2352, rule_lower_2381, rule_lower_2400, rule_lower_2415, rule_lower_2431, rule_lower_2451, rule_lower_2466, rule_lower_2508, rule_lower_2580, rule_lower_2803, rule_lower_2822, rule_lower_2837, rule_lower_3014, rule_lower_3031, rule_lower_3051, rule_lower_3071, rule_lower_3110, rule_lower_3174, rule_lower_53, rule_lower_58, rule_lower_63, rule_lower_68, rule_lower_73, rule_lower_78, rule_lower_108, rule_lower_132, rule_lower_273, rule_lower_279, rule_lower_284, rule_lower_308, rule_lower_313, rule_lower_316, rule_lower_336, rule_lower_342, rule_lower_368, rule_lower_375, rule_lower_379, rule_lower_383, rule_lower_387, rule_lower_450, rule_lower_463, rule_lower_477, rule_lower_485, rule_lower_493, rule_lower_501, rule_lower_509, rule_lower_517, rule_lower_525, rule_lower_533, rule_lower_541, rule_lower_549, rule_lower_554, rule_lower_559, rule_lower_567, rule_lower_570, rule_lower_578, rule_lower_581, rule_lower_589, rule_lower_592, rule_lower_600, rule_lower_603, rule_lower_685, rule_lower_690, rule_lower_696, rule_lower_704, rule_lower_710, rule_lower_724, rule_lower_727, rule_lower_744, rule_lower_747, rule_lower_764, rule_lower_770, rule_lower_784, rule_lower_790, rule_lower_805, rule_lower_836, rule_lower_841, rule_lower_846, rule_lower_851, rule_lower_865, rule_lower_906, rule_lower_914, rule_lower_995, rule_lower_1000, rule_lower_1005, rule_lower_1010, rule_lower_1015, rule_lower_1020, rule_lower_1025, rule_lower_1030, rule_lower_1035, rule_lower_1040, rule_lower_1045, rule_lower_1050, rule_lower_1059, rule_lower_1071, rule_lower_1119, rule_lower_1145, rule_lower_1190, rule_lower_1204, rule_lower_1233, rule_lower_1239, rule_lower_1245, rule_lower_1251, rule_lower_1294, rule_lower_1300, rule_lower_1339, rule_lower_1359, rule_lower_1391, rule_lower_1424, rule_lower_1461, rule_lower_1528, rule_lower_1549, rule_lower_1553, rule_lower_1642, rule_lower_1646, rule_lower_1699, rule_lower_1720, rule_lower_1791, rule_lower_1797, rule_lower_1827, rule_lower_1857, rule_lower_1862, rule_lower_1916, rule_lower_1931, rule_lower_1937, rule_lower_1940, rule_lower_1951, rule_lower_1955, rule_lower_1958, rule_lower_1982, rule_lower_1986, rule_lower_1989, rule_lower_2000, rule_lower_2004, rule_lower_2016, rule_lower_2035, rule_lower_2038, rule_lower_2041, rule_lower_2044, rule_lower_2052, rule_lower_2074, rule_lower_2080, rule_lower_2086, rule_lower_2092, rule_lower_2099, rule_lower_2108, rule_lower_2113, rule_lower_2146, rule_lower_2176, rule_lower_2203, rule_lower_2237, rule_lower_2242, rule_lower_2262, rule_lower_2267, rule_lower_2280, rule_lower_2285, rule_lower_2301, rule_lower_2304, rule_lower_2307, rule_lower_2310, rule_lower_2316, rule_lower_2321, rule_lower_2357, rule_lower_2359, rule_lower_2361, rule_lower_2363, rule_lower_2365, rule_lower_2367, rule_lower_2369, rule_lower_2371, rule_lower_2373, rule_lower_2375, rule_lower_2377, rule_lower_2390, rule_lower_2395, rule_lower_2408, rule_lower_2423, rule_lower_2439, rule_lower_2446, rule_lower_2454, rule_lower_2461, rule_lower_2469, rule_lower_2476, rule_lower_2481, rule_lower_2486, rule_lower_2491, rule_lower_2496, rule_lower_2499, rule_lower_2502, rule_lower_2518, rule_lower_2529, rule_lower_2574, rule_lower_2587, rule_lower_2595, rule_lower_2604, rule_lower_2607, rule_lower_2610, rule_lower_2613, rule_lower_2619, rule_lower_2647, rule_lower_2650, rule_lower_2653, rule_lower_2656, rule_lower_2659, rule_lower_2662, rule_lower_2666, rule_lower_2672, rule_lower_2678, rule_lower_2684, rule_lower_2690, rule_lower_2696, rule_lower_2705, rule_lower_2709, rule_lower_2713, rule_lower_2717, rule_lower_2722, rule_lower_2726, rule_lower_2730, rule_lower_2735, rule_lower_2770, rule_lower_2773, rule_lower_2809, rule_lower_2818, rule_lower_2842, rule_lower_2849, rule_lower_2863, rule_lower_2887, rule_lower_2900, rule_lower_2913, rule_lower_2927, rule_lower_3022, rule_lower_3042, rule_lower_3062, rule_lower_3082, rule_lower_3217, rule_lower_3220, rule_lower_3225, rule_lower_3286, rule_lower_3292, rule_lower_dynamic_neon_81, rule_lower_dynamic_neon_87, rule_lower_86, rule_lower_319, rule_lower_359, rule_lower_390, rule_lower_434, rule_lower_472, rule_lower_482, rule_lower_490, rule_lower_498, rule_lower_506, rule_lower_514, rule_lower_522, rule_lower_530, rule_lower_538, rule_lower_546, rule_lower_564, rule_lower_575, rule_lower_586, rule_lower_597, rule_lower_718, rule_lower_721, rule_lower_738, rule_lower_741, rule_lower_758, rule_lower_761, rule_lower_778, rule_lower_781, rule_lower_831, rule_lower_876, rule_lower_956, rule_lower_1153, rule_lower_1197, rule_lower_1211, rule_lower_1289, rule_lower_1349, rule_lower_1387, rule_lower_1421, rule_lower_1458, rule_lower_1525, rule_lower_1545, rule_lower_1638, rule_lower_1736, rule_lower_1778, rule_lower_1844, rule_lower_1848, rule_lower_1946, rule_lower_1961, rule_lower_1995, rule_lower_2030, rule_lower_2179, rule_lower_2209, rule_lower_2294, rule_lower_2622, rule_lower_2742, rule_lower_dynamic_neon_43, rule_lower_dynamic_neon_57, rule_lower_dynamic_neon_71, rule_lower_dynamic_neon_92, rule_lower_dynamic_neon_97, rule_lower_137, rule_lower_322, rule_lower_826, rule_lower_924, rule_lower_1261, rule_lower_1329, rule_lower_1385, rule_lower_1419, rule_lower_1456, rule_lower_1523, rule_lower_1588, rule_lower_1661, rule_lower_1734, rule_lower_1772, rule_lower_1852, rule_lower_2215, rule_lower_2298, rule_lower_2625, rule_lower_2746, rule_lower_dynamic_neon_15, rule_lower_dynamic_neon_19, rule_lower_dynamic_neon_23, rule_lower_dynamic_neon_27, rule_lower_dynamic_neon_31, rule_lower_dynamic_neon_35, rule_lower_dynamic_neon_39, rule_lower_dynamic_neon_53, rule_lower_dynamic_neon_67, rule_lower_142, rule_lower_821, rule_lower_871, rule_lower_1320, rule_lower_1381, rule_lower_1452, rule_lower_1519, rule_lower_1583, rule_lower_1659, rule_lower_1729, rule_lower_1840, rule_lower_2628, rule_lower_2750, rule_lower_dynamic_neon_47, rule_lower_dynamic_neon_61, rule_lower_dynamic_neon_75, rule_lower_801, rule_lower_1315, rule_lower_1377, rule_lower_1415, rule_lower_1449, rule_lower_1516, rule_lower_1654, rule_lower_1695, rule_lower_2633, rule_lower_2754, rule_lower_dynamic_neon_3, rule_lower_dynamic_neon_11, rule_lower_1412, rule_lower_2638, rule_lower_2759, rule_lower_dynamic_neon_7, rule_lower_2643, rule_lower_2763] := by
  native_decide

/-- `do_shift` -/
def term_703 : Isle.Term :=
  ⟨703, "do_shift", [59, 14, 27, 15], 27, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/lower.isle", 1601⟩⟩
theorem program_term_703 : program.term? 703 = some term_703 := by native_decide
@[isel_data] theorem term_703_kind : term_703.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_703_name : term_703.name = "do_shift" := rfl

theorem program_rulesOf_703 : program.rulesOf 703 =
    [rule_lower_1631, rule_lower_1622, rule_lower_1623, rule_lower_1612] := by
  native_decide

/-- `shift_mask` -/
def term_704 : Isle.Term :=
  ⟨704, "shift_mask", [14], 65, (.decl ⟨false, false, false, false⟩ (some (.external "shift_mask")) none), ⟨"src/isa/aarch64/lower.isle", 1618⟩⟩
theorem program_term_704 : program.term? 704 = some term_704 := by native_decide
@[isel_data] theorem term_704_kind : term_704.kind = (.decl ⟨false, false, false, false⟩ (some (.external "shift_mask")) none) := rfl
@[isel_data] theorem term_704_name : term_704.name = "shift_mask" := rfl

/-- `lower_cond_result_bool` -/
def term_715 : Isle.Term :=
  ⟨715, "lower_cond_result_bool", [123], 27, (.decl ⟨false, false, false, false⟩ (some .internal) none), ⟨"src/isa/aarch64/lower.isle", 2221⟩⟩
theorem program_term_715 : program.term? 715 = some term_715 := by native_decide
@[isel_data] theorem term_715_kind : term_715.kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_715_name : term_715.name = "lower_cond_result_bool" := rfl

theorem program_rulesOf_715 : program.rulesOf 715 =
    [rule_lower_2222, rule_lower_2224, rule_lower_2226, rule_lower_2228, rule_lower_2231] := by
  native_decide

/-- `u64_wrapping_sub` -/
def term_1167 : Isle.Term :=
  ⟨1167, "u64_wrapping_sub", [4, 4], 4, (.decl ⟨true, false, false, false⟩ (some (.external "u64_wrapping_sub")) none), ⟨"<OUT_DIR>/numerics.isle", 2071⟩⟩
theorem program_term_1167 : program.term? 1167 = some term_1167 := by native_decide
@[isel_data] theorem term_1167_kind : term_1167.kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_wrapping_sub")) none) := rfl
@[isel_data] theorem term_1167_name : term_1167.name = "u64_wrapping_sub" := rfl

/-- `u64_is_odd` -/
def term_1199 : Isle.Term :=
  ⟨1199, "u64_is_odd", [4], 0, (.decl ⟨true, false, false, false⟩ (some (.external "u64_is_odd")) none), ⟨"<OUT_DIR>/numerics.isle", 2228⟩⟩
theorem program_term_1199 : program.term? 1199 = some term_1199 := by native_decide
@[isel_data] theorem term_1199_kind : term_1199.kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_is_odd")) none) := rfl
@[isel_data] theorem term_1199_name : term_1199.name = "u64_is_odd" := rfl

/-- `value_array_2` -/
def term_1614 : Isle.Term :=
  ⟨1614, "value_array_2", [15, 15], 147, (.decl ⟨false, false, false, false⟩ (some (.external "pack_value_array_2")) (some (.external "unpack_value_array_2" true))), ⟨"<OUT_DIR>/clif_lower.isle", 100⟩⟩
theorem program_term_1614 : program.term? 1614 = some term_1614 := by native_decide
@[isel_data] theorem term_1614_kind : term_1614.kind = (.decl ⟨false, false, false, false⟩ (some (.external "pack_value_array_2")) (some (.external "unpack_value_array_2" true))) := rfl
@[isel_data] theorem term_1614_name : term_1614.name = "value_array_2" := rfl

/-- `ProducesFlags.ProducesFlagsSideEffect` -/
def term_1791 : Isle.Term :=
  ⟨1791, "ProducesFlags.ProducesFlagsSideEffect", [58], 47, (.enumVariant 1), ⟨"src/prelude_lower.isle", 574⟩⟩
theorem program_term_1791 : program.term? 1791 = some term_1791 := by native_decide
@[isel_data] theorem term_1791_kind : term_1791.kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_1791_name : term_1791.name = "ProducesFlags.ProducesFlagsSideEffect" := rfl

/-- `ProducesFlags.ProducesFlagsTwiceSideEffect` -/
def term_1792 : Isle.Term :=
  ⟨1792, "ProducesFlags.ProducesFlagsTwiceSideEffect", [58, 58], 47, (.enumVariant 2), ⟨"src/prelude_lower.isle", 575⟩⟩
theorem program_term_1792 : program.term? 1792 = some term_1792 := by native_decide
@[isel_data] theorem term_1792_kind : term_1792.kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_1792_name : term_1792.name = "ProducesFlags.ProducesFlagsTwiceSideEffect" := rfl

/-- `ProducesFlags.ProducesFlagsReturnsReg` -/
def term_1793 : Isle.Term :=
  ⟨1793, "ProducesFlags.ProducesFlagsReturnsReg", [58, 27], 47, (.enumVariant 3), ⟨"src/prelude_lower.isle", 578⟩⟩
theorem program_term_1793 : program.term? 1793 = some term_1793 := by native_decide
@[isel_data] theorem term_1793_kind : term_1793.kind = (.enumVariant 3) := rfl
@[isel_data] theorem term_1793_name : term_1793.name = "ProducesFlags.ProducesFlagsReturnsReg" := rfl

/-- `ProducesFlags.ProducesFlagsReturnsResultWithConsumer` -/
def term_1794 : Isle.Term :=
  ⟨1794, "ProducesFlags.ProducesFlagsReturnsResultWithConsumer", [58, 27], 47, (.enumVariant 4), ⟨"src/prelude_lower.isle", 579⟩⟩
theorem program_term_1794 : program.term? 1794 = some term_1794 := by native_decide
@[isel_data] theorem term_1794_kind : term_1794.kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_1794_name : term_1794.name = "ProducesFlags.ProducesFlagsReturnsResultWithConsumer" := rfl

/-- `ProducesFlags.ProducesFlagsOpportunisticDef` -/
def term_1795 : Isle.Term :=
  ⟨1795, "ProducesFlags.ProducesFlagsOpportunisticDef", [58, 27, 15], 47, (.enumVariant 5), ⟨"src/prelude_lower.isle", 596⟩⟩
theorem program_term_1795 : program.term? 1795 = some term_1795 := by native_decide
@[isel_data] theorem term_1795_kind : term_1795.kind = (.enumVariant 5) := rfl
@[isel_data] theorem term_1795_name : term_1795.name = "ProducesFlags.ProducesFlagsOpportunisticDef" := rfl

/-- `ProducesFlags.ProducesFlagsOpportunisticDef2` -/
def term_1796 : Isle.Term :=
  ⟨1796, "ProducesFlags.ProducesFlagsOpportunisticDef2", [58, 27, 15, 58], 47, (.enumVariant 6), ⟨"src/prelude_lower.isle", 599⟩⟩
theorem program_term_1796 : program.term? 1796 = some term_1796 := by native_decide
@[isel_data] theorem term_1796_kind : term_1796.kind = (.enumVariant 6) := rfl
@[isel_data] theorem term_1796_name : term_1796.name = "ProducesFlags.ProducesFlagsOpportunisticDef2" := rfl

/-- `ConsumesFlags.ConsumesFlagsSideEffect` -/
def term_1799 : Isle.Term :=
  ⟨1799, "ConsumesFlags.ConsumesFlagsSideEffect", [58], 49, (.enumVariant 0), ⟨"src/prelude_lower.isle", 663⟩⟩
theorem program_term_1799 : program.term? 1799 = some term_1799 := by native_decide
@[isel_data] theorem term_1799_kind : term_1799.kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_1799_name : term_1799.name = "ConsumesFlags.ConsumesFlagsSideEffect" := rfl

/-- `ConsumesFlags.ConsumesFlagsSideEffect2` -/
def term_1800 : Isle.Term :=
  ⟨1800, "ConsumesFlags.ConsumesFlagsSideEffect2", [58, 58], 49, (.enumVariant 1), ⟨"src/prelude_lower.isle", 664⟩⟩
theorem program_term_1800 : program.term? 1800 = some term_1800 := by native_decide
@[isel_data] theorem term_1800_kind : term_1800.kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_1800_name : term_1800.name = "ConsumesFlags.ConsumesFlagsSideEffect2" := rfl

/-- `ConsumesFlags.ConsumesFlagsReturnsResultWithProducer` -/
def term_1801 : Isle.Term :=
  ⟨1801, "ConsumesFlags.ConsumesFlagsReturnsResultWithProducer", [58, 27], 49, (.enumVariant 2), ⟨"src/prelude_lower.isle", 665⟩⟩
theorem program_term_1801 : program.term? 1801 = some term_1801 := by native_decide
@[isel_data] theorem term_1801_kind : term_1801.kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_1801_name : term_1801.name = "ConsumesFlags.ConsumesFlagsReturnsResultWithProducer" := rfl

/-- `ConsumesFlags.ConsumesFlagsReturnsReg` -/
def term_1802 : Isle.Term :=
  ⟨1802, "ConsumesFlags.ConsumesFlagsReturnsReg", [58, 27], 49, (.enumVariant 3), ⟨"src/prelude_lower.isle", 666⟩⟩
theorem program_term_1802 : program.term? 1802 = some term_1802 := by native_decide
@[isel_data] theorem term_1802_kind : term_1802.kind = (.enumVariant 3) := rfl
@[isel_data] theorem term_1802_name : term_1802.name = "ConsumesFlags.ConsumesFlagsReturnsReg" := rfl

/-- `ConsumesFlags.ConsumesFlagsTwiceReturnsValueRegs` -/
def term_1803 : Isle.Term :=
  ⟨1803, "ConsumesFlags.ConsumesFlagsTwiceReturnsValueRegs", [58, 58, 22], 49, (.enumVariant 4), ⟨"src/prelude_lower.isle", 667⟩⟩
theorem program_term_1803 : program.term? 1803 = some term_1803 := by native_decide
@[isel_data] theorem term_1803_kind : term_1803.kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_1803_name : term_1803.name = "ConsumesFlags.ConsumesFlagsTwiceReturnsValueRegs" := rfl

/-- `ConsumesFlags.ConsumesFlagsFourTimesReturnsValueRegs` -/
def term_1804 : Isle.Term :=
  ⟨1804, "ConsumesFlags.ConsumesFlagsFourTimesReturnsValueRegs", [58, 58, 58, 58, 22], 49, (.enumVariant 5), ⟨"src/prelude_lower.isle", 670⟩⟩
theorem program_term_1804 : program.term? 1804 = some term_1804 := by native_decide
@[isel_data] theorem term_1804_kind : term_1804.kind = (.enumVariant 5) := rfl
@[isel_data] theorem term_1804_name : term_1804.name = "ConsumesFlags.ConsumesFlagsFourTimesReturnsValueRegs" := rfl

/-- `ConsumesFlags.ConsumesFlagsNop` -/
def term_1805 : Isle.Term :=
  ⟨1805, "ConsumesFlags.ConsumesFlagsNop", [], 49, (.enumVariant 6), ⟨"src/prelude_lower.isle", 675⟩⟩
theorem program_term_1805 : program.term? 1805 = some term_1805 := by native_decide
@[isel_data] theorem term_1805_kind : term_1805.kind = (.enumVariant 6) := rfl
@[isel_data] theorem term_1805_name : term_1805.name = "ConsumesFlags.ConsumesFlagsNop" := rfl

/-- `ArgumentExtension.Uext` -/
def term_1816 : Isle.Term :=
  ⟨1816, "ArgumentExtension.Uext", [], 56, (.enumVariant 1), ⟨"src/prelude_lower.isle", 1421⟩⟩
theorem program_term_1816 : program.term? 1816 = some term_1816 := by native_decide
@[isel_data] theorem term_1816_kind : term_1816.kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_1816_name : term_1816.name = "ArgumentExtension.Uext" := rfl

/-- `ArgumentExtension.Sext` -/
def term_1817 : Isle.Term :=
  ⟨1817, "ArgumentExtension.Sext", [], 56, (.enumVariant 2), ⟨"src/prelude_lower.isle", 1422⟩⟩
theorem program_term_1817 : program.term? 1817 = some term_1817 := by native_decide
@[isel_data] theorem term_1817_kind : term_1817.kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_1817_name : term_1817.name = "ArgumentExtension.Sext" := rfl

/-- `MInst.AluRRR` -/
def term_1820 : Isle.Term :=
  ⟨1820, "MInst.AluRRR", [59, 93, 28, 27, 27], 58, (.enumVariant 2), ⟨"src/isa/aarch64/inst.isle", 19⟩⟩
theorem program_term_1820 : program.term? 1820 = some term_1820 := by native_decide
@[isel_data] theorem term_1820_kind : term_1820.kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_1820_name : term_1820.name = "MInst.AluRRR" := rfl

/-- `MInst.AluRRRR` -/
def term_1821 : Isle.Term :=
  ⟨1821, "MInst.AluRRRR", [60, 93, 28, 27, 27, 27], 58, (.enumVariant 3), ⟨"src/isa/aarch64/inst.isle", 27⟩⟩
theorem program_term_1821 : program.term? 1821 = some term_1821 := by native_decide
@[isel_data] theorem term_1821_kind : term_1821.kind = (.enumVariant 3) := rfl
@[isel_data] theorem term_1821_name : term_1821.name = "MInst.AluRRRR" := rfl

/-- `MInst.AluRRImm12` -/
def term_1822 : Isle.Term :=
  ⟨1822, "MInst.AluRRImm12", [59, 93, 28, 27, 64], 58, (.enumVariant 4), ⟨"src/isa/aarch64/inst.isle", 37⟩⟩
theorem program_term_1822 : program.term? 1822 = some term_1822 := by native_decide
@[isel_data] theorem term_1822_kind : term_1822.kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_1822_name : term_1822.name = "MInst.AluRRImm12" := rfl

/-- `MInst.AluRRImmLogic` -/
def term_1823 : Isle.Term :=
  ⟨1823, "MInst.AluRRImmLogic", [59, 93, 28, 27, 65], 58, (.enumVariant 5), ⟨"src/isa/aarch64/inst.isle", 45⟩⟩
theorem program_term_1823 : program.term? 1823 = some term_1823 := by native_decide
@[isel_data] theorem term_1823_kind : term_1823.kind = (.enumVariant 5) := rfl
@[isel_data] theorem term_1823_name : term_1823.name = "MInst.AluRRImmLogic" := rfl

/-- `MInst.AluRRImmShift` -/
def term_1824 : Isle.Term :=
  ⟨1824, "MInst.AluRRImmShift", [59, 93, 28, 27, 66], 58, (.enumVariant 6), ⟨"src/isa/aarch64/inst.isle", 53⟩⟩
theorem program_term_1824 : program.term? 1824 = some term_1824 := by native_decide
@[isel_data] theorem term_1824_kind : term_1824.kind = (.enumVariant 6) := rfl
@[isel_data] theorem term_1824_name : term_1824.name = "MInst.AluRRImmShift" := rfl

/-- `MInst.AluRRRShift` -/
def term_1825 : Isle.Term :=
  ⟨1825, "MInst.AluRRRShift", [59, 93, 28, 27, 27, 68], 58, (.enumVariant 7), ⟨"src/isa/aarch64/inst.isle", 62⟩⟩
theorem program_term_1825 : program.term? 1825 = some term_1825 := by native_decide
@[isel_data] theorem term_1825_kind : term_1825.kind = (.enumVariant 7) := rfl
@[isel_data] theorem term_1825_name : term_1825.name = "MInst.AluRRRShift" := rfl

/-- `MInst.AluRRRExtend` -/
def term_1826 : Isle.Term :=
  ⟨1826, "MInst.AluRRRExtend", [59, 93, 28, 27, 27, 84], 58, (.enumVariant 8), ⟨"src/isa/aarch64/inst.isle", 72⟩⟩
theorem program_term_1826 : program.term? 1826 = some term_1826 := by native_decide
@[isel_data] theorem term_1826_kind : term_1826.kind = (.enumVariant 8) := rfl
@[isel_data] theorem term_1826_name : term_1826.name = "MInst.AluRRRExtend" := rfl

/-- `MInst.Extend` -/
def term_1846 : Isle.Term :=
  ⟨1846, "MInst.Extend", [28, 27, 0, 1, 1], 58, (.enumVariant 28), ⟨"src/isa/aarch64/inst.isle", 205⟩⟩
theorem program_term_1846 : program.term? 1846 = some term_1846 := by native_decide
@[isel_data] theorem term_1846_kind : term_1846.kind = (.enumVariant 28) := rfl
@[isel_data] theorem term_1846_name : term_1846.name = "MInst.Extend" := rfl

/-- `MInst.CSet` -/
def term_1851 : Isle.Term :=
  ⟨1851, "MInst.CSet", [28, 96], 58, (.enumVariant 33), ⟨"src/isa/aarch64/inst.isle", 248⟩⟩
theorem program_term_1851 : program.term? 1851 = some term_1851 := by native_decide
@[isel_data] theorem term_1851_kind : term_1851.kind = (.enumVariant 33) := rfl
@[isel_data] theorem term_1851_name : term_1851.name = "MInst.CSet" := rfl

/-- `MInst.CCmp` -/
def term_1853 : Isle.Term :=
  ⟨1853, "MInst.CCmp", [93, 27, 27, 70, 96], 58, (.enumVariant 35), ⟨"src/isa/aarch64/inst.isle", 258⟩⟩
theorem program_term_1853 : program.term? 1853 = some term_1853 := by native_decide
@[isel_data] theorem term_1853_kind : term_1853.kind = (.enumVariant 35) := rfl
@[isel_data] theorem term_1853_name : term_1853.name = "MInst.CCmp" := rfl

/-- `ALUOp.Add` -/
def term_1962 : Isle.Term :=
  ⟨1962, "ALUOp.Add", [], 59, (.enumVariant 0), ⟨"src/isa/aarch64/inst.isle", 1238⟩⟩
theorem program_term_1962 : program.term? 1962 = some term_1962 := by native_decide
@[isel_data] theorem term_1962_kind : term_1962.kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_1962_name : term_1962.name = "ALUOp.Add" := rfl

/-- `ALUOp.Orr` -/
def term_1964 : Isle.Term :=
  ⟨1964, "ALUOp.Orr", [], 59, (.enumVariant 2), ⟨"src/isa/aarch64/inst.isle", 1240⟩⟩
theorem program_term_1964 : program.term? 1964 = some term_1964 := by native_decide
@[isel_data] theorem term_1964_kind : term_1964.kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_1964_name : term_1964.name = "ALUOp.Orr" := rfl

/-- `ALUOp.And` -/
def term_1966 : Isle.Term :=
  ⟨1966, "ALUOp.And", [], 59, (.enumVariant 4), ⟨"src/isa/aarch64/inst.isle", 1242⟩⟩
theorem program_term_1966 : program.term? 1966 = some term_1966 := by native_decide
@[isel_data] theorem term_1966_kind : term_1966.kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_1966_name : term_1966.name = "ALUOp.And" := rfl

/-- `ALUOp.AndS` -/
def term_1967 : Isle.Term :=
  ⟨1967, "ALUOp.AndS", [], 59, (.enumVariant 5), ⟨"src/isa/aarch64/inst.isle", 1243⟩⟩
theorem program_term_1967 : program.term? 1967 = some term_1967 := by native_decide
@[isel_data] theorem term_1967_kind : term_1967.kind = (.enumVariant 5) := rfl
@[isel_data] theorem term_1967_name : term_1967.name = "ALUOp.AndS" := rfl

/-- `ALUOp.AddS` -/
def term_1971 : Isle.Term :=
  ⟨1971, "ALUOp.AddS", [], 59, (.enumVariant 9), ⟨"src/isa/aarch64/inst.isle", 1250⟩⟩
theorem program_term_1971 : program.term? 1971 = some term_1971 := by native_decide
@[isel_data] theorem term_1971_kind : term_1971.kind = (.enumVariant 9) := rfl
@[isel_data] theorem term_1971_name : term_1971.name = "ALUOp.AddS" := rfl

/-- `ALUOp.SubS` -/
def term_1972 : Isle.Term :=
  ⟨1972, "ALUOp.SubS", [], 59, (.enumVariant 10), ⟨"src/isa/aarch64/inst.isle", 1252⟩⟩
theorem program_term_1972 : program.term? 1972 = some term_1972 := by native_decide
@[isel_data] theorem term_1972_kind : term_1972.kind = (.enumVariant 10) := rfl
@[isel_data] theorem term_1972_name : term_1972.name = "ALUOp.SubS" := rfl

/-- `ALUOp.SMulH` -/
def term_1973 : Isle.Term :=
  ⟨1973, "ALUOp.SMulH", [], 59, (.enumVariant 11), ⟨"src/isa/aarch64/inst.isle", 1254⟩⟩
theorem program_term_1973 : program.term? 1973 = some term_1973 := by native_decide
@[isel_data] theorem term_1973_kind : term_1973.kind = (.enumVariant 11) := rfl
@[isel_data] theorem term_1973_name : term_1973.name = "ALUOp.SMulH" := rfl

/-- `ALUOp.UMulH` -/
def term_1974 : Isle.Term :=
  ⟨1974, "ALUOp.UMulH", [], 59, (.enumVariant 12), ⟨"src/isa/aarch64/inst.isle", 1256⟩⟩
theorem program_term_1974 : program.term? 1974 = some term_1974 := by native_decide
@[isel_data] theorem term_1974_kind : term_1974.kind = (.enumVariant 12) := rfl
@[isel_data] theorem term_1974_name : term_1974.name = "ALUOp.UMulH" := rfl

/-- `ALUOp.Lsr` -/
def term_1978 : Isle.Term :=
  ⟨1978, "ALUOp.Lsr", [], 59, (.enumVariant 16), ⟨"src/isa/aarch64/inst.isle", 1260⟩⟩
theorem program_term_1978 : program.term? 1978 = some term_1978 := by native_decide
@[isel_data] theorem term_1978_kind : term_1978.kind = (.enumVariant 16) := rfl
@[isel_data] theorem term_1978_name : term_1978.name = "ALUOp.Lsr" := rfl

/-- `ALUOp.SbcS` -/
def term_1984 : Isle.Term :=
  ⟨1984, "ALUOp.SbcS", [], 59, (.enumVariant 22), ⟨"src/isa/aarch64/inst.isle", 1270⟩⟩
theorem program_term_1984 : program.term? 1984 = some term_1984 := by native_decide
@[isel_data] theorem term_1984_kind : term_1984.kind = (.enumVariant 22) := rfl
@[isel_data] theorem term_1984_name : term_1984.name = "ALUOp.SbcS" := rfl

/-- `ALUOp3.MAdd` -/
def term_1985 : Isle.Term :=
  ⟨1985, "ALUOp3.MAdd", [], 60, (.enumVariant 0), ⟨"src/isa/aarch64/inst.isle", 1277⟩⟩
theorem program_term_1985 : program.term? 1985 = some term_1985 := by native_decide
@[isel_data] theorem term_1985_kind : term_1985.kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_1985_name : term_1985.name = "ALUOp3.MAdd" := rfl

/-- `ALUOp3.UMAddL` -/
def term_1987 : Isle.Term :=
  ⟨1987, "ALUOp3.UMAddL", [], 60, (.enumVariant 2), ⟨"src/isa/aarch64/inst.isle", 1281⟩⟩
theorem program_term_1987 : program.term? 1987 = some term_1987 := by native_decide
@[isel_data] theorem term_1987_kind : term_1987.kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_1987_name : term_1987.name = "ALUOp3.UMAddL" := rfl

/-- `ALUOp3.SMAddL` -/
def term_1988 : Isle.Term :=
  ⟨1988, "ALUOp3.SMAddL", [], 60, (.enumVariant 3), ⟨"src/isa/aarch64/inst.isle", 1283⟩⟩
theorem program_term_1988 : program.term? 1988 = some term_1988 := by native_decide
@[isel_data] theorem term_1988_kind : term_1988.kind = (.enumVariant 3) := rfl
@[isel_data] theorem term_1988_name : term_1988.name = "ALUOp3.SMAddL" := rfl

/-- `ExtendOp.UXTB` -/
def term_1996 : Isle.Term :=
  ⟨1996, "ExtendOp.UXTB", [], 84, (.enumVariant 0), ⟨"src/isa/aarch64/inst.isle", 1398⟩⟩
theorem program_term_1996 : program.term? 1996 = some term_1996 := by native_decide
@[isel_data] theorem term_1996_kind : term_1996.kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_1996_name : term_1996.name = "ExtendOp.UXTB" := rfl

/-- `ExtendOp.UXTH` -/
def term_1997 : Isle.Term :=
  ⟨1997, "ExtendOp.UXTH", [], 84, (.enumVariant 1), ⟨"src/isa/aarch64/inst.isle", 1399⟩⟩
theorem program_term_1997 : program.term? 1997 = some term_1997 := by native_decide
@[isel_data] theorem term_1997_kind : term_1997.kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_1997_name : term_1997.name = "ExtendOp.UXTH" := rfl

/-- `ExtendOp.UXTW` -/
def term_1998 : Isle.Term :=
  ⟨1998, "ExtendOp.UXTW", [], 84, (.enumVariant 2), ⟨"src/isa/aarch64/inst.isle", 1400⟩⟩
theorem program_term_1998 : program.term? 1998 = some term_1998 := by native_decide
@[isel_data] theorem term_1998_kind : term_1998.kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_1998_name : term_1998.name = "ExtendOp.UXTW" := rfl

/-- `ExtendOp.SXTB` -/
def term_2000 : Isle.Term :=
  ⟨2000, "ExtendOp.SXTB", [], 84, (.enumVariant 4), ⟨"src/isa/aarch64/inst.isle", 1402⟩⟩
theorem program_term_2000 : program.term? 2000 = some term_2000 := by native_decide
@[isel_data] theorem term_2000_kind : term_2000.kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_2000_name : term_2000.name = "ExtendOp.SXTB" := rfl

/-- `ExtendOp.SXTH` -/
def term_2001 : Isle.Term :=
  ⟨2001, "ExtendOp.SXTH", [], 84, (.enumVariant 5), ⟨"src/isa/aarch64/inst.isle", 1403⟩⟩
theorem program_term_2001 : program.term? 2001 = some term_2001 := by native_decide
@[isel_data] theorem term_2001_kind : term_2001.kind = (.enumVariant 5) := rfl
@[isel_data] theorem term_2001_name : term_2001.name = "ExtendOp.SXTH" := rfl

/-- `ExtendOp.SXTW` -/
def term_2002 : Isle.Term :=
  ⟨2002, "ExtendOp.SXTW", [], 84, (.enumVariant 6), ⟨"src/isa/aarch64/inst.isle", 1404⟩⟩
theorem program_term_2002 : program.term? 2002 = some term_2002 := by native_decide
@[isel_data] theorem term_2002_kind : term_2002.kind = (.enumVariant 6) := rfl
@[isel_data] theorem term_2002_name : term_2002.name = "ExtendOp.SXTW" := rfl

/-- `OperandSize.Size32` -/
def term_2028 : Isle.Term :=
  ⟨2028, "OperandSize.Size32", [], 93, (.enumVariant 0), ⟨"src/isa/aarch64/inst.isle", 1578⟩⟩
theorem program_term_2028 : program.term? 2028 = some term_2028 := by native_decide
@[isel_data] theorem term_2028_kind : term_2028.kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_2028_name : term_2028.name = "OperandSize.Size32" := rfl

/-- `OperandSize.Size64` -/
def term_2029 : Isle.Term :=
  ⟨2029, "OperandSize.Size64", [], 93, (.enumVariant 1), ⟨"src/isa/aarch64/inst.isle", 1579⟩⟩
theorem program_term_2029 : program.term? 2029 = some term_2029 := by native_decide
@[isel_data] theorem term_2029_kind : term_2029.kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_2029_name : term_2029.name = "OperandSize.Size64" := rfl

/-- `Cond.Eq` -/
def term_2037 : Isle.Term :=
  ⟨2037, "Cond.Eq", [], 96, (.enumVariant 0), ⟨"src/isa/aarch64/inst.isle", 1658⟩⟩
theorem program_term_2037 : program.term? 2037 = some term_2037 := by native_decide
@[isel_data] theorem term_2037_kind : term_2037.kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_2037_name : term_2037.name = "Cond.Eq" := rfl

/-- `Cond.Ne` -/
def term_2038 : Isle.Term :=
  ⟨2038, "Cond.Ne", [], 96, (.enumVariant 1), ⟨"src/isa/aarch64/inst.isle", 1659⟩⟩
theorem program_term_2038 : program.term? 2038 = some term_2038 := by native_decide
@[isel_data] theorem term_2038_kind : term_2038.kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_2038_name : term_2038.name = "Cond.Ne" := rfl

/-- `Cond.Hs` -/
def term_2039 : Isle.Term :=
  ⟨2039, "Cond.Hs", [], 96, (.enumVariant 2), ⟨"src/isa/aarch64/inst.isle", 1660⟩⟩
theorem program_term_2039 : program.term? 2039 = some term_2039 := by native_decide
@[isel_data] theorem term_2039_kind : term_2039.kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_2039_name : term_2039.name = "Cond.Hs" := rfl

/-- `Cond.Hi` -/
def term_2045 : Isle.Term :=
  ⟨2045, "Cond.Hi", [], 96, (.enumVariant 8), ⟨"src/isa/aarch64/inst.isle", 1666⟩⟩
theorem program_term_2045 : program.term? 2045 = some term_2045 := by native_decide
@[isel_data] theorem term_2045_kind : term_2045.kind = (.enumVariant 8) := rfl
@[isel_data] theorem term_2045_name : term_2045.name = "Cond.Hi" := rfl

/-- `Cond.Gt` -/
def term_2049 : Isle.Term :=
  ⟨2049, "Cond.Gt", [], 96, (.enumVariant 12), ⟨"src/isa/aarch64/inst.isle", 1670⟩⟩
theorem program_term_2049 : program.term? 2049 = some term_2049 := by native_decide
@[isel_data] theorem term_2049_kind : term_2049.kind = (.enumVariant 12) := rfl
@[isel_data] theorem term_2049_name : term_2049.name = "Cond.Gt" := rfl

/-- `CondResult.Zero` -/
def term_2236 : Isle.Term :=
  ⟨2236, "CondResult.Zero", [27, 93], 123, (.enumVariant 0), ⟨"src/isa/aarch64/inst.isle", 4945⟩⟩
theorem program_term_2236 : program.term? 2236 = some term_2236 := by native_decide
@[isel_data] theorem term_2236_kind : term_2236.kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_2236_name : term_2236.name = "CondResult.Zero" := rfl

/-- `CondResult.NotZero` -/
def term_2237 : Isle.Term :=
  ⟨2237, "CondResult.NotZero", [27, 93], 123, (.enumVariant 1), ⟨"src/isa/aarch64/inst.isle", 4946⟩⟩
theorem program_term_2237 : program.term? 2237 = some term_2237 := by native_decide
@[isel_data] theorem term_2237_kind : term_2237.kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_2237_name : term_2237.name = "CondResult.NotZero" := rfl

/-- `CondResult.Cond` -/
def term_2238 : Isle.Term :=
  ⟨2238, "CondResult.Cond", [47, 96], 123, (.enumVariant 2), ⟨"src/isa/aarch64/inst.isle", 4947⟩⟩
theorem program_term_2238 : program.term? 2238 = some term_2238 := by native_decide
@[isel_data] theorem term_2238_kind : term_2238.kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_2238_name : term_2238.name = "CondResult.Cond" := rfl

/-- `CondResult.Or` -/
def term_2239 : Isle.Term :=
  ⟨2239, "CondResult.Or", [47, 96, 96], 123, (.enumVariant 3), ⟨"src/isa/aarch64/inst.isle", 4948⟩⟩
theorem program_term_2239 : program.term? 2239 = some term_2239 := by native_decide
@[isel_data] theorem term_2239_kind : term_2239.kind = (.enumVariant 3) := rfl
@[isel_data] theorem term_2239_name : term_2239.name = "CondResult.Or" := rfl

/-- `CondResult.And` -/
def term_2240 : Isle.Term :=
  ⟨2240, "CondResult.And", [47, 96, 96], 123, (.enumVariant 4), ⟨"src/isa/aarch64/inst.isle", 4949⟩⟩
theorem program_term_2240 : program.term? 2240 = some term_2240 := by native_decide
@[isel_data] theorem term_2240_kind : term_2240.kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_2240_name : term_2240.name = "CondResult.And" := rfl

/-- `IntCC.Equal` -/
def term_2269 : Isle.Term :=
  ⟨2269, "IntCC.Equal", [], 145, (.enumVariant 0), ⟨"<OUT_DIR>/clif_lower.isle", 70⟩⟩
theorem program_term_2269 : program.term? 2269 = some term_2269 := by native_decide
@[isel_data] theorem term_2269_kind : term_2269.kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_2269_name : term_2269.name = "IntCC.Equal" := rfl

/-- `IntCC.NotEqual` -/
def term_2270 : Isle.Term :=
  ⟨2270, "IntCC.NotEqual", [], 145, (.enumVariant 1), ⟨"<OUT_DIR>/clif_lower.isle", 71⟩⟩
theorem program_term_2270 : program.term? 2270 = some term_2270 := by native_decide
@[isel_data] theorem term_2270_kind : term_2270.kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_2270_name : term_2270.name = "IntCC.NotEqual" := rfl

/-- `IntCC.SignedGreaterThan` -/
def term_2271 : Isle.Term :=
  ⟨2271, "IntCC.SignedGreaterThan", [], 145, (.enumVariant 2), ⟨"<OUT_DIR>/clif_lower.isle", 72⟩⟩
theorem program_term_2271 : program.term? 2271 = some term_2271 := by native_decide
@[isel_data] theorem term_2271_kind : term_2271.kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_2271_name : term_2271.name = "IntCC.SignedGreaterThan" := rfl

/-- `IntCC.SignedGreaterThanOrEqual` -/
def term_2272 : Isle.Term :=
  ⟨2272, "IntCC.SignedGreaterThanOrEqual", [], 145, (.enumVariant 3), ⟨"<OUT_DIR>/clif_lower.isle", 73⟩⟩
theorem program_term_2272 : program.term? 2272 = some term_2272 := by native_decide
@[isel_data] theorem term_2272_kind : term_2272.kind = (.enumVariant 3) := rfl
@[isel_data] theorem term_2272_name : term_2272.name = "IntCC.SignedGreaterThanOrEqual" := rfl

/-- `IntCC.SignedLessThan` -/
def term_2273 : Isle.Term :=
  ⟨2273, "IntCC.SignedLessThan", [], 145, (.enumVariant 4), ⟨"<OUT_DIR>/clif_lower.isle", 74⟩⟩
theorem program_term_2273 : program.term? 2273 = some term_2273 := by native_decide
@[isel_data] theorem term_2273_kind : term_2273.kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_2273_name : term_2273.name = "IntCC.SignedLessThan" := rfl

/-- `IntCC.SignedLessThanOrEqual` -/
def term_2274 : Isle.Term :=
  ⟨2274, "IntCC.SignedLessThanOrEqual", [], 145, (.enumVariant 5), ⟨"<OUT_DIR>/clif_lower.isle", 75⟩⟩
theorem program_term_2274 : program.term? 2274 = some term_2274 := by native_decide
@[isel_data] theorem term_2274_kind : term_2274.kind = (.enumVariant 5) := rfl
@[isel_data] theorem term_2274_name : term_2274.name = "IntCC.SignedLessThanOrEqual" := rfl

/-- `IntCC.UnsignedGreaterThan` -/
def term_2275 : Isle.Term :=
  ⟨2275, "IntCC.UnsignedGreaterThan", [], 145, (.enumVariant 6), ⟨"<OUT_DIR>/clif_lower.isle", 76⟩⟩
theorem program_term_2275 : program.term? 2275 = some term_2275 := by native_decide
@[isel_data] theorem term_2275_kind : term_2275.kind = (.enumVariant 6) := rfl
@[isel_data] theorem term_2275_name : term_2275.name = "IntCC.UnsignedGreaterThan" := rfl

/-- `IntCC.UnsignedGreaterThanOrEqual` -/
def term_2276 : Isle.Term :=
  ⟨2276, "IntCC.UnsignedGreaterThanOrEqual", [], 145, (.enumVariant 7), ⟨"<OUT_DIR>/clif_lower.isle", 77⟩⟩
theorem program_term_2276 : program.term? 2276 = some term_2276 := by native_decide
@[isel_data] theorem term_2276_kind : term_2276.kind = (.enumVariant 7) := rfl
@[isel_data] theorem term_2276_name : term_2276.name = "IntCC.UnsignedGreaterThanOrEqual" := rfl

/-- `IntCC.UnsignedLessThan` -/
def term_2277 : Isle.Term :=
  ⟨2277, "IntCC.UnsignedLessThan", [], 145, (.enumVariant 8), ⟨"<OUT_DIR>/clif_lower.isle", 78⟩⟩
theorem program_term_2277 : program.term? 2277 = some term_2277 := by native_decide
@[isel_data] theorem term_2277_kind : term_2277.kind = (.enumVariant 8) := rfl
@[isel_data] theorem term_2277_name : term_2277.name = "IntCC.UnsignedLessThan" := rfl

/-- `IntCC.UnsignedLessThanOrEqual` -/
def term_2278 : Isle.Term :=
  ⟨2278, "IntCC.UnsignedLessThanOrEqual", [], 145, (.enumVariant 9), ⟨"<OUT_DIR>/clif_lower.isle", 79⟩⟩
theorem program_term_2278 : program.term? 2278 = some term_2278 := by native_decide
@[isel_data] theorem term_2278_kind : term_2278.kind = (.enumVariant 9) := rfl
@[isel_data] theorem term_2278_name : term_2278.name = "IntCC.UnsignedLessThanOrEqual" := rfl

/-- `Opcode.Iconst` -/
def term_2341 : Isle.Term :=
  ⟨2341, "Opcode.Iconst", [], 151, (.enumVariant 57), ⟨"<OUT_DIR>/clif_lower.isle", 183⟩⟩
theorem program_term_2341 : program.term? 2341 = some term_2341 := by native_decide
@[isel_data] theorem term_2341_kind : term_2341.kind = (.enumVariant 57) := rfl
@[isel_data] theorem term_2341_name : term_2341.name = "Opcode.Iconst" := rfl

/-- `Opcode.Icmp` -/
def term_2356 : Isle.Term :=
  ⟨2356, "Opcode.Icmp", [], 151, (.enumVariant 72), ⟨"<OUT_DIR>/clif_lower.isle", 198⟩⟩
theorem program_term_2356 : program.term? 2356 = some term_2356 := by native_decide
@[isel_data] theorem term_2356_kind : term_2356.kind = (.enumVariant 72) := rfl
@[isel_data] theorem term_2356_name : term_2356.name = "Opcode.Icmp" := rfl

/-- `Opcode.Iadd` -/
def term_2357 : Isle.Term :=
  ⟨2357, "Opcode.Iadd", [], 151, (.enumVariant 73), ⟨"<OUT_DIR>/clif_lower.isle", 199⟩⟩
theorem program_term_2357 : program.term? 2357 = some term_2357 := by native_decide
@[isel_data] theorem term_2357_kind : term_2357.kind = (.enumVariant 73) := rfl
@[isel_data] theorem term_2357_name : term_2357.name = "Opcode.Iadd" := rfl

/-- `Opcode.UaddOverflow` -/
def term_2372 : Isle.Term :=
  ⟨2372, "Opcode.UaddOverflow", [], 151, (.enumVariant 88), ⟨"<OUT_DIR>/clif_lower.isle", 214⟩⟩
theorem program_term_2372 : program.term? 2372 = some term_2372 := by native_decide
@[isel_data] theorem term_2372_kind : term_2372.kind = (.enumVariant 88) := rfl
@[isel_data] theorem term_2372_name : term_2372.name = "Opcode.UaddOverflow" := rfl

/-- `Opcode.UmulOverflow` -/
def term_2376 : Isle.Term :=
  ⟨2376, "Opcode.UmulOverflow", [], 151, (.enumVariant 92), ⟨"<OUT_DIR>/clif_lower.isle", 218⟩⟩
theorem program_term_2376 : program.term? 2376 = some term_2376 := by native_decide
@[isel_data] theorem term_2376_kind : term_2376.kind = (.enumVariant 92) := rfl
@[isel_data] theorem term_2376_name : term_2376.name = "Opcode.UmulOverflow" := rfl

/-- `Opcode.SmulOverflow` -/
def term_2377 : Isle.Term :=
  ⟨2377, "Opcode.SmulOverflow", [], 151, (.enumVariant 93), ⟨"<OUT_DIR>/clif_lower.isle", 219⟩⟩
theorem program_term_2377 : program.term? 2377 = some term_2377 := by native_decide
@[isel_data] theorem term_2377_kind : term_2377.kind = (.enumVariant 93) := rfl
@[isel_data] theorem term_2377_name : term_2377.name = "Opcode.SmulOverflow" := rfl

/-- `Opcode.Ushr` -/
def term_2388 : Isle.Term :=
  ⟨2388, "Opcode.Ushr", [], 151, (.enumVariant 104), ⟨"<OUT_DIR>/clif_lower.isle", 230⟩⟩
theorem program_term_2388 : program.term? 2388 = some term_2388 := by native_decide
@[isel_data] theorem term_2388_kind : term_2388.kind = (.enumVariant 104) := rfl
@[isel_data] theorem term_2388_name : term_2388.name = "Opcode.Ushr" := rfl

/-- `InstructionData.Binary` -/
def term_2449 : Isle.Term :=
  ⟨2449, "InstructionData.Binary", [151, 147], 152, (.enumVariant 2), ⟨"<OUT_DIR>/clif_lower.isle", 298⟩⟩
theorem program_term_2449 : program.term? 2449 = some term_2449 := by native_decide
@[isel_data] theorem term_2449_kind : term_2449.kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_2449_name : term_2449.name = "InstructionData.Binary" := rfl

/-- `InstructionData.IntCompare` -/
def term_2461 : Isle.Term :=
  ⟨2461, "InstructionData.IntCompare", [151, 147, 145], 152, (.enumVariant 14), ⟨"<OUT_DIR>/clif_lower.isle", 310⟩⟩
theorem program_term_2461 : program.term? 2461 = some term_2461 := by native_decide
@[isel_data] theorem term_2461_kind : term_2461.kind = (.enumVariant 14) := rfl
@[isel_data] theorem term_2461_name : term_2461.name = "InstructionData.IntCompare" := rfl

/-- `InstructionData.UnaryImm` -/
def term_2482 : Isle.Term :=
  ⟨2482, "InstructionData.UnaryImm", [151, 134], 152, (.enumVariant 35), ⟨"<OUT_DIR>/clif_lower.isle", 331⟩⟩
theorem program_term_2482 : program.term? 2482 = some term_2482 := by native_decide
@[isel_data] theorem term_2482_kind : term_2482.kind = (.enumVariant 35) := rfl
@[isel_data] theorem term_2482_name : term_2482.name = "InstructionData.UnaryImm" := rfl

theorem program_termByName_lower : program.termByName? "lower" = some term_686 := by
  native_decide

/-- The facts about the exported program that the isel proofs use. Proofs are stated for
an arbitrary `p : Program` with `Data p`, never for `Isle.Aarch64.program` itself, so the kernel
cannot unfold the program data while checking them (with `program` directly, some `simp` proof
steps made the kernel reduce the program and run out of memory); `data_program` instantiates. -/
structure Data (p : Program) : Prop where
  t1 : Interp.termOf p 1 = pure term_1
  t2 : Interp.termOf p 2 = pure term_2
  t87 : Interp.termOf p 87 = pure term_87
  t110 : Interp.termOf p 110 = pure term_110
  t111 : Interp.termOf p 111 = pure term_111
  t113 : Interp.termOf p 113 = pure term_113
  t119 : Interp.termOf p 119 = pure term_119
  t120 : Interp.termOf p 120 = pure term_120
  t126 : Interp.termOf p 126 = pure term_126
  t144 : Interp.termOf p 144 = pure term_144
  t159 : Interp.termOf p 159 = pure term_159
  t160 : Interp.termOf p 160 = pure term_160
  t164 : Interp.termOf p 164 = pure term_164
  t166 : Interp.termOf p 166 = pure term_166
  t170 : Interp.termOf p 170 = pure term_170
  t172 : Interp.termOf p 172 = pure term_172
  r172 : p.rulesOf 172 =
    [rule_prelude_lower_105]
  t175 : Interp.termOf p 175 = pure term_175
  t181 : Interp.termOf p 181 = pure term_181
  t182 : Interp.termOf p 182 = pure term_182
  t183 : Interp.termOf p 183 = pure term_183
  t185 : Interp.termOf p 185 = pure term_185
  t201 : Interp.termOf p 201 = pure term_201
  t205 : Interp.termOf p 205 = pure term_205
  t207 : Interp.termOf p 207 = pure term_207
  t209 : Interp.termOf p 209 = pure term_209
  t235 : Interp.termOf p 235 = pure term_235
  t246 : Interp.termOf p 246 = pure term_246
  r246 : p.rulesOf 246 =
    [rule_prelude_lower_644]
  t249 : Interp.termOf p 249 = pure term_249
  r249 : p.rulesOf 249 =
    [rule_prelude_lower_715]
  t250 : Interp.termOf p 250 = pure term_250
  r250 : p.rulesOf 250 =
    [rule_prelude_lower_725]
  t251 : Interp.termOf p 251 = pure term_251
  r251 : p.rulesOf 251 =
    [rule_prelude_lower_744, rule_prelude_lower_750]
  t254 : Interp.termOf p 254 = pure term_254
  r254 : p.rulesOf 254 =
    [rule_prelude_lower_789, rule_prelude_lower_798, rule_prelude_lower_807, rule_prelude_lower_812, rule_prelude_lower_818, rule_prelude_lower_829, rule_prelude_lower_837, rule_prelude_lower_850, rule_prelude_lower_864, rule_prelude_lower_881, rule_prelude_lower_903, rule_prelude_lower_912, rule_prelude_lower_927, rule_prelude_lower_943, rule_prelude_lower_951, rule_prelude_lower_965]
  t305 : Interp.termOf p 305 = pure term_305
  r305 : p.rulesOf 305 =
    [rule_inst_1592, rule_inst_1593]
  t323 : Interp.termOf p 323 = pure term_323
  t325 : Interp.termOf p 325 = pure term_325
  t327 : Interp.termOf p 327 = pure term_327
  t328 : Interp.termOf p 328 = pure term_328
  t338 : Interp.termOf p 338 = pure term_338
  t348 : Interp.termOf p 348 = pure term_348
  t352 : Interp.termOf p 352 = pure term_352
  t356 : Interp.termOf p 356 = pure term_356
  t360 : Interp.termOf p 360 = pure term_360
  r360 : p.rulesOf 360 =
    [rule_inst_2529]
  t361 : Interp.termOf p 361 = pure term_361
  r361 : p.rulesOf 361 =
    [rule_inst_2537]
  t362 : Interp.termOf p 362 = pure term_362
  r362 : p.rulesOf 362 =
    [rule_inst_2545]
  t376 : Interp.termOf p 376 = pure term_376
  r376 : p.rulesOf 376 =
    [rule_inst_2648]
  t379 : Interp.termOf p 379 = pure term_379
  r379 : p.rulesOf 379 =
    [rule_inst_2675]
  t383 : Interp.termOf p 383 = pure term_383
  r383 : p.rulesOf 383 =
    [rule_inst_2709]
  t385 : Interp.termOf p 385 = pure term_385
  r385 : p.rulesOf 385 =
    [rule_inst_2726]
  t390 : Interp.termOf p 390 = pure term_390
  r390 : p.rulesOf 390 =
    [rule_inst_2767]
  t391 : Interp.termOf p 391 = pure term_391
  r391 : p.rulesOf 391 =
    [rule_inst_2774]
  t392 : Interp.termOf p 392 = pure term_392
  r392 : p.rulesOf 392 =
    [rule_inst_2781]
  t393 : Interp.termOf p 393 = pure term_393
  r393 : p.rulesOf 393 =
    [rule_inst_2786]
  t417 : Interp.termOf p 417 = pure term_417
  r417 : p.rulesOf 417 =
    [rule_inst_2991]
  t424 : Interp.termOf p 424 = pure term_424
  r424 : p.rulesOf 424 =
    [rule_inst_3044]
  t426 : Interp.termOf p 426 = pure term_426
  r426 : p.rulesOf 426 =
    [rule_inst_3068]
  t430 : Interp.termOf p 430 = pure term_430
  r430 : p.rulesOf 430 =
    [rule_inst_3103]
  t432 : Interp.termOf p 432 = pure term_432
  r432 : p.rulesOf 432 =
    [rule_inst_3118]
  t433 : Interp.termOf p 433 = pure term_433
  r433 : p.rulesOf 433 =
    [rule_inst_3122]
  t451 : Interp.termOf p 451 = pure term_451
  r451 : p.rulesOf 451 =
    [rule_inst_3213]
  t452 : Interp.termOf p 452 = pure term_452
  r452 : p.rulesOf 452 =
    [rule_inst_3218]
  t497 : Interp.termOf p 497 = pure term_497
  r497 : p.rulesOf 497 =
    [rule_inst_3412]
  t501 : Interp.termOf p 501 = pure term_501
  r501 : p.rulesOf 501 =
    [rule_inst_3427]
  t502 : Interp.termOf p 502 = pure term_502
  r502 : p.rulesOf 502 =
    [rule_inst_3431]
  t555 : Interp.termOf p 555 = pure term_555
  r555 : p.rulesOf 555 =
    [rule_inst_3803, rule_inst_3804, rule_inst_3799]
  t556 : Interp.termOf p 556 = pure term_556
  r556 : p.rulesOf 556 =
    [rule_inst_3813, rule_inst_3814, rule_inst_3809]
  t592 : Interp.termOf p 592 = pure term_592
  t593 : Interp.termOf p 593 = pure term_593
  t649 : Interp.termOf p 649 = pure term_649
  r649 : p.rulesOf 649 =
    [rule_inst_4954, rule_inst_4955, rule_inst_4956, rule_inst_4957, rule_inst_4959]
  t651 : Interp.termOf p 651 = pure term_651
  r651 : p.rulesOf 651 =
    [rule_inst_5094, rule_inst_5077, rule_inst_5058, rule_inst_5049, rule_inst_5032, rule_inst_5013, rule_inst_4993, rule_inst_4988, rule_inst_4983, rule_inst_4979, rule_inst_4977]
  t652 : Interp.termOf p 652 = pure term_652
  r652 : p.rulesOf 652 =
    [rule_inst_5171, rule_inst_5173, rule_inst_5170, rule_inst_5172, rule_inst_5165, rule_inst_5155, rule_inst_5160, rule_inst_5142, rule_inst_5134, rule_inst_5128, rule_inst_5117, rule_inst_5108]
  t653 : Interp.termOf p 653 = pure term_653
  r653 : p.rulesOf 653 =
    [rule_inst_5179, rule_inst_5181, rule_inst_5183, rule_inst_5185, rule_inst_5189, rule_inst_5191, rule_inst_5201]
  t654 : Interp.termOf p 654 = pure term_654
  r654 : p.rulesOf 654 =
    [rule_inst_5195]
  t657 : Interp.termOf p 657 = pure term_657
  r657 : p.rulesOf 657 =
    [rule_inst_5264, rule_inst_5265, rule_inst_5266, rule_inst_5267]
  t686 : Interp.termOf p 686 = pure term_686
  r686 : p.rulesOf 686 =
    [rule_lower_419, rule_lower_402, rule_lower_1444, rule_lower_1481, rule_lower_116, rule_lower_125, rule_lower_1442, rule_lower_1479, rule_lower_2779, rule_lower_120, rule_lower_128, rule_lower_165, rule_lower_1439, rule_lower_1476, rule_lower_2784, rule_lower_93, rule_lower_167, rule_lower_1437, rule_lower_1474, rule_lower_1501, rule_lower_1507, rule_lower_2789, rule_lower_3091, rule_lower_3155, rule_lower_90, rule_lower_169, rule_lower_1435, rule_lower_1472, rule_lower_1540, rule_lower_2152, rule_lower_2793, rule_lower_3097, rule_lower_3161, rule_lower_102, rule_lower_171, rule_lower_1408, rule_lower_1434, rule_lower_1471, rule_lower_1539, rule_lower_2158, rule_lower_2185, rule_lower_2798, rule_lower_2828, rule_lower_3008, rule_lower_3101, rule_lower_3165, rule_lower_98, rule_lower_190, rule_lower_437, rule_lower_609, rule_lower_810, rule_lower_861, rule_lower_1163, rule_lower_1222, rule_lower_1224, rule_lower_1226, rule_lower_1228, rule_lower_1406, rule_lower_1431, rule_lower_1468, rule_lower_1536, rule_lower_2120, rule_lower_2164, rule_lower_2191, rule_lower_2386, rule_lower_2404, rule_lower_2419, rule_lower_2435, rule_lower_2815, rule_lower_3018, rule_lower_3036, rule_lower_3056, rule_lower_3076, rule_lower_3126, rule_lower_3140, rule_lower_3190, rule_lower_3204, rule_lower_111, rule_lower_203, rule_lower_205, rule_lower_207, rule_lower_209, rule_lower_211, rule_lower_213, rule_lower_215, rule_lower_217, rule_lower_222, rule_lower_224, rule_lower_226, rule_lower_228, rule_lower_230, rule_lower_232, rule_lower_240, rule_lower_242, rule_lower_244, rule_lower_246, rule_lower_248, rule_lower_250, rule_lower_260, rule_lower_262, rule_lower_264, rule_lower_266, rule_lower_268, rule_lower_270, rule_lower_294, rule_lower_300, rule_lower_440, rule_lower_608, rule_lower_693, rule_lower_699, rule_lower_707, rule_lower_713, rule_lower_730, rule_lower_733, rule_lower_750, rule_lower_753, rule_lower_767, rule_lower_773, rule_lower_787, rule_lower_793, rule_lower_816, rule_lower_857, rule_lower_1056, rule_lower_1068, rule_lower_1116, rule_lower_1167, rule_lower_1236, rule_lower_1242, rule_lower_1248, rule_lower_1254, rule_lower_1266, rule_lower_1272, rule_lower_1281, rule_lower_1283, rule_lower_1401, rule_lower_1429, rule_lower_1466, rule_lower_1534, rule_lower_1704, rule_lower_1707, rule_lower_1803, rule_lower_1808, rule_lower_2138, rule_lower_2170, rule_lower_2197, rule_lower_2288, rule_lower_2328, rule_lower_2331, rule_lower_2334, rule_lower_2337, rule_lower_2340, rule_lower_2343, rule_lower_2346, rule_lower_2349, rule_lower_2352, rule_lower_2381, rule_lower_2400, rule_lower_2415, rule_lower_2431, rule_lower_2451, rule_lower_2466, rule_lower_2508, rule_lower_2580, rule_lower_2803, rule_lower_2822, rule_lower_2837, rule_lower_3014, rule_lower_3031, rule_lower_3051, rule_lower_3071, rule_lower_3110, rule_lower_3174, rule_lower_53, rule_lower_58, rule_lower_63, rule_lower_68, rule_lower_73, rule_lower_78, rule_lower_108, rule_lower_132, rule_lower_273, rule_lower_279, rule_lower_284, rule_lower_308, rule_lower_313, rule_lower_316, rule_lower_336, rule_lower_342, rule_lower_368, rule_lower_375, rule_lower_379, rule_lower_383, rule_lower_387, rule_lower_450, rule_lower_463, rule_lower_477, rule_lower_485, rule_lower_493, rule_lower_501, rule_lower_509, rule_lower_517, rule_lower_525, rule_lower_533, rule_lower_541, rule_lower_549, rule_lower_554, rule_lower_559, rule_lower_567, rule_lower_570, rule_lower_578, rule_lower_581, rule_lower_589, rule_lower_592, rule_lower_600, rule_lower_603, rule_lower_685, rule_lower_690, rule_lower_696, rule_lower_704, rule_lower_710, rule_lower_724, rule_lower_727, rule_lower_744, rule_lower_747, rule_lower_764, rule_lower_770, rule_lower_784, rule_lower_790, rule_lower_805, rule_lower_836, rule_lower_841, rule_lower_846, rule_lower_851, rule_lower_865, rule_lower_906, rule_lower_914, rule_lower_995, rule_lower_1000, rule_lower_1005, rule_lower_1010, rule_lower_1015, rule_lower_1020, rule_lower_1025, rule_lower_1030, rule_lower_1035, rule_lower_1040, rule_lower_1045, rule_lower_1050, rule_lower_1059, rule_lower_1071, rule_lower_1119, rule_lower_1145, rule_lower_1190, rule_lower_1204, rule_lower_1233, rule_lower_1239, rule_lower_1245, rule_lower_1251, rule_lower_1294, rule_lower_1300, rule_lower_1339, rule_lower_1359, rule_lower_1391, rule_lower_1424, rule_lower_1461, rule_lower_1528, rule_lower_1549, rule_lower_1553, rule_lower_1642, rule_lower_1646, rule_lower_1699, rule_lower_1720, rule_lower_1791, rule_lower_1797, rule_lower_1827, rule_lower_1857, rule_lower_1862, rule_lower_1916, rule_lower_1931, rule_lower_1937, rule_lower_1940, rule_lower_1951, rule_lower_1955, rule_lower_1958, rule_lower_1982, rule_lower_1986, rule_lower_1989, rule_lower_2000, rule_lower_2004, rule_lower_2016, rule_lower_2035, rule_lower_2038, rule_lower_2041, rule_lower_2044, rule_lower_2052, rule_lower_2074, rule_lower_2080, rule_lower_2086, rule_lower_2092, rule_lower_2099, rule_lower_2108, rule_lower_2113, rule_lower_2146, rule_lower_2176, rule_lower_2203, rule_lower_2237, rule_lower_2242, rule_lower_2262, rule_lower_2267, rule_lower_2280, rule_lower_2285, rule_lower_2301, rule_lower_2304, rule_lower_2307, rule_lower_2310, rule_lower_2316, rule_lower_2321, rule_lower_2357, rule_lower_2359, rule_lower_2361, rule_lower_2363, rule_lower_2365, rule_lower_2367, rule_lower_2369, rule_lower_2371, rule_lower_2373, rule_lower_2375, rule_lower_2377, rule_lower_2390, rule_lower_2395, rule_lower_2408, rule_lower_2423, rule_lower_2439, rule_lower_2446, rule_lower_2454, rule_lower_2461, rule_lower_2469, rule_lower_2476, rule_lower_2481, rule_lower_2486, rule_lower_2491, rule_lower_2496, rule_lower_2499, rule_lower_2502, rule_lower_2518, rule_lower_2529, rule_lower_2574, rule_lower_2587, rule_lower_2595, rule_lower_2604, rule_lower_2607, rule_lower_2610, rule_lower_2613, rule_lower_2619, rule_lower_2647, rule_lower_2650, rule_lower_2653, rule_lower_2656, rule_lower_2659, rule_lower_2662, rule_lower_2666, rule_lower_2672, rule_lower_2678, rule_lower_2684, rule_lower_2690, rule_lower_2696, rule_lower_2705, rule_lower_2709, rule_lower_2713, rule_lower_2717, rule_lower_2722, rule_lower_2726, rule_lower_2730, rule_lower_2735, rule_lower_2770, rule_lower_2773, rule_lower_2809, rule_lower_2818, rule_lower_2842, rule_lower_2849, rule_lower_2863, rule_lower_2887, rule_lower_2900, rule_lower_2913, rule_lower_2927, rule_lower_3022, rule_lower_3042, rule_lower_3062, rule_lower_3082, rule_lower_3217, rule_lower_3220, rule_lower_3225, rule_lower_3286, rule_lower_3292, rule_lower_dynamic_neon_81, rule_lower_dynamic_neon_87, rule_lower_86, rule_lower_319, rule_lower_359, rule_lower_390, rule_lower_434, rule_lower_472, rule_lower_482, rule_lower_490, rule_lower_498, rule_lower_506, rule_lower_514, rule_lower_522, rule_lower_530, rule_lower_538, rule_lower_546, rule_lower_564, rule_lower_575, rule_lower_586, rule_lower_597, rule_lower_718, rule_lower_721, rule_lower_738, rule_lower_741, rule_lower_758, rule_lower_761, rule_lower_778, rule_lower_781, rule_lower_831, rule_lower_876, rule_lower_956, rule_lower_1153, rule_lower_1197, rule_lower_1211, rule_lower_1289, rule_lower_1349, rule_lower_1387, rule_lower_1421, rule_lower_1458, rule_lower_1525, rule_lower_1545, rule_lower_1638, rule_lower_1736, rule_lower_1778, rule_lower_1844, rule_lower_1848, rule_lower_1946, rule_lower_1961, rule_lower_1995, rule_lower_2030, rule_lower_2179, rule_lower_2209, rule_lower_2294, rule_lower_2622, rule_lower_2742, rule_lower_dynamic_neon_43, rule_lower_dynamic_neon_57, rule_lower_dynamic_neon_71, rule_lower_dynamic_neon_92, rule_lower_dynamic_neon_97, rule_lower_137, rule_lower_322, rule_lower_826, rule_lower_924, rule_lower_1261, rule_lower_1329, rule_lower_1385, rule_lower_1419, rule_lower_1456, rule_lower_1523, rule_lower_1588, rule_lower_1661, rule_lower_1734, rule_lower_1772, rule_lower_1852, rule_lower_2215, rule_lower_2298, rule_lower_2625, rule_lower_2746, rule_lower_dynamic_neon_15, rule_lower_dynamic_neon_19, rule_lower_dynamic_neon_23, rule_lower_dynamic_neon_27, rule_lower_dynamic_neon_31, rule_lower_dynamic_neon_35, rule_lower_dynamic_neon_39, rule_lower_dynamic_neon_53, rule_lower_dynamic_neon_67, rule_lower_142, rule_lower_821, rule_lower_871, rule_lower_1320, rule_lower_1381, rule_lower_1452, rule_lower_1519, rule_lower_1583, rule_lower_1659, rule_lower_1729, rule_lower_1840, rule_lower_2628, rule_lower_2750, rule_lower_dynamic_neon_47, rule_lower_dynamic_neon_61, rule_lower_dynamic_neon_75, rule_lower_801, rule_lower_1315, rule_lower_1377, rule_lower_1415, rule_lower_1449, rule_lower_1516, rule_lower_1654, rule_lower_1695, rule_lower_2633, rule_lower_2754, rule_lower_dynamic_neon_3, rule_lower_dynamic_neon_11, rule_lower_1412, rule_lower_2638, rule_lower_2759, rule_lower_dynamic_neon_7, rule_lower_2643, rule_lower_2763]
  t703 : Interp.termOf p 703 = pure term_703
  r703 : p.rulesOf 703 =
    [rule_lower_1631, rule_lower_1622, rule_lower_1623, rule_lower_1612]
  t704 : Interp.termOf p 704 = pure term_704
  t715 : Interp.termOf p 715 = pure term_715
  r715 : p.rulesOf 715 =
    [rule_lower_2222, rule_lower_2224, rule_lower_2226, rule_lower_2228, rule_lower_2231]
  t1167 : Interp.termOf p 1167 = pure term_1167
  t1199 : Interp.termOf p 1199 = pure term_1199
  t1614 : Interp.termOf p 1614 = pure term_1614
  t1791 : Interp.termOf p 1791 = pure term_1791
  t1792 : Interp.termOf p 1792 = pure term_1792
  t1793 : Interp.termOf p 1793 = pure term_1793
  t1794 : Interp.termOf p 1794 = pure term_1794
  t1795 : Interp.termOf p 1795 = pure term_1795
  t1796 : Interp.termOf p 1796 = pure term_1796
  t1799 : Interp.termOf p 1799 = pure term_1799
  t1800 : Interp.termOf p 1800 = pure term_1800
  t1801 : Interp.termOf p 1801 = pure term_1801
  t1802 : Interp.termOf p 1802 = pure term_1802
  t1803 : Interp.termOf p 1803 = pure term_1803
  t1804 : Interp.termOf p 1804 = pure term_1804
  t1805 : Interp.termOf p 1805 = pure term_1805
  t1816 : Interp.termOf p 1816 = pure term_1816
  t1817 : Interp.termOf p 1817 = pure term_1817
  t1820 : Interp.termOf p 1820 = pure term_1820
  t1821 : Interp.termOf p 1821 = pure term_1821
  t1822 : Interp.termOf p 1822 = pure term_1822
  t1823 : Interp.termOf p 1823 = pure term_1823
  t1824 : Interp.termOf p 1824 = pure term_1824
  t1825 : Interp.termOf p 1825 = pure term_1825
  t1826 : Interp.termOf p 1826 = pure term_1826
  t1846 : Interp.termOf p 1846 = pure term_1846
  t1851 : Interp.termOf p 1851 = pure term_1851
  t1853 : Interp.termOf p 1853 = pure term_1853
  t1962 : Interp.termOf p 1962 = pure term_1962
  t1964 : Interp.termOf p 1964 = pure term_1964
  t1966 : Interp.termOf p 1966 = pure term_1966
  t1967 : Interp.termOf p 1967 = pure term_1967
  t1971 : Interp.termOf p 1971 = pure term_1971
  t1972 : Interp.termOf p 1972 = pure term_1972
  t1973 : Interp.termOf p 1973 = pure term_1973
  t1974 : Interp.termOf p 1974 = pure term_1974
  t1978 : Interp.termOf p 1978 = pure term_1978
  t1984 : Interp.termOf p 1984 = pure term_1984
  t1985 : Interp.termOf p 1985 = pure term_1985
  t1987 : Interp.termOf p 1987 = pure term_1987
  t1988 : Interp.termOf p 1988 = pure term_1988
  t1996 : Interp.termOf p 1996 = pure term_1996
  t1997 : Interp.termOf p 1997 = pure term_1997
  t1998 : Interp.termOf p 1998 = pure term_1998
  t2000 : Interp.termOf p 2000 = pure term_2000
  t2001 : Interp.termOf p 2001 = pure term_2001
  t2002 : Interp.termOf p 2002 = pure term_2002
  t2028 : Interp.termOf p 2028 = pure term_2028
  t2029 : Interp.termOf p 2029 = pure term_2029
  t2037 : Interp.termOf p 2037 = pure term_2037
  t2038 : Interp.termOf p 2038 = pure term_2038
  t2039 : Interp.termOf p 2039 = pure term_2039
  t2045 : Interp.termOf p 2045 = pure term_2045
  t2049 : Interp.termOf p 2049 = pure term_2049
  t2236 : Interp.termOf p 2236 = pure term_2236
  t2237 : Interp.termOf p 2237 = pure term_2237
  t2238 : Interp.termOf p 2238 = pure term_2238
  t2239 : Interp.termOf p 2239 = pure term_2239
  t2240 : Interp.termOf p 2240 = pure term_2240
  t2269 : Interp.termOf p 2269 = pure term_2269
  t2270 : Interp.termOf p 2270 = pure term_2270
  t2271 : Interp.termOf p 2271 = pure term_2271
  t2272 : Interp.termOf p 2272 = pure term_2272
  t2273 : Interp.termOf p 2273 = pure term_2273
  t2274 : Interp.termOf p 2274 = pure term_2274
  t2275 : Interp.termOf p 2275 = pure term_2275
  t2276 : Interp.termOf p 2276 = pure term_2276
  t2277 : Interp.termOf p 2277 = pure term_2277
  t2278 : Interp.termOf p 2278 = pure term_2278
  t2341 : Interp.termOf p 2341 = pure term_2341
  t2356 : Interp.termOf p 2356 = pure term_2356
  t2357 : Interp.termOf p 2357 = pure term_2357
  t2372 : Interp.termOf p 2372 = pure term_2372
  t2376 : Interp.termOf p 2376 = pure term_2376
  t2377 : Interp.termOf p 2377 = pure term_2377
  t2388 : Interp.termOf p 2388 = pure term_2388
  t2449 : Interp.termOf p 2449 = pure term_2449
  t2461 : Interp.termOf p 2461 = pure term_2461
  t2482 : Interp.termOf p 2482 = pure term_2482
  lower : p.termByName? "lower" = some term_686

-- elaborating a ~200-field structure instance nests deeply (no kernel reduction involved)
set_option maxRecDepth 4000 in
theorem data_program : Data program where
  t1 := by rw [Interp.termOf, program_term_1]
  t2 := by rw [Interp.termOf, program_term_2]
  t87 := by rw [Interp.termOf, program_term_87]
  t110 := by rw [Interp.termOf, program_term_110]
  t111 := by rw [Interp.termOf, program_term_111]
  t113 := by rw [Interp.termOf, program_term_113]
  t119 := by rw [Interp.termOf, program_term_119]
  t120 := by rw [Interp.termOf, program_term_120]
  t126 := by rw [Interp.termOf, program_term_126]
  t144 := by rw [Interp.termOf, program_term_144]
  t159 := by rw [Interp.termOf, program_term_159]
  t160 := by rw [Interp.termOf, program_term_160]
  t164 := by rw [Interp.termOf, program_term_164]
  t166 := by rw [Interp.termOf, program_term_166]
  t170 := by rw [Interp.termOf, program_term_170]
  t172 := by rw [Interp.termOf, program_term_172]
  r172 := program_rulesOf_172
  t175 := by rw [Interp.termOf, program_term_175]
  t181 := by rw [Interp.termOf, program_term_181]
  t182 := by rw [Interp.termOf, program_term_182]
  t183 := by rw [Interp.termOf, program_term_183]
  t185 := by rw [Interp.termOf, program_term_185]
  t201 := by rw [Interp.termOf, program_term_201]
  t205 := by rw [Interp.termOf, program_term_205]
  t207 := by rw [Interp.termOf, program_term_207]
  t209 := by rw [Interp.termOf, program_term_209]
  t235 := by rw [Interp.termOf, program_term_235]
  t246 := by rw [Interp.termOf, program_term_246]
  r246 := program_rulesOf_246
  t249 := by rw [Interp.termOf, program_term_249]
  r249 := program_rulesOf_249
  t250 := by rw [Interp.termOf, program_term_250]
  r250 := program_rulesOf_250
  t251 := by rw [Interp.termOf, program_term_251]
  r251 := program_rulesOf_251
  t254 := by rw [Interp.termOf, program_term_254]
  r254 := program_rulesOf_254
  t305 := by rw [Interp.termOf, program_term_305]
  r305 := program_rulesOf_305
  t323 := by rw [Interp.termOf, program_term_323]
  t325 := by rw [Interp.termOf, program_term_325]
  t327 := by rw [Interp.termOf, program_term_327]
  t328 := by rw [Interp.termOf, program_term_328]
  t338 := by rw [Interp.termOf, program_term_338]
  t348 := by rw [Interp.termOf, program_term_348]
  t352 := by rw [Interp.termOf, program_term_352]
  t356 := by rw [Interp.termOf, program_term_356]
  t360 := by rw [Interp.termOf, program_term_360]
  r360 := program_rulesOf_360
  t361 := by rw [Interp.termOf, program_term_361]
  r361 := program_rulesOf_361
  t362 := by rw [Interp.termOf, program_term_362]
  r362 := program_rulesOf_362
  t376 := by rw [Interp.termOf, program_term_376]
  r376 := program_rulesOf_376
  t379 := by rw [Interp.termOf, program_term_379]
  r379 := program_rulesOf_379
  t383 := by rw [Interp.termOf, program_term_383]
  r383 := program_rulesOf_383
  t385 := by rw [Interp.termOf, program_term_385]
  r385 := program_rulesOf_385
  t390 := by rw [Interp.termOf, program_term_390]
  r390 := program_rulesOf_390
  t391 := by rw [Interp.termOf, program_term_391]
  r391 := program_rulesOf_391
  t392 := by rw [Interp.termOf, program_term_392]
  r392 := program_rulesOf_392
  t393 := by rw [Interp.termOf, program_term_393]
  r393 := program_rulesOf_393
  t417 := by rw [Interp.termOf, program_term_417]
  r417 := program_rulesOf_417
  t424 := by rw [Interp.termOf, program_term_424]
  r424 := program_rulesOf_424
  t426 := by rw [Interp.termOf, program_term_426]
  r426 := program_rulesOf_426
  t430 := by rw [Interp.termOf, program_term_430]
  r430 := program_rulesOf_430
  t432 := by rw [Interp.termOf, program_term_432]
  r432 := program_rulesOf_432
  t433 := by rw [Interp.termOf, program_term_433]
  r433 := program_rulesOf_433
  t451 := by rw [Interp.termOf, program_term_451]
  r451 := program_rulesOf_451
  t452 := by rw [Interp.termOf, program_term_452]
  r452 := program_rulesOf_452
  t497 := by rw [Interp.termOf, program_term_497]
  r497 := program_rulesOf_497
  t501 := by rw [Interp.termOf, program_term_501]
  r501 := program_rulesOf_501
  t502 := by rw [Interp.termOf, program_term_502]
  r502 := program_rulesOf_502
  t555 := by rw [Interp.termOf, program_term_555]
  r555 := program_rulesOf_555
  t556 := by rw [Interp.termOf, program_term_556]
  r556 := program_rulesOf_556
  t592 := by rw [Interp.termOf, program_term_592]
  t593 := by rw [Interp.termOf, program_term_593]
  t649 := by rw [Interp.termOf, program_term_649]
  r649 := program_rulesOf_649
  t651 := by rw [Interp.termOf, program_term_651]
  r651 := program_rulesOf_651
  t652 := by rw [Interp.termOf, program_term_652]
  r652 := program_rulesOf_652
  t653 := by rw [Interp.termOf, program_term_653]
  r653 := program_rulesOf_653
  t654 := by rw [Interp.termOf, program_term_654]
  r654 := program_rulesOf_654
  t657 := by rw [Interp.termOf, program_term_657]
  r657 := program_rulesOf_657
  t686 := by rw [Interp.termOf, program_term_686]
  r686 := program_rulesOf_686
  t703 := by rw [Interp.termOf, program_term_703]
  r703 := program_rulesOf_703
  t704 := by rw [Interp.termOf, program_term_704]
  t715 := by rw [Interp.termOf, program_term_715]
  r715 := program_rulesOf_715
  t1167 := by rw [Interp.termOf, program_term_1167]
  t1199 := by rw [Interp.termOf, program_term_1199]
  t1614 := by rw [Interp.termOf, program_term_1614]
  t1791 := by rw [Interp.termOf, program_term_1791]
  t1792 := by rw [Interp.termOf, program_term_1792]
  t1793 := by rw [Interp.termOf, program_term_1793]
  t1794 := by rw [Interp.termOf, program_term_1794]
  t1795 := by rw [Interp.termOf, program_term_1795]
  t1796 := by rw [Interp.termOf, program_term_1796]
  t1799 := by rw [Interp.termOf, program_term_1799]
  t1800 := by rw [Interp.termOf, program_term_1800]
  t1801 := by rw [Interp.termOf, program_term_1801]
  t1802 := by rw [Interp.termOf, program_term_1802]
  t1803 := by rw [Interp.termOf, program_term_1803]
  t1804 := by rw [Interp.termOf, program_term_1804]
  t1805 := by rw [Interp.termOf, program_term_1805]
  t1816 := by rw [Interp.termOf, program_term_1816]
  t1817 := by rw [Interp.termOf, program_term_1817]
  t1820 := by rw [Interp.termOf, program_term_1820]
  t1821 := by rw [Interp.termOf, program_term_1821]
  t1822 := by rw [Interp.termOf, program_term_1822]
  t1823 := by rw [Interp.termOf, program_term_1823]
  t1824 := by rw [Interp.termOf, program_term_1824]
  t1825 := by rw [Interp.termOf, program_term_1825]
  t1826 := by rw [Interp.termOf, program_term_1826]
  t1846 := by rw [Interp.termOf, program_term_1846]
  t1851 := by rw [Interp.termOf, program_term_1851]
  t1853 := by rw [Interp.termOf, program_term_1853]
  t1962 := by rw [Interp.termOf, program_term_1962]
  t1964 := by rw [Interp.termOf, program_term_1964]
  t1966 := by rw [Interp.termOf, program_term_1966]
  t1967 := by rw [Interp.termOf, program_term_1967]
  t1971 := by rw [Interp.termOf, program_term_1971]
  t1972 := by rw [Interp.termOf, program_term_1972]
  t1973 := by rw [Interp.termOf, program_term_1973]
  t1974 := by rw [Interp.termOf, program_term_1974]
  t1978 := by rw [Interp.termOf, program_term_1978]
  t1984 := by rw [Interp.termOf, program_term_1984]
  t1985 := by rw [Interp.termOf, program_term_1985]
  t1987 := by rw [Interp.termOf, program_term_1987]
  t1988 := by rw [Interp.termOf, program_term_1988]
  t1996 := by rw [Interp.termOf, program_term_1996]
  t1997 := by rw [Interp.termOf, program_term_1997]
  t1998 := by rw [Interp.termOf, program_term_1998]
  t2000 := by rw [Interp.termOf, program_term_2000]
  t2001 := by rw [Interp.termOf, program_term_2001]
  t2002 := by rw [Interp.termOf, program_term_2002]
  t2028 := by rw [Interp.termOf, program_term_2028]
  t2029 := by rw [Interp.termOf, program_term_2029]
  t2037 := by rw [Interp.termOf, program_term_2037]
  t2038 := by rw [Interp.termOf, program_term_2038]
  t2039 := by rw [Interp.termOf, program_term_2039]
  t2045 := by rw [Interp.termOf, program_term_2045]
  t2049 := by rw [Interp.termOf, program_term_2049]
  t2236 := by rw [Interp.termOf, program_term_2236]
  t2237 := by rw [Interp.termOf, program_term_2237]
  t2238 := by rw [Interp.termOf, program_term_2238]
  t2239 := by rw [Interp.termOf, program_term_2239]
  t2240 := by rw [Interp.termOf, program_term_2240]
  t2269 := by rw [Interp.termOf, program_term_2269]
  t2270 := by rw [Interp.termOf, program_term_2270]
  t2271 := by rw [Interp.termOf, program_term_2271]
  t2272 := by rw [Interp.termOf, program_term_2272]
  t2273 := by rw [Interp.termOf, program_term_2273]
  t2274 := by rw [Interp.termOf, program_term_2274]
  t2275 := by rw [Interp.termOf, program_term_2275]
  t2276 := by rw [Interp.termOf, program_term_2276]
  t2277 := by rw [Interp.termOf, program_term_2277]
  t2278 := by rw [Interp.termOf, program_term_2278]
  t2341 := by rw [Interp.termOf, program_term_2341]
  t2356 := by rw [Interp.termOf, program_term_2356]
  t2357 := by rw [Interp.termOf, program_term_2357]
  t2372 := by rw [Interp.termOf, program_term_2372]
  t2376 := by rw [Interp.termOf, program_term_2376]
  t2377 := by rw [Interp.termOf, program_term_2377]
  t2388 := by rw [Interp.termOf, program_term_2388]
  t2449 := by rw [Interp.termOf, program_term_2449]
  t2461 := by rw [Interp.termOf, program_term_2461]
  t2482 := by rw [Interp.termOf, program_term_2482]
  lower := program_termByName_lower

/-! ### Enum variant names, `$Type` constants, integer literals -/

@[isel_data] theorem variantNames_152_2 : (variantNames 152)[2]? = some "Binary" := by native_decide
@[isel_data] theorem variantNames_151_73 : (variantNames 151)[73]? = some "Iadd" := by native_decide
@[isel_data] theorem variantNames_152_35 : (variantNames 152)[35]? = some "UnaryImm" := by native_decide
@[isel_data] theorem variantNames_151_57 : (variantNames 151)[57]? = some "Iconst" := by native_decide
@[isel_data] theorem variantNames_152_14 : (variantNames 152)[14]? = some "IntCompare" := by native_decide
@[isel_data] theorem variantNames_151_72 : (variantNames 151)[72]? = some "Icmp" := by native_decide
@[isel_data] theorem variantNames_151_104 : (variantNames 151)[104]? = some "Ushr" := by native_decide
@[isel_data] theorem variantNames_59_16 : (variantNames 59)[16]? = some "Lsr" := by native_decide
@[isel_data] theorem variantNames_59_0 : (variantNames 59)[0]? = some "Add" := by native_decide
@[isel_data] theorem variantNames_123_0 : (variantNames 123)[0]? = some "Zero" := by native_decide
@[isel_data] theorem variantNames_96_0 : (variantNames 96)[0]? = some "Eq" := by native_decide
@[isel_data] theorem variantNames_123_1 : (variantNames 123)[1]? = some "NotZero" := by native_decide
@[isel_data] theorem variantNames_96_1 : (variantNames 96)[1]? = some "Ne" := by native_decide
@[isel_data] theorem variantNames_123_2 : (variantNames 123)[2]? = some "Cond" := by native_decide
@[isel_data] theorem variantNames_123_3 : (variantNames 123)[3]? = some "Or" := by native_decide
@[isel_data] theorem variantNames_123_4 : (variantNames 123)[4]? = some "And" := by native_decide
@[isel_data] theorem variantNames_145_0 : (variantNames 145)[0]? = some "Equal" := by native_decide
@[isel_data] theorem variantNames_145_1 : (variantNames 145)[1]? = some "NotEqual" := by native_decide
@[isel_data] theorem variantNames_145_7 : (variantNames 145)[7]? = some "UnsignedGreaterThanOrEqual" := by native_decide
@[isel_data] theorem variantNames_96_8 : (variantNames 96)[8]? = some "Hi" := by native_decide
@[isel_data] theorem variantNames_145_3 : (variantNames 145)[3]? = some "SignedGreaterThanOrEqual" := by native_decide
@[isel_data] theorem variantNames_96_12 : (variantNames 96)[12]? = some "Gt" := by native_decide
@[isel_data] theorem variantNames_93_0 : (variantNames 93)[0]? = some "Size32" := by native_decide
@[isel_data] theorem variantNames_56_1 : (variantNames 56)[1]? = some "Uext" := by native_decide
@[isel_data] theorem variantNames_56_2 : (variantNames 56)[2]? = some "Sext" := by native_decide
@[isel_data] theorem variantNames_58_2 : (variantNames 58)[2]? = some "AluRRR" := by native_decide
@[isel_data] theorem variantNames_58_4 : (variantNames 58)[4]? = some "AluRRImm12" := by native_decide
@[isel_data] theorem variantNames_47_4 : (variantNames 47)[4]? = some "ProducesFlagsReturnsResultWithConsumer" := by native_decide
@[isel_data] theorem variantNames_49_2 : (variantNames 49)[2]? = some "ConsumesFlagsReturnsResultWithProducer" := by native_decide
@[isel_data] theorem variantNames_49_0 : (variantNames 49)[0]? = some "ConsumesFlagsSideEffect" := by native_decide
@[isel_data] theorem variantNames_49_6 : (variantNames 49)[6]? = some "ConsumesFlagsNop" := by native_decide
@[isel_data] theorem variantNames_47_3 : (variantNames 47)[3]? = some "ProducesFlagsReturnsReg" := by native_decide
@[isel_data] theorem variantNames_47_1 : (variantNames 47)[1]? = some "ProducesFlagsSideEffect" := by native_decide
@[isel_data] theorem variantNames_49_3 : (variantNames 49)[3]? = some "ConsumesFlagsReturnsReg" := by native_decide
@[isel_data] theorem variantNames_47_5 : (variantNames 47)[5]? = some "ProducesFlagsOpportunisticDef" := by native_decide
@[isel_data] theorem variantNames_49_4 : (variantNames 49)[4]? = some "ConsumesFlagsTwiceReturnsValueRegs" := by native_decide
@[isel_data] theorem variantNames_49_5 : (variantNames 49)[5]? = some "ConsumesFlagsFourTimesReturnsValueRegs" := by native_decide
@[isel_data] theorem variantNames_47_6 : (variantNames 47)[6]? = some "ProducesFlagsOpportunisticDef2" := by native_decide
@[isel_data] theorem variantNames_47_2 : (variantNames 47)[2]? = some "ProducesFlagsTwiceSideEffect" := by native_decide
@[isel_data] theorem variantNames_59_10 : (variantNames 59)[10]? = some "SubS" := by native_decide
@[isel_data] theorem variantNames_58_33 : (variantNames 58)[33]? = some "CSet" := by native_decide
@[isel_data] theorem variantNames_49_1 : (variantNames 49)[1]? = some "ConsumesFlagsSideEffect2" := by native_decide
@[isel_data] theorem variantNames_59_2 : (variantNames 59)[2]? = some "Orr" := by native_decide
@[isel_data] theorem variantNames_59_4 : (variantNames 59)[4]? = some "And" := by native_decide
@[isel_data] theorem variantNames_151_93 : (variantNames 151)[93]? = some "SmulOverflow" := by native_decide
@[isel_data] theorem variantNames_93_1 : (variantNames 93)[1]? = some "Size64" := by native_decide
@[isel_data] theorem variantNames_58_3 : (variantNames 58)[3]? = some "AluRRRR" := by native_decide
@[isel_data] theorem variantNames_60_3 : (variantNames 60)[3]? = some "SMAddL" := by native_decide
@[isel_data] theorem variantNames_58_8 : (variantNames 58)[8]? = some "AluRRRExtend" := by native_decide
@[isel_data] theorem variantNames_84_6 : (variantNames 84)[6]? = some "SXTW" := by native_decide
@[isel_data] theorem variantNames_60_0 : (variantNames 60)[0]? = some "MAdd" := by native_decide
@[isel_data] theorem variantNames_151_92 : (variantNames 151)[92]? = some "UmulOverflow" := by native_decide
@[isel_data] theorem variantNames_60_2 : (variantNames 60)[2]? = some "UMAddL" := by native_decide
@[isel_data] theorem variantNames_84_2 : (variantNames 84)[2]? = some "UXTW" := by native_decide
@[isel_data] theorem variantNames_151_88 : (variantNames 151)[88]? = some "UaddOverflow" := by native_decide
@[isel_data] theorem variantNames_59_9 : (variantNames 59)[9]? = some "AddS" := by native_decide
@[isel_data] theorem variantNames_96_2 : (variantNames 96)[2]? = some "Hs" := by native_decide
@[isel_data] theorem variantNames_145_2 : (variantNames 145)[2]? = some "SignedGreaterThan" := by native_decide
@[isel_data] theorem variantNames_145_4 : (variantNames 145)[4]? = some "SignedLessThan" := by native_decide
@[isel_data] theorem variantNames_145_6 : (variantNames 145)[6]? = some "UnsignedGreaterThan" := by native_decide
@[isel_data] theorem variantNames_145_8 : (variantNames 145)[8]? = some "UnsignedLessThan" := by native_decide
@[isel_data] theorem variantNames_145_5 : (variantNames 145)[5]? = some "SignedLessThanOrEqual" := by native_decide
@[isel_data] theorem variantNames_145_9 : (variantNames 145)[9]? = some "UnsignedLessThanOrEqual" := by native_decide
@[isel_data] theorem variantNames_84_4 : (variantNames 84)[4]? = some "SXTB" := by native_decide
@[isel_data] theorem variantNames_84_5 : (variantNames 84)[5]? = some "SXTH" := by native_decide
@[isel_data] theorem variantNames_84_0 : (variantNames 84)[0]? = some "UXTB" := by native_decide
@[isel_data] theorem variantNames_84_1 : (variantNames 84)[1]? = some "UXTH" := by native_decide
@[isel_data] theorem variantNames_58_6 : (variantNames 58)[6]? = some "AluRRImmShift" := by native_decide
@[isel_data] theorem variantNames_58_28 : (variantNames 58)[28]? = some "Extend" := by native_decide
@[isel_data] theorem variantNames_59_11 : (variantNames 59)[11]? = some "SMulH" := by native_decide
@[isel_data] theorem variantNames_58_7 : (variantNames 58)[7]? = some "AluRRRShift" := by native_decide
@[isel_data] theorem variantNames_59_12 : (variantNames 59)[12]? = some "UMulH" := by native_decide
@[isel_data] theorem variantNames_58_5 : (variantNames 58)[5]? = some "AluRRImmLogic" := by native_decide
@[isel_data] theorem variantNames_59_5 : (variantNames 59)[5]? = some "AndS" := by native_decide
@[isel_data] theorem variantNames_59_22 : (variantNames 59)[22]? = some "SbcS" := by native_decide
@[isel_data] theorem variantNames_58_35 : (variantNames 58)[35]? = some "CCmp" := by native_decide
@[isel_data] theorem typeName_14 : program.typeName 14 = "Type" := by native_decide
@[isel_data] theorem normInt_1_0 : normInt 1 (0) = 0 := by native_decide
@[isel_data] theorem normInt_6_0 : normInt 6 (0) = 0 := by native_decide
@[isel_data] theorem normInt_6_1 : normInt 6 (1) = 1 := by native_decide
@[isel_data] theorem normInt_4_0 : normInt 4 (0) = 0 := by native_decide
@[isel_data] theorem normInt_4_1 : normInt 4 (1) = 1 := by native_decide
@[isel_data] theorem normInt_1_32 : normInt 1 (32) = 32 := by native_decide
@[isel_data] theorem normInt_4_63 : normInt 4 (63) = 63 := by native_decide
@[isel_data] theorem normInt_4_255 : normInt 4 (255) = 255 := by native_decide

@[isel_data] theorem tyMInst_eq : tyMInst = 58 := by native_decide
@[isel_data] theorem tyALUOp_eq : tyALUOp = 59 := by native_decide
@[isel_data] theorem tyALUOp3_eq : tyALUOp3 = 60 := by native_decide
@[isel_data] theorem tyOperandSize_eq : tyOperandSize = 93 := by native_decide
@[isel_data] theorem tyCond_eq : tyCond = 96 := by native_decide
@[isel_data] theorem tyExtendOp_eq : tyExtendOp = 84 := by native_decide
@[isel_data] theorem tyAMode_eq : tyAMode = 89 := by native_decide
@[isel_data] theorem tyCondBrKind_eq : tyCondBrKind = 83 := by native_decide
@[isel_data] theorem tyMoveWideOp_eq : tyMoveWideOp = 61 := by native_decide
@[isel_data] theorem tyBfmOp_eq : tyBfmOp = 62 := by native_decide
@[isel_data] theorem tyBitOp_eq : tyBitOp = 85 := by native_decide
@[isel_data] theorem tyScalarSize_eq : tyScalarSize = 95 := by native_decide
@[isel_data] theorem tyIntCC_eq : tyIntCC = 145 := by native_decide
@[isel_data] theorem tyOpcode_eq : tyOpcode = 151 := by native_decide
@[isel_data] theorem tyInstData_eq : tyInstData = 152 := by native_decide

end Backend.Proof
