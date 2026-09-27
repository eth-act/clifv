import FV.Backend
import FV.Backend.Proof.IselAttr

/-!
# ISLE data facts for the isel proofs (generated, do not edit)

Regenerate: `lake env lean --run FVTest/Backend/Proof/Probe/GenData.lean probe > FV/Backend/Proof/IselData.lean`.

Roots: 4 root rules (probe); 156 terms reachable from them (patterns, if-lets,
right-hand sides, and the rules of every internal constructor they call, transitively), of
which the internal constructors have 626 rules. `lower`/`lower_branch` are included with
their full rule lists.

`Data p` bundles `Interp.termOf p t = pure T.x` and `p.rulesOf t = [...]` for these terms.
Rule proofs are stated for an abstract `p` with `Data p`, so the kernel never unfolds the
program while checking them; `data_program : Data program` proves every field by `rfl` (the
exported program is a structure literal over flat tables, `FV/Isle/Generated/*Table.lean`),
and `termByName? "lower"` by kernel `decide`.
-/

namespace Backend.Proof

open Isle Isle.Aarch64

/-! ### Term fields (`rfl`) -/

@[isel_data] theorem term_1_kind : T.«def_inst».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "def_inst" false))) := rfl
@[isel_data] theorem term_1_name : T.«def_inst».name = "def_inst" := rfl
@[isel_data] theorem term_2_kind : T.«value_type».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "value_type" true))) := rfl
@[isel_data] theorem term_2_name : T.«value_type».name = "value_type" := rfl
@[isel_data] theorem term_87_kind : T.«ty_bits».kind = (.decl ⟨true, false, false, false⟩ (some (.external "ty_bits")) none) := rfl
@[isel_data] theorem term_87_name : T.«ty_bits».name = "ty_bits" := rfl
@[isel_data] theorem term_110_kind : T.«fits_in_16».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "fits_in_16" false))) := rfl
@[isel_data] theorem term_110_name : T.«fits_in_16».name = "fits_in_16" := rfl
@[isel_data] theorem term_111_kind : T.«fits_in_32».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "fits_in_32" false))) := rfl
@[isel_data] theorem term_111_name : T.«fits_in_32».name = "fits_in_32" := rfl
@[isel_data] theorem term_113_kind : T.«fits_in_64».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "fits_in_64" false))) := rfl
@[isel_data] theorem term_113_name : T.«fits_in_64».name = "fits_in_64" := rfl
@[isel_data] theorem term_119_kind : T.«ty_int_ref_scalar_64_extract».kind = (.decl ⟨true, false, true, false⟩ none (some (.external "ty_int_ref_scalar_64_extract" false))) := rfl
@[isel_data] theorem term_119_name : T.«ty_int_ref_scalar_64_extract».name = "ty_int_ref_scalar_64_extract" := rfl
@[isel_data] theorem term_120_kind : T.«ty_32_or_64».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "ty_32_or_64" false))) := rfl
@[isel_data] theorem term_120_name : T.«ty_32_or_64».name = "ty_32_or_64" := rfl
@[isel_data] theorem term_126_kind : T.«ty_int».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "ty_int" false))) := rfl
@[isel_data] theorem term_126_name : T.«ty_int».name = "ty_int" := rfl
@[isel_data] theorem term_144_kind : T.«u64_from_imm64».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "u64_from_imm64" true))) := rfl
@[isel_data] theorem term_144_name : T.«u64_from_imm64».name = "u64_from_imm64" := rfl
@[isel_data] theorem term_159_kind : T.«signed_cond_code».kind = (.decl ⟨true, false, true, false⟩ (some (.external "signed_cond_code")) none) := rfl
@[isel_data] theorem term_159_name : T.«signed_cond_code».name = "signed_cond_code" := rfl
@[isel_data] theorem term_160_kind : T.«unsigned_cond_code».kind = (.decl ⟨true, false, true, false⟩ (some (.external "unsigned_cond_code")) none) := rfl
@[isel_data] theorem term_160_name : T.«unsigned_cond_code».name = "unsigned_cond_code" := rfl
@[isel_data] theorem term_164_kind : T.«value_reg».kind = (.decl ⟨false, false, false, false⟩ (some (.external "value_reg")) none) := rfl
@[isel_data] theorem term_164_name : T.«value_reg».name = "value_reg" := rfl
@[isel_data] theorem term_166_kind : T.«value_regs».kind = (.decl ⟨false, false, false, false⟩ (some (.external "value_regs")) none) := rfl
@[isel_data] theorem term_166_name : T.«value_regs».name = "value_regs" := rfl
@[isel_data] theorem term_170_kind : T.«output».kind = (.decl ⟨false, false, false, false⟩ (some (.external "output")) none) := rfl
@[isel_data] theorem term_170_name : T.«output».name = "output" := rfl
@[isel_data] theorem term_172_kind : T.«output_reg».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_172_name : T.«output_reg».name = "output_reg" := rfl
@[isel_data] theorem term_175_kind : T.«temp_writable_reg».kind = (.decl ⟨false, false, false, false⟩ (some (.external "temp_writable_reg")) none) := rfl
@[isel_data] theorem term_175_name : T.«temp_writable_reg».name = "temp_writable_reg" := rfl
@[isel_data] theorem term_181_kind : T.«opportunistic_def».kind = (.decl ⟨false, false, false, false⟩ (some (.external "opportunistic_def")) none) := rfl
@[isel_data] theorem term_181_name : T.«opportunistic_def».name = "opportunistic_def" := rfl
@[isel_data] theorem term_182_kind : T.«put_in_reg».kind = (.decl ⟨false, false, false, false⟩ (some (.external "put_in_reg")) none) := rfl
@[isel_data] theorem term_182_name : T.«put_in_reg».name = "put_in_reg" := rfl
@[isel_data] theorem term_183_kind : T.«put_in_regs».kind = (.decl ⟨false, false, false, false⟩ (some (.external "put_in_regs")) none) := rfl
@[isel_data] theorem term_183_name : T.«put_in_regs».name = "put_in_regs" := rfl
@[isel_data] theorem term_185_kind : T.«value_regs_get».kind = (.decl ⟨false, false, false, false⟩ (some (.external "value_regs_get")) none) := rfl
@[isel_data] theorem term_185_name : T.«value_regs_get».name = "value_regs_get" := rfl
@[isel_data] theorem term_201_kind : T.«writable_reg_to_reg».kind = (.decl ⟨true, false, false, false⟩ (some (.external "writable_reg_to_reg")) none) := rfl
@[isel_data] theorem term_201_name : T.«writable_reg_to_reg».name = "writable_reg_to_reg" := rfl
@[isel_data] theorem term_205_kind : T.«first_result».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "first_result" false))) := rfl
@[isel_data] theorem term_205_name : T.«first_result».name = "first_result" := rfl
@[isel_data] theorem term_207_kind : T.«is_second_result».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "is_second_result" false))) := rfl
@[isel_data] theorem term_207_name : T.«is_second_result».name = "is_second_result" := rfl
@[isel_data] theorem term_209_kind : T.«inst_data_value».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "inst_data_value" true))) := rfl
@[isel_data] theorem term_209_name : T.«inst_data_value».name = "inst_data_value" := rfl
@[isel_data] theorem term_235_kind : T.«emit».kind = (.decl ⟨false, false, false, false⟩ (some (.external "emit")) none) := rfl
@[isel_data] theorem term_235_name : T.«emit».name = "emit" := rfl
@[isel_data] theorem term_246_kind : T.«produces_flags_concat».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_246_name : T.«produces_flags_concat».name = "produces_flags_concat" := rfl
@[isel_data] theorem term_249_kind : T.«produces_flags_opportunistic_def».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_249_name : T.«produces_flags_opportunistic_def».name = "produces_flags_opportunistic_def" := rfl
@[isel_data] theorem term_250_kind : T.«produces_flags_opportunistic_def2».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_250_name : T.«produces_flags_opportunistic_def2».name = "produces_flags_opportunistic_def2" := rfl
@[isel_data] theorem term_251_kind : T.«consumes_flags_concat».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_251_name : T.«consumes_flags_concat».name = "consumes_flags_concat" := rfl
@[isel_data] theorem term_254_kind : T.«with_flags».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_254_name : T.«with_flags».name = "with_flags" := rfl
@[isel_data] theorem term_305_kind : T.«operand_size».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_305_name : T.«operand_size».name = "operand_size" := rfl
@[isel_data] theorem term_323_kind : T.«imm_shift_from_imm64».kind = (.decl ⟨true, false, true, false⟩ (some (.external "imm_shift_from_imm64")) none) := rfl
@[isel_data] theorem term_323_name : T.«imm_shift_from_imm64».name = "imm_shift_from_imm64" := rfl
@[isel_data] theorem term_325_kind : T.«imm12_from_u64».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "imm12_from_u64" false))) := rfl
@[isel_data] theorem term_325_name : T.«imm12_from_u64».name = "imm12_from_u64" := rfl
@[isel_data] theorem term_327_kind : T.«u8_into_imm12».kind = (.decl ⟨false, false, false, false⟩ (some (.external "u8_into_imm12")) none) := rfl
@[isel_data] theorem term_327_name : T.«u8_into_imm12».name = "u8_into_imm12" := rfl
@[isel_data] theorem term_328_kind : T.«u64_into_imm_logic».kind = (.decl ⟨false, false, false, false⟩ (some (.external "u64_into_imm_logic")) none) := rfl
@[isel_data] theorem term_328_name : T.«u64_into_imm_logic».name = "u64_into_imm_logic" := rfl
@[isel_data] theorem term_338_kind : T.«ashr_from_u64».kind = (.decl ⟨true, false, true, false⟩ (some (.external "ashr_from_u64")) none) := rfl
@[isel_data] theorem term_338_name : T.«ashr_from_u64».name = "ashr_from_u64" := rfl
@[isel_data] theorem term_348_kind : T.«nzcv».kind = (.decl ⟨false, false, false, false⟩ (some (.external "nzcv")) none) := rfl
@[isel_data] theorem term_348_name : T.«nzcv».name = "nzcv" := rfl
@[isel_data] theorem term_352_kind : T.«zero_reg».kind = (.decl ⟨false, false, false, false⟩ (some (.external "zero_reg")) none) := rfl
@[isel_data] theorem term_352_name : T.«zero_reg».name = "zero_reg" := rfl
@[isel_data] theorem term_356_kind : T.«writable_zero_reg».kind = (.decl ⟨false, false, false, false⟩ (some (.external "writable_zero_reg")) none) := rfl
@[isel_data] theorem term_356_name : T.«writable_zero_reg».name = "writable_zero_reg" := rfl
@[isel_data] theorem term_360_kind : T.«alu_rr_imm_logic».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_360_name : T.«alu_rr_imm_logic».name = "alu_rr_imm_logic" := rfl
@[isel_data] theorem term_361_kind : T.«alu_rr_imm_shift».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_361_name : T.«alu_rr_imm_shift».name = "alu_rr_imm_shift" := rfl
@[isel_data] theorem term_362_kind : T.«alu_rrr».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_362_name : T.«alu_rrr».name = "alu_rrr" := rfl
@[isel_data] theorem term_376_kind : T.«alu_rr_imm12».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_376_name : T.«alu_rr_imm12».name = "alu_rr_imm12" := rfl
@[isel_data] theorem term_379_kind : T.«cmp_rr_shift_asr».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_379_name : T.«cmp_rr_shift_asr».name = "cmp_rr_shift_asr" := rfl
@[isel_data] theorem term_383_kind : T.«alu_rrr_with_flags_paired».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_383_name : T.«alu_rrr_with_flags_paired».name = "alu_rrr_with_flags_paired" := rfl
@[isel_data] theorem term_385_kind : T.«sbcs_side_effect».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_385_name : T.«sbcs_side_effect».name = "sbcs_side_effect" := rfl
@[isel_data] theorem term_390_kind : T.«cmp».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_390_name : T.«cmp».name = "cmp" := rfl
@[isel_data] theorem term_391_kind : T.«cmp_imm».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_391_name : T.«cmp_imm».name = "cmp_imm" := rfl
@[isel_data] theorem term_392_kind : T.«cmp64_imm».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_392_name : T.«cmp64_imm».name = "cmp64_imm" := rfl
@[isel_data] theorem term_393_kind : T.«cmp_extend».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_393_name : T.«cmp_extend».name = "cmp_extend" := rfl
@[isel_data] theorem term_417_kind : T.«extend».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_417_name : T.«extend».name = "extend" := rfl
@[isel_data] theorem term_424_kind : T.«tst_imm».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_424_name : T.«tst_imm».name = "tst_imm" := rfl
@[isel_data] theorem term_426_kind : T.«cset».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_426_name : T.«cset».name = "cset" := rfl
@[isel_data] theorem term_430_kind : T.«ccmp».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_430_name : T.«ccmp».name = "ccmp" := rfl
@[isel_data] theorem term_432_kind : T.«add».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_432_name : T.«add».name = "add" := rfl
@[isel_data] theorem term_433_kind : T.«add_imm».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_433_name : T.«add_imm».name = "add_imm" := rfl
@[isel_data] theorem term_451_kind : T.«umulh».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_451_name : T.«umulh».name = "umulh" := rfl
@[isel_data] theorem term_452_kind : T.«smulh».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_452_name : T.«smulh».name = "smulh" := rfl
@[isel_data] theorem term_497_kind : T.«orr».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_497_name : T.«orr».name = "orr" := rfl
@[isel_data] theorem term_501_kind : T.«and_reg».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_501_name : T.«and_reg».name = "and_reg" := rfl
@[isel_data] theorem term_502_kind : T.«and_imm».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_502_name : T.«and_imm».name = "and_imm" := rfl
@[isel_data] theorem term_555_kind : T.«put_in_reg_sext32».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_555_name : T.«put_in_reg_sext32».name = "put_in_reg_sext32" := rfl
@[isel_data] theorem term_556_kind : T.«put_in_reg_zext32».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_556_name : T.«put_in_reg_zext32».name = "put_in_reg_zext32" := rfl
@[isel_data] theorem term_592_kind : T.«cond_code».kind = (.decl ⟨false, false, false, false⟩ (some (.external "cond_code")) none) := rfl
@[isel_data] theorem term_592_name : T.«cond_code».name = "cond_code" := rfl
@[isel_data] theorem term_593_kind : T.«invert_cond».kind = (.decl ⟨false, false, false, false⟩ (some (.external "invert_cond")) none) := rfl
@[isel_data] theorem term_593_name : T.«invert_cond».name = "invert_cond" := rfl
@[isel_data] theorem term_649_kind : T.«cond_result_invert».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_649_name : T.«cond_result_invert».name = "cond_result_invert" := rfl
@[isel_data] theorem term_651_kind : T.«is_nonzero».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_651_name : T.«is_nonzero».name = "is_nonzero" := rfl
@[isel_data] theorem term_652_kind : T.«emit_icmp».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_652_name : T.«emit_icmp».name = "emit_icmp" := rfl
@[isel_data] theorem term_653_kind : T.«emit_icmp_i128».kind = (.decl ⟨false, false, false, true⟩ (some .internal) none) := rfl
@[isel_data] theorem term_653_name : T.«emit_icmp_i128».name = "emit_icmp_i128" := rfl
@[isel_data] theorem term_654_kind : T.«emit_icmp_i128_eq_ne».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_654_name : T.«emit_icmp_i128_eq_ne».name = "emit_icmp_i128_eq_ne" := rfl
@[isel_data] theorem term_657_kind : T.«lower_extend_op».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_657_name : T.«lower_extend_op».name = "lower_extend_op" := rfl
@[isel_data] theorem term_686_kind : T.«lower».kind = (.decl ⟨false, false, true, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_686_name : T.«lower».name = "lower" := rfl
@[isel_data] theorem term_687_kind : T.«lower_branch».kind = (.decl ⟨false, false, true, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_687_name : T.«lower_branch».name = "lower_branch" := rfl
@[isel_data] theorem term_703_kind : T.«do_shift».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_703_name : T.«do_shift».name = "do_shift" := rfl
@[isel_data] theorem term_704_kind : T.«shift_mask».kind = (.decl ⟨false, false, false, false⟩ (some (.external "shift_mask")) none) := rfl
@[isel_data] theorem term_704_name : T.«shift_mask».name = "shift_mask" := rfl
@[isel_data] theorem term_715_kind : T.«lower_cond_result_bool».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_715_name : T.«lower_cond_result_bool».name = "lower_cond_result_bool" := rfl
@[isel_data] theorem term_1167_kind : T.«u64_wrapping_sub».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_wrapping_sub")) none) := rfl
@[isel_data] theorem term_1167_name : T.«u64_wrapping_sub».name = "u64_wrapping_sub" := rfl
@[isel_data] theorem term_1199_kind : T.«u64_is_odd».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_is_odd")) none) := rfl
@[isel_data] theorem term_1199_name : T.«u64_is_odd».name = "u64_is_odd" := rfl
@[isel_data] theorem term_1614_kind : T.«value_array_2».kind = (.decl ⟨false, false, false, false⟩ (some (.external "pack_value_array_2")) (some (.external "unpack_value_array_2" true))) := rfl
@[isel_data] theorem term_1614_name : T.«value_array_2».name = "value_array_2" := rfl
@[isel_data] theorem term_1791_kind : T.«ProducesFlags.ProducesFlagsSideEffect».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_1791_name : T.«ProducesFlags.ProducesFlagsSideEffect».name = "ProducesFlags.ProducesFlagsSideEffect" := rfl
@[isel_data] theorem term_1792_kind : T.«ProducesFlags.ProducesFlagsTwiceSideEffect».kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_1792_name : T.«ProducesFlags.ProducesFlagsTwiceSideEffect».name = "ProducesFlags.ProducesFlagsTwiceSideEffect" := rfl
@[isel_data] theorem term_1793_kind : T.«ProducesFlags.ProducesFlagsReturnsReg».kind = (.enumVariant 3) := rfl
@[isel_data] theorem term_1793_name : T.«ProducesFlags.ProducesFlagsReturnsReg».name = "ProducesFlags.ProducesFlagsReturnsReg" := rfl
@[isel_data] theorem term_1794_kind : T.«ProducesFlags.ProducesFlagsReturnsResultWithConsumer».kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_1794_name : T.«ProducesFlags.ProducesFlagsReturnsResultWithConsumer».name = "ProducesFlags.ProducesFlagsReturnsResultWithConsumer" := rfl
@[isel_data] theorem term_1795_kind : T.«ProducesFlags.ProducesFlagsOpportunisticDef».kind = (.enumVariant 5) := rfl
@[isel_data] theorem term_1795_name : T.«ProducesFlags.ProducesFlagsOpportunisticDef».name = "ProducesFlags.ProducesFlagsOpportunisticDef" := rfl
@[isel_data] theorem term_1796_kind : T.«ProducesFlags.ProducesFlagsOpportunisticDef2».kind = (.enumVariant 6) := rfl
@[isel_data] theorem term_1796_name : T.«ProducesFlags.ProducesFlagsOpportunisticDef2».name = "ProducesFlags.ProducesFlagsOpportunisticDef2" := rfl
@[isel_data] theorem term_1799_kind : T.«ConsumesFlags.ConsumesFlagsSideEffect».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_1799_name : T.«ConsumesFlags.ConsumesFlagsSideEffect».name = "ConsumesFlags.ConsumesFlagsSideEffect" := rfl
@[isel_data] theorem term_1800_kind : T.«ConsumesFlags.ConsumesFlagsSideEffect2».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_1800_name : T.«ConsumesFlags.ConsumesFlagsSideEffect2».name = "ConsumesFlags.ConsumesFlagsSideEffect2" := rfl
@[isel_data] theorem term_1801_kind : T.«ConsumesFlags.ConsumesFlagsReturnsResultWithProducer».kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_1801_name : T.«ConsumesFlags.ConsumesFlagsReturnsResultWithProducer».name = "ConsumesFlags.ConsumesFlagsReturnsResultWithProducer" := rfl
@[isel_data] theorem term_1802_kind : T.«ConsumesFlags.ConsumesFlagsReturnsReg».kind = (.enumVariant 3) := rfl
@[isel_data] theorem term_1802_name : T.«ConsumesFlags.ConsumesFlagsReturnsReg».name = "ConsumesFlags.ConsumesFlagsReturnsReg" := rfl
@[isel_data] theorem term_1803_kind : T.«ConsumesFlags.ConsumesFlagsTwiceReturnsValueRegs».kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_1803_name : T.«ConsumesFlags.ConsumesFlagsTwiceReturnsValueRegs».name = "ConsumesFlags.ConsumesFlagsTwiceReturnsValueRegs" := rfl
@[isel_data] theorem term_1804_kind : T.«ConsumesFlags.ConsumesFlagsFourTimesReturnsValueRegs».kind = (.enumVariant 5) := rfl
@[isel_data] theorem term_1804_name : T.«ConsumesFlags.ConsumesFlagsFourTimesReturnsValueRegs».name = "ConsumesFlags.ConsumesFlagsFourTimesReturnsValueRegs" := rfl
@[isel_data] theorem term_1805_kind : T.«ConsumesFlags.ConsumesFlagsNop».kind = (.enumVariant 6) := rfl
@[isel_data] theorem term_1805_name : T.«ConsumesFlags.ConsumesFlagsNop».name = "ConsumesFlags.ConsumesFlagsNop" := rfl
@[isel_data] theorem term_1816_kind : T.«ArgumentExtension.Uext».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_1816_name : T.«ArgumentExtension.Uext».name = "ArgumentExtension.Uext" := rfl
@[isel_data] theorem term_1817_kind : T.«ArgumentExtension.Sext».kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_1817_name : T.«ArgumentExtension.Sext».name = "ArgumentExtension.Sext" := rfl
@[isel_data] theorem term_1820_kind : T.«MInst.AluRRR».kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_1820_name : T.«MInst.AluRRR».name = "MInst.AluRRR" := rfl
@[isel_data] theorem term_1821_kind : T.«MInst.AluRRRR».kind = (.enumVariant 3) := rfl
@[isel_data] theorem term_1821_name : T.«MInst.AluRRRR».name = "MInst.AluRRRR" := rfl
@[isel_data] theorem term_1822_kind : T.«MInst.AluRRImm12».kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_1822_name : T.«MInst.AluRRImm12».name = "MInst.AluRRImm12" := rfl
@[isel_data] theorem term_1823_kind : T.«MInst.AluRRImmLogic».kind = (.enumVariant 5) := rfl
@[isel_data] theorem term_1823_name : T.«MInst.AluRRImmLogic».name = "MInst.AluRRImmLogic" := rfl
@[isel_data] theorem term_1824_kind : T.«MInst.AluRRImmShift».kind = (.enumVariant 6) := rfl
@[isel_data] theorem term_1824_name : T.«MInst.AluRRImmShift».name = "MInst.AluRRImmShift" := rfl
@[isel_data] theorem term_1825_kind : T.«MInst.AluRRRShift».kind = (.enumVariant 7) := rfl
@[isel_data] theorem term_1825_name : T.«MInst.AluRRRShift».name = "MInst.AluRRRShift" := rfl
@[isel_data] theorem term_1826_kind : T.«MInst.AluRRRExtend».kind = (.enumVariant 8) := rfl
@[isel_data] theorem term_1826_name : T.«MInst.AluRRRExtend».name = "MInst.AluRRRExtend" := rfl
@[isel_data] theorem term_1846_kind : T.«MInst.Extend».kind = (.enumVariant 28) := rfl
@[isel_data] theorem term_1846_name : T.«MInst.Extend».name = "MInst.Extend" := rfl
@[isel_data] theorem term_1851_kind : T.«MInst.CSet».kind = (.enumVariant 33) := rfl
@[isel_data] theorem term_1851_name : T.«MInst.CSet».name = "MInst.CSet" := rfl
@[isel_data] theorem term_1853_kind : T.«MInst.CCmp».kind = (.enumVariant 35) := rfl
@[isel_data] theorem term_1853_name : T.«MInst.CCmp».name = "MInst.CCmp" := rfl
@[isel_data] theorem term_1962_kind : T.«ALUOp.Add».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_1962_name : T.«ALUOp.Add».name = "ALUOp.Add" := rfl
@[isel_data] theorem term_1964_kind : T.«ALUOp.Orr».kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_1964_name : T.«ALUOp.Orr».name = "ALUOp.Orr" := rfl
@[isel_data] theorem term_1966_kind : T.«ALUOp.And».kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_1966_name : T.«ALUOp.And».name = "ALUOp.And" := rfl
@[isel_data] theorem term_1967_kind : T.«ALUOp.AndS».kind = (.enumVariant 5) := rfl
@[isel_data] theorem term_1967_name : T.«ALUOp.AndS».name = "ALUOp.AndS" := rfl
@[isel_data] theorem term_1971_kind : T.«ALUOp.AddS».kind = (.enumVariant 9) := rfl
@[isel_data] theorem term_1971_name : T.«ALUOp.AddS».name = "ALUOp.AddS" := rfl
@[isel_data] theorem term_1972_kind : T.«ALUOp.SubS».kind = (.enumVariant 10) := rfl
@[isel_data] theorem term_1972_name : T.«ALUOp.SubS».name = "ALUOp.SubS" := rfl
@[isel_data] theorem term_1973_kind : T.«ALUOp.SMulH».kind = (.enumVariant 11) := rfl
@[isel_data] theorem term_1973_name : T.«ALUOp.SMulH».name = "ALUOp.SMulH" := rfl
@[isel_data] theorem term_1974_kind : T.«ALUOp.UMulH».kind = (.enumVariant 12) := rfl
@[isel_data] theorem term_1974_name : T.«ALUOp.UMulH».name = "ALUOp.UMulH" := rfl
@[isel_data] theorem term_1978_kind : T.«ALUOp.Lsr».kind = (.enumVariant 16) := rfl
@[isel_data] theorem term_1978_name : T.«ALUOp.Lsr».name = "ALUOp.Lsr" := rfl
@[isel_data] theorem term_1984_kind : T.«ALUOp.SbcS».kind = (.enumVariant 22) := rfl
@[isel_data] theorem term_1984_name : T.«ALUOp.SbcS».name = "ALUOp.SbcS" := rfl
@[isel_data] theorem term_1985_kind : T.«ALUOp3.MAdd».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_1985_name : T.«ALUOp3.MAdd».name = "ALUOp3.MAdd" := rfl
@[isel_data] theorem term_1987_kind : T.«ALUOp3.UMAddL».kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_1987_name : T.«ALUOp3.UMAddL».name = "ALUOp3.UMAddL" := rfl
@[isel_data] theorem term_1988_kind : T.«ALUOp3.SMAddL».kind = (.enumVariant 3) := rfl
@[isel_data] theorem term_1988_name : T.«ALUOp3.SMAddL».name = "ALUOp3.SMAddL" := rfl
@[isel_data] theorem term_1996_kind : T.«ExtendOp.UXTB».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_1996_name : T.«ExtendOp.UXTB».name = "ExtendOp.UXTB" := rfl
@[isel_data] theorem term_1997_kind : T.«ExtendOp.UXTH».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_1997_name : T.«ExtendOp.UXTH».name = "ExtendOp.UXTH" := rfl
@[isel_data] theorem term_1998_kind : T.«ExtendOp.UXTW».kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_1998_name : T.«ExtendOp.UXTW».name = "ExtendOp.UXTW" := rfl
@[isel_data] theorem term_2000_kind : T.«ExtendOp.SXTB».kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_2000_name : T.«ExtendOp.SXTB».name = "ExtendOp.SXTB" := rfl
@[isel_data] theorem term_2001_kind : T.«ExtendOp.SXTH».kind = (.enumVariant 5) := rfl
@[isel_data] theorem term_2001_name : T.«ExtendOp.SXTH».name = "ExtendOp.SXTH" := rfl
@[isel_data] theorem term_2002_kind : T.«ExtendOp.SXTW».kind = (.enumVariant 6) := rfl
@[isel_data] theorem term_2002_name : T.«ExtendOp.SXTW».name = "ExtendOp.SXTW" := rfl
@[isel_data] theorem term_2028_kind : T.«OperandSize.Size32».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_2028_name : T.«OperandSize.Size32».name = "OperandSize.Size32" := rfl
@[isel_data] theorem term_2029_kind : T.«OperandSize.Size64».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_2029_name : T.«OperandSize.Size64».name = "OperandSize.Size64" := rfl
@[isel_data] theorem term_2037_kind : T.«Cond.Eq».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_2037_name : T.«Cond.Eq».name = "Cond.Eq" := rfl
@[isel_data] theorem term_2038_kind : T.«Cond.Ne».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_2038_name : T.«Cond.Ne».name = "Cond.Ne" := rfl
@[isel_data] theorem term_2039_kind : T.«Cond.Hs».kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_2039_name : T.«Cond.Hs».name = "Cond.Hs" := rfl
@[isel_data] theorem term_2045_kind : T.«Cond.Hi».kind = (.enumVariant 8) := rfl
@[isel_data] theorem term_2045_name : T.«Cond.Hi».name = "Cond.Hi" := rfl
@[isel_data] theorem term_2049_kind : T.«Cond.Gt».kind = (.enumVariant 12) := rfl
@[isel_data] theorem term_2049_name : T.«Cond.Gt».name = "Cond.Gt" := rfl
@[isel_data] theorem term_2236_kind : T.«CondResult.Zero».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_2236_name : T.«CondResult.Zero».name = "CondResult.Zero" := rfl
@[isel_data] theorem term_2237_kind : T.«CondResult.NotZero».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_2237_name : T.«CondResult.NotZero».name = "CondResult.NotZero" := rfl
@[isel_data] theorem term_2238_kind : T.«CondResult.Cond».kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_2238_name : T.«CondResult.Cond».name = "CondResult.Cond" := rfl
@[isel_data] theorem term_2239_kind : T.«CondResult.Or».kind = (.enumVariant 3) := rfl
@[isel_data] theorem term_2239_name : T.«CondResult.Or».name = "CondResult.Or" := rfl
@[isel_data] theorem term_2240_kind : T.«CondResult.And».kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_2240_name : T.«CondResult.And».name = "CondResult.And" := rfl
@[isel_data] theorem term_2269_kind : T.«IntCC.Equal».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_2269_name : T.«IntCC.Equal».name = "IntCC.Equal" := rfl
@[isel_data] theorem term_2270_kind : T.«IntCC.NotEqual».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_2270_name : T.«IntCC.NotEqual».name = "IntCC.NotEqual" := rfl
@[isel_data] theorem term_2271_kind : T.«IntCC.SignedGreaterThan».kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_2271_name : T.«IntCC.SignedGreaterThan».name = "IntCC.SignedGreaterThan" := rfl
@[isel_data] theorem term_2272_kind : T.«IntCC.SignedGreaterThanOrEqual».kind = (.enumVariant 3) := rfl
@[isel_data] theorem term_2272_name : T.«IntCC.SignedGreaterThanOrEqual».name = "IntCC.SignedGreaterThanOrEqual" := rfl
@[isel_data] theorem term_2273_kind : T.«IntCC.SignedLessThan».kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_2273_name : T.«IntCC.SignedLessThan».name = "IntCC.SignedLessThan" := rfl
@[isel_data] theorem term_2274_kind : T.«IntCC.SignedLessThanOrEqual».kind = (.enumVariant 5) := rfl
@[isel_data] theorem term_2274_name : T.«IntCC.SignedLessThanOrEqual».name = "IntCC.SignedLessThanOrEqual" := rfl
@[isel_data] theorem term_2275_kind : T.«IntCC.UnsignedGreaterThan».kind = (.enumVariant 6) := rfl
@[isel_data] theorem term_2275_name : T.«IntCC.UnsignedGreaterThan».name = "IntCC.UnsignedGreaterThan" := rfl
@[isel_data] theorem term_2276_kind : T.«IntCC.UnsignedGreaterThanOrEqual».kind = (.enumVariant 7) := rfl
@[isel_data] theorem term_2276_name : T.«IntCC.UnsignedGreaterThanOrEqual».name = "IntCC.UnsignedGreaterThanOrEqual" := rfl
@[isel_data] theorem term_2277_kind : T.«IntCC.UnsignedLessThan».kind = (.enumVariant 8) := rfl
@[isel_data] theorem term_2277_name : T.«IntCC.UnsignedLessThan».name = "IntCC.UnsignedLessThan" := rfl
@[isel_data] theorem term_2278_kind : T.«IntCC.UnsignedLessThanOrEqual».kind = (.enumVariant 9) := rfl
@[isel_data] theorem term_2278_name : T.«IntCC.UnsignedLessThanOrEqual».name = "IntCC.UnsignedLessThanOrEqual" := rfl
@[isel_data] theorem term_2341_kind : T.«Opcode.Iconst».kind = (.enumVariant 57) := rfl
@[isel_data] theorem term_2341_name : T.«Opcode.Iconst».name = "Opcode.Iconst" := rfl
@[isel_data] theorem term_2356_kind : T.«Opcode.Icmp».kind = (.enumVariant 72) := rfl
@[isel_data] theorem term_2356_name : T.«Opcode.Icmp».name = "Opcode.Icmp" := rfl
@[isel_data] theorem term_2357_kind : T.«Opcode.Iadd».kind = (.enumVariant 73) := rfl
@[isel_data] theorem term_2357_name : T.«Opcode.Iadd».name = "Opcode.Iadd" := rfl
@[isel_data] theorem term_2372_kind : T.«Opcode.UaddOverflow».kind = (.enumVariant 88) := rfl
@[isel_data] theorem term_2372_name : T.«Opcode.UaddOverflow».name = "Opcode.UaddOverflow" := rfl
@[isel_data] theorem term_2376_kind : T.«Opcode.UmulOverflow».kind = (.enumVariant 92) := rfl
@[isel_data] theorem term_2376_name : T.«Opcode.UmulOverflow».name = "Opcode.UmulOverflow" := rfl
@[isel_data] theorem term_2377_kind : T.«Opcode.SmulOverflow».kind = (.enumVariant 93) := rfl
@[isel_data] theorem term_2377_name : T.«Opcode.SmulOverflow».name = "Opcode.SmulOverflow" := rfl
@[isel_data] theorem term_2388_kind : T.«Opcode.Ushr».kind = (.enumVariant 104) := rfl
@[isel_data] theorem term_2388_name : T.«Opcode.Ushr».name = "Opcode.Ushr" := rfl
@[isel_data] theorem term_2449_kind : T.«InstructionData.Binary».kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_2449_name : T.«InstructionData.Binary».name = "InstructionData.Binary" := rfl
@[isel_data] theorem term_2461_kind : T.«InstructionData.IntCompare».kind = (.enumVariant 14) := rfl
@[isel_data] theorem term_2461_name : T.«InstructionData.IntCompare».name = "InstructionData.IntCompare" := rfl
@[isel_data] theorem term_2482_kind : T.«InstructionData.UnaryImm».kind = (.enumVariant 35) := rfl
@[isel_data] theorem term_2482_name : T.«InstructionData.UnaryImm».name = "InstructionData.UnaryImm" := rfl

/-- The facts about the exported program that the isel proofs use. Proofs are stated for an
arbitrary `p : Program` with `Data p`, never for `Isle.Aarch64.program` itself, so the kernel
cannot unfold the program data while checking them; `data_program` instantiates. -/
structure Data (p : Program) : Prop where
  t1 : Interp.termOf p 1 = pure T.«def_inst»
  t2 : Interp.termOf p 2 = pure T.«value_type»
  t87 : Interp.termOf p 87 = pure T.«ty_bits»
  t110 : Interp.termOf p 110 = pure T.«fits_in_16»
  t111 : Interp.termOf p 111 = pure T.«fits_in_32»
  t113 : Interp.termOf p 113 = pure T.«fits_in_64»
  t119 : Interp.termOf p 119 = pure T.«ty_int_ref_scalar_64_extract»
  t120 : Interp.termOf p 120 = pure T.«ty_32_or_64»
  t126 : Interp.termOf p 126 = pure T.«ty_int»
  t144 : Interp.termOf p 144 = pure T.«u64_from_imm64»
  t159 : Interp.termOf p 159 = pure T.«signed_cond_code»
  t160 : Interp.termOf p 160 = pure T.«unsigned_cond_code»
  t164 : Interp.termOf p 164 = pure T.«value_reg»
  t166 : Interp.termOf p 166 = pure T.«value_regs»
  t170 : Interp.termOf p 170 = pure T.«output»
  t172 : Interp.termOf p 172 = pure T.«output_reg»
  r172 : p.rulesOf 172 =
    [rule_prelude_lower_105]
  t175 : Interp.termOf p 175 = pure T.«temp_writable_reg»
  t181 : Interp.termOf p 181 = pure T.«opportunistic_def»
  t182 : Interp.termOf p 182 = pure T.«put_in_reg»
  t183 : Interp.termOf p 183 = pure T.«put_in_regs»
  t185 : Interp.termOf p 185 = pure T.«value_regs_get»
  t201 : Interp.termOf p 201 = pure T.«writable_reg_to_reg»
  t205 : Interp.termOf p 205 = pure T.«first_result»
  t207 : Interp.termOf p 207 = pure T.«is_second_result»
  t209 : Interp.termOf p 209 = pure T.«inst_data_value»
  t235 : Interp.termOf p 235 = pure T.«emit»
  t246 : Interp.termOf p 246 = pure T.«produces_flags_concat»
  r246 : p.rulesOf 246 =
    [rule_prelude_lower_644]
  t249 : Interp.termOf p 249 = pure T.«produces_flags_opportunistic_def»
  r249 : p.rulesOf 249 =
    [rule_prelude_lower_715]
  t250 : Interp.termOf p 250 = pure T.«produces_flags_opportunistic_def2»
  r250 : p.rulesOf 250 =
    [rule_prelude_lower_725]
  t251 : Interp.termOf p 251 = pure T.«consumes_flags_concat»
  r251 : p.rulesOf 251 =
    [rule_prelude_lower_744, rule_prelude_lower_750]
  t254 : Interp.termOf p 254 = pure T.«with_flags»
  r254 : p.rulesOf 254 =
    [rule_prelude_lower_789, rule_prelude_lower_798, rule_prelude_lower_807, rule_prelude_lower_812, rule_prelude_lower_818, rule_prelude_lower_829, rule_prelude_lower_837, rule_prelude_lower_850, rule_prelude_lower_864, rule_prelude_lower_881, rule_prelude_lower_903, rule_prelude_lower_912, rule_prelude_lower_927, rule_prelude_lower_943, rule_prelude_lower_951, rule_prelude_lower_965]
  t305 : Interp.termOf p 305 = pure T.«operand_size»
  r305 : p.rulesOf 305 =
    [rule_inst_1592, rule_inst_1593]
  t323 : Interp.termOf p 323 = pure T.«imm_shift_from_imm64»
  t325 : Interp.termOf p 325 = pure T.«imm12_from_u64»
  t327 : Interp.termOf p 327 = pure T.«u8_into_imm12»
  t328 : Interp.termOf p 328 = pure T.«u64_into_imm_logic»
  t338 : Interp.termOf p 338 = pure T.«ashr_from_u64»
  t348 : Interp.termOf p 348 = pure T.«nzcv»
  t352 : Interp.termOf p 352 = pure T.«zero_reg»
  t356 : Interp.termOf p 356 = pure T.«writable_zero_reg»
  t360 : Interp.termOf p 360 = pure T.«alu_rr_imm_logic»
  r360 : p.rulesOf 360 =
    [rule_inst_2529]
  t361 : Interp.termOf p 361 = pure T.«alu_rr_imm_shift»
  r361 : p.rulesOf 361 =
    [rule_inst_2537]
  t362 : Interp.termOf p 362 = pure T.«alu_rrr»
  r362 : p.rulesOf 362 =
    [rule_inst_2545]
  t376 : Interp.termOf p 376 = pure T.«alu_rr_imm12»
  r376 : p.rulesOf 376 =
    [rule_inst_2648]
  t379 : Interp.termOf p 379 = pure T.«cmp_rr_shift_asr»
  r379 : p.rulesOf 379 =
    [rule_inst_2675]
  t383 : Interp.termOf p 383 = pure T.«alu_rrr_with_flags_paired»
  r383 : p.rulesOf 383 =
    [rule_inst_2709]
  t385 : Interp.termOf p 385 = pure T.«sbcs_side_effect»
  r385 : p.rulesOf 385 =
    [rule_inst_2726]
  t390 : Interp.termOf p 390 = pure T.«cmp»
  r390 : p.rulesOf 390 =
    [rule_inst_2767]
  t391 : Interp.termOf p 391 = pure T.«cmp_imm»
  r391 : p.rulesOf 391 =
    [rule_inst_2774]
  t392 : Interp.termOf p 392 = pure T.«cmp64_imm»
  r392 : p.rulesOf 392 =
    [rule_inst_2781]
  t393 : Interp.termOf p 393 = pure T.«cmp_extend»
  r393 : p.rulesOf 393 =
    [rule_inst_2786]
  t417 : Interp.termOf p 417 = pure T.«extend»
  r417 : p.rulesOf 417 =
    [rule_inst_2991]
  t424 : Interp.termOf p 424 = pure T.«tst_imm»
  r424 : p.rulesOf 424 =
    [rule_inst_3044]
  t426 : Interp.termOf p 426 = pure T.«cset»
  r426 : p.rulesOf 426 =
    [rule_inst_3068]
  t430 : Interp.termOf p 430 = pure T.«ccmp»
  r430 : p.rulesOf 430 =
    [rule_inst_3103]
  t432 : Interp.termOf p 432 = pure T.«add»
  r432 : p.rulesOf 432 =
    [rule_inst_3118]
  t433 : Interp.termOf p 433 = pure T.«add_imm»
  r433 : p.rulesOf 433 =
    [rule_inst_3122]
  t451 : Interp.termOf p 451 = pure T.«umulh»
  r451 : p.rulesOf 451 =
    [rule_inst_3213]
  t452 : Interp.termOf p 452 = pure T.«smulh»
  r452 : p.rulesOf 452 =
    [rule_inst_3218]
  t497 : Interp.termOf p 497 = pure T.«orr»
  r497 : p.rulesOf 497 =
    [rule_inst_3412]
  t501 : Interp.termOf p 501 = pure T.«and_reg»
  r501 : p.rulesOf 501 =
    [rule_inst_3427]
  t502 : Interp.termOf p 502 = pure T.«and_imm»
  r502 : p.rulesOf 502 =
    [rule_inst_3431]
  t555 : Interp.termOf p 555 = pure T.«put_in_reg_sext32»
  r555 : p.rulesOf 555 =
    [rule_inst_3803, rule_inst_3804, rule_inst_3799]
  t556 : Interp.termOf p 556 = pure T.«put_in_reg_zext32»
  r556 : p.rulesOf 556 =
    [rule_inst_3813, rule_inst_3814, rule_inst_3809]
  t592 : Interp.termOf p 592 = pure T.«cond_code»
  t593 : Interp.termOf p 593 = pure T.«invert_cond»
  t649 : Interp.termOf p 649 = pure T.«cond_result_invert»
  r649 : p.rulesOf 649 =
    [rule_inst_4954, rule_inst_4955, rule_inst_4956, rule_inst_4957, rule_inst_4959]
  t651 : Interp.termOf p 651 = pure T.«is_nonzero»
  r651 : p.rulesOf 651 =
    [rule_inst_5094, rule_inst_5077, rule_inst_5058, rule_inst_5049, rule_inst_5032, rule_inst_5013, rule_inst_4993, rule_inst_4988, rule_inst_4983, rule_inst_4979, rule_inst_4977]
  t652 : Interp.termOf p 652 = pure T.«emit_icmp»
  r652 : p.rulesOf 652 =
    [rule_inst_5171, rule_inst_5173, rule_inst_5170, rule_inst_5172, rule_inst_5165, rule_inst_5155, rule_inst_5160, rule_inst_5142, rule_inst_5134, rule_inst_5128, rule_inst_5117, rule_inst_5108]
  t653 : Interp.termOf p 653 = pure T.«emit_icmp_i128»
  r653 : p.rulesOf 653 =
    [rule_inst_5179, rule_inst_5181, rule_inst_5183, rule_inst_5185, rule_inst_5189, rule_inst_5191, rule_inst_5201]
  t654 : Interp.termOf p 654 = pure T.«emit_icmp_i128_eq_ne»
  r654 : p.rulesOf 654 =
    [rule_inst_5195]
  t657 : Interp.termOf p 657 = pure T.«lower_extend_op»
  r657 : p.rulesOf 657 =
    [rule_inst_5264, rule_inst_5265, rule_inst_5266, rule_inst_5267]
  t686 : Interp.termOf p 686 = pure T.«lower»
  r686 : p.rulesOf 686 =
    [rule_lower_419, rule_lower_402, rule_lower_1444, rule_lower_1481, rule_lower_116, rule_lower_125, rule_lower_1442, rule_lower_1479, rule_lower_2779, rule_lower_120, rule_lower_128, rule_lower_165, rule_lower_1439, rule_lower_1476, rule_lower_2784, rule_lower_93, rule_lower_167, rule_lower_1437, rule_lower_1474, rule_lower_1501, rule_lower_1507, rule_lower_2789, rule_lower_3091, rule_lower_3155, rule_lower_90, rule_lower_169, rule_lower_1435, rule_lower_1472, rule_lower_1540, rule_lower_2152, rule_lower_2793, rule_lower_3097, rule_lower_3161, rule_lower_102, rule_lower_171, rule_lower_1408, rule_lower_1434, rule_lower_1471, rule_lower_1539, rule_lower_2158, rule_lower_2185, rule_lower_2798, rule_lower_2828, rule_lower_3008, rule_lower_3101, rule_lower_3165, rule_lower_98, rule_lower_190, rule_lower_437, rule_lower_609, rule_lower_810, rule_lower_861, rule_lower_1163, rule_lower_1222, rule_lower_1224, rule_lower_1226, rule_lower_1228, rule_lower_1406, rule_lower_1431, rule_lower_1468, rule_lower_1536, rule_lower_2120, rule_lower_2164, rule_lower_2191, rule_lower_2386, rule_lower_2404, rule_lower_2419, rule_lower_2435, rule_lower_2815, rule_lower_3018, rule_lower_3036, rule_lower_3056, rule_lower_3076, rule_lower_3126, rule_lower_3140, rule_lower_3190, rule_lower_3204, rule_lower_111, rule_lower_203, rule_lower_205, rule_lower_207, rule_lower_209, rule_lower_211, rule_lower_213, rule_lower_215, rule_lower_217, rule_lower_222, rule_lower_224, rule_lower_226, rule_lower_228, rule_lower_230, rule_lower_232, rule_lower_240, rule_lower_242, rule_lower_244, rule_lower_246, rule_lower_248, rule_lower_250, rule_lower_260, rule_lower_262, rule_lower_264, rule_lower_266, rule_lower_268, rule_lower_270, rule_lower_294, rule_lower_300, rule_lower_440, rule_lower_608, rule_lower_693, rule_lower_699, rule_lower_707, rule_lower_713, rule_lower_730, rule_lower_733, rule_lower_750, rule_lower_753, rule_lower_767, rule_lower_773, rule_lower_787, rule_lower_793, rule_lower_816, rule_lower_857, rule_lower_1056, rule_lower_1068, rule_lower_1116, rule_lower_1167, rule_lower_1236, rule_lower_1242, rule_lower_1248, rule_lower_1254, rule_lower_1266, rule_lower_1272, rule_lower_1281, rule_lower_1283, rule_lower_1401, rule_lower_1429, rule_lower_1466, rule_lower_1534, rule_lower_1704, rule_lower_1707, rule_lower_1803, rule_lower_1808, rule_lower_2138, rule_lower_2170, rule_lower_2197, rule_lower_2288, rule_lower_2328, rule_lower_2331, rule_lower_2334, rule_lower_2337, rule_lower_2340, rule_lower_2343, rule_lower_2346, rule_lower_2349, rule_lower_2352, rule_lower_2381, rule_lower_2400, rule_lower_2415, rule_lower_2431, rule_lower_2451, rule_lower_2466, rule_lower_2508, rule_lower_2580, rule_lower_2803, rule_lower_2822, rule_lower_2837, rule_lower_3014, rule_lower_3031, rule_lower_3051, rule_lower_3071, rule_lower_3110, rule_lower_3174, rule_lower_53, rule_lower_58, rule_lower_63, rule_lower_68, rule_lower_73, rule_lower_78, rule_lower_108, rule_lower_132, rule_lower_273, rule_lower_279, rule_lower_284, rule_lower_308, rule_lower_313, rule_lower_316, rule_lower_336, rule_lower_342, rule_lower_368, rule_lower_375, rule_lower_379, rule_lower_383, rule_lower_387, rule_lower_450, rule_lower_463, rule_lower_477, rule_lower_485, rule_lower_493, rule_lower_501, rule_lower_509, rule_lower_517, rule_lower_525, rule_lower_533, rule_lower_541, rule_lower_549, rule_lower_554, rule_lower_559, rule_lower_567, rule_lower_570, rule_lower_578, rule_lower_581, rule_lower_589, rule_lower_592, rule_lower_600, rule_lower_603, rule_lower_685, rule_lower_690, rule_lower_696, rule_lower_704, rule_lower_710, rule_lower_724, rule_lower_727, rule_lower_744, rule_lower_747, rule_lower_764, rule_lower_770, rule_lower_784, rule_lower_790, rule_lower_805, rule_lower_836, rule_lower_841, rule_lower_846, rule_lower_851, rule_lower_865, rule_lower_906, rule_lower_914, rule_lower_995, rule_lower_1000, rule_lower_1005, rule_lower_1010, rule_lower_1015, rule_lower_1020, rule_lower_1025, rule_lower_1030, rule_lower_1035, rule_lower_1040, rule_lower_1045, rule_lower_1050, rule_lower_1059, rule_lower_1071, rule_lower_1119, rule_lower_1145, rule_lower_1190, rule_lower_1204, rule_lower_1233, rule_lower_1239, rule_lower_1245, rule_lower_1251, rule_lower_1294, rule_lower_1300, rule_lower_1339, rule_lower_1359, rule_lower_1391, rule_lower_1424, rule_lower_1461, rule_lower_1528, rule_lower_1549, rule_lower_1553, rule_lower_1642, rule_lower_1646, rule_lower_1699, rule_lower_1720, rule_lower_1791, rule_lower_1797, rule_lower_1827, rule_lower_1857, rule_lower_1862, rule_lower_1916, rule_lower_1931, rule_lower_1937, rule_lower_1940, rule_lower_1951, rule_lower_1955, rule_lower_1958, rule_lower_1982, rule_lower_1986, rule_lower_1989, rule_lower_2000, rule_lower_2004, rule_lower_2016, rule_lower_2035, rule_lower_2038, rule_lower_2041, rule_lower_2044, rule_lower_2052, rule_lower_2074, rule_lower_2080, rule_lower_2086, rule_lower_2092, rule_lower_2099, rule_lower_2108, rule_lower_2113, rule_lower_2146, rule_lower_2176, rule_lower_2203, rule_lower_2237, rule_lower_2242, rule_lower_2262, rule_lower_2267, rule_lower_2280, rule_lower_2285, rule_lower_2301, rule_lower_2304, rule_lower_2307, rule_lower_2310, rule_lower_2316, rule_lower_2321, rule_lower_2357, rule_lower_2359, rule_lower_2361, rule_lower_2363, rule_lower_2365, rule_lower_2367, rule_lower_2369, rule_lower_2371, rule_lower_2373, rule_lower_2375, rule_lower_2377, rule_lower_2390, rule_lower_2395, rule_lower_2408, rule_lower_2423, rule_lower_2439, rule_lower_2446, rule_lower_2454, rule_lower_2461, rule_lower_2469, rule_lower_2476, rule_lower_2481, rule_lower_2486, rule_lower_2491, rule_lower_2496, rule_lower_2499, rule_lower_2502, rule_lower_2518, rule_lower_2529, rule_lower_2574, rule_lower_2587, rule_lower_2595, rule_lower_2604, rule_lower_2607, rule_lower_2610, rule_lower_2613, rule_lower_2619, rule_lower_2647, rule_lower_2650, rule_lower_2653, rule_lower_2656, rule_lower_2659, rule_lower_2662, rule_lower_2666, rule_lower_2672, rule_lower_2678, rule_lower_2684, rule_lower_2690, rule_lower_2696, rule_lower_2705, rule_lower_2709, rule_lower_2713, rule_lower_2717, rule_lower_2722, rule_lower_2726, rule_lower_2730, rule_lower_2735, rule_lower_2770, rule_lower_2773, rule_lower_2809, rule_lower_2818, rule_lower_2842, rule_lower_2849, rule_lower_2863, rule_lower_2887, rule_lower_2900, rule_lower_2913, rule_lower_2927, rule_lower_3022, rule_lower_3042, rule_lower_3062, rule_lower_3082, rule_lower_3217, rule_lower_3220, rule_lower_3225, rule_lower_3286, rule_lower_3292, rule_lower_dynamic_neon_81, rule_lower_dynamic_neon_87, rule_lower_86, rule_lower_319, rule_lower_359, rule_lower_390, rule_lower_434, rule_lower_472, rule_lower_482, rule_lower_490, rule_lower_498, rule_lower_506, rule_lower_514, rule_lower_522, rule_lower_530, rule_lower_538, rule_lower_546, rule_lower_564, rule_lower_575, rule_lower_586, rule_lower_597, rule_lower_718, rule_lower_721, rule_lower_738, rule_lower_741, rule_lower_758, rule_lower_761, rule_lower_778, rule_lower_781, rule_lower_831, rule_lower_876, rule_lower_956, rule_lower_1153, rule_lower_1197, rule_lower_1211, rule_lower_1289, rule_lower_1349, rule_lower_1387, rule_lower_1421, rule_lower_1458, rule_lower_1525, rule_lower_1545, rule_lower_1638, rule_lower_1736, rule_lower_1778, rule_lower_1844, rule_lower_1848, rule_lower_1946, rule_lower_1961, rule_lower_1995, rule_lower_2030, rule_lower_2179, rule_lower_2209, rule_lower_2294, rule_lower_2622, rule_lower_2742, rule_lower_dynamic_neon_43, rule_lower_dynamic_neon_57, rule_lower_dynamic_neon_71, rule_lower_dynamic_neon_92, rule_lower_dynamic_neon_97, rule_lower_137, rule_lower_322, rule_lower_826, rule_lower_924, rule_lower_1261, rule_lower_1329, rule_lower_1385, rule_lower_1419, rule_lower_1456, rule_lower_1523, rule_lower_1588, rule_lower_1661, rule_lower_1734, rule_lower_1772, rule_lower_1852, rule_lower_2215, rule_lower_2298, rule_lower_2625, rule_lower_2746, rule_lower_dynamic_neon_15, rule_lower_dynamic_neon_19, rule_lower_dynamic_neon_23, rule_lower_dynamic_neon_27, rule_lower_dynamic_neon_31, rule_lower_dynamic_neon_35, rule_lower_dynamic_neon_39, rule_lower_dynamic_neon_53, rule_lower_dynamic_neon_67, rule_lower_142, rule_lower_821, rule_lower_871, rule_lower_1320, rule_lower_1381, rule_lower_1452, rule_lower_1519, rule_lower_1583, rule_lower_1659, rule_lower_1729, rule_lower_1840, rule_lower_2628, rule_lower_2750, rule_lower_dynamic_neon_47, rule_lower_dynamic_neon_61, rule_lower_dynamic_neon_75, rule_lower_801, rule_lower_1315, rule_lower_1377, rule_lower_1415, rule_lower_1449, rule_lower_1516, rule_lower_1654, rule_lower_1695, rule_lower_2633, rule_lower_2754, rule_lower_dynamic_neon_3, rule_lower_dynamic_neon_11, rule_lower_1412, rule_lower_2638, rule_lower_2759, rule_lower_dynamic_neon_7, rule_lower_2643, rule_lower_2763]
  t687 : Interp.termOf p 687 = pure T.«lower_branch»
  r687 : p.rulesOf 687 =
    [rule_lower_2542, rule_lower_3251, rule_lower_3257, rule_lower_2551, rule_lower_2561, rule_lower_3231, rule_lower_3270, rule_lower_3277]
  t703 : Interp.termOf p 703 = pure T.«do_shift»
  r703 : p.rulesOf 703 =
    [rule_lower_1631, rule_lower_1622, rule_lower_1623, rule_lower_1612]
  t704 : Interp.termOf p 704 = pure T.«shift_mask»
  t715 : Interp.termOf p 715 = pure T.«lower_cond_result_bool»
  r715 : p.rulesOf 715 =
    [rule_lower_2222, rule_lower_2224, rule_lower_2226, rule_lower_2228, rule_lower_2231]
  t1167 : Interp.termOf p 1167 = pure T.«u64_wrapping_sub»
  t1199 : Interp.termOf p 1199 = pure T.«u64_is_odd»
  t1614 : Interp.termOf p 1614 = pure T.«value_array_2»
  t1791 : Interp.termOf p 1791 = pure T.«ProducesFlags.ProducesFlagsSideEffect»
  t1792 : Interp.termOf p 1792 = pure T.«ProducesFlags.ProducesFlagsTwiceSideEffect»
  t1793 : Interp.termOf p 1793 = pure T.«ProducesFlags.ProducesFlagsReturnsReg»
  t1794 : Interp.termOf p 1794 = pure T.«ProducesFlags.ProducesFlagsReturnsResultWithConsumer»
  t1795 : Interp.termOf p 1795 = pure T.«ProducesFlags.ProducesFlagsOpportunisticDef»
  t1796 : Interp.termOf p 1796 = pure T.«ProducesFlags.ProducesFlagsOpportunisticDef2»
  t1799 : Interp.termOf p 1799 = pure T.«ConsumesFlags.ConsumesFlagsSideEffect»
  t1800 : Interp.termOf p 1800 = pure T.«ConsumesFlags.ConsumesFlagsSideEffect2»
  t1801 : Interp.termOf p 1801 = pure T.«ConsumesFlags.ConsumesFlagsReturnsResultWithProducer»
  t1802 : Interp.termOf p 1802 = pure T.«ConsumesFlags.ConsumesFlagsReturnsReg»
  t1803 : Interp.termOf p 1803 = pure T.«ConsumesFlags.ConsumesFlagsTwiceReturnsValueRegs»
  t1804 : Interp.termOf p 1804 = pure T.«ConsumesFlags.ConsumesFlagsFourTimesReturnsValueRegs»
  t1805 : Interp.termOf p 1805 = pure T.«ConsumesFlags.ConsumesFlagsNop»
  t1816 : Interp.termOf p 1816 = pure T.«ArgumentExtension.Uext»
  t1817 : Interp.termOf p 1817 = pure T.«ArgumentExtension.Sext»
  t1820 : Interp.termOf p 1820 = pure T.«MInst.AluRRR»
  t1821 : Interp.termOf p 1821 = pure T.«MInst.AluRRRR»
  t1822 : Interp.termOf p 1822 = pure T.«MInst.AluRRImm12»
  t1823 : Interp.termOf p 1823 = pure T.«MInst.AluRRImmLogic»
  t1824 : Interp.termOf p 1824 = pure T.«MInst.AluRRImmShift»
  t1825 : Interp.termOf p 1825 = pure T.«MInst.AluRRRShift»
  t1826 : Interp.termOf p 1826 = pure T.«MInst.AluRRRExtend»
  t1846 : Interp.termOf p 1846 = pure T.«MInst.Extend»
  t1851 : Interp.termOf p 1851 = pure T.«MInst.CSet»
  t1853 : Interp.termOf p 1853 = pure T.«MInst.CCmp»
  t1962 : Interp.termOf p 1962 = pure T.«ALUOp.Add»
  t1964 : Interp.termOf p 1964 = pure T.«ALUOp.Orr»
  t1966 : Interp.termOf p 1966 = pure T.«ALUOp.And»
  t1967 : Interp.termOf p 1967 = pure T.«ALUOp.AndS»
  t1971 : Interp.termOf p 1971 = pure T.«ALUOp.AddS»
  t1972 : Interp.termOf p 1972 = pure T.«ALUOp.SubS»
  t1973 : Interp.termOf p 1973 = pure T.«ALUOp.SMulH»
  t1974 : Interp.termOf p 1974 = pure T.«ALUOp.UMulH»
  t1978 : Interp.termOf p 1978 = pure T.«ALUOp.Lsr»
  t1984 : Interp.termOf p 1984 = pure T.«ALUOp.SbcS»
  t1985 : Interp.termOf p 1985 = pure T.«ALUOp3.MAdd»
  t1987 : Interp.termOf p 1987 = pure T.«ALUOp3.UMAddL»
  t1988 : Interp.termOf p 1988 = pure T.«ALUOp3.SMAddL»
  t1996 : Interp.termOf p 1996 = pure T.«ExtendOp.UXTB»
  t1997 : Interp.termOf p 1997 = pure T.«ExtendOp.UXTH»
  t1998 : Interp.termOf p 1998 = pure T.«ExtendOp.UXTW»
  t2000 : Interp.termOf p 2000 = pure T.«ExtendOp.SXTB»
  t2001 : Interp.termOf p 2001 = pure T.«ExtendOp.SXTH»
  t2002 : Interp.termOf p 2002 = pure T.«ExtendOp.SXTW»
  t2028 : Interp.termOf p 2028 = pure T.«OperandSize.Size32»
  t2029 : Interp.termOf p 2029 = pure T.«OperandSize.Size64»
  t2037 : Interp.termOf p 2037 = pure T.«Cond.Eq»
  t2038 : Interp.termOf p 2038 = pure T.«Cond.Ne»
  t2039 : Interp.termOf p 2039 = pure T.«Cond.Hs»
  t2045 : Interp.termOf p 2045 = pure T.«Cond.Hi»
  t2049 : Interp.termOf p 2049 = pure T.«Cond.Gt»
  t2236 : Interp.termOf p 2236 = pure T.«CondResult.Zero»
  t2237 : Interp.termOf p 2237 = pure T.«CondResult.NotZero»
  t2238 : Interp.termOf p 2238 = pure T.«CondResult.Cond»
  t2239 : Interp.termOf p 2239 = pure T.«CondResult.Or»
  t2240 : Interp.termOf p 2240 = pure T.«CondResult.And»
  t2269 : Interp.termOf p 2269 = pure T.«IntCC.Equal»
  t2270 : Interp.termOf p 2270 = pure T.«IntCC.NotEqual»
  t2271 : Interp.termOf p 2271 = pure T.«IntCC.SignedGreaterThan»
  t2272 : Interp.termOf p 2272 = pure T.«IntCC.SignedGreaterThanOrEqual»
  t2273 : Interp.termOf p 2273 = pure T.«IntCC.SignedLessThan»
  t2274 : Interp.termOf p 2274 = pure T.«IntCC.SignedLessThanOrEqual»
  t2275 : Interp.termOf p 2275 = pure T.«IntCC.UnsignedGreaterThan»
  t2276 : Interp.termOf p 2276 = pure T.«IntCC.UnsignedGreaterThanOrEqual»
  t2277 : Interp.termOf p 2277 = pure T.«IntCC.UnsignedLessThan»
  t2278 : Interp.termOf p 2278 = pure T.«IntCC.UnsignedLessThanOrEqual»
  t2341 : Interp.termOf p 2341 = pure T.«Opcode.Iconst»
  t2356 : Interp.termOf p 2356 = pure T.«Opcode.Icmp»
  t2357 : Interp.termOf p 2357 = pure T.«Opcode.Iadd»
  t2372 : Interp.termOf p 2372 = pure T.«Opcode.UaddOverflow»
  t2376 : Interp.termOf p 2376 = pure T.«Opcode.UmulOverflow»
  t2377 : Interp.termOf p 2377 = pure T.«Opcode.SmulOverflow»
  t2388 : Interp.termOf p 2388 = pure T.«Opcode.Ushr»
  t2449 : Interp.termOf p 2449 = pure T.«InstructionData.Binary»
  t2461 : Interp.termOf p 2461 = pure T.«InstructionData.IntCompare»
  t2482 : Interp.termOf p 2482 = pure T.«InstructionData.UnaryImm»
  lower : p.termByName? "lower" = some T.lower

/-! ### The facts for `program` (each `rfl`: indexing the flat tables, up to ~2500 deep in
`Meta.whnf`; one declaration each, so each has its own heartbeat budget) -/

set_option maxRecDepth 20000

theorem program_term_1 : Interp.termOf program 1 = pure T.«def_inst» := rfl
theorem program_term_2 : Interp.termOf program 2 = pure T.«value_type» := rfl
theorem program_term_87 : Interp.termOf program 87 = pure T.«ty_bits» := rfl
theorem program_term_110 : Interp.termOf program 110 = pure T.«fits_in_16» := rfl
theorem program_term_111 : Interp.termOf program 111 = pure T.«fits_in_32» := rfl
theorem program_term_113 : Interp.termOf program 113 = pure T.«fits_in_64» := rfl
theorem program_term_119 : Interp.termOf program 119 = pure T.«ty_int_ref_scalar_64_extract» := rfl
theorem program_term_120 : Interp.termOf program 120 = pure T.«ty_32_or_64» := rfl
theorem program_term_126 : Interp.termOf program 126 = pure T.«ty_int» := rfl
theorem program_term_144 : Interp.termOf program 144 = pure T.«u64_from_imm64» := rfl
theorem program_term_159 : Interp.termOf program 159 = pure T.«signed_cond_code» := rfl
theorem program_term_160 : Interp.termOf program 160 = pure T.«unsigned_cond_code» := rfl
theorem program_term_164 : Interp.termOf program 164 = pure T.«value_reg» := rfl
theorem program_term_166 : Interp.termOf program 166 = pure T.«value_regs» := rfl
theorem program_term_170 : Interp.termOf program 170 = pure T.«output» := rfl
theorem program_term_172 : Interp.termOf program 172 = pure T.«output_reg» := rfl
theorem program_rulesOf_172 : program.rulesOf 172 =
    [rule_prelude_lower_105] := rfl
theorem program_term_175 : Interp.termOf program 175 = pure T.«temp_writable_reg» := rfl
theorem program_term_181 : Interp.termOf program 181 = pure T.«opportunistic_def» := rfl
theorem program_term_182 : Interp.termOf program 182 = pure T.«put_in_reg» := rfl
theorem program_term_183 : Interp.termOf program 183 = pure T.«put_in_regs» := rfl
theorem program_term_185 : Interp.termOf program 185 = pure T.«value_regs_get» := rfl
theorem program_term_201 : Interp.termOf program 201 = pure T.«writable_reg_to_reg» := rfl
theorem program_term_205 : Interp.termOf program 205 = pure T.«first_result» := rfl
theorem program_term_207 : Interp.termOf program 207 = pure T.«is_second_result» := rfl
theorem program_term_209 : Interp.termOf program 209 = pure T.«inst_data_value» := rfl
theorem program_term_235 : Interp.termOf program 235 = pure T.«emit» := rfl
theorem program_term_246 : Interp.termOf program 246 = pure T.«produces_flags_concat» := rfl
theorem program_rulesOf_246 : program.rulesOf 246 =
    [rule_prelude_lower_644] := rfl
theorem program_term_249 : Interp.termOf program 249 = pure T.«produces_flags_opportunistic_def» := rfl
theorem program_rulesOf_249 : program.rulesOf 249 =
    [rule_prelude_lower_715] := rfl
theorem program_term_250 : Interp.termOf program 250 = pure T.«produces_flags_opportunistic_def2» := rfl
theorem program_rulesOf_250 : program.rulesOf 250 =
    [rule_prelude_lower_725] := rfl
theorem program_term_251 : Interp.termOf program 251 = pure T.«consumes_flags_concat» := rfl
theorem program_rulesOf_251 : program.rulesOf 251 =
    [rule_prelude_lower_744, rule_prelude_lower_750] := rfl
theorem program_term_254 : Interp.termOf program 254 = pure T.«with_flags» := rfl
theorem program_rulesOf_254 : program.rulesOf 254 =
    [rule_prelude_lower_789, rule_prelude_lower_798, rule_prelude_lower_807, rule_prelude_lower_812, rule_prelude_lower_818, rule_prelude_lower_829, rule_prelude_lower_837, rule_prelude_lower_850, rule_prelude_lower_864, rule_prelude_lower_881, rule_prelude_lower_903, rule_prelude_lower_912, rule_prelude_lower_927, rule_prelude_lower_943, rule_prelude_lower_951, rule_prelude_lower_965] := rfl
theorem program_term_305 : Interp.termOf program 305 = pure T.«operand_size» := rfl
theorem program_rulesOf_305 : program.rulesOf 305 =
    [rule_inst_1592, rule_inst_1593] := rfl
theorem program_term_323 : Interp.termOf program 323 = pure T.«imm_shift_from_imm64» := rfl
theorem program_term_325 : Interp.termOf program 325 = pure T.«imm12_from_u64» := rfl
theorem program_term_327 : Interp.termOf program 327 = pure T.«u8_into_imm12» := rfl
theorem program_term_328 : Interp.termOf program 328 = pure T.«u64_into_imm_logic» := rfl
theorem program_term_338 : Interp.termOf program 338 = pure T.«ashr_from_u64» := rfl
theorem program_term_348 : Interp.termOf program 348 = pure T.«nzcv» := rfl
theorem program_term_352 : Interp.termOf program 352 = pure T.«zero_reg» := rfl
theorem program_term_356 : Interp.termOf program 356 = pure T.«writable_zero_reg» := rfl
theorem program_term_360 : Interp.termOf program 360 = pure T.«alu_rr_imm_logic» := rfl
theorem program_rulesOf_360 : program.rulesOf 360 =
    [rule_inst_2529] := rfl
theorem program_term_361 : Interp.termOf program 361 = pure T.«alu_rr_imm_shift» := rfl
theorem program_rulesOf_361 : program.rulesOf 361 =
    [rule_inst_2537] := rfl
theorem program_term_362 : Interp.termOf program 362 = pure T.«alu_rrr» := rfl
theorem program_rulesOf_362 : program.rulesOf 362 =
    [rule_inst_2545] := rfl
theorem program_term_376 : Interp.termOf program 376 = pure T.«alu_rr_imm12» := rfl
theorem program_rulesOf_376 : program.rulesOf 376 =
    [rule_inst_2648] := rfl
theorem program_term_379 : Interp.termOf program 379 = pure T.«cmp_rr_shift_asr» := rfl
theorem program_rulesOf_379 : program.rulesOf 379 =
    [rule_inst_2675] := rfl
theorem program_term_383 : Interp.termOf program 383 = pure T.«alu_rrr_with_flags_paired» := rfl
theorem program_rulesOf_383 : program.rulesOf 383 =
    [rule_inst_2709] := rfl
theorem program_term_385 : Interp.termOf program 385 = pure T.«sbcs_side_effect» := rfl
theorem program_rulesOf_385 : program.rulesOf 385 =
    [rule_inst_2726] := rfl
theorem program_term_390 : Interp.termOf program 390 = pure T.«cmp» := rfl
theorem program_rulesOf_390 : program.rulesOf 390 =
    [rule_inst_2767] := rfl
theorem program_term_391 : Interp.termOf program 391 = pure T.«cmp_imm» := rfl
theorem program_rulesOf_391 : program.rulesOf 391 =
    [rule_inst_2774] := rfl
theorem program_term_392 : Interp.termOf program 392 = pure T.«cmp64_imm» := rfl
theorem program_rulesOf_392 : program.rulesOf 392 =
    [rule_inst_2781] := rfl
theorem program_term_393 : Interp.termOf program 393 = pure T.«cmp_extend» := rfl
theorem program_rulesOf_393 : program.rulesOf 393 =
    [rule_inst_2786] := rfl
theorem program_term_417 : Interp.termOf program 417 = pure T.«extend» := rfl
theorem program_rulesOf_417 : program.rulesOf 417 =
    [rule_inst_2991] := rfl
theorem program_term_424 : Interp.termOf program 424 = pure T.«tst_imm» := rfl
theorem program_rulesOf_424 : program.rulesOf 424 =
    [rule_inst_3044] := rfl
theorem program_term_426 : Interp.termOf program 426 = pure T.«cset» := rfl
theorem program_rulesOf_426 : program.rulesOf 426 =
    [rule_inst_3068] := rfl
theorem program_term_430 : Interp.termOf program 430 = pure T.«ccmp» := rfl
theorem program_rulesOf_430 : program.rulesOf 430 =
    [rule_inst_3103] := rfl
theorem program_term_432 : Interp.termOf program 432 = pure T.«add» := rfl
theorem program_rulesOf_432 : program.rulesOf 432 =
    [rule_inst_3118] := rfl
theorem program_term_433 : Interp.termOf program 433 = pure T.«add_imm» := rfl
theorem program_rulesOf_433 : program.rulesOf 433 =
    [rule_inst_3122] := rfl
theorem program_term_451 : Interp.termOf program 451 = pure T.«umulh» := rfl
theorem program_rulesOf_451 : program.rulesOf 451 =
    [rule_inst_3213] := rfl
theorem program_term_452 : Interp.termOf program 452 = pure T.«smulh» := rfl
theorem program_rulesOf_452 : program.rulesOf 452 =
    [rule_inst_3218] := rfl
theorem program_term_497 : Interp.termOf program 497 = pure T.«orr» := rfl
theorem program_rulesOf_497 : program.rulesOf 497 =
    [rule_inst_3412] := rfl
theorem program_term_501 : Interp.termOf program 501 = pure T.«and_reg» := rfl
theorem program_rulesOf_501 : program.rulesOf 501 =
    [rule_inst_3427] := rfl
theorem program_term_502 : Interp.termOf program 502 = pure T.«and_imm» := rfl
theorem program_rulesOf_502 : program.rulesOf 502 =
    [rule_inst_3431] := rfl
theorem program_term_555 : Interp.termOf program 555 = pure T.«put_in_reg_sext32» := rfl
theorem program_rulesOf_555 : program.rulesOf 555 =
    [rule_inst_3803, rule_inst_3804, rule_inst_3799] := rfl
theorem program_term_556 : Interp.termOf program 556 = pure T.«put_in_reg_zext32» := rfl
theorem program_rulesOf_556 : program.rulesOf 556 =
    [rule_inst_3813, rule_inst_3814, rule_inst_3809] := rfl
theorem program_term_592 : Interp.termOf program 592 = pure T.«cond_code» := rfl
theorem program_term_593 : Interp.termOf program 593 = pure T.«invert_cond» := rfl
theorem program_term_649 : Interp.termOf program 649 = pure T.«cond_result_invert» := rfl
theorem program_rulesOf_649 : program.rulesOf 649 =
    [rule_inst_4954, rule_inst_4955, rule_inst_4956, rule_inst_4957, rule_inst_4959] := rfl
theorem program_term_651 : Interp.termOf program 651 = pure T.«is_nonzero» := rfl
theorem program_rulesOf_651 : program.rulesOf 651 =
    [rule_inst_5094, rule_inst_5077, rule_inst_5058, rule_inst_5049, rule_inst_5032, rule_inst_5013, rule_inst_4993, rule_inst_4988, rule_inst_4983, rule_inst_4979, rule_inst_4977] := rfl
theorem program_term_652 : Interp.termOf program 652 = pure T.«emit_icmp» := rfl
theorem program_rulesOf_652 : program.rulesOf 652 =
    [rule_inst_5171, rule_inst_5173, rule_inst_5170, rule_inst_5172, rule_inst_5165, rule_inst_5155, rule_inst_5160, rule_inst_5142, rule_inst_5134, rule_inst_5128, rule_inst_5117, rule_inst_5108] := rfl
theorem program_term_653 : Interp.termOf program 653 = pure T.«emit_icmp_i128» := rfl
theorem program_rulesOf_653 : program.rulesOf 653 =
    [rule_inst_5179, rule_inst_5181, rule_inst_5183, rule_inst_5185, rule_inst_5189, rule_inst_5191, rule_inst_5201] := rfl
theorem program_term_654 : Interp.termOf program 654 = pure T.«emit_icmp_i128_eq_ne» := rfl
theorem program_rulesOf_654 : program.rulesOf 654 =
    [rule_inst_5195] := rfl
theorem program_term_657 : Interp.termOf program 657 = pure T.«lower_extend_op» := rfl
theorem program_rulesOf_657 : program.rulesOf 657 =
    [rule_inst_5264, rule_inst_5265, rule_inst_5266, rule_inst_5267] := rfl
theorem program_term_686 : Interp.termOf program 686 = pure T.«lower» := rfl
theorem program_rulesOf_686 : program.rulesOf 686 =
    [rule_lower_419, rule_lower_402, rule_lower_1444, rule_lower_1481, rule_lower_116, rule_lower_125, rule_lower_1442, rule_lower_1479, rule_lower_2779, rule_lower_120, rule_lower_128, rule_lower_165, rule_lower_1439, rule_lower_1476, rule_lower_2784, rule_lower_93, rule_lower_167, rule_lower_1437, rule_lower_1474, rule_lower_1501, rule_lower_1507, rule_lower_2789, rule_lower_3091, rule_lower_3155, rule_lower_90, rule_lower_169, rule_lower_1435, rule_lower_1472, rule_lower_1540, rule_lower_2152, rule_lower_2793, rule_lower_3097, rule_lower_3161, rule_lower_102, rule_lower_171, rule_lower_1408, rule_lower_1434, rule_lower_1471, rule_lower_1539, rule_lower_2158, rule_lower_2185, rule_lower_2798, rule_lower_2828, rule_lower_3008, rule_lower_3101, rule_lower_3165, rule_lower_98, rule_lower_190, rule_lower_437, rule_lower_609, rule_lower_810, rule_lower_861, rule_lower_1163, rule_lower_1222, rule_lower_1224, rule_lower_1226, rule_lower_1228, rule_lower_1406, rule_lower_1431, rule_lower_1468, rule_lower_1536, rule_lower_2120, rule_lower_2164, rule_lower_2191, rule_lower_2386, rule_lower_2404, rule_lower_2419, rule_lower_2435, rule_lower_2815, rule_lower_3018, rule_lower_3036, rule_lower_3056, rule_lower_3076, rule_lower_3126, rule_lower_3140, rule_lower_3190, rule_lower_3204, rule_lower_111, rule_lower_203, rule_lower_205, rule_lower_207, rule_lower_209, rule_lower_211, rule_lower_213, rule_lower_215, rule_lower_217, rule_lower_222, rule_lower_224, rule_lower_226, rule_lower_228, rule_lower_230, rule_lower_232, rule_lower_240, rule_lower_242, rule_lower_244, rule_lower_246, rule_lower_248, rule_lower_250, rule_lower_260, rule_lower_262, rule_lower_264, rule_lower_266, rule_lower_268, rule_lower_270, rule_lower_294, rule_lower_300, rule_lower_440, rule_lower_608, rule_lower_693, rule_lower_699, rule_lower_707, rule_lower_713, rule_lower_730, rule_lower_733, rule_lower_750, rule_lower_753, rule_lower_767, rule_lower_773, rule_lower_787, rule_lower_793, rule_lower_816, rule_lower_857, rule_lower_1056, rule_lower_1068, rule_lower_1116, rule_lower_1167, rule_lower_1236, rule_lower_1242, rule_lower_1248, rule_lower_1254, rule_lower_1266, rule_lower_1272, rule_lower_1281, rule_lower_1283, rule_lower_1401, rule_lower_1429, rule_lower_1466, rule_lower_1534, rule_lower_1704, rule_lower_1707, rule_lower_1803, rule_lower_1808, rule_lower_2138, rule_lower_2170, rule_lower_2197, rule_lower_2288, rule_lower_2328, rule_lower_2331, rule_lower_2334, rule_lower_2337, rule_lower_2340, rule_lower_2343, rule_lower_2346, rule_lower_2349, rule_lower_2352, rule_lower_2381, rule_lower_2400, rule_lower_2415, rule_lower_2431, rule_lower_2451, rule_lower_2466, rule_lower_2508, rule_lower_2580, rule_lower_2803, rule_lower_2822, rule_lower_2837, rule_lower_3014, rule_lower_3031, rule_lower_3051, rule_lower_3071, rule_lower_3110, rule_lower_3174, rule_lower_53, rule_lower_58, rule_lower_63, rule_lower_68, rule_lower_73, rule_lower_78, rule_lower_108, rule_lower_132, rule_lower_273, rule_lower_279, rule_lower_284, rule_lower_308, rule_lower_313, rule_lower_316, rule_lower_336, rule_lower_342, rule_lower_368, rule_lower_375, rule_lower_379, rule_lower_383, rule_lower_387, rule_lower_450, rule_lower_463, rule_lower_477, rule_lower_485, rule_lower_493, rule_lower_501, rule_lower_509, rule_lower_517, rule_lower_525, rule_lower_533, rule_lower_541, rule_lower_549, rule_lower_554, rule_lower_559, rule_lower_567, rule_lower_570, rule_lower_578, rule_lower_581, rule_lower_589, rule_lower_592, rule_lower_600, rule_lower_603, rule_lower_685, rule_lower_690, rule_lower_696, rule_lower_704, rule_lower_710, rule_lower_724, rule_lower_727, rule_lower_744, rule_lower_747, rule_lower_764, rule_lower_770, rule_lower_784, rule_lower_790, rule_lower_805, rule_lower_836, rule_lower_841, rule_lower_846, rule_lower_851, rule_lower_865, rule_lower_906, rule_lower_914, rule_lower_995, rule_lower_1000, rule_lower_1005, rule_lower_1010, rule_lower_1015, rule_lower_1020, rule_lower_1025, rule_lower_1030, rule_lower_1035, rule_lower_1040, rule_lower_1045, rule_lower_1050, rule_lower_1059, rule_lower_1071, rule_lower_1119, rule_lower_1145, rule_lower_1190, rule_lower_1204, rule_lower_1233, rule_lower_1239, rule_lower_1245, rule_lower_1251, rule_lower_1294, rule_lower_1300, rule_lower_1339, rule_lower_1359, rule_lower_1391, rule_lower_1424, rule_lower_1461, rule_lower_1528, rule_lower_1549, rule_lower_1553, rule_lower_1642, rule_lower_1646, rule_lower_1699, rule_lower_1720, rule_lower_1791, rule_lower_1797, rule_lower_1827, rule_lower_1857, rule_lower_1862, rule_lower_1916, rule_lower_1931, rule_lower_1937, rule_lower_1940, rule_lower_1951, rule_lower_1955, rule_lower_1958, rule_lower_1982, rule_lower_1986, rule_lower_1989, rule_lower_2000, rule_lower_2004, rule_lower_2016, rule_lower_2035, rule_lower_2038, rule_lower_2041, rule_lower_2044, rule_lower_2052, rule_lower_2074, rule_lower_2080, rule_lower_2086, rule_lower_2092, rule_lower_2099, rule_lower_2108, rule_lower_2113, rule_lower_2146, rule_lower_2176, rule_lower_2203, rule_lower_2237, rule_lower_2242, rule_lower_2262, rule_lower_2267, rule_lower_2280, rule_lower_2285, rule_lower_2301, rule_lower_2304, rule_lower_2307, rule_lower_2310, rule_lower_2316, rule_lower_2321, rule_lower_2357, rule_lower_2359, rule_lower_2361, rule_lower_2363, rule_lower_2365, rule_lower_2367, rule_lower_2369, rule_lower_2371, rule_lower_2373, rule_lower_2375, rule_lower_2377, rule_lower_2390, rule_lower_2395, rule_lower_2408, rule_lower_2423, rule_lower_2439, rule_lower_2446, rule_lower_2454, rule_lower_2461, rule_lower_2469, rule_lower_2476, rule_lower_2481, rule_lower_2486, rule_lower_2491, rule_lower_2496, rule_lower_2499, rule_lower_2502, rule_lower_2518, rule_lower_2529, rule_lower_2574, rule_lower_2587, rule_lower_2595, rule_lower_2604, rule_lower_2607, rule_lower_2610, rule_lower_2613, rule_lower_2619, rule_lower_2647, rule_lower_2650, rule_lower_2653, rule_lower_2656, rule_lower_2659, rule_lower_2662, rule_lower_2666, rule_lower_2672, rule_lower_2678, rule_lower_2684, rule_lower_2690, rule_lower_2696, rule_lower_2705, rule_lower_2709, rule_lower_2713, rule_lower_2717, rule_lower_2722, rule_lower_2726, rule_lower_2730, rule_lower_2735, rule_lower_2770, rule_lower_2773, rule_lower_2809, rule_lower_2818, rule_lower_2842, rule_lower_2849, rule_lower_2863, rule_lower_2887, rule_lower_2900, rule_lower_2913, rule_lower_2927, rule_lower_3022, rule_lower_3042, rule_lower_3062, rule_lower_3082, rule_lower_3217, rule_lower_3220, rule_lower_3225, rule_lower_3286, rule_lower_3292, rule_lower_dynamic_neon_81, rule_lower_dynamic_neon_87, rule_lower_86, rule_lower_319, rule_lower_359, rule_lower_390, rule_lower_434, rule_lower_472, rule_lower_482, rule_lower_490, rule_lower_498, rule_lower_506, rule_lower_514, rule_lower_522, rule_lower_530, rule_lower_538, rule_lower_546, rule_lower_564, rule_lower_575, rule_lower_586, rule_lower_597, rule_lower_718, rule_lower_721, rule_lower_738, rule_lower_741, rule_lower_758, rule_lower_761, rule_lower_778, rule_lower_781, rule_lower_831, rule_lower_876, rule_lower_956, rule_lower_1153, rule_lower_1197, rule_lower_1211, rule_lower_1289, rule_lower_1349, rule_lower_1387, rule_lower_1421, rule_lower_1458, rule_lower_1525, rule_lower_1545, rule_lower_1638, rule_lower_1736, rule_lower_1778, rule_lower_1844, rule_lower_1848, rule_lower_1946, rule_lower_1961, rule_lower_1995, rule_lower_2030, rule_lower_2179, rule_lower_2209, rule_lower_2294, rule_lower_2622, rule_lower_2742, rule_lower_dynamic_neon_43, rule_lower_dynamic_neon_57, rule_lower_dynamic_neon_71, rule_lower_dynamic_neon_92, rule_lower_dynamic_neon_97, rule_lower_137, rule_lower_322, rule_lower_826, rule_lower_924, rule_lower_1261, rule_lower_1329, rule_lower_1385, rule_lower_1419, rule_lower_1456, rule_lower_1523, rule_lower_1588, rule_lower_1661, rule_lower_1734, rule_lower_1772, rule_lower_1852, rule_lower_2215, rule_lower_2298, rule_lower_2625, rule_lower_2746, rule_lower_dynamic_neon_15, rule_lower_dynamic_neon_19, rule_lower_dynamic_neon_23, rule_lower_dynamic_neon_27, rule_lower_dynamic_neon_31, rule_lower_dynamic_neon_35, rule_lower_dynamic_neon_39, rule_lower_dynamic_neon_53, rule_lower_dynamic_neon_67, rule_lower_142, rule_lower_821, rule_lower_871, rule_lower_1320, rule_lower_1381, rule_lower_1452, rule_lower_1519, rule_lower_1583, rule_lower_1659, rule_lower_1729, rule_lower_1840, rule_lower_2628, rule_lower_2750, rule_lower_dynamic_neon_47, rule_lower_dynamic_neon_61, rule_lower_dynamic_neon_75, rule_lower_801, rule_lower_1315, rule_lower_1377, rule_lower_1415, rule_lower_1449, rule_lower_1516, rule_lower_1654, rule_lower_1695, rule_lower_2633, rule_lower_2754, rule_lower_dynamic_neon_3, rule_lower_dynamic_neon_11, rule_lower_1412, rule_lower_2638, rule_lower_2759, rule_lower_dynamic_neon_7, rule_lower_2643, rule_lower_2763] := rfl
theorem program_term_687 : Interp.termOf program 687 = pure T.«lower_branch» := rfl
theorem program_rulesOf_687 : program.rulesOf 687 =
    [rule_lower_2542, rule_lower_3251, rule_lower_3257, rule_lower_2551, rule_lower_2561, rule_lower_3231, rule_lower_3270, rule_lower_3277] := rfl
theorem program_term_703 : Interp.termOf program 703 = pure T.«do_shift» := rfl
theorem program_rulesOf_703 : program.rulesOf 703 =
    [rule_lower_1631, rule_lower_1622, rule_lower_1623, rule_lower_1612] := rfl
theorem program_term_704 : Interp.termOf program 704 = pure T.«shift_mask» := rfl
theorem program_term_715 : Interp.termOf program 715 = pure T.«lower_cond_result_bool» := rfl
theorem program_rulesOf_715 : program.rulesOf 715 =
    [rule_lower_2222, rule_lower_2224, rule_lower_2226, rule_lower_2228, rule_lower_2231] := rfl
theorem program_term_1167 : Interp.termOf program 1167 = pure T.«u64_wrapping_sub» := rfl
theorem program_term_1199 : Interp.termOf program 1199 = pure T.«u64_is_odd» := rfl
theorem program_term_1614 : Interp.termOf program 1614 = pure T.«value_array_2» := rfl
theorem program_term_1791 : Interp.termOf program 1791 = pure T.«ProducesFlags.ProducesFlagsSideEffect» := rfl
theorem program_term_1792 : Interp.termOf program 1792 = pure T.«ProducesFlags.ProducesFlagsTwiceSideEffect» := rfl
theorem program_term_1793 : Interp.termOf program 1793 = pure T.«ProducesFlags.ProducesFlagsReturnsReg» := rfl
theorem program_term_1794 : Interp.termOf program 1794 = pure T.«ProducesFlags.ProducesFlagsReturnsResultWithConsumer» := rfl
theorem program_term_1795 : Interp.termOf program 1795 = pure T.«ProducesFlags.ProducesFlagsOpportunisticDef» := rfl
theorem program_term_1796 : Interp.termOf program 1796 = pure T.«ProducesFlags.ProducesFlagsOpportunisticDef2» := rfl
theorem program_term_1799 : Interp.termOf program 1799 = pure T.«ConsumesFlags.ConsumesFlagsSideEffect» := rfl
theorem program_term_1800 : Interp.termOf program 1800 = pure T.«ConsumesFlags.ConsumesFlagsSideEffect2» := rfl
theorem program_term_1801 : Interp.termOf program 1801 = pure T.«ConsumesFlags.ConsumesFlagsReturnsResultWithProducer» := rfl
theorem program_term_1802 : Interp.termOf program 1802 = pure T.«ConsumesFlags.ConsumesFlagsReturnsReg» := rfl
theorem program_term_1803 : Interp.termOf program 1803 = pure T.«ConsumesFlags.ConsumesFlagsTwiceReturnsValueRegs» := rfl
theorem program_term_1804 : Interp.termOf program 1804 = pure T.«ConsumesFlags.ConsumesFlagsFourTimesReturnsValueRegs» := rfl
theorem program_term_1805 : Interp.termOf program 1805 = pure T.«ConsumesFlags.ConsumesFlagsNop» := rfl
theorem program_term_1816 : Interp.termOf program 1816 = pure T.«ArgumentExtension.Uext» := rfl
theorem program_term_1817 : Interp.termOf program 1817 = pure T.«ArgumentExtension.Sext» := rfl
theorem program_term_1820 : Interp.termOf program 1820 = pure T.«MInst.AluRRR» := rfl
theorem program_term_1821 : Interp.termOf program 1821 = pure T.«MInst.AluRRRR» := rfl
theorem program_term_1822 : Interp.termOf program 1822 = pure T.«MInst.AluRRImm12» := rfl
theorem program_term_1823 : Interp.termOf program 1823 = pure T.«MInst.AluRRImmLogic» := rfl
theorem program_term_1824 : Interp.termOf program 1824 = pure T.«MInst.AluRRImmShift» := rfl
theorem program_term_1825 : Interp.termOf program 1825 = pure T.«MInst.AluRRRShift» := rfl
theorem program_term_1826 : Interp.termOf program 1826 = pure T.«MInst.AluRRRExtend» := rfl
theorem program_term_1846 : Interp.termOf program 1846 = pure T.«MInst.Extend» := rfl
theorem program_term_1851 : Interp.termOf program 1851 = pure T.«MInst.CSet» := rfl
theorem program_term_1853 : Interp.termOf program 1853 = pure T.«MInst.CCmp» := rfl
theorem program_term_1962 : Interp.termOf program 1962 = pure T.«ALUOp.Add» := rfl
theorem program_term_1964 : Interp.termOf program 1964 = pure T.«ALUOp.Orr» := rfl
theorem program_term_1966 : Interp.termOf program 1966 = pure T.«ALUOp.And» := rfl
theorem program_term_1967 : Interp.termOf program 1967 = pure T.«ALUOp.AndS» := rfl
theorem program_term_1971 : Interp.termOf program 1971 = pure T.«ALUOp.AddS» := rfl
theorem program_term_1972 : Interp.termOf program 1972 = pure T.«ALUOp.SubS» := rfl
theorem program_term_1973 : Interp.termOf program 1973 = pure T.«ALUOp.SMulH» := rfl
theorem program_term_1974 : Interp.termOf program 1974 = pure T.«ALUOp.UMulH» := rfl
theorem program_term_1978 : Interp.termOf program 1978 = pure T.«ALUOp.Lsr» := rfl
theorem program_term_1984 : Interp.termOf program 1984 = pure T.«ALUOp.SbcS» := rfl
theorem program_term_1985 : Interp.termOf program 1985 = pure T.«ALUOp3.MAdd» := rfl
theorem program_term_1987 : Interp.termOf program 1987 = pure T.«ALUOp3.UMAddL» := rfl
theorem program_term_1988 : Interp.termOf program 1988 = pure T.«ALUOp3.SMAddL» := rfl
theorem program_term_1996 : Interp.termOf program 1996 = pure T.«ExtendOp.UXTB» := rfl
theorem program_term_1997 : Interp.termOf program 1997 = pure T.«ExtendOp.UXTH» := rfl
theorem program_term_1998 : Interp.termOf program 1998 = pure T.«ExtendOp.UXTW» := rfl
theorem program_term_2000 : Interp.termOf program 2000 = pure T.«ExtendOp.SXTB» := rfl
theorem program_term_2001 : Interp.termOf program 2001 = pure T.«ExtendOp.SXTH» := rfl
theorem program_term_2002 : Interp.termOf program 2002 = pure T.«ExtendOp.SXTW» := rfl
theorem program_term_2028 : Interp.termOf program 2028 = pure T.«OperandSize.Size32» := rfl
theorem program_term_2029 : Interp.termOf program 2029 = pure T.«OperandSize.Size64» := rfl
theorem program_term_2037 : Interp.termOf program 2037 = pure T.«Cond.Eq» := rfl
theorem program_term_2038 : Interp.termOf program 2038 = pure T.«Cond.Ne» := rfl
theorem program_term_2039 : Interp.termOf program 2039 = pure T.«Cond.Hs» := rfl
theorem program_term_2045 : Interp.termOf program 2045 = pure T.«Cond.Hi» := rfl
theorem program_term_2049 : Interp.termOf program 2049 = pure T.«Cond.Gt» := rfl
theorem program_term_2236 : Interp.termOf program 2236 = pure T.«CondResult.Zero» := rfl
theorem program_term_2237 : Interp.termOf program 2237 = pure T.«CondResult.NotZero» := rfl
theorem program_term_2238 : Interp.termOf program 2238 = pure T.«CondResult.Cond» := rfl
theorem program_term_2239 : Interp.termOf program 2239 = pure T.«CondResult.Or» := rfl
theorem program_term_2240 : Interp.termOf program 2240 = pure T.«CondResult.And» := rfl
theorem program_term_2269 : Interp.termOf program 2269 = pure T.«IntCC.Equal» := rfl
theorem program_term_2270 : Interp.termOf program 2270 = pure T.«IntCC.NotEqual» := rfl
theorem program_term_2271 : Interp.termOf program 2271 = pure T.«IntCC.SignedGreaterThan» := rfl
theorem program_term_2272 : Interp.termOf program 2272 = pure T.«IntCC.SignedGreaterThanOrEqual» := rfl
theorem program_term_2273 : Interp.termOf program 2273 = pure T.«IntCC.SignedLessThan» := rfl
theorem program_term_2274 : Interp.termOf program 2274 = pure T.«IntCC.SignedLessThanOrEqual» := rfl
theorem program_term_2275 : Interp.termOf program 2275 = pure T.«IntCC.UnsignedGreaterThan» := rfl
theorem program_term_2276 : Interp.termOf program 2276 = pure T.«IntCC.UnsignedGreaterThanOrEqual» := rfl
theorem program_term_2277 : Interp.termOf program 2277 = pure T.«IntCC.UnsignedLessThan» := rfl
theorem program_term_2278 : Interp.termOf program 2278 = pure T.«IntCC.UnsignedLessThanOrEqual» := rfl
theorem program_term_2341 : Interp.termOf program 2341 = pure T.«Opcode.Iconst» := rfl
theorem program_term_2356 : Interp.termOf program 2356 = pure T.«Opcode.Icmp» := rfl
theorem program_term_2357 : Interp.termOf program 2357 = pure T.«Opcode.Iadd» := rfl
theorem program_term_2372 : Interp.termOf program 2372 = pure T.«Opcode.UaddOverflow» := rfl
theorem program_term_2376 : Interp.termOf program 2376 = pure T.«Opcode.UmulOverflow» := rfl
theorem program_term_2377 : Interp.termOf program 2377 = pure T.«Opcode.SmulOverflow» := rfl
theorem program_term_2388 : Interp.termOf program 2388 = pure T.«Opcode.Ushr» := rfl
theorem program_term_2449 : Interp.termOf program 2449 = pure T.«InstructionData.Binary» := rfl
theorem program_term_2461 : Interp.termOf program 2461 = pure T.«InstructionData.IntCompare» := rfl
theorem program_term_2482 : Interp.termOf program 2482 = pure T.«InstructionData.UnaryImm» := rfl

theorem program_termByName_lower : program.termByName? "lower" = some T.lower := by
  decide +kernel

theorem data_program : Data program where
  t1 := program_term_1
  t2 := program_term_2
  t87 := program_term_87
  t110 := program_term_110
  t111 := program_term_111
  t113 := program_term_113
  t119 := program_term_119
  t120 := program_term_120
  t126 := program_term_126
  t144 := program_term_144
  t159 := program_term_159
  t160 := program_term_160
  t164 := program_term_164
  t166 := program_term_166
  t170 := program_term_170
  t172 := program_term_172
  r172 := program_rulesOf_172
  t175 := program_term_175
  t181 := program_term_181
  t182 := program_term_182
  t183 := program_term_183
  t185 := program_term_185
  t201 := program_term_201
  t205 := program_term_205
  t207 := program_term_207
  t209 := program_term_209
  t235 := program_term_235
  t246 := program_term_246
  r246 := program_rulesOf_246
  t249 := program_term_249
  r249 := program_rulesOf_249
  t250 := program_term_250
  r250 := program_rulesOf_250
  t251 := program_term_251
  r251 := program_rulesOf_251
  t254 := program_term_254
  r254 := program_rulesOf_254
  t305 := program_term_305
  r305 := program_rulesOf_305
  t323 := program_term_323
  t325 := program_term_325
  t327 := program_term_327
  t328 := program_term_328
  t338 := program_term_338
  t348 := program_term_348
  t352 := program_term_352
  t356 := program_term_356
  t360 := program_term_360
  r360 := program_rulesOf_360
  t361 := program_term_361
  r361 := program_rulesOf_361
  t362 := program_term_362
  r362 := program_rulesOf_362
  t376 := program_term_376
  r376 := program_rulesOf_376
  t379 := program_term_379
  r379 := program_rulesOf_379
  t383 := program_term_383
  r383 := program_rulesOf_383
  t385 := program_term_385
  r385 := program_rulesOf_385
  t390 := program_term_390
  r390 := program_rulesOf_390
  t391 := program_term_391
  r391 := program_rulesOf_391
  t392 := program_term_392
  r392 := program_rulesOf_392
  t393 := program_term_393
  r393 := program_rulesOf_393
  t417 := program_term_417
  r417 := program_rulesOf_417
  t424 := program_term_424
  r424 := program_rulesOf_424
  t426 := program_term_426
  r426 := program_rulesOf_426
  t430 := program_term_430
  r430 := program_rulesOf_430
  t432 := program_term_432
  r432 := program_rulesOf_432
  t433 := program_term_433
  r433 := program_rulesOf_433
  t451 := program_term_451
  r451 := program_rulesOf_451
  t452 := program_term_452
  r452 := program_rulesOf_452
  t497 := program_term_497
  r497 := program_rulesOf_497
  t501 := program_term_501
  r501 := program_rulesOf_501
  t502 := program_term_502
  r502 := program_rulesOf_502
  t555 := program_term_555
  r555 := program_rulesOf_555
  t556 := program_term_556
  r556 := program_rulesOf_556
  t592 := program_term_592
  t593 := program_term_593
  t649 := program_term_649
  r649 := program_rulesOf_649
  t651 := program_term_651
  r651 := program_rulesOf_651
  t652 := program_term_652
  r652 := program_rulesOf_652
  t653 := program_term_653
  r653 := program_rulesOf_653
  t654 := program_term_654
  r654 := program_rulesOf_654
  t657 := program_term_657
  r657 := program_rulesOf_657
  t686 := program_term_686
  r686 := program_rulesOf_686
  t687 := program_term_687
  r687 := program_rulesOf_687
  t703 := program_term_703
  r703 := program_rulesOf_703
  t704 := program_term_704
  t715 := program_term_715
  r715 := program_rulesOf_715
  t1167 := program_term_1167
  t1199 := program_term_1199
  t1614 := program_term_1614
  t1791 := program_term_1791
  t1792 := program_term_1792
  t1793 := program_term_1793
  t1794 := program_term_1794
  t1795 := program_term_1795
  t1796 := program_term_1796
  t1799 := program_term_1799
  t1800 := program_term_1800
  t1801 := program_term_1801
  t1802 := program_term_1802
  t1803 := program_term_1803
  t1804 := program_term_1804
  t1805 := program_term_1805
  t1816 := program_term_1816
  t1817 := program_term_1817
  t1820 := program_term_1820
  t1821 := program_term_1821
  t1822 := program_term_1822
  t1823 := program_term_1823
  t1824 := program_term_1824
  t1825 := program_term_1825
  t1826 := program_term_1826
  t1846 := program_term_1846
  t1851 := program_term_1851
  t1853 := program_term_1853
  t1962 := program_term_1962
  t1964 := program_term_1964
  t1966 := program_term_1966
  t1967 := program_term_1967
  t1971 := program_term_1971
  t1972 := program_term_1972
  t1973 := program_term_1973
  t1974 := program_term_1974
  t1978 := program_term_1978
  t1984 := program_term_1984
  t1985 := program_term_1985
  t1987 := program_term_1987
  t1988 := program_term_1988
  t1996 := program_term_1996
  t1997 := program_term_1997
  t1998 := program_term_1998
  t2000 := program_term_2000
  t2001 := program_term_2001
  t2002 := program_term_2002
  t2028 := program_term_2028
  t2029 := program_term_2029
  t2037 := program_term_2037
  t2038 := program_term_2038
  t2039 := program_term_2039
  t2045 := program_term_2045
  t2049 := program_term_2049
  t2236 := program_term_2236
  t2237 := program_term_2237
  t2238 := program_term_2238
  t2239 := program_term_2239
  t2240 := program_term_2240
  t2269 := program_term_2269
  t2270 := program_term_2270
  t2271 := program_term_2271
  t2272 := program_term_2272
  t2273 := program_term_2273
  t2274 := program_term_2274
  t2275 := program_term_2275
  t2276 := program_term_2276
  t2277 := program_term_2277
  t2278 := program_term_2278
  t2341 := program_term_2341
  t2356 := program_term_2356
  t2357 := program_term_2357
  t2372 := program_term_2372
  t2376 := program_term_2376
  t2377 := program_term_2377
  t2388 := program_term_2388
  t2449 := program_term_2449
  t2461 := program_term_2461
  t2482 := program_term_2482
  lower := program_termByName_lower

/-! ### Integer literals (`normInt`), type ids -/

@[isel_data] theorem normInt_1_32 : normInt 1 (32) = 32 := rfl
@[isel_data] theorem normInt_4_63 : normInt 4 (63) = 63 := rfl
@[isel_data] theorem normInt_1_0 : normInt 1 (0) = 0 := rfl
@[isel_data] theorem normInt_4_255 : normInt 4 (255) = 255 := rfl
@[isel_data] theorem normInt_6_0 : normInt 6 (0) = 0 := rfl
@[isel_data] theorem normInt_6_1 : normInt 6 (1) = 1 := rfl
@[isel_data] theorem normInt_4_0 : normInt 4 (0) = 0 := rfl
@[isel_data] theorem normInt_4_1 : normInt 4 (1) = 1 := rfl
@[isel_data] theorem normInt_1_1 : normInt 1 (1) = 1 := rfl
@[isel_data] theorem normInt_5_40022753436544980677706866553451184640 : normInt 5 (40022753436544980677706866553451184640) = 40022753436544980677706866553451184640 := rfl
@[isel_data] theorem normInt_5_41357194091136896220700492464948314881 : normInt 5 (41357194091136896220700492464948314881) = 41357194091136896220700492464948314881 := rfl
@[isel_data] theorem normInt_5_38693505158040971420872748913983226112 : normInt 5 (38693505158040971420872748913983226112) = 38693505158040971420872748913983226112 := rfl
@[isel_data] theorem normInt_5_41362386467224802506860000736977486594 : normInt 5 (41362386467224802506860000736977486594) = 41362386467224802506860000736977486594 := rfl
@[isel_data] theorem normInt_5_36024664572132682148381476266902159616 : normInt 5 (36024664572132682148381476266902159616) = 36024664572132682148381476266902159616 := rfl
@[isel_data] theorem normInt_5_41362427190500344320355979912890680580 : normInt 5 (41362427190500344320355979912890680580) = 41362427190500344320355979912890680580 := rfl
@[isel_data] theorem normInt_5_30686901955007814682223719185998020864 : normInt 5 (30686901955007814682223719185998020864) = 30686901955007814682223719185998020864 := rfl
@[isel_data] theorem normInt_5_41362427191743139026172726477975062792 : normInt 5 (41362427191743139026172726477975062792) = 41362427191743139026172726477975062792 := rfl
@[isel_data] theorem normInt_5_30609036675948388650355540050116153344 : normInt 5 (30609036675948388650355540050116153344) = 30609036675948388650355540050116153344 := rfl
@[isel_data] theorem normInt_5_41284561912683712994304547342093195272 : normInt 5 (41284561912683712994304547342093195272) = 41284561912683712994304547342093195272 := rfl
@[isel_data] theorem normInt_5_30686616892700419341528320311204774144 : normInt 5 (30686616892700419341528320311204774144) = 30686616892700419341528320311204774144 := rfl
@[isel_data] theorem normInt_5_41362142129435743685477327603181816072 : normInt 5 (41362142129435743685477327603181816072) = 41362142129435743685477327603181816072 := rfl
@[isel_data] theorem normInt_5_30686901951279430565641561564801794304 : normInt 5 (30686901951279430565641561564801794304) = 30686901951279430565641561564801794304 := rfl
@[isel_data] theorem normInt_5_41362427188014754909590568856778836232 : normInt 5 (41362427188014754909590568856778836232) = 41362427188014754909590568856778836232 := rfl
@[isel_data] theorem normInt_5_39950100895832629191365197868744970240 : normInt 5 (39950100895832629191365197868744970240) = 39950100895832629191365197868744970240 := rfl
@[isel_data] theorem normInt_5_41284541550424544734358823780242100481 : normInt 5 (41284541550424544734358823780242100481) = 41284541550424544734358823780242100481 := rfl
@[isel_data] theorem normInt_5_38693260819630515246292341806293057792 : normInt 5 (38693260819630515246292341806293057792) = 38693260819630515246292341806293057792 := rfl
@[isel_data] theorem normInt_5_41362142128814346332279593629287318274 : normInt 5 (41362142128814346332279593629287318274) = 41362142128814346332279593629287318274 := rfl
@[isel_data] theorem normInt_5_36024664569647092737326704519438008576 : normInt 5 (36024664569647092737326704519438008576) = 36024664569647092737326704519438008576 := rfl
@[isel_data] theorem normInt_5_41362427188014754909301208165426529540 : normInt 5 (41362427188014754909301208165426529540) = 41362427188014754909301208165426529540 := rfl
@[isel_data] theorem normInt_5_18687320815856387368178823909286805505 : normInt 5 (18687320815856387368178823909286805505) = 18687320815856387368178823909286805505 := rfl
@[isel_data] theorem normInt_5_16018520953223639909183530438118932995 : normInt 5 (16018520953223639909183530438118932995) = 16018520953223639909183530438118932995 := rfl
@[isel_data] theorem normInt_5_17342576855639742879858139805557719810 : normInt 5 (17342576855639742879858139805557719810) = 17342576855639742879858139805557719810 := rfl
@[isel_data] theorem normInt_5_10680758337341567148842519922299176455 : normInt 5 (10680758337341567148842519922299176455) = 10680758337341567148842519922299176455 := rfl
@[isel_data] theorem normInt_5_12004814239757670119517129289737963270 : normInt 5 (12004814239757670119517129289737963270) = 12004814239757670119517129289737963270 := rfl
@[isel_data] theorem normInt_5_14673614102390417578512422760905835780 : normInt 5 (14673614102390417578512422760905835780) = 14673614102390417578512422760905835780 := rfl
@[isel_data] theorem normInt_3_64 : normInt 3 (64) = 64 := rfl
@[isel_data] theorem normInt_3_2 : normInt 3 (2) = 2 := rfl
@[isel_data] theorem normInt_3_32 : normInt 3 (32) = 32 := rfl
@[isel_data] theorem normInt_4_32 : normInt 4 (32) = 32 := rfl
@[isel_data] theorem normInt_1_63 : normInt 1 (63) = 63 := rfl
@[isel_data] theorem normInt_4_128 : normInt 4 (128) = 128 := rfl
@[isel_data] theorem normInt_1_24 : normInt 1 (24) = 24 := rfl
@[isel_data] theorem normInt_1_16 : normInt 1 (16) = 16 := rfl
@[isel_data] theorem normInt_4_8388608 : normInt 4 (8388608) = 8388608 := rfl
@[isel_data] theorem normInt_4_32768 : normInt 4 (32768) = 32768 := rfl
@[isel_data] theorem normInt_10_0 : normInt 10 (0) = 0 := rfl
@[isel_data] theorem normInt_1_7 : normInt 1 (7) = 7 := rfl
@[isel_data] theorem normInt_5_neg169808226154284360427508033573982305791 : normInt 5 (-169808226154284360427508033573982305791) = 170474140766654103035866573857785905665 := rfl
@[isel_data] theorem normInt_1_8 : normInt 1 (8) = 8 := rfl
@[isel_data] theorem normInt_1_15 : normInt 1 (15) = 15 := rfl
@[isel_data] theorem normInt_5_664619068533544770747334646890102785 : normInt 5 (664619068533544770747334646890102785) = 664619068533544770747334646890102785 := rfl
@[isel_data] theorem normInt_1_31 : normInt 1 (31) = 31 := rfl
@[isel_data] theorem normInt_5_633825300187901677051779743745 : normInt 5 (633825300187901677051779743745) = 633825300187901677051779743745 := rfl
@[isel_data] theorem normInt_141_0 : normInt 141 (0) = 0 := rfl

@[isel_data] theorem tyMInst_eq : tyMInst = 58 := rfl
@[isel_data] theorem tyALUOp_eq : tyALUOp = 59 := rfl
@[isel_data] theorem tyALUOp3_eq : tyALUOp3 = 60 := rfl
@[isel_data] theorem tyOperandSize_eq : tyOperandSize = 93 := rfl
@[isel_data] theorem tyCond_eq : tyCond = 96 := rfl
@[isel_data] theorem tyExtendOp_eq : tyExtendOp = 84 := rfl
@[isel_data] theorem tyAMode_eq : tyAMode = 89 := rfl
@[isel_data] theorem tyCondBrKind_eq : tyCondBrKind = 83 := rfl
@[isel_data] theorem tyMoveWideOp_eq : tyMoveWideOp = 61 := rfl
@[isel_data] theorem tyBfmOp_eq : tyBfmOp = 62 := rfl
@[isel_data] theorem tyBitOp_eq : tyBitOp = 85 := rfl
@[isel_data] theorem tyScalarSize_eq : tyScalarSize = 95 := rfl
@[isel_data] theorem tyIntCC_eq : tyIntCC = 145 := rfl
@[isel_data] theorem tyOpcode_eq : tyOpcode = 151 := rfl
@[isel_data] theorem tyInstData_eq : tyInstData = 152 := rfl
@[isel_data] theorem tyImmExtend_eq : tyImmExtend = 122 := rfl
@[isel_data] theorem tyRelocDistance_eq : tyRelocDistance = 38 := rfl

end Backend.Proof
