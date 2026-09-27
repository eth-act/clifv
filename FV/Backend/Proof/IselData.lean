import FV.Backend
import FV.Backend.Proof.IselAttr

/-!
# ISLE data facts for the isel proofs (generated, do not edit)

Regenerate: `lake env lean --run FVTest/Backend/Proof/Probe/GenData.lean closure > FV/Backend/Proof/IselData.lean`.

Roots: 129 root rules (closure); 536 terms reachable from them (patterns, if-lets,
right-hand sides, and the rules of every internal constructor they call, transitively), of
which the internal constructors have 838 rules. `lower`/`lower_branch` are included with
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
@[isel_data] theorem term_31_kind : T.«i64_sextend_imm64».kind = (.decl ⟨true, false, false, false⟩ (some (.external "i64_sextend_imm64")) none) := rfl
@[isel_data] theorem term_31_name : T.«i64_sextend_imm64».name = "i64_sextend_imm64" := rfl
@[isel_data] theorem term_87_kind : T.«ty_bits».kind = (.decl ⟨true, false, false, false⟩ (some (.external "ty_bits")) none) := rfl
@[isel_data] theorem term_87_name : T.«ty_bits».name = "ty_bits" := rfl
@[isel_data] theorem term_93_kind : T.«ty_bytes».kind = (.decl ⟨true, false, false, false⟩ (some (.external "ty_bytes")) none) := rfl
@[isel_data] theorem term_93_name : T.«ty_bytes».name = "ty_bytes" := rfl
@[isel_data] theorem term_103_kind : T.«little_or_native_endian».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "little_or_native_endian" false))) := rfl
@[isel_data] theorem term_103_name : T.«little_or_native_endian».name = "little_or_native_endian" := rfl
@[isel_data] theorem term_110_kind : T.«fits_in_16».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "fits_in_16" false))) := rfl
@[isel_data] theorem term_110_name : T.«fits_in_16».name = "fits_in_16" := rfl
@[isel_data] theorem term_111_kind : T.«fits_in_32».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "fits_in_32" false))) := rfl
@[isel_data] theorem term_111_name : T.«fits_in_32».name = "fits_in_32" := rfl
@[isel_data] theorem term_113_kind : T.«fits_in_64».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "fits_in_64" false))) := rfl
@[isel_data] theorem term_113_name : T.«fits_in_64».name = "fits_in_64" := rfl
@[isel_data] theorem term_118_kind : T.«ty_int_ref_scalar_64».kind = (.decl ⟨true, false, true, false⟩ (some (.external "ty_int_ref_scalar_64")) none) := rfl
@[isel_data] theorem term_118_name : T.«ty_int_ref_scalar_64».name = "ty_int_ref_scalar_64" := rfl
@[isel_data] theorem term_119_kind : T.«ty_int_ref_scalar_64_extract».kind = (.decl ⟨true, false, true, false⟩ none (some (.external "ty_int_ref_scalar_64_extract" false))) := rfl
@[isel_data] theorem term_119_name : T.«ty_int_ref_scalar_64_extract».name = "ty_int_ref_scalar_64_extract" := rfl
@[isel_data] theorem term_120_kind : T.«ty_32_or_64».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "ty_32_or_64" false))) := rfl
@[isel_data] theorem term_120_name : T.«ty_32_or_64».name = "ty_32_or_64" := rfl
@[isel_data] theorem term_126_kind : T.«ty_int».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "ty_int" false))) := rfl
@[isel_data] theorem term_126_name : T.«ty_int».name = "ty_int" := rfl
@[isel_data] theorem term_128_kind : T.«ty_scalar_float».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "ty_scalar_float" false))) := rfl
@[isel_data] theorem term_128_name : T.«ty_scalar_float».name = "ty_scalar_float" := rfl
@[isel_data] theorem term_132_kind : T.«ty_vec64».kind = (.decl ⟨true, false, true, false⟩ (some (.external "ty_vec64_ctor")) (some (.external "ty_vec64" false))) := rfl
@[isel_data] theorem term_132_name : T.«ty_vec64».name = "ty_vec64" := rfl
@[isel_data] theorem term_133_kind : T.«ty_vec128».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "ty_vec128" false))) := rfl
@[isel_data] theorem term_133_name : T.«ty_vec128».name = "ty_vec128" := rfl
@[isel_data] theorem term_141_kind : T.«not_i64x2».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "not_i64x2" false))) := rfl
@[isel_data] theorem term_141_name : T.«not_i64x2».name = "not_i64x2" := rfl
@[isel_data] theorem term_144_kind : T.«u64_from_imm64».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "u64_from_imm64" true))) := rfl
@[isel_data] theorem term_144_name : T.«u64_from_imm64».name = "u64_from_imm64" := rfl
@[isel_data] theorem term_145_kind : T.«nonzero_u64_from_imm64».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "nonzero_u64_from_imm64" false))) := rfl
@[isel_data] theorem term_145_name : T.«nonzero_u64_from_imm64».name = "nonzero_u64_from_imm64" := rfl
@[isel_data] theorem term_152_kind : T.«multi_lane».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "multi_lane" false))) := rfl
@[isel_data] theorem term_152_name : T.«multi_lane».name = "multi_lane" := rfl
@[isel_data] theorem term_153_kind : T.«dynamic_lane».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "dynamic_lane" false))) := rfl
@[isel_data] theorem term_153_name : T.«dynamic_lane».name = "dynamic_lane" := rfl
@[isel_data] theorem term_156_kind : T.«offset32_to_i32».kind = (.decl ⟨true, false, false, false⟩ (some (.external "offset32_to_i32")) none) := rfl
@[isel_data] theorem term_156_name : T.«offset32_to_i32».name = "offset32_to_i32" := rfl
@[isel_data] theorem term_157_kind : T.«i32_to_offset32».kind = (.decl ⟨true, false, false, false⟩ (some (.external "i32_to_offset32")) none) := rfl
@[isel_data] theorem term_157_name : T.«i32_to_offset32».name = "i32_to_offset32" := rfl
@[isel_data] theorem term_159_kind : T.«signed_cond_code».kind = (.decl ⟨true, false, true, false⟩ (some (.external "signed_cond_code")) none) := rfl
@[isel_data] theorem term_159_name : T.«signed_cond_code».name = "signed_cond_code" := rfl
@[isel_data] theorem term_160_kind : T.«unsigned_cond_code».kind = (.decl ⟨true, false, true, false⟩ (some (.external "unsigned_cond_code")) none) := rfl
@[isel_data] theorem term_160_name : T.«unsigned_cond_code».name = "unsigned_cond_code" := rfl
@[isel_data] theorem term_161_kind : T.«trap_code_division_by_zero».kind = (.decl ⟨true, false, false, false⟩ (some (.external "trap_code_division_by_zero")) none) := rfl
@[isel_data] theorem term_161_name : T.«trap_code_division_by_zero».name = "trap_code_division_by_zero" := rfl
@[isel_data] theorem term_162_kind : T.«trap_code_integer_overflow».kind = (.decl ⟨true, false, false, false⟩ (some (.external "trap_code_integer_overflow")) none) := rfl
@[isel_data] theorem term_162_name : T.«trap_code_integer_overflow».name = "trap_code_integer_overflow" := rfl
@[isel_data] theorem term_164_kind : T.«value_reg».kind = (.decl ⟨false, false, false, false⟩ (some (.external "value_reg")) none) := rfl
@[isel_data] theorem term_164_name : T.«value_reg».name = "value_reg" := rfl
@[isel_data] theorem term_166_kind : T.«value_regs».kind = (.decl ⟨false, false, false, false⟩ (some (.external "value_regs")) none) := rfl
@[isel_data] theorem term_166_name : T.«value_regs».name = "value_regs" := rfl
@[isel_data] theorem term_169_kind : T.«output_none».kind = (.decl ⟨false, false, false, false⟩ (some (.external "output_none")) none) := rfl
@[isel_data] theorem term_169_name : T.«output_none».name = "output_none" := rfl
@[isel_data] theorem term_170_kind : T.«output».kind = (.decl ⟨false, false, false, false⟩ (some (.external "output")) none) := rfl
@[isel_data] theorem term_170_name : T.«output».name = "output" := rfl
@[isel_data] theorem term_172_kind : T.«output_reg».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_172_name : T.«output_reg».name = "output_reg" := rfl
@[isel_data] theorem term_174_kind : T.«output_vec».kind = (.decl ⟨false, false, false, false⟩ (some (.external "output_vec")) none) := rfl
@[isel_data] theorem term_174_name : T.«output_vec».name = "output_vec" := rfl
@[isel_data] theorem term_175_kind : T.«temp_writable_reg».kind = (.decl ⟨false, false, false, false⟩ (some (.external "temp_writable_reg")) none) := rfl
@[isel_data] theorem term_175_name : T.«temp_writable_reg».name = "temp_writable_reg" := rfl
@[isel_data] theorem term_178_name : T.«invalid_reg».name = "invalid_reg" := rfl
@[isel_data] theorem term_181_kind : T.«opportunistic_def».kind = (.decl ⟨false, false, false, false⟩ (some (.external "opportunistic_def")) none) := rfl
@[isel_data] theorem term_181_name : T.«opportunistic_def».name = "opportunistic_def" := rfl
@[isel_data] theorem term_182_kind : T.«put_in_reg».kind = (.decl ⟨false, false, false, false⟩ (some (.external "put_in_reg")) none) := rfl
@[isel_data] theorem term_182_name : T.«put_in_reg».name = "put_in_reg" := rfl
@[isel_data] theorem term_183_kind : T.«put_in_regs».kind = (.decl ⟨false, false, false, false⟩ (some (.external "put_in_regs")) none) := rfl
@[isel_data] theorem term_183_name : T.«put_in_regs».name = "put_in_regs" := rfl
@[isel_data] theorem term_184_kind : T.«put_in_regs_vec».kind = (.decl ⟨false, false, false, false⟩ (some (.external "put_in_regs_vec")) none) := rfl
@[isel_data] theorem term_184_name : T.«put_in_regs_vec».name = "put_in_regs_vec" := rfl
@[isel_data] theorem term_185_kind : T.«value_regs_get».kind = (.decl ⟨false, false, false, false⟩ (some (.external "value_regs_get")) none) := rfl
@[isel_data] theorem term_185_name : T.«value_regs_get».name = "value_regs_get" := rfl
@[isel_data] theorem term_190_kind : T.«single_target».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "single_target" false))) := rfl
@[isel_data] theorem term_190_name : T.«single_target».name = "single_target" := rfl
@[isel_data] theorem term_191_kind : T.«two_targets».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "two_targets" false))) := rfl
@[isel_data] theorem term_191_name : T.«two_targets».name = "two_targets" := rfl
@[isel_data] theorem term_192_kind : T.«jump_table_targets».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "jump_table_targets" false))) := rfl
@[isel_data] theorem term_192_name : T.«jump_table_targets».name = "jump_table_targets" := rfl
@[isel_data] theorem term_193_kind : T.«jump_table_size».kind = (.decl ⟨false, false, false, false⟩ (some (.external "jump_table_size")) none) := rfl
@[isel_data] theorem term_193_name : T.«jump_table_size».name = "jump_table_size" := rfl
@[isel_data] theorem term_194_kind : T.«value_list_slice».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "value_list_slice" true))) := rfl
@[isel_data] theorem term_194_name : T.«value_list_slice».name = "value_list_slice" := rfl
@[isel_data] theorem term_201_kind : T.«writable_reg_to_reg».kind = (.decl ⟨true, false, false, false⟩ (some (.external "writable_reg_to_reg")) none) := rfl
@[isel_data] theorem term_201_name : T.«writable_reg_to_reg».name = "writable_reg_to_reg" := rfl
@[isel_data] theorem term_205_kind : T.«first_result».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "first_result" false))) := rfl
@[isel_data] theorem term_205_name : T.«first_result».name = "first_result" := rfl
@[isel_data] theorem term_207_kind : T.«is_second_result».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "is_second_result" false))) := rfl
@[isel_data] theorem term_207_name : T.«is_second_result».name = "is_second_result" := rfl
@[isel_data] theorem term_209_kind : T.«inst_data_value».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "inst_data_value" true))) := rfl
@[isel_data] theorem term_209_name : T.«inst_data_value».name = "inst_data_value" := rfl
@[isel_data] theorem term_219_kind : T.«i64_from_iconst».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "i64_from_iconst" false))) := rfl
@[isel_data] theorem term_219_name : T.«i64_from_iconst».name = "i64_from_iconst" := rfl
@[isel_data] theorem term_221_kind : T.«is_sinkable_inst».kind = (.decl ⟨true, false, true, false⟩ (some (.external "is_sinkable_inst")) none) := rfl
@[isel_data] theorem term_221_name : T.«is_sinkable_inst».name = "is_sinkable_inst" := rfl
@[isel_data] theorem term_222_kind : T.«maybe_uextend».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "maybe_uextend" false))) := rfl
@[isel_data] theorem term_222_name : T.«maybe_uextend».name = "maybe_uextend" := rfl
@[isel_data] theorem term_235_kind : T.«emit».kind = (.decl ⟨false, false, false, false⟩ (some (.external "emit")) none) := rfl
@[isel_data] theorem term_235_name : T.«emit».name = "emit" := rfl
@[isel_data] theorem term_236_kind : T.«sink_inst».kind = (.decl ⟨false, false, false, false⟩ (some (.external "sink_inst")) none) := rfl
@[isel_data] theorem term_236_name : T.«sink_inst».name = "sink_inst" := rfl
@[isel_data] theorem term_242_kind : T.«emit_side_effect».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_242_name : T.«emit_side_effect».name = "emit_side_effect" := rfl
@[isel_data] theorem term_243_kind : T.«side_effect».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_243_name : T.«side_effect».name = "side_effect" := rfl
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
@[isel_data] theorem term_256_kind : T.«with_flags_side_effect».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_256_name : T.«with_flags_side_effect».name = "with_flags_side_effect" := rfl
@[isel_data] theorem term_264_kind : T.«box_external_name».kind = (.decl ⟨false, false, false, false⟩ (some (.external "box_external_name")) none) := rfl
@[isel_data] theorem term_264_name : T.«box_external_name».name = "box_external_name" := rfl
@[isel_data] theorem term_265_kind : T.«func_ref_data».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "func_ref_data" true))) := rfl
@[isel_data] theorem term_265_name : T.«func_ref_data».name = "func_ref_data" := rfl
@[isel_data] theorem term_267_kind : T.«symbol_value_data».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "symbol_value_data" false))) := rfl
@[isel_data] theorem term_267_name : T.«symbol_value_data».name = "symbol_value_data" := rfl
@[isel_data] theorem term_278_kind : T.«abi_sig».kind = (.decl ⟨false, false, false, false⟩ (some (.external "abi_sig")) none) := rfl
@[isel_data] theorem term_278_name : T.«abi_sig».name = "abi_sig" := rfl
@[isel_data] theorem term_286_kind : T.«abi_stackslot_addr».kind = (.decl ⟨false, false, false, false⟩ (some (.external "abi_stackslot_addr")) none) := rfl
@[isel_data] theorem term_286_name : T.«abi_stackslot_addr».name = "abi_stackslot_addr" := rfl
@[isel_data] theorem term_287_kind : T.«abi_stackslot_offset_into_slot_region».kind = (.decl ⟨false, false, false, false⟩ (some (.external "abi_stackslot_offset_into_slot_region")) none) := rfl
@[isel_data] theorem term_287_name : T.«abi_stackslot_offset_into_slot_region».name = "abi_stackslot_offset_into_slot_region" := rfl
@[isel_data] theorem term_294_kind : T.«lower_return».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_294_name : T.«lower_return».name = "lower_return" := rfl
@[isel_data] theorem term_295_kind : T.«gen_return».kind = (.decl ⟨false, false, false, false⟩ (some (.external "gen_return")) none) := rfl
@[isel_data] theorem term_295_name : T.«gen_return».name = "gen_return" := rfl
@[isel_data] theorem term_296_kind : T.«gen_call_output».kind = (.decl ⟨false, false, false, false⟩ (some (.external "gen_call_output")) none) := rfl
@[isel_data] theorem term_296_name : T.«gen_call_output».name = "gen_call_output" := rfl
@[isel_data] theorem term_297_kind : T.«gen_call_args».kind = (.decl ⟨false, false, false, false⟩ (some (.external "gen_call_args")) none) := rfl
@[isel_data] theorem term_297_name : T.«gen_call_args».name = "gen_call_args" := rfl
@[isel_data] theorem term_299_kind : T.«gen_call_rets».kind = (.decl ⟨false, false, false, false⟩ (some (.external "gen_call_rets")) none) := rfl
@[isel_data] theorem term_299_name : T.«gen_call_rets».name = "gen_call_rets" := rfl
@[isel_data] theorem term_303_kind : T.«try_call_none».kind = (.decl ⟨false, false, false, false⟩ (some (.external "try_call_none")) none) := rfl
@[isel_data] theorem term_303_name : T.«try_call_none».name = "try_call_none" := rfl
@[isel_data] theorem term_304_kind : T.«safe_divisor_from_imm64».kind = (.decl ⟨true, false, true, false⟩ (some (.external "safe_divisor_from_imm64")) none) := rfl
@[isel_data] theorem term_304_name : T.«safe_divisor_from_imm64».name = "safe_divisor_from_imm64" := rfl
@[isel_data] theorem term_305_kind : T.«operand_size».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_305_name : T.«operand_size».name = "operand_size" := rfl
@[isel_data] theorem term_306_kind : T.«diff_from_32».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_306_name : T.«diff_from_32».name = "diff_from_32" := rfl
@[isel_data] theorem term_307_kind : T.«scalar_size».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_307_name : T.«scalar_size».name = "scalar_size" := rfl
@[isel_data] theorem term_310_kind : T.«vector_size».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_310_name : T.«vector_size».name = "vector_size" := rfl
@[isel_data] theorem term_316_kind : T.«use_fp16».kind = (.decl ⟨true, false, false, false⟩ (some (.external "use_fp16")) none) := rfl
@[isel_data] theorem term_316_name : T.«use_fp16».name = "use_fp16" := rfl
@[isel_data] theorem term_318_kind : T.«move_wide_const_from_u64».kind = (.decl ⟨true, false, true, false⟩ (some (.external "move_wide_const_from_u64")) none) := rfl
@[isel_data] theorem term_318_name : T.«move_wide_const_from_u64».name = "move_wide_const_from_u64" := rfl
@[isel_data] theorem term_319_kind : T.«move_wide_const_from_inverted_u64».kind = (.decl ⟨true, false, true, false⟩ (some (.external "move_wide_const_from_inverted_u64")) none) := rfl
@[isel_data] theorem term_319_name : T.«move_wide_const_from_inverted_u64».name = "move_wide_const_from_inverted_u64" := rfl
@[isel_data] theorem term_320_kind : T.«imm_logic_from_u64».kind = (.decl ⟨true, false, true, false⟩ (some (.external "imm_logic_from_u64")) none) := rfl
@[isel_data] theorem term_320_name : T.«imm_logic_from_u64».name = "imm_logic_from_u64" := rfl
@[isel_data] theorem term_321_kind : T.«imm_size_from_type».kind = (.decl ⟨true, false, true, false⟩ (some (.external "imm_size_from_type")) none) := rfl
@[isel_data] theorem term_321_name : T.«imm_size_from_type».name = "imm_size_from_type" := rfl
@[isel_data] theorem term_322_kind : T.«imm_logic_from_imm64».kind = (.decl ⟨true, false, true, false⟩ (some (.external "imm_logic_from_imm64")) none) := rfl
@[isel_data] theorem term_322_name : T.«imm_logic_from_imm64».name = "imm_logic_from_imm64" := rfl
@[isel_data] theorem term_323_kind : T.«imm_shift_from_imm64».kind = (.decl ⟨true, false, true, false⟩ (some (.external "imm_shift_from_imm64")) none) := rfl
@[isel_data] theorem term_323_name : T.«imm_shift_from_imm64».name = "imm_shift_from_imm64" := rfl
@[isel_data] theorem term_324_kind : T.«imm_shift_from_u8».kind = (.decl ⟨false, false, false, false⟩ (some (.external "imm_shift_from_u8")) none) := rfl
@[isel_data] theorem term_324_name : T.«imm_shift_from_u8».name = "imm_shift_from_u8" := rfl
@[isel_data] theorem term_325_kind : T.«imm12_from_u64».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "imm12_from_u64" false))) := rfl
@[isel_data] theorem term_325_name : T.«imm12_from_u64».name = "imm12_from_u64" := rfl
@[isel_data] theorem term_326_kind : T.«u8_into_uimm5».kind = (.decl ⟨false, false, false, false⟩ (some (.external "u8_into_uimm5")) none) := rfl
@[isel_data] theorem term_326_name : T.«u8_into_uimm5».name = "u8_into_uimm5" := rfl
@[isel_data] theorem term_327_kind : T.«u8_into_imm12».kind = (.decl ⟨false, false, false, false⟩ (some (.external "u8_into_imm12")) none) := rfl
@[isel_data] theorem term_327_name : T.«u8_into_imm12».name = "u8_into_imm12" := rfl
@[isel_data] theorem term_328_kind : T.«u64_into_imm_logic».kind = (.decl ⟨false, false, false, false⟩ (some (.external "u64_into_imm_logic")) none) := rfl
@[isel_data] theorem term_328_name : T.«u64_into_imm_logic».name = "u64_into_imm_logic" := rfl
@[isel_data] theorem term_329_kind : T.«branch_target».kind = (.decl ⟨false, false, false, false⟩ (some (.external "branch_target")) none) := rfl
@[isel_data] theorem term_329_name : T.«branch_target».name = "branch_target" := rfl
@[isel_data] theorem term_330_kind : T.«targets_jt_space».kind = (.decl ⟨false, false, false, false⟩ (some (.external "targets_jt_space")) none) := rfl
@[isel_data] theorem term_330_name : T.«targets_jt_space».name = "targets_jt_space" := rfl
@[isel_data] theorem term_336_kind : T.«lshl_from_imm64».kind = (.decl ⟨true, false, true, false⟩ (some (.external "lshl_from_imm64")) none) := rfl
@[isel_data] theorem term_336_name : T.«lshl_from_imm64».name = "lshl_from_imm64" := rfl
@[isel_data] theorem term_338_kind : T.«ashr_from_u64».kind = (.decl ⟨true, false, true, false⟩ (some (.external "ashr_from_u64")) none) := rfl
@[isel_data] theorem term_338_name : T.«ashr_from_u64».name = "ashr_from_u64" := rfl
@[isel_data] theorem term_339_kind : T.«integral_ty».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "integral_ty" false))) := rfl
@[isel_data] theorem term_339_name : T.«integral_ty».name = "integral_ty" := rfl
@[isel_data] theorem term_344_kind : T.«imm12_from_negated_value».kind = (.decl ⟨true, false, true, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_344_name : T.«imm12_from_negated_value».name = "imm12_from_negated_value" := rfl
@[isel_data] theorem term_345_kind : T.«extended_value_from_value».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "extended_value_from_value" false))) := rfl
@[isel_data] theorem term_345_name : T.«extended_value_from_value».name = "extended_value_from_value" := rfl
@[isel_data] theorem term_346_kind : T.«put_extended_in_reg».kind = (.decl ⟨false, false, false, false⟩ (some (.external "put_extended_in_reg")) none) := rfl
@[isel_data] theorem term_346_name : T.«put_extended_in_reg».name = "put_extended_in_reg" := rfl
@[isel_data] theorem term_347_kind : T.«get_extended_op».kind = (.decl ⟨false, false, false, false⟩ (some (.external "get_extended_op")) none) := rfl
@[isel_data] theorem term_347_name : T.«get_extended_op».name = "get_extended_op" := rfl
@[isel_data] theorem term_348_kind : T.«nzcv».kind = (.decl ⟨false, false, false, false⟩ (some (.external "nzcv")) none) := rfl
@[isel_data] theorem term_348_name : T.«nzcv».name = "nzcv" := rfl
@[isel_data] theorem term_349_kind : T.«cond_br_zero».kind = (.decl ⟨false, false, false, false⟩ (some (.external "cond_br_zero")) none) := rfl
@[isel_data] theorem term_349_name : T.«cond_br_zero».name = "cond_br_zero" := rfl
@[isel_data] theorem term_350_kind : T.«cond_br_not_zero».kind = (.decl ⟨false, false, false, false⟩ (some (.external "cond_br_not_zero")) none) := rfl
@[isel_data] theorem term_350_name : T.«cond_br_not_zero».name = "cond_br_not_zero" := rfl
@[isel_data] theorem term_351_kind : T.«cond_br_cond».kind = (.decl ⟨false, false, false, false⟩ (some (.external "cond_br_cond")) none) := rfl
@[isel_data] theorem term_351_name : T.«cond_br_cond».name = "cond_br_cond" := rfl
@[isel_data] theorem term_352_kind : T.«zero_reg».kind = (.decl ⟨false, false, false, false⟩ (some (.external "zero_reg")) none) := rfl
@[isel_data] theorem term_352_name : T.«zero_reg».name = "zero_reg" := rfl
@[isel_data] theorem term_356_kind : T.«writable_zero_reg».kind = (.decl ⟨false, false, false, false⟩ (some (.external "writable_zero_reg")) none) := rfl
@[isel_data] theorem term_356_name : T.«writable_zero_reg».name = "writable_zero_reg" := rfl
@[isel_data] theorem term_358_kind : T.«movz».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_358_name : T.«movz».name = "movz" := rfl
@[isel_data] theorem term_359_kind : T.«movn».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_359_name : T.«movn».name = "movn" := rfl
@[isel_data] theorem term_360_kind : T.«alu_rr_imm_logic».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_360_name : T.«alu_rr_imm_logic».name = "alu_rr_imm_logic" := rfl
@[isel_data] theorem term_361_kind : T.«alu_rr_imm_shift».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_361_name : T.«alu_rr_imm_shift».name = "alu_rr_imm_shift" := rfl
@[isel_data] theorem term_362_kind : T.«alu_rrr».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_362_name : T.«alu_rrr».name = "alu_rrr" := rfl
@[isel_data] theorem term_363_kind : T.«vec_rrr».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_363_name : T.«vec_rrr».name = "vec_rrr" := rfl
@[isel_data] theorem term_370_kind : T.«fpu_cmp».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_370_name : T.«fpu_cmp».name = "fpu_cmp" := rfl
@[isel_data] theorem term_371_kind : T.«vec_lanes».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_371_name : T.«vec_lanes».name = "vec_lanes" := rfl
@[isel_data] theorem term_376_kind : T.«alu_rr_imm12».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_376_name : T.«alu_rr_imm12».name = "alu_rr_imm12" := rfl
@[isel_data] theorem term_377_kind : T.«alu_rrr_shift».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_377_name : T.«alu_rrr_shift».name = "alu_rrr_shift" := rfl
@[isel_data] theorem term_379_kind : T.«cmp_rr_shift_asr».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_379_name : T.«cmp_rr_shift_asr».name = "cmp_rr_shift_asr" := rfl
@[isel_data] theorem term_380_kind : T.«alu_rrr_extend».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_380_name : T.«alu_rrr_extend».name = "alu_rrr_extend" := rfl
@[isel_data] theorem term_381_kind : T.«alu_rr_extend_reg».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_381_name : T.«alu_rr_extend_reg».name = "alu_rr_extend_reg" := rfl
@[isel_data] theorem term_382_kind : T.«alu_rrrr».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_382_name : T.«alu_rrrr».name = "alu_rrrr" := rfl
@[isel_data] theorem term_383_kind : T.«alu_rrr_with_flags_paired».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_383_name : T.«alu_rrr_with_flags_paired».name = "alu_rrr_with_flags_paired" := rfl
@[isel_data] theorem term_385_kind : T.«sbcs_side_effect».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_385_name : T.«sbcs_side_effect».name = "sbcs_side_effect" := rfl
@[isel_data] theorem term_386_kind : T.«bit_rr».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_386_name : T.«bit_rr».name = "bit_rr" := rfl
@[isel_data] theorem term_390_kind : T.«cmp».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_390_name : T.«cmp».name = "cmp" := rfl
@[isel_data] theorem term_391_kind : T.«cmp_imm».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_391_name : T.«cmp_imm».name = "cmp_imm" := rfl
@[isel_data] theorem term_392_kind : T.«cmp64_imm».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_392_name : T.«cmp64_imm».name = "cmp64_imm" := rfl
@[isel_data] theorem term_393_kind : T.«cmp_extend».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_393_name : T.«cmp_extend».name = "cmp_extend" := rfl
@[isel_data] theorem term_395_kind : T.«vec_misc».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_395_name : T.«vec_misc».name = "vec_misc" := rfl
@[isel_data] theorem term_406_kind : T.«fpu_csel».kind = (.decl ⟨false, false, false, true⟩ (some .internal) none) := rfl
@[isel_data] theorem term_406_name : T.«fpu_csel».name = "fpu_csel" := rfl
@[isel_data] theorem term_407_kind : T.«vec_csel».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_407_name : T.«vec_csel».name = "vec_csel" := rfl
@[isel_data] theorem term_409_kind : T.«mov_to_fpu».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_409_name : T.«mov_to_fpu».name = "mov_to_fpu" := rfl
@[isel_data] theorem term_410_kind : T.«size_for_mov_to_fpu».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_410_name : T.«size_for_mov_to_fpu».name = "size_for_mov_to_fpu" := rfl
@[isel_data] theorem term_414_kind : T.«mov_from_vec».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_414_name : T.«mov_from_vec».name = "mov_from_vec" := rfl
@[isel_data] theorem term_417_kind : T.«extend».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_417_name : T.«extend».name = "extend" := rfl
@[isel_data] theorem term_418_kind : T.«bitfield_move».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_418_name : T.«bitfield_move».name = "bitfield_move" := rfl
@[isel_data] theorem term_424_kind : T.«tst_imm».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_424_name : T.«tst_imm».name = "tst_imm" := rfl
@[isel_data] theorem term_425_kind : T.«csel».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_425_name : T.«csel».name = "csel" := rfl
@[isel_data] theorem term_426_kind : T.«cset».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_426_name : T.«cset».name = "cset" := rfl
@[isel_data] theorem term_430_kind : T.«ccmp».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_430_name : T.«ccmp».name = "ccmp" := rfl
@[isel_data] theorem term_432_kind : T.«add».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_432_name : T.«add».name = "add" := rfl
@[isel_data] theorem term_433_kind : T.«add_imm».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_433_name : T.«add_imm».name = "add_imm" := rfl
@[isel_data] theorem term_434_kind : T.«add_extend».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_434_name : T.«add_extend».name = "add_extend" := rfl
@[isel_data] theorem term_435_kind : T.«add_shift».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_435_name : T.«add_shift».name = "add_shift" := rfl
@[isel_data] theorem term_437_kind : T.«sub».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_437_name : T.«sub».name = "sub" := rfl
@[isel_data] theorem term_438_kind : T.«sub_imm».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_438_name : T.«sub_imm».name = "sub_imm" := rfl
@[isel_data] theorem term_439_kind : T.«sub_extend».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_439_name : T.«sub_extend».name = "sub_extend" := rfl
@[isel_data] theorem term_440_kind : T.«sub_shift».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_440_name : T.«sub_shift».name = "sub_shift" := rfl
@[isel_data] theorem term_443_kind : T.«madd».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_443_name : T.«madd».name = "madd" := rfl
@[isel_data] theorem term_444_kind : T.«msub».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_444_name : T.«msub».name = "msub" := rfl
@[isel_data] theorem term_451_kind : T.«umulh».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_451_name : T.«umulh».name = "umulh" := rfl
@[isel_data] theorem term_452_kind : T.«smulh».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_452_name : T.«smulh».name = "smulh" := rfl
@[isel_data] theorem term_469_kind : T.«addp».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_469_name : T.«addp».name = "addp" := rfl
@[isel_data] theorem term_473_kind : T.«addv».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_473_name : T.«addv».name = "addv" := rfl
@[isel_data] theorem term_487_kind : T.«asr_imm».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_487_name : T.«asr_imm».name = "asr_imm" := rfl
@[isel_data] theorem term_488_kind : T.«lsr».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_488_name : T.«lsr».name = "lsr" := rfl
@[isel_data] theorem term_489_kind : T.«lsr_imm».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_489_name : T.«lsr_imm».name = "lsr_imm" := rfl
@[isel_data] theorem term_490_kind : T.«lsl».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_490_name : T.«lsl».name = "lsl" := rfl
@[isel_data] theorem term_491_kind : T.«lsl_imm».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_491_name : T.«lsl_imm».name = "lsl_imm" := rfl
@[isel_data] theorem term_492_kind : T.«a64_udiv».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_492_name : T.«a64_udiv».name = "a64_udiv" := rfl
@[isel_data] theorem term_493_kind : T.«a64_sdiv».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_493_name : T.«a64_sdiv».name = "a64_sdiv" := rfl
@[isel_data] theorem term_495_kind : T.«orr_not».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_495_name : T.«orr_not».name = "orr_not" := rfl
@[isel_data] theorem term_496_kind : T.«orr_not_shift».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_496_name : T.«orr_not_shift».name = "orr_not_shift" := rfl
@[isel_data] theorem term_497_kind : T.«orr».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_497_name : T.«orr».name = "orr" := rfl
@[isel_data] theorem term_498_kind : T.«orr_imm».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_498_name : T.«orr_imm».name = "orr_imm" := rfl
@[isel_data] theorem term_501_kind : T.«and_reg».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_501_name : T.«and_reg».name = "and_reg" := rfl
@[isel_data] theorem term_502_kind : T.«and_imm».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_502_name : T.«and_imm».name = "and_imm" := rfl
@[isel_data] theorem term_513_kind : T.«a64_rotr».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_513_name : T.«a64_rotr».name = "a64_rotr" := rfl
@[isel_data] theorem term_514_kind : T.«a64_rotr_imm».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_514_name : T.«a64_rotr_imm».name = "a64_rotr_imm" := rfl
@[isel_data] theorem term_515_kind : T.«a64_extr».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_515_name : T.«a64_extr».name = "a64_extr" := rfl
@[isel_data] theorem term_516_kind : T.«a64_extr_imm».kind = (.decl ⟨false, false, false, false⟩ (some (.external "a64_extr_imm")) none) := rfl
@[isel_data] theorem term_516_name : T.«a64_extr_imm».name = "a64_extr_imm" := rfl
@[isel_data] theorem term_517_kind : T.«rbit».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_517_name : T.«rbit».name = "rbit" := rfl
@[isel_data] theorem term_518_kind : T.«a64_clz».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_518_name : T.«a64_clz».name = "a64_clz" := rfl
@[isel_data] theorem term_520_kind : T.«a64_rev16».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_520_name : T.«a64_rev16».name = "a64_rev16" := rfl
@[isel_data] theorem term_521_kind : T.«a64_rev32».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_521_name : T.«a64_rev32».name = "a64_rev32" := rfl
@[isel_data] theorem term_522_kind : T.«a64_rev64».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_522_name : T.«a64_rev64».name = "a64_rev64" := rfl
@[isel_data] theorem term_524_kind : T.«vec_cnt».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_524_name : T.«vec_cnt».name = "vec_cnt" := rfl
@[isel_data] theorem term_528_kind : T.«udf».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_528_name : T.«udf».name = "udf" := rfl
@[isel_data] theorem term_529_kind : T.«aarch64_uload8».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_529_name : T.«aarch64_uload8».name = "aarch64_uload8" := rfl
@[isel_data] theorem term_530_kind : T.«aarch64_sload8».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_530_name : T.«aarch64_sload8».name = "aarch64_sload8" := rfl
@[isel_data] theorem term_531_kind : T.«aarch64_uload16».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_531_name : T.«aarch64_uload16».name = "aarch64_uload16" := rfl
@[isel_data] theorem term_532_kind : T.«aarch64_sload16».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_532_name : T.«aarch64_sload16».name = "aarch64_sload16" := rfl
@[isel_data] theorem term_533_kind : T.«aarch64_uload32».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_533_name : T.«aarch64_uload32».name = "aarch64_uload32" := rfl
@[isel_data] theorem term_534_kind : T.«aarch64_sload32».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_534_name : T.«aarch64_sload32».name = "aarch64_sload32" := rfl
@[isel_data] theorem term_535_kind : T.«aarch64_uload64».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_535_name : T.«aarch64_uload64».name = "aarch64_uload64" := rfl
@[isel_data] theorem term_541_kind : T.«aarch64_store8».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_541_name : T.«aarch64_store8».name = "aarch64_store8" := rfl
@[isel_data] theorem term_542_kind : T.«aarch64_store16».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_542_name : T.«aarch64_store16».name = "aarch64_store16" := rfl
@[isel_data] theorem term_543_kind : T.«aarch64_store32».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_543_name : T.«aarch64_store32».name = "aarch64_store32" := rfl
@[isel_data] theorem term_544_kind : T.«aarch64_store64».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_544_name : T.«aarch64_store64».name = "aarch64_store64" := rfl
@[isel_data] theorem term_553_kind : T.«imm».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_553_name : T.«imm».name = "imm" := rfl
@[isel_data] theorem term_554_kind : T.«load_constant_full».kind = (.decl ⟨false, false, false, false⟩ (some (.external "load_constant_full")) none) := rfl
@[isel_data] theorem term_554_name : T.«load_constant_full».name = "load_constant_full" := rfl
@[isel_data] theorem term_555_kind : T.«put_in_reg_sext32».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_555_name : T.«put_in_reg_sext32».name = "put_in_reg_sext32" := rfl
@[isel_data] theorem term_556_kind : T.«put_in_reg_zext32».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_556_name : T.«put_in_reg_zext32».name = "put_in_reg_zext32" := rfl
@[isel_data] theorem term_557_kind : T.«put_in_reg_sext64».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_557_name : T.«put_in_reg_sext64».name = "put_in_reg_sext64" := rfl
@[isel_data] theorem term_558_kind : T.«put_in_reg_zext64».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_558_name : T.«put_in_reg_zext64».name = "put_in_reg_zext64" := rfl
@[isel_data] theorem term_559_kind : T.«trap_if_zero_divisor».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_559_name : T.«trap_if_zero_divisor».name = "trap_if_zero_divisor" := rfl
@[isel_data] theorem term_560_kind : T.«size_from_ty».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_560_name : T.«size_from_ty».name = "size_from_ty" := rfl
@[isel_data] theorem term_561_kind : T.«trap_if_div_overflow».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_561_name : T.«trap_if_div_overflow».name = "trap_if_div_overflow" := rfl
@[isel_data] theorem term_562_kind : T.«intmin_check».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_562_name : T.«intmin_check».name = "intmin_check" := rfl
@[isel_data] theorem term_565_kind : T.«alu_rs_imm_logic_commutative».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_565_name : T.«alu_rs_imm_logic_commutative».name = "alu_rs_imm_logic_commutative" := rfl
@[isel_data] theorem term_566_kind : T.«alu_rs_imm_logic».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_566_name : T.«alu_rs_imm_logic».name = "alu_rs_imm_logic" := rfl
@[isel_data] theorem term_569_kind : T.«is_pic».kind = (.decl ⟨true, false, false, false⟩ (some (.external "is_pic")) none) := rfl
@[isel_data] theorem term_569_name : T.«is_pic».name = "is_pic" := rfl
@[isel_data] theorem term_570_kind : T.«load_ext_name».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_570_name : T.«load_ext_name».name = "load_ext_name" := rfl
@[isel_data] theorem term_571_kind : T.«load_ext_name_got».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_571_name : T.«load_ext_name_got».name = "load_ext_name_got" := rfl
@[isel_data] theorem term_572_kind : T.«load_ext_name_near».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_572_name : T.«load_ext_name_near».name = "load_ext_name_near" := rfl
@[isel_data] theorem term_573_kind : T.«load_ext_name_far».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_573_name : T.«load_ext_name_far».name = "load_ext_name_far" := rfl
@[isel_data] theorem term_574_kind : T.«amode».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_574_name : T.«amode».name = "amode" := rfl
@[isel_data] theorem term_575_kind : T.«amode_no_more_iconst».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_575_name : T.«amode_no_more_iconst».name = "amode_no_more_iconst" := rfl
@[isel_data] theorem term_576_kind : T.«amode_reg_scaled».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_576_name : T.«amode_reg_scaled».name = "amode_reg_scaled" := rfl
@[isel_data] theorem term_577_kind : T.«amode_add».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_577_name : T.«amode_add».name = "amode_add" := rfl
@[isel_data] theorem term_580_kind : T.«uimm12_scaled_from_i64».kind = (.decl ⟨true, false, true, false⟩ (some (.external "uimm12_scaled_from_i64")) none) := rfl
@[isel_data] theorem term_580_name : T.«uimm12_scaled_from_i64».name = "uimm12_scaled_from_i64" := rfl
@[isel_data] theorem term_581_kind : T.«uimm12_scaled_nonzero_from_i64».kind = (.decl ⟨true, false, true, false⟩ (some (.external "uimm12_scaled_nonzero_from_i64")) none) := rfl
@[isel_data] theorem term_581_name : T.«uimm12_scaled_nonzero_from_i64».name = "uimm12_scaled_nonzero_from_i64" := rfl
@[isel_data] theorem term_582_kind : T.«simm9_from_i64».kind = (.decl ⟨true, false, true, false⟩ (some (.external "simm9_from_i64")) none) := rfl
@[isel_data] theorem term_582_name : T.«simm9_from_i64».name = "simm9_from_i64" := rfl
@[isel_data] theorem term_592_kind : T.«cond_code».kind = (.decl ⟨false, false, false, false⟩ (some (.external "cond_code")) none) := rfl
@[isel_data] theorem term_592_name : T.«cond_code».name = "cond_code" := rfl
@[isel_data] theorem term_593_kind : T.«invert_cond».kind = (.decl ⟨false, false, false, false⟩ (some (.external "invert_cond")) none) := rfl
@[isel_data] theorem term_593_name : T.«invert_cond».name = "invert_cond" := rfl
@[isel_data] theorem term_634_kind : T.«gen_call_info».kind = (.decl ⟨false, false, false, false⟩ (some (.external "gen_call_info")) none) := rfl
@[isel_data] theorem term_634_name : T.«gen_call_info».name = "gen_call_info" := rfl
@[isel_data] theorem term_635_kind : T.«gen_call_ind_info».kind = (.decl ⟨false, false, false, false⟩ (some (.external "gen_call_ind_info")) none) := rfl
@[isel_data] theorem term_635_name : T.«gen_call_ind_info».name = "gen_call_ind_info" := rfl
@[isel_data] theorem term_638_kind : T.«call_impl».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_638_name : T.«call_impl».name = "call_impl" := rfl
@[isel_data] theorem term_639_kind : T.«call_ind_impl».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_639_name : T.«call_ind_impl».name = "call_ind_impl" := rfl
@[isel_data] theorem term_643_kind : T.«compute_stack_addr».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_643_name : T.«compute_stack_addr».name = "compute_stack_addr" := rfl
@[isel_data] theorem term_649_kind : T.«cond_result_invert».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_649_name : T.«cond_result_invert».name = "cond_result_invert" := rfl
@[isel_data] theorem term_650_kind : T.«is_nonzero_cmp».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_650_name : T.«is_nonzero_cmp».name = "is_nonzero_cmp" := rfl
@[isel_data] theorem term_651_kind : T.«is_nonzero».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_651_name : T.«is_nonzero».name = "is_nonzero" := rfl
@[isel_data] theorem term_652_kind : T.«emit_icmp».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_652_name : T.«emit_icmp».name = "emit_icmp" := rfl
@[isel_data] theorem term_653_kind : T.«emit_icmp_i128».kind = (.decl ⟨false, false, false, true⟩ (some .internal) none) := rfl
@[isel_data] theorem term_653_name : T.«emit_icmp_i128».name = "emit_icmp_i128" := rfl
@[isel_data] theorem term_654_kind : T.«emit_icmp_i128_eq_ne».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_654_name : T.«emit_icmp_i128_eq_ne».name = "emit_icmp_i128_eq_ne" := rfl
@[isel_data] theorem term_655_kind : T.«emit_fcmp».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_655_name : T.«emit_fcmp».name = "emit_fcmp" := rfl
@[isel_data] theorem term_656_kind : T.«fp_cond_code».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_656_name : T.«fp_cond_code».name = "fp_cond_code" := rfl
@[isel_data] theorem term_657_kind : T.«lower_extend_op».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_657_name : T.«lower_extend_op».name = "lower_extend_op" := rfl
@[isel_data] theorem term_659_kind : T.«lower_select».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_659_name : T.«lower_select».name = "lower_select" := rfl
@[isel_data] theorem term_660_kind : T.«lower_select_cond».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_660_name : T.«lower_select_cond».name = "lower_select_cond" := rfl
@[isel_data] theorem term_661_kind : T.«aarch64_jump».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_661_name : T.«aarch64_jump».name = "aarch64_jump" := rfl
@[isel_data] theorem term_662_kind : T.«jt_sequence».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_662_name : T.«jt_sequence».name = "jt_sequence" := rfl
@[isel_data] theorem term_663_kind : T.«a64_br_cond».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_663_name : T.«a64_br_cond».name = "a64_br_cond" := rfl
@[isel_data] theorem term_664_kind : T.«a64_br_zero».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_664_name : T.«a64_br_zero».name = "a64_br_zero" := rfl
@[isel_data] theorem term_665_kind : T.«a64_br_not_zero».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_665_name : T.«a64_br_not_zero».name = "a64_br_not_zero" := rfl
@[isel_data] theorem term_666_kind : T.«test_branch».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_666_name : T.«test_branch».name = "test_branch" := rfl
@[isel_data] theorem term_667_kind : T.«tbnz».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_667_name : T.«tbnz».name = "tbnz" := rfl
@[isel_data] theorem term_668_kind : T.«tbz».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_668_name : T.«tbz».name = "tbz" := rfl
@[isel_data] theorem term_669_kind : T.«emit_island».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_669_name : T.«emit_island».name = "emit_island" := rfl
@[isel_data] theorem term_670_kind : T.«br_table_impl».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_670_name : T.«br_table_impl».name = "br_table_impl" := rfl
@[isel_data] theorem term_686_kind : T.«lower».kind = (.decl ⟨false, false, true, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_686_name : T.«lower».name = "lower" := rfl
@[isel_data] theorem term_687_kind : T.«lower_branch».kind = (.decl ⟨false, false, true, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_687_name : T.«lower_branch».name = "lower_branch" := rfl
@[isel_data] theorem term_698_kind : T.«put_nonzero_in_reg».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_698_name : T.«put_nonzero_in_reg».name = "put_nonzero_in_reg" := rfl
@[isel_data] theorem term_699_kind : T.«aarch64_uload».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_699_name : T.«aarch64_uload».name = "aarch64_uload" := rfl
@[isel_data] theorem term_700_kind : T.«aarch64_sload».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_700_name : T.«aarch64_sload».name = "aarch64_sload" := rfl
@[isel_data] theorem term_702_kind : T.«shift_masked_imm».kind = (.decl ⟨true, false, false, false⟩ (some (.external "shift_masked_imm")) none) := rfl
@[isel_data] theorem term_702_name : T.«shift_masked_imm».name = "shift_masked_imm" := rfl
@[isel_data] theorem term_703_kind : T.«do_shift».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_703_name : T.«do_shift».name = "do_shift" := rfl
@[isel_data] theorem term_704_kind : T.«shift_mask».kind = (.decl ⟨false, false, false, false⟩ (some (.external "shift_mask")) none) := rfl
@[isel_data] theorem term_704_name : T.«shift_mask».name = "shift_mask" := rfl
@[isel_data] theorem term_706_kind : T.«bfm_immr».kind = (.decl ⟨false, false, false, false⟩ (some (.external "bfm_immr")) none) := rfl
@[isel_data] theorem term_706_name : T.«bfm_immr».name = "bfm_immr" := rfl
@[isel_data] theorem term_707_kind : T.«bfm_imms».kind = (.decl ⟨false, false, false, false⟩ (some (.external "bfm_imms")) none) := rfl
@[isel_data] theorem term_707_name : T.«bfm_imms».name = "bfm_imms" := rfl
@[isel_data] theorem term_709_kind : T.«negate_imm_shift».kind = (.decl ⟨false, false, false, false⟩ (some (.external "negate_imm_shift")) none) := rfl
@[isel_data] theorem term_709_name : T.«negate_imm_shift».name = "negate_imm_shift" := rfl
@[isel_data] theorem term_710_kind : T.«small_rotr».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_710_name : T.«small_rotr».name = "small_rotr" := rfl
@[isel_data] theorem term_711_kind : T.«rotr_mask».kind = (.decl ⟨false, false, false, false⟩ (some (.external "rotr_mask")) none) := rfl
@[isel_data] theorem term_711_name : T.«rotr_mask».name = "rotr_mask" := rfl
@[isel_data] theorem term_712_kind : T.«small_rotr_imm».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_712_name : T.«small_rotr_imm».name = "small_rotr_imm" := rfl
@[isel_data] theorem term_713_kind : T.«rotr_opposite_amount».kind = (.decl ⟨false, false, false, false⟩ (some (.external "rotr_opposite_amount")) none) := rfl
@[isel_data] theorem term_713_name : T.«rotr_opposite_amount».name = "rotr_opposite_amount" := rfl
@[isel_data] theorem term_715_kind : T.«lower_cond_result_bool».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_715_name : T.«lower_cond_result_bool».name = "lower_cond_result_bool" := rfl
@[isel_data] theorem term_722_kind : T.«br_cond_result».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[isel_data] theorem term_722_name : T.«br_cond_result».name = "br_cond_result" := rfl
@[isel_data] theorem term_723_kind : T.«test_and_compare_bit_const».kind = (.decl ⟨true, false, true, false⟩ (some (.external "test_and_compare_bit_const")) none) := rfl
@[isel_data] theorem term_723_name : T.«test_and_compare_bit_const».name = "test_and_compare_bit_const" := rfl
@[isel_data] theorem term_978_kind : T.«i32_checked_add».kind = (.decl ⟨true, false, true, false⟩ (some (.external "i32_checked_add")) none) := rfl
@[isel_data] theorem term_978_name : T.«i32_checked_add».name = "i32_checked_add" := rfl
@[isel_data] theorem term_1154_kind : T.«i64_checked_neg».kind = (.decl ⟨true, false, true, false⟩ (some (.external "i64_checked_neg")) none) := rfl
@[isel_data] theorem term_1154_name : T.«i64_checked_neg».name = "i64_checked_neg" := rfl
@[isel_data] theorem term_1157_kind : T.«u64_eq».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_eq")) none) := rfl
@[isel_data] theorem term_1157_name : T.«u64_eq».name = "u64_eq" := rfl
@[isel_data] theorem term_1161_kind : T.«u64_gt».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_gt")) none) := rfl
@[isel_data] theorem term_1161_name : T.«u64_gt».name = "u64_gt" := rfl
@[isel_data] theorem term_1164_kind : T.«u64_wrapping_add».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_wrapping_add")) none) := rfl
@[isel_data] theorem term_1164_name : T.«u64_wrapping_add».name = "u64_wrapping_add" := rfl
@[isel_data] theorem term_1167_kind : T.«u64_wrapping_sub».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_wrapping_sub")) none) := rfl
@[isel_data] theorem term_1167_name : T.«u64_wrapping_sub».name = "u64_wrapping_sub" := rfl
@[isel_data] theorem term_1182_kind : T.«u64_wrapping_shl».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_wrapping_shl")) none) := rfl
@[isel_data] theorem term_1182_name : T.«u64_wrapping_shl».name = "u64_wrapping_shl" := rfl
@[isel_data] theorem term_1199_kind : T.«u64_is_odd».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_is_odd")) none) := rfl
@[isel_data] theorem term_1199_name : T.«u64_is_odd».name = "u64_is_odd" := rfl
@[isel_data] theorem term_1378_kind : T.«u8_into_u32».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u8_into_u32")) none) := rfl
@[isel_data] theorem term_1378_name : T.«u8_into_u32».name = "u8_into_u32" := rfl
@[isel_data] theorem term_1382_kind : T.«u8_into_u64».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u8_into_u64")) none) := rfl
@[isel_data] theorem term_1382_name : T.«u8_into_u64».name = "u8_into_u64" := rfl
@[isel_data] theorem term_1431_kind : T.«u16_into_u64».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u16_into_u64")) none) := rfl
@[isel_data] theorem term_1431_name : T.«u16_into_u64».name = "u16_into_u64" := rfl
@[isel_data] theorem term_1455_kind : T.«i32_into_i64».kind = (.decl ⟨true, false, false, false⟩ (some (.external "i32_into_i64")) none) := rfl
@[isel_data] theorem term_1455_name : T.«i32_into_i64».name = "i32_into_i64" := rfl
@[isel_data] theorem term_1485_kind : T.«u32_into_u64».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u32_into_u64")) none) := rfl
@[isel_data] theorem term_1485_name : T.«u32_into_u64».name = "u32_into_u64" := rfl
@[isel_data] theorem term_1508_kind : T.«i32_from_i64».kind = (.decl ⟨true, false, false, false⟩ none (some (.external "i64_from_i32" false))) := rfl
@[isel_data] theorem term_1508_name : T.«i32_from_i64».name = "i32_from_i64" := rfl
@[isel_data] theorem term_1514_kind : T.«i64_cast_unsigned».kind = (.decl ⟨true, false, false, false⟩ (some (.external "i64_cast_unsigned")) none) := rfl
@[isel_data] theorem term_1514_name : T.«i64_cast_unsigned».name = "i64_cast_unsigned" := rfl
@[isel_data] theorem term_1527_kind : T.«u8_from_u64».kind = (.decl ⟨true, false, false, false⟩ none (some (.external "u64_from_u8" false))) := rfl
@[isel_data] theorem term_1527_name : T.«u8_from_u64».name = "u8_from_u64" := rfl
@[isel_data] theorem term_1614_kind : T.«value_array_2».kind = (.decl ⟨false, false, false, false⟩ (some (.external "pack_value_array_2")) (some (.external "unpack_value_array_2" true))) := rfl
@[isel_data] theorem term_1614_name : T.«value_array_2».name = "value_array_2" := rfl
@[isel_data] theorem term_1615_kind : T.«value_array_3».kind = (.decl ⟨false, false, false, false⟩ (some (.external "pack_value_array_3")) (some (.external "unpack_value_array_3" true))) := rfl
@[isel_data] theorem term_1615_name : T.«value_array_3».name = "value_array_3" := rfl
@[isel_data] theorem term_1616_kind : T.«block_array_2».kind = (.decl ⟨false, false, false, false⟩ (some (.external "pack_block_array_2")) (some (.external "unpack_block_array_2" true))) := rfl
@[isel_data] theorem term_1616_name : T.«block_array_2».name = "block_array_2" := rfl
@[isel_data] theorem term_1785_kind : T.«RelocDistance.Near».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_1785_name : T.«RelocDistance.Near».name = "RelocDistance.Near" := rfl
@[isel_data] theorem term_1786_kind : T.«RelocDistance.Far».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_1786_name : T.«RelocDistance.Far».name = "RelocDistance.Far" := rfl
@[isel_data] theorem term_1787_kind : T.«SideEffectNoResult.Inst».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_1787_name : T.«SideEffectNoResult.Inst».name = "SideEffectNoResult.Inst" := rfl
@[isel_data] theorem term_1788_kind : T.«SideEffectNoResult.Inst2».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_1788_name : T.«SideEffectNoResult.Inst2».name = "SideEffectNoResult.Inst2" := rfl
@[isel_data] theorem term_1789_kind : T.«SideEffectNoResult.Inst3».kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_1789_name : T.«SideEffectNoResult.Inst3».name = "SideEffectNoResult.Inst3" := rfl
@[isel_data] theorem term_1790_kind : T.«ProducesFlags.AlreadyExistingFlags».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_1790_name : T.«ProducesFlags.AlreadyExistingFlags».name = "ProducesFlags.AlreadyExistingFlags" := rfl
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
@[isel_data] theorem term_1827_kind : T.«MInst.BitRR».kind = (.enumVariant 9) := rfl
@[isel_data] theorem term_1827_name : T.«MInst.BitRR».name = "MInst.BitRR" := rfl
@[isel_data] theorem term_1828_kind : T.«MInst.ULoad8».kind = (.enumVariant 10) := rfl
@[isel_data] theorem term_1828_name : T.«MInst.ULoad8».name = "MInst.ULoad8" := rfl
@[isel_data] theorem term_1829_kind : T.«MInst.SLoad8».kind = (.enumVariant 11) := rfl
@[isel_data] theorem term_1829_name : T.«MInst.SLoad8».name = "MInst.SLoad8" := rfl
@[isel_data] theorem term_1830_kind : T.«MInst.ULoad16».kind = (.enumVariant 12) := rfl
@[isel_data] theorem term_1830_name : T.«MInst.ULoad16».name = "MInst.ULoad16" := rfl
@[isel_data] theorem term_1831_kind : T.«MInst.SLoad16».kind = (.enumVariant 13) := rfl
@[isel_data] theorem term_1831_name : T.«MInst.SLoad16».name = "MInst.SLoad16" := rfl
@[isel_data] theorem term_1832_kind : T.«MInst.ULoad32».kind = (.enumVariant 14) := rfl
@[isel_data] theorem term_1832_name : T.«MInst.ULoad32».name = "MInst.ULoad32" := rfl
@[isel_data] theorem term_1833_kind : T.«MInst.SLoad32».kind = (.enumVariant 15) := rfl
@[isel_data] theorem term_1833_name : T.«MInst.SLoad32».name = "MInst.SLoad32" := rfl
@[isel_data] theorem term_1834_kind : T.«MInst.ULoad64».kind = (.enumVariant 16) := rfl
@[isel_data] theorem term_1834_name : T.«MInst.ULoad64».name = "MInst.ULoad64" := rfl
@[isel_data] theorem term_1835_kind : T.«MInst.Store8».kind = (.enumVariant 17) := rfl
@[isel_data] theorem term_1835_name : T.«MInst.Store8».name = "MInst.Store8" := rfl
@[isel_data] theorem term_1836_kind : T.«MInst.Store16».kind = (.enumVariant 18) := rfl
@[isel_data] theorem term_1836_name : T.«MInst.Store16».name = "MInst.Store16" := rfl
@[isel_data] theorem term_1837_kind : T.«MInst.Store32».kind = (.enumVariant 19) := rfl
@[isel_data] theorem term_1837_name : T.«MInst.Store32».name = "MInst.Store32" := rfl
@[isel_data] theorem term_1838_kind : T.«MInst.Store64».kind = (.enumVariant 20) := rfl
@[isel_data] theorem term_1838_name : T.«MInst.Store64».name = "MInst.Store64" := rfl
@[isel_data] theorem term_1844_kind : T.«MInst.MovWide».kind = (.enumVariant 26) := rfl
@[isel_data] theorem term_1844_name : T.«MInst.MovWide».name = "MInst.MovWide" := rfl
@[isel_data] theorem term_1846_kind : T.«MInst.Extend».kind = (.enumVariant 28) := rfl
@[isel_data] theorem term_1846_name : T.«MInst.Extend».name = "MInst.Extend" := rfl
@[isel_data] theorem term_1847_kind : T.«MInst.BitfieldMove».kind = (.enumVariant 29) := rfl
@[isel_data] theorem term_1847_name : T.«MInst.BitfieldMove».name = "MInst.BitfieldMove" := rfl
@[isel_data] theorem term_1849_kind : T.«MInst.CSel».kind = (.enumVariant 31) := rfl
@[isel_data] theorem term_1849_name : T.«MInst.CSel».name = "MInst.CSel" := rfl
@[isel_data] theorem term_1851_kind : T.«MInst.CSet».kind = (.enumVariant 33) := rfl
@[isel_data] theorem term_1851_name : T.«MInst.CSet».name = "MInst.CSet" := rfl
@[isel_data] theorem term_1853_kind : T.«MInst.CCmp».kind = (.enumVariant 35) := rfl
@[isel_data] theorem term_1853_name : T.«MInst.CCmp».name = "MInst.CCmp" := rfl
@[isel_data] theorem term_1854_kind : T.«MInst.CCmpImm».kind = (.enumVariant 36) := rfl
@[isel_data] theorem term_1854_name : T.«MInst.CCmpImm».name = "MInst.CCmpImm" := rfl
@[isel_data] theorem term_1874_kind : T.«MInst.FpuCmp».kind = (.enumVariant 56) := rfl
@[isel_data] theorem term_1874_name : T.«MInst.FpuCmp».name = "MInst.FpuCmp" := rfl
@[isel_data] theorem term_1889_kind : T.«MInst.FpuCSel16».kind = (.enumVariant 71) := rfl
@[isel_data] theorem term_1889_name : T.«MInst.FpuCSel16».name = "MInst.FpuCSel16" := rfl
@[isel_data] theorem term_1890_kind : T.«MInst.FpuCSel32».kind = (.enumVariant 72) := rfl
@[isel_data] theorem term_1890_name : T.«MInst.FpuCSel32».name = "MInst.FpuCSel32" := rfl
@[isel_data] theorem term_1891_kind : T.«MInst.FpuCSel64».kind = (.enumVariant 73) := rfl
@[isel_data] theorem term_1891_name : T.«MInst.FpuCSel64».name = "MInst.FpuCSel64" := rfl
@[isel_data] theorem term_1893_kind : T.«MInst.MovToFpu».kind = (.enumVariant 75) := rfl
@[isel_data] theorem term_1893_name : T.«MInst.MovToFpu».name = "MInst.MovToFpu" := rfl
@[isel_data] theorem term_1896_kind : T.«MInst.MovFromVec».kind = (.enumVariant 78) := rfl
@[isel_data] theorem term_1896_name : T.«MInst.MovFromVec».name = "MInst.MovFromVec" := rfl
@[isel_data] theorem term_1911_kind : T.«MInst.VecRRR».kind = (.enumVariant 93) := rfl
@[isel_data] theorem term_1911_name : T.«MInst.VecRRR».name = "MInst.VecRRR" := rfl
@[isel_data] theorem term_1914_kind : T.«MInst.VecMisc».kind = (.enumVariant 96) := rfl
@[isel_data] theorem term_1914_name : T.«MInst.VecMisc».name = "MInst.VecMisc" := rfl
@[isel_data] theorem term_1915_kind : T.«MInst.VecLanes».kind = (.enumVariant 97) := rfl
@[isel_data] theorem term_1915_name : T.«MInst.VecLanes».name = "MInst.VecLanes" := rfl
@[isel_data] theorem term_1924_kind : T.«MInst.VecCSel».kind = (.enumVariant 106) := rfl
@[isel_data] theorem term_1924_name : T.«MInst.VecCSel».name = "MInst.VecCSel" := rfl
@[isel_data] theorem term_1927_kind : T.«MInst.Call».kind = (.enumVariant 109) := rfl
@[isel_data] theorem term_1927_name : T.«MInst.Call».name = "MInst.Call" := rfl
@[isel_data] theorem term_1928_kind : T.«MInst.CallInd».kind = (.enumVariant 110) := rfl
@[isel_data] theorem term_1928_name : T.«MInst.CallInd».name = "MInst.CallInd" := rfl
@[isel_data] theorem term_1935_kind : T.«MInst.Jump».kind = (.enumVariant 117) := rfl
@[isel_data] theorem term_1935_name : T.«MInst.Jump».name = "MInst.Jump" := rfl
@[isel_data] theorem term_1936_kind : T.«MInst.CondBr».kind = (.enumVariant 118) := rfl
@[isel_data] theorem term_1936_name : T.«MInst.CondBr».name = "MInst.CondBr" := rfl
@[isel_data] theorem term_1937_kind : T.«MInst.TestBitAndBranch».kind = (.enumVariant 119) := rfl
@[isel_data] theorem term_1937_name : T.«MInst.TestBitAndBranch».name = "MInst.TestBitAndBranch" := rfl
@[isel_data] theorem term_1938_kind : T.«MInst.TrapIf».kind = (.enumVariant 120) := rfl
@[isel_data] theorem term_1938_name : T.«MInst.TrapIf».name = "MInst.TrapIf" := rfl
@[isel_data] theorem term_1941_kind : T.«MInst.Udf».kind = (.enumVariant 123) := rfl
@[isel_data] theorem term_1941_name : T.«MInst.Udf».name = "MInst.Udf" := rfl
@[isel_data] theorem term_1946_kind : T.«MInst.JTSequence».kind = (.enumVariant 128) := rfl
@[isel_data] theorem term_1946_name : T.«MInst.JTSequence».name = "MInst.JTSequence" := rfl
@[isel_data] theorem term_1947_kind : T.«MInst.LoadExtNameGot».kind = (.enumVariant 129) := rfl
@[isel_data] theorem term_1947_name : T.«MInst.LoadExtNameGot».name = "MInst.LoadExtNameGot" := rfl
@[isel_data] theorem term_1948_kind : T.«MInst.LoadExtNameNear».kind = (.enumVariant 130) := rfl
@[isel_data] theorem term_1948_name : T.«MInst.LoadExtNameNear».name = "MInst.LoadExtNameNear" := rfl
@[isel_data] theorem term_1949_kind : T.«MInst.LoadExtNameFar».kind = (.enumVariant 131) := rfl
@[isel_data] theorem term_1949_name : T.«MInst.LoadExtNameFar».name = "MInst.LoadExtNameFar" := rfl
@[isel_data] theorem term_1954_kind : T.«MInst.EmitIsland».kind = (.enumVariant 136) := rfl
@[isel_data] theorem term_1954_name : T.«MInst.EmitIsland».name = "MInst.EmitIsland" := rfl
@[isel_data] theorem term_1962_kind : T.«ALUOp.Add».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_1962_name : T.«ALUOp.Add».name = "ALUOp.Add" := rfl
@[isel_data] theorem term_1963_kind : T.«ALUOp.Sub».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_1963_name : T.«ALUOp.Sub».name = "ALUOp.Sub" := rfl
@[isel_data] theorem term_1964_kind : T.«ALUOp.Orr».kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_1964_name : T.«ALUOp.Orr».name = "ALUOp.Orr" := rfl
@[isel_data] theorem term_1965_kind : T.«ALUOp.OrrNot».kind = (.enumVariant 3) := rfl
@[isel_data] theorem term_1965_name : T.«ALUOp.OrrNot».name = "ALUOp.OrrNot" := rfl
@[isel_data] theorem term_1966_kind : T.«ALUOp.And».kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_1966_name : T.«ALUOp.And».name = "ALUOp.And" := rfl
@[isel_data] theorem term_1967_kind : T.«ALUOp.AndS».kind = (.enumVariant 5) := rfl
@[isel_data] theorem term_1967_name : T.«ALUOp.AndS».name = "ALUOp.AndS" := rfl
@[isel_data] theorem term_1968_kind : T.«ALUOp.AndNot».kind = (.enumVariant 6) := rfl
@[isel_data] theorem term_1968_name : T.«ALUOp.AndNot».name = "ALUOp.AndNot" := rfl
@[isel_data] theorem term_1969_kind : T.«ALUOp.Eor».kind = (.enumVariant 7) := rfl
@[isel_data] theorem term_1969_name : T.«ALUOp.Eor».name = "ALUOp.Eor" := rfl
@[isel_data] theorem term_1970_kind : T.«ALUOp.EorNot».kind = (.enumVariant 8) := rfl
@[isel_data] theorem term_1970_name : T.«ALUOp.EorNot».name = "ALUOp.EorNot" := rfl
@[isel_data] theorem term_1971_kind : T.«ALUOp.AddS».kind = (.enumVariant 9) := rfl
@[isel_data] theorem term_1971_name : T.«ALUOp.AddS».name = "ALUOp.AddS" := rfl
@[isel_data] theorem term_1972_kind : T.«ALUOp.SubS».kind = (.enumVariant 10) := rfl
@[isel_data] theorem term_1972_name : T.«ALUOp.SubS».name = "ALUOp.SubS" := rfl
@[isel_data] theorem term_1973_kind : T.«ALUOp.SMulH».kind = (.enumVariant 11) := rfl
@[isel_data] theorem term_1973_name : T.«ALUOp.SMulH».name = "ALUOp.SMulH" := rfl
@[isel_data] theorem term_1974_kind : T.«ALUOp.UMulH».kind = (.enumVariant 12) := rfl
@[isel_data] theorem term_1974_name : T.«ALUOp.UMulH».name = "ALUOp.UMulH" := rfl
@[isel_data] theorem term_1975_kind : T.«ALUOp.SDiv».kind = (.enumVariant 13) := rfl
@[isel_data] theorem term_1975_name : T.«ALUOp.SDiv».name = "ALUOp.SDiv" := rfl
@[isel_data] theorem term_1976_kind : T.«ALUOp.UDiv».kind = (.enumVariant 14) := rfl
@[isel_data] theorem term_1976_name : T.«ALUOp.UDiv».name = "ALUOp.UDiv" := rfl
@[isel_data] theorem term_1977_kind : T.«ALUOp.Extr».kind = (.enumVariant 15) := rfl
@[isel_data] theorem term_1977_name : T.«ALUOp.Extr».name = "ALUOp.Extr" := rfl
@[isel_data] theorem term_1978_kind : T.«ALUOp.Lsr».kind = (.enumVariant 16) := rfl
@[isel_data] theorem term_1978_name : T.«ALUOp.Lsr».name = "ALUOp.Lsr" := rfl
@[isel_data] theorem term_1979_kind : T.«ALUOp.Asr».kind = (.enumVariant 17) := rfl
@[isel_data] theorem term_1979_name : T.«ALUOp.Asr».name = "ALUOp.Asr" := rfl
@[isel_data] theorem term_1980_kind : T.«ALUOp.Lsl».kind = (.enumVariant 18) := rfl
@[isel_data] theorem term_1980_name : T.«ALUOp.Lsl».name = "ALUOp.Lsl" := rfl
@[isel_data] theorem term_1984_kind : T.«ALUOp.SbcS».kind = (.enumVariant 22) := rfl
@[isel_data] theorem term_1984_name : T.«ALUOp.SbcS».name = "ALUOp.SbcS" := rfl
@[isel_data] theorem term_1985_kind : T.«ALUOp3.MAdd».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_1985_name : T.«ALUOp3.MAdd».name = "ALUOp3.MAdd" := rfl
@[isel_data] theorem term_1986_kind : T.«ALUOp3.MSub».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_1986_name : T.«ALUOp3.MSub».name = "ALUOp3.MSub" := rfl
@[isel_data] theorem term_1987_kind : T.«ALUOp3.UMAddL».kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_1987_name : T.«ALUOp3.UMAddL».name = "ALUOp3.UMAddL" := rfl
@[isel_data] theorem term_1988_kind : T.«ALUOp3.SMAddL».kind = (.enumVariant 3) := rfl
@[isel_data] theorem term_1988_name : T.«ALUOp3.SMAddL».name = "ALUOp3.SMAddL" := rfl
@[isel_data] theorem term_1989_kind : T.«MoveWideOp.MovZ».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_1989_name : T.«MoveWideOp.MovZ».name = "MoveWideOp.MovZ" := rfl
@[isel_data] theorem term_1990_kind : T.«MoveWideOp.MovN».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_1990_name : T.«MoveWideOp.MovN».name = "MoveWideOp.MovN" := rfl
@[isel_data] theorem term_1991_kind : T.«BfmOp.UBfm».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_1991_name : T.«BfmOp.UBfm».name = "BfmOp.UBfm" := rfl
@[isel_data] theorem term_1992_kind : T.«BfmOp.SBfm».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_1992_name : T.«BfmOp.SBfm».name = "BfmOp.SBfm" := rfl
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
@[isel_data] theorem term_2004_kind : T.«BitOp.RBit».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_2004_name : T.«BitOp.RBit».name = "BitOp.RBit" := rfl
@[isel_data] theorem term_2005_kind : T.«BitOp.Clz».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_2005_name : T.«BitOp.Clz».name = "BitOp.Clz" := rfl
@[isel_data] theorem term_2007_kind : T.«BitOp.Rev16».kind = (.enumVariant 3) := rfl
@[isel_data] theorem term_2007_name : T.«BitOp.Rev16».name = "BitOp.Rev16" := rfl
@[isel_data] theorem term_2008_kind : T.«BitOp.Rev32».kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_2008_name : T.«BitOp.Rev32».name = "BitOp.Rev32" := rfl
@[isel_data] theorem term_2009_kind : T.«BitOp.Rev64».kind = (.enumVariant 5) := rfl
@[isel_data] theorem term_2009_name : T.«BitOp.Rev64».name = "BitOp.Rev64" := rfl
@[isel_data] theorem term_2012_kind : T.«AMode.RegReg».kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_2012_name : T.«AMode.RegReg».name = "AMode.RegReg" := rfl
@[isel_data] theorem term_2013_kind : T.«AMode.RegScaled».kind = (.enumVariant 3) := rfl
@[isel_data] theorem term_2013_name : T.«AMode.RegScaled».name = "AMode.RegScaled" := rfl
@[isel_data] theorem term_2014_kind : T.«AMode.RegScaledExtended».kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_2014_name : T.«AMode.RegScaledExtended».name = "AMode.RegScaledExtended" := rfl
@[isel_data] theorem term_2015_kind : T.«AMode.RegExtended».kind = (.enumVariant 5) := rfl
@[isel_data] theorem term_2015_name : T.«AMode.RegExtended».name = "AMode.RegExtended" := rfl
@[isel_data] theorem term_2016_kind : T.«AMode.Unscaled».kind = (.enumVariant 6) := rfl
@[isel_data] theorem term_2016_name : T.«AMode.Unscaled».name = "AMode.Unscaled" := rfl
@[isel_data] theorem term_2017_kind : T.«AMode.UnsignedOffset».kind = (.enumVariant 7) := rfl
@[isel_data] theorem term_2017_name : T.«AMode.UnsignedOffset».name = "AMode.UnsignedOffset" := rfl
@[isel_data] theorem term_2024_kind : T.«AMode.SlotOffset».kind = (.enumVariant 14) := rfl
@[isel_data] theorem term_2024_name : T.«AMode.SlotOffset».name = "AMode.SlotOffset" := rfl
@[isel_data] theorem term_2028_kind : T.«OperandSize.Size32».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_2028_name : T.«OperandSize.Size32».name = "OperandSize.Size32" := rfl
@[isel_data] theorem term_2029_kind : T.«OperandSize.Size64».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_2029_name : T.«OperandSize.Size64».name = "OperandSize.Size64" := rfl
@[isel_data] theorem term_2030_kind : T.«TestBitAndBranchKind.Z».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_2030_name : T.«TestBitAndBranchKind.Z».name = "TestBitAndBranchKind.Z" := rfl
@[isel_data] theorem term_2031_kind : T.«TestBitAndBranchKind.NZ».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_2031_name : T.«TestBitAndBranchKind.NZ».name = "TestBitAndBranchKind.NZ" := rfl
@[isel_data] theorem term_2032_kind : T.«ScalarSize.Size8».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_2032_name : T.«ScalarSize.Size8».name = "ScalarSize.Size8" := rfl
@[isel_data] theorem term_2033_kind : T.«ScalarSize.Size16».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_2033_name : T.«ScalarSize.Size16».name = "ScalarSize.Size16" := rfl
@[isel_data] theorem term_2034_kind : T.«ScalarSize.Size32».kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_2034_name : T.«ScalarSize.Size32».name = "ScalarSize.Size32" := rfl
@[isel_data] theorem term_2035_kind : T.«ScalarSize.Size64».kind = (.enumVariant 3) := rfl
@[isel_data] theorem term_2035_name : T.«ScalarSize.Size64».name = "ScalarSize.Size64" := rfl
@[isel_data] theorem term_2036_kind : T.«ScalarSize.Size128».kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_2036_name : T.«ScalarSize.Size128».name = "ScalarSize.Size128" := rfl
@[isel_data] theorem term_2037_kind : T.«Cond.Eq».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_2037_name : T.«Cond.Eq».name = "Cond.Eq" := rfl
@[isel_data] theorem term_2038_kind : T.«Cond.Ne».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_2038_name : T.«Cond.Ne».name = "Cond.Ne" := rfl
@[isel_data] theorem term_2039_kind : T.«Cond.Hs».kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_2039_name : T.«Cond.Hs».name = "Cond.Hs" := rfl
@[isel_data] theorem term_2041_kind : T.«Cond.Mi».kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_2041_name : T.«Cond.Mi».name = "Cond.Mi" := rfl
@[isel_data] theorem term_2042_kind : T.«Cond.Pl».kind = (.enumVariant 5) := rfl
@[isel_data] theorem term_2042_name : T.«Cond.Pl».name = "Cond.Pl" := rfl
@[isel_data] theorem term_2043_kind : T.«Cond.Vs».kind = (.enumVariant 6) := rfl
@[isel_data] theorem term_2043_name : T.«Cond.Vs».name = "Cond.Vs" := rfl
@[isel_data] theorem term_2044_kind : T.«Cond.Vc».kind = (.enumVariant 7) := rfl
@[isel_data] theorem term_2044_name : T.«Cond.Vc».name = "Cond.Vc" := rfl
@[isel_data] theorem term_2045_kind : T.«Cond.Hi».kind = (.enumVariant 8) := rfl
@[isel_data] theorem term_2045_name : T.«Cond.Hi».name = "Cond.Hi" := rfl
@[isel_data] theorem term_2046_kind : T.«Cond.Ls».kind = (.enumVariant 9) := rfl
@[isel_data] theorem term_2046_name : T.«Cond.Ls».name = "Cond.Ls" := rfl
@[isel_data] theorem term_2047_kind : T.«Cond.Ge».kind = (.enumVariant 10) := rfl
@[isel_data] theorem term_2047_name : T.«Cond.Ge».name = "Cond.Ge" := rfl
@[isel_data] theorem term_2048_kind : T.«Cond.Lt».kind = (.enumVariant 11) := rfl
@[isel_data] theorem term_2048_name : T.«Cond.Lt».name = "Cond.Lt" := rfl
@[isel_data] theorem term_2049_kind : T.«Cond.Gt».kind = (.enumVariant 12) := rfl
@[isel_data] theorem term_2049_name : T.«Cond.Gt».name = "Cond.Gt" := rfl
@[isel_data] theorem term_2050_kind : T.«Cond.Le».kind = (.enumVariant 13) := rfl
@[isel_data] theorem term_2050_name : T.«Cond.Le».name = "Cond.Le" := rfl
@[isel_data] theorem term_2053_kind : T.«VectorSize.Size8x8».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_2053_name : T.«VectorSize.Size8x8».name = "VectorSize.Size8x8" := rfl
@[isel_data] theorem term_2054_kind : T.«VectorSize.Size8x16».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_2054_name : T.«VectorSize.Size8x16».name = "VectorSize.Size8x16" := rfl
@[isel_data] theorem term_2055_kind : T.«VectorSize.Size16x4».kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_2055_name : T.«VectorSize.Size16x4».name = "VectorSize.Size16x4" := rfl
@[isel_data] theorem term_2056_kind : T.«VectorSize.Size16x8».kind = (.enumVariant 3) := rfl
@[isel_data] theorem term_2056_name : T.«VectorSize.Size16x8».name = "VectorSize.Size16x8" := rfl
@[isel_data] theorem term_2057_kind : T.«VectorSize.Size32x2».kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_2057_name : T.«VectorSize.Size32x2».name = "VectorSize.Size32x2" := rfl
@[isel_data] theorem term_2058_kind : T.«VectorSize.Size32x4».kind = (.enumVariant 5) := rfl
@[isel_data] theorem term_2058_name : T.«VectorSize.Size32x4».name = "VectorSize.Size32x4" := rfl
@[isel_data] theorem term_2059_kind : T.«VectorSize.Size64x2».kind = (.enumVariant 6) := rfl
@[isel_data] theorem term_2059_name : T.«VectorSize.Size64x2».name = "VectorSize.Size64x2" := rfl
@[isel_data] theorem term_2124_kind : T.«VecALUOp.Umin».kind = (.enumVariant 23) := rfl
@[isel_data] theorem term_2124_name : T.«VecALUOp.Umin».name = "VecALUOp.Umin" := rfl
@[isel_data] theorem term_2125_kind : T.«VecALUOp.Smin».kind = (.enumVariant 24) := rfl
@[isel_data] theorem term_2125_name : T.«VecALUOp.Smin».name = "VecALUOp.Smin" := rfl
@[isel_data] theorem term_2126_kind : T.«VecALUOp.Umax».kind = (.enumVariant 25) := rfl
@[isel_data] theorem term_2126_name : T.«VecALUOp.Umax».name = "VecALUOp.Umax" := rfl
@[isel_data] theorem term_2127_kind : T.«VecALUOp.Smax».kind = (.enumVariant 26) := rfl
@[isel_data] theorem term_2127_name : T.«VecALUOp.Smax».name = "VecALUOp.Smax" := rfl
@[isel_data] theorem term_2135_kind : T.«VecALUOp.Addp».kind = (.enumVariant 34) := rfl
@[isel_data] theorem term_2135_name : T.«VecALUOp.Addp».name = "VecALUOp.Addp" := rfl
@[isel_data] theorem term_2165_kind : T.«VecMisc2.Cnt».kind = (.enumVariant 17) := rfl
@[isel_data] theorem term_2165_name : T.«VecMisc2.Cnt».name = "VecMisc2.Cnt" := rfl
@[isel_data] theorem term_2200_kind : T.«VecLanesOp.Addv».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_2200_name : T.«VecLanesOp.Addv».name = "VecLanesOp.Addv" := rfl
@[isel_data] theorem term_2234_kind : T.«ImmExtend.Sign».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_2234_name : T.«ImmExtend.Sign».name = "ImmExtend.Sign" := rfl
@[isel_data] theorem term_2235_kind : T.«ImmExtend.Zero».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_2235_name : T.«ImmExtend.Zero».name = "ImmExtend.Zero" := rfl
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
@[isel_data] theorem term_2242_kind : T.«ExtType.Signed».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_2242_name : T.«ExtType.Signed».name = "ExtType.Signed" := rfl
@[isel_data] theorem term_2243_kind : T.«ExtType.Unsigned».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_2243_name : T.«ExtType.Unsigned».name = "ExtType.Unsigned" := rfl
@[isel_data] theorem term_2255_kind : T.«FloatCC.Equal».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_2255_name : T.«FloatCC.Equal».name = "FloatCC.Equal" := rfl
@[isel_data] theorem term_2256_kind : T.«FloatCC.GreaterThan».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_2256_name : T.«FloatCC.GreaterThan».name = "FloatCC.GreaterThan" := rfl
@[isel_data] theorem term_2257_kind : T.«FloatCC.GreaterThanOrEqual».kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_2257_name : T.«FloatCC.GreaterThanOrEqual».name = "FloatCC.GreaterThanOrEqual" := rfl
@[isel_data] theorem term_2258_kind : T.«FloatCC.LessThan».kind = (.enumVariant 3) := rfl
@[isel_data] theorem term_2258_name : T.«FloatCC.LessThan».name = "FloatCC.LessThan" := rfl
@[isel_data] theorem term_2259_kind : T.«FloatCC.LessThanOrEqual».kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_2259_name : T.«FloatCC.LessThanOrEqual».name = "FloatCC.LessThanOrEqual" := rfl
@[isel_data] theorem term_2260_kind : T.«FloatCC.NotEqual».kind = (.enumVariant 5) := rfl
@[isel_data] theorem term_2260_name : T.«FloatCC.NotEqual».name = "FloatCC.NotEqual" := rfl
@[isel_data] theorem term_2261_kind : T.«FloatCC.Ordered».kind = (.enumVariant 6) := rfl
@[isel_data] theorem term_2261_name : T.«FloatCC.Ordered».name = "FloatCC.Ordered" := rfl
@[isel_data] theorem term_2262_kind : T.«FloatCC.OrderedNotEqual».kind = (.enumVariant 7) := rfl
@[isel_data] theorem term_2262_name : T.«FloatCC.OrderedNotEqual».name = "FloatCC.OrderedNotEqual" := rfl
@[isel_data] theorem term_2263_kind : T.«FloatCC.Unordered».kind = (.enumVariant 8) := rfl
@[isel_data] theorem term_2263_name : T.«FloatCC.Unordered».name = "FloatCC.Unordered" := rfl
@[isel_data] theorem term_2264_kind : T.«FloatCC.UnorderedOrEqual».kind = (.enumVariant 9) := rfl
@[isel_data] theorem term_2264_name : T.«FloatCC.UnorderedOrEqual».name = "FloatCC.UnorderedOrEqual" := rfl
@[isel_data] theorem term_2265_kind : T.«FloatCC.UnorderedOrGreaterThan».kind = (.enumVariant 10) := rfl
@[isel_data] theorem term_2265_name : T.«FloatCC.UnorderedOrGreaterThan».name = "FloatCC.UnorderedOrGreaterThan" := rfl
@[isel_data] theorem term_2266_kind : T.«FloatCC.UnorderedOrGreaterThanOrEqual».kind = (.enumVariant 11) := rfl
@[isel_data] theorem term_2266_name : T.«FloatCC.UnorderedOrGreaterThanOrEqual».name = "FloatCC.UnorderedOrGreaterThanOrEqual" := rfl
@[isel_data] theorem term_2267_kind : T.«FloatCC.UnorderedOrLessThan».kind = (.enumVariant 12) := rfl
@[isel_data] theorem term_2267_name : T.«FloatCC.UnorderedOrLessThan».name = "FloatCC.UnorderedOrLessThan" := rfl
@[isel_data] theorem term_2268_kind : T.«FloatCC.UnorderedOrLessThanOrEqual».kind = (.enumVariant 13) := rfl
@[isel_data] theorem term_2268_name : T.«FloatCC.UnorderedOrLessThanOrEqual».name = "FloatCC.UnorderedOrLessThanOrEqual" := rfl
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
@[isel_data] theorem term_2284_kind : T.«Opcode.Jump».kind = (.enumVariant 0) := rfl
@[isel_data] theorem term_2284_name : T.«Opcode.Jump».name = "Opcode.Jump" := rfl
@[isel_data] theorem term_2285_kind : T.«Opcode.Brif».kind = (.enumVariant 1) := rfl
@[isel_data] theorem term_2285_name : T.«Opcode.Brif».name = "Opcode.Brif" := rfl
@[isel_data] theorem term_2286_kind : T.«Opcode.BrTable».kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_2286_name : T.«Opcode.BrTable».name = "Opcode.BrTable" := rfl
@[isel_data] theorem term_2288_kind : T.«Opcode.Trap».kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_2288_name : T.«Opcode.Trap».name = "Opcode.Trap" := rfl
@[isel_data] theorem term_2291_kind : T.«Opcode.Return».kind = (.enumVariant 7) := rfl
@[isel_data] theorem term_2291_name : T.«Opcode.Return».name = "Opcode.Return" := rfl
@[isel_data] theorem term_2292_kind : T.«Opcode.Call».kind = (.enumVariant 8) := rfl
@[isel_data] theorem term_2292_name : T.«Opcode.Call».name = "Opcode.Call" := rfl
@[isel_data] theorem term_2304_kind : T.«Opcode.Smin».kind = (.enumVariant 20) := rfl
@[isel_data] theorem term_2304_name : T.«Opcode.Smin».name = "Opcode.Smin" := rfl
@[isel_data] theorem term_2305_kind : T.«Opcode.Umin».kind = (.enumVariant 21) := rfl
@[isel_data] theorem term_2305_name : T.«Opcode.Umin».name = "Opcode.Umin" := rfl
@[isel_data] theorem term_2306_kind : T.«Opcode.Smax».kind = (.enumVariant 22) := rfl
@[isel_data] theorem term_2306_name : T.«Opcode.Smax».name = "Opcode.Smax" := rfl
@[isel_data] theorem term_2307_kind : T.«Opcode.Umax».kind = (.enumVariant 23) := rfl
@[isel_data] theorem term_2307_name : T.«Opcode.Umax».name = "Opcode.Umax" := rfl
@[isel_data] theorem term_2313_kind : T.«Opcode.Load».kind = (.enumVariant 29) := rfl
@[isel_data] theorem term_2313_name : T.«Opcode.Load».name = "Opcode.Load" := rfl
@[isel_data] theorem term_2314_kind : T.«Opcode.Store».kind = (.enumVariant 30) := rfl
@[isel_data] theorem term_2314_name : T.«Opcode.Store».name = "Opcode.Store" := rfl
@[isel_data] theorem term_2315_kind : T.«Opcode.Uload8».kind = (.enumVariant 31) := rfl
@[isel_data] theorem term_2315_name : T.«Opcode.Uload8».name = "Opcode.Uload8" := rfl
@[isel_data] theorem term_2316_kind : T.«Opcode.Sload8».kind = (.enumVariant 32) := rfl
@[isel_data] theorem term_2316_name : T.«Opcode.Sload8».name = "Opcode.Sload8" := rfl
@[isel_data] theorem term_2317_kind : T.«Opcode.Istore8».kind = (.enumVariant 33) := rfl
@[isel_data] theorem term_2317_name : T.«Opcode.Istore8».name = "Opcode.Istore8" := rfl
@[isel_data] theorem term_2318_kind : T.«Opcode.Uload16».kind = (.enumVariant 34) := rfl
@[isel_data] theorem term_2318_name : T.«Opcode.Uload16».name = "Opcode.Uload16" := rfl
@[isel_data] theorem term_2319_kind : T.«Opcode.Sload16».kind = (.enumVariant 35) := rfl
@[isel_data] theorem term_2319_name : T.«Opcode.Sload16».name = "Opcode.Sload16" := rfl
@[isel_data] theorem term_2320_kind : T.«Opcode.Istore16».kind = (.enumVariant 36) := rfl
@[isel_data] theorem term_2320_name : T.«Opcode.Istore16».name = "Opcode.Istore16" := rfl
@[isel_data] theorem term_2321_kind : T.«Opcode.Uload32».kind = (.enumVariant 37) := rfl
@[isel_data] theorem term_2321_name : T.«Opcode.Uload32».name = "Opcode.Uload32" := rfl
@[isel_data] theorem term_2322_kind : T.«Opcode.Sload32».kind = (.enumVariant 38) := rfl
@[isel_data] theorem term_2322_name : T.«Opcode.Sload32».name = "Opcode.Sload32" := rfl
@[isel_data] theorem term_2323_kind : T.«Opcode.Istore32».kind = (.enumVariant 39) := rfl
@[isel_data] theorem term_2323_name : T.«Opcode.Istore32».name = "Opcode.Istore32" := rfl
@[isel_data] theorem term_2331_kind : T.«Opcode.StackAddr».kind = (.enumVariant 47) := rfl
@[isel_data] theorem term_2331_name : T.«Opcode.StackAddr».name = "Opcode.StackAddr" := rfl
@[isel_data] theorem term_2333_kind : T.«Opcode.SymbolValue».kind = (.enumVariant 49) := rfl
@[isel_data] theorem term_2333_name : T.«Opcode.SymbolValue».name = "Opcode.SymbolValue" := rfl
@[isel_data] theorem term_2341_kind : T.«Opcode.Iconst».kind = (.enumVariant 57) := rfl
@[isel_data] theorem term_2341_name : T.«Opcode.Iconst».name = "Opcode.Iconst" := rfl
@[isel_data] theorem term_2348_kind : T.«Opcode.Nop».kind = (.enumVariant 64) := rfl
@[isel_data] theorem term_2348_name : T.«Opcode.Nop».name = "Opcode.Nop" := rfl
@[isel_data] theorem term_2349_kind : T.«Opcode.Select».kind = (.enumVariant 65) := rfl
@[isel_data] theorem term_2349_name : T.«Opcode.Select».name = "Opcode.Select" := rfl
@[isel_data] theorem term_2356_kind : T.«Opcode.Icmp».kind = (.enumVariant 72) := rfl
@[isel_data] theorem term_2356_name : T.«Opcode.Icmp».name = "Opcode.Icmp" := rfl
@[isel_data] theorem term_2357_kind : T.«Opcode.Iadd».kind = (.enumVariant 73) := rfl
@[isel_data] theorem term_2357_name : T.«Opcode.Iadd».name = "Opcode.Iadd" := rfl
@[isel_data] theorem term_2358_kind : T.«Opcode.Isub».kind = (.enumVariant 74) := rfl
@[isel_data] theorem term_2358_name : T.«Opcode.Isub».name = "Opcode.Isub" := rfl
@[isel_data] theorem term_2359_kind : T.«Opcode.Ineg».kind = (.enumVariant 75) := rfl
@[isel_data] theorem term_2359_name : T.«Opcode.Ineg».name = "Opcode.Ineg" := rfl
@[isel_data] theorem term_2361_kind : T.«Opcode.Imul».kind = (.enumVariant 77) := rfl
@[isel_data] theorem term_2361_name : T.«Opcode.Imul».name = "Opcode.Imul" := rfl
@[isel_data] theorem term_2362_kind : T.«Opcode.Umulhi».kind = (.enumVariant 78) := rfl
@[isel_data] theorem term_2362_name : T.«Opcode.Umulhi».name = "Opcode.Umulhi" := rfl
@[isel_data] theorem term_2363_kind : T.«Opcode.Smulhi».kind = (.enumVariant 79) := rfl
@[isel_data] theorem term_2363_name : T.«Opcode.Smulhi».name = "Opcode.Smulhi" := rfl
@[isel_data] theorem term_2366_kind : T.«Opcode.Udiv».kind = (.enumVariant 82) := rfl
@[isel_data] theorem term_2366_name : T.«Opcode.Udiv».name = "Opcode.Udiv" := rfl
@[isel_data] theorem term_2367_kind : T.«Opcode.Sdiv».kind = (.enumVariant 83) := rfl
@[isel_data] theorem term_2367_name : T.«Opcode.Sdiv».name = "Opcode.Sdiv" := rfl
@[isel_data] theorem term_2368_kind : T.«Opcode.Urem».kind = (.enumVariant 84) := rfl
@[isel_data] theorem term_2368_name : T.«Opcode.Urem».name = "Opcode.Urem" := rfl
@[isel_data] theorem term_2369_kind : T.«Opcode.Srem».kind = (.enumVariant 85) := rfl
@[isel_data] theorem term_2369_name : T.«Opcode.Srem».name = "Opcode.Srem" := rfl
@[isel_data] theorem term_2372_kind : T.«Opcode.UaddOverflow».kind = (.enumVariant 88) := rfl
@[isel_data] theorem term_2372_name : T.«Opcode.UaddOverflow».name = "Opcode.UaddOverflow" := rfl
@[isel_data] theorem term_2376_kind : T.«Opcode.UmulOverflow».kind = (.enumVariant 92) := rfl
@[isel_data] theorem term_2376_name : T.«Opcode.UmulOverflow».name = "Opcode.UmulOverflow" := rfl
@[isel_data] theorem term_2377_kind : T.«Opcode.SmulOverflow».kind = (.enumVariant 93) := rfl
@[isel_data] theorem term_2377_name : T.«Opcode.SmulOverflow».name = "Opcode.SmulOverflow" := rfl
@[isel_data] theorem term_2381_kind : T.«Opcode.Band».kind = (.enumVariant 97) := rfl
@[isel_data] theorem term_2381_name : T.«Opcode.Band».name = "Opcode.Band" := rfl
@[isel_data] theorem term_2382_kind : T.«Opcode.Bor».kind = (.enumVariant 98) := rfl
@[isel_data] theorem term_2382_name : T.«Opcode.Bor».name = "Opcode.Bor" := rfl
@[isel_data] theorem term_2383_kind : T.«Opcode.Bxor».kind = (.enumVariant 99) := rfl
@[isel_data] theorem term_2383_name : T.«Opcode.Bxor».name = "Opcode.Bxor" := rfl
@[isel_data] theorem term_2384_kind : T.«Opcode.Bnot».kind = (.enumVariant 100) := rfl
@[isel_data] theorem term_2384_name : T.«Opcode.Bnot».name = "Opcode.Bnot" := rfl
@[isel_data] theorem term_2385_kind : T.«Opcode.Rotl».kind = (.enumVariant 101) := rfl
@[isel_data] theorem term_2385_name : T.«Opcode.Rotl».name = "Opcode.Rotl" := rfl
@[isel_data] theorem term_2386_kind : T.«Opcode.Rotr».kind = (.enumVariant 102) := rfl
@[isel_data] theorem term_2386_name : T.«Opcode.Rotr».name = "Opcode.Rotr" := rfl
@[isel_data] theorem term_2387_kind : T.«Opcode.Ishl».kind = (.enumVariant 103) := rfl
@[isel_data] theorem term_2387_name : T.«Opcode.Ishl».name = "Opcode.Ishl" := rfl
@[isel_data] theorem term_2388_kind : T.«Opcode.Ushr».kind = (.enumVariant 104) := rfl
@[isel_data] theorem term_2388_name : T.«Opcode.Ushr».name = "Opcode.Ushr" := rfl
@[isel_data] theorem term_2389_kind : T.«Opcode.Sshr».kind = (.enumVariant 105) := rfl
@[isel_data] theorem term_2389_name : T.«Opcode.Sshr».name = "Opcode.Sshr" := rfl
@[isel_data] theorem term_2390_kind : T.«Opcode.Bitrev».kind = (.enumVariant 106) := rfl
@[isel_data] theorem term_2390_name : T.«Opcode.Bitrev».name = "Opcode.Bitrev" := rfl
@[isel_data] theorem term_2391_kind : T.«Opcode.Clz».kind = (.enumVariant 107) := rfl
@[isel_data] theorem term_2391_name : T.«Opcode.Clz».name = "Opcode.Clz" := rfl
@[isel_data] theorem term_2393_kind : T.«Opcode.Ctz».kind = (.enumVariant 109) := rfl
@[isel_data] theorem term_2393_name : T.«Opcode.Ctz».name = "Opcode.Ctz" := rfl
@[isel_data] theorem term_2394_kind : T.«Opcode.Bswap».kind = (.enumVariant 110) := rfl
@[isel_data] theorem term_2394_name : T.«Opcode.Bswap».name = "Opcode.Bswap" := rfl
@[isel_data] theorem term_2395_kind : T.«Opcode.Popcnt».kind = (.enumVariant 111) := rfl
@[isel_data] theorem term_2395_name : T.«Opcode.Popcnt».name = "Opcode.Popcnt" := rfl
@[isel_data] theorem term_2396_kind : T.«Opcode.Fcmp».kind = (.enumVariant 112) := rfl
@[isel_data] theorem term_2396_name : T.«Opcode.Fcmp».name = "Opcode.Fcmp" := rfl
@[isel_data] theorem term_2415_kind : T.«Opcode.Ireduce».kind = (.enumVariant 131) := rfl
@[isel_data] theorem term_2415_name : T.«Opcode.Ireduce».name = "Opcode.Ireduce" := rfl
@[isel_data] theorem term_2425_kind : T.«Opcode.Uextend».kind = (.enumVariant 141) := rfl
@[isel_data] theorem term_2425_name : T.«Opcode.Uextend».name = "Opcode.Uextend" := rfl
@[isel_data] theorem term_2426_kind : T.«Opcode.Sextend».kind = (.enumVariant 142) := rfl
@[isel_data] theorem term_2426_name : T.«Opcode.Sextend».name = "Opcode.Sextend" := rfl
@[isel_data] theorem term_2449_kind : T.«InstructionData.Binary».kind = (.enumVariant 2) := rfl
@[isel_data] theorem term_2449_name : T.«InstructionData.Binary».name = "InstructionData.Binary" := rfl
@[isel_data] theorem term_2451_kind : T.«InstructionData.BranchTable».kind = (.enumVariant 4) := rfl
@[isel_data] theorem term_2451_name : T.«InstructionData.BranchTable».name = "InstructionData.BranchTable" := rfl
@[isel_data] theorem term_2452_kind : T.«InstructionData.Brif».kind = (.enumVariant 5) := rfl
@[isel_data] theorem term_2452_name : T.«InstructionData.Brif».name = "InstructionData.Brif" := rfl
@[isel_data] theorem term_2453_kind : T.«InstructionData.Call».kind = (.enumVariant 6) := rfl
@[isel_data] theorem term_2453_name : T.«InstructionData.Call».name = "InstructionData.Call" := rfl
@[isel_data] theorem term_2458_kind : T.«InstructionData.FloatCompare».kind = (.enumVariant 11) := rfl
@[isel_data] theorem term_2458_name : T.«InstructionData.FloatCompare».name = "InstructionData.FloatCompare" := rfl
@[isel_data] theorem term_2461_kind : T.«InstructionData.IntCompare».kind = (.enumVariant 14) := rfl
@[isel_data] theorem term_2461_name : T.«InstructionData.IntCompare».name = "InstructionData.IntCompare" := rfl
@[isel_data] theorem term_2462_kind : T.«InstructionData.Jump».kind = (.enumVariant 15) := rfl
@[isel_data] theorem term_2462_name : T.«InstructionData.Jump».name = "InstructionData.Jump" := rfl
@[isel_data] theorem term_2463_kind : T.«InstructionData.Load».kind = (.enumVariant 16) := rfl
@[isel_data] theorem term_2463_name : T.«InstructionData.Load».name = "InstructionData.Load" := rfl
@[isel_data] theorem term_2465_kind : T.«InstructionData.MultiAry».kind = (.enumVariant 18) := rfl
@[isel_data] theorem term_2465_name : T.«InstructionData.MultiAry».name = "InstructionData.MultiAry" := rfl
@[isel_data] theorem term_2466_kind : T.«InstructionData.NullAry».kind = (.enumVariant 19) := rfl
@[isel_data] theorem term_2466_name : T.«InstructionData.NullAry».name = "InstructionData.NullAry" := rfl
@[isel_data] theorem term_2468_kind : T.«InstructionData.StackAddr».kind = (.enumVariant 21) := rfl
@[isel_data] theorem term_2468_name : T.«InstructionData.StackAddr».name = "InstructionData.StackAddr" := rfl
@[isel_data] theorem term_2469_kind : T.«InstructionData.Store».kind = (.enumVariant 22) := rfl
@[isel_data] theorem term_2469_name : T.«InstructionData.Store».name = "InstructionData.Store" := rfl
@[isel_data] theorem term_2471_kind : T.«InstructionData.Ternary».kind = (.enumVariant 24) := rfl
@[isel_data] theorem term_2471_name : T.«InstructionData.Ternary».name = "InstructionData.Ternary" := rfl
@[isel_data] theorem term_2473_kind : T.«InstructionData.Trap».kind = (.enumVariant 26) := rfl
@[isel_data] theorem term_2473_name : T.«InstructionData.Trap».name = "InstructionData.Trap" := rfl
@[isel_data] theorem term_2476_kind : T.«InstructionData.Unary».kind = (.enumVariant 29) := rfl
@[isel_data] theorem term_2476_name : T.«InstructionData.Unary».name = "InstructionData.Unary" := rfl
@[isel_data] theorem term_2478_kind : T.«InstructionData.UnaryGlobalValue».kind = (.enumVariant 31) := rfl
@[isel_data] theorem term_2478_name : T.«InstructionData.UnaryGlobalValue».name = "InstructionData.UnaryGlobalValue" := rfl
@[isel_data] theorem term_2482_kind : T.«InstructionData.UnaryImm».kind = (.enumVariant 35) := rfl
@[isel_data] theorem term_2482_name : T.«InstructionData.UnaryImm».name = "InstructionData.UnaryImm" := rfl

/-- The facts about the exported program that the isel proofs use. Proofs are stated for an
arbitrary `p : Program` with `Data p`, never for `Isle.Aarch64.program` itself, so the kernel
cannot unfold the program data while checking them; `data_program` instantiates. -/
structure Data (p : Program) : Prop where
  t1 : Interp.termOf p 1 = pure T.«def_inst»
  t2 : Interp.termOf p 2 = pure T.«value_type»
  t31 : Interp.termOf p 31 = pure T.«i64_sextend_imm64»
  t87 : Interp.termOf p 87 = pure T.«ty_bits»
  t93 : Interp.termOf p 93 = pure T.«ty_bytes»
  t103 : Interp.termOf p 103 = pure T.«little_or_native_endian»
  t110 : Interp.termOf p 110 = pure T.«fits_in_16»
  t111 : Interp.termOf p 111 = pure T.«fits_in_32»
  t113 : Interp.termOf p 113 = pure T.«fits_in_64»
  t118 : Interp.termOf p 118 = pure T.«ty_int_ref_scalar_64»
  t119 : Interp.termOf p 119 = pure T.«ty_int_ref_scalar_64_extract»
  t120 : Interp.termOf p 120 = pure T.«ty_32_or_64»
  t126 : Interp.termOf p 126 = pure T.«ty_int»
  t128 : Interp.termOf p 128 = pure T.«ty_scalar_float»
  t132 : Interp.termOf p 132 = pure T.«ty_vec64»
  t133 : Interp.termOf p 133 = pure T.«ty_vec128»
  t141 : Interp.termOf p 141 = pure T.«not_i64x2»
  t144 : Interp.termOf p 144 = pure T.«u64_from_imm64»
  t145 : Interp.termOf p 145 = pure T.«nonzero_u64_from_imm64»
  t152 : Interp.termOf p 152 = pure T.«multi_lane»
  t153 : Interp.termOf p 153 = pure T.«dynamic_lane»
  t156 : Interp.termOf p 156 = pure T.«offset32_to_i32»
  t157 : Interp.termOf p 157 = pure T.«i32_to_offset32»
  t159 : Interp.termOf p 159 = pure T.«signed_cond_code»
  t160 : Interp.termOf p 160 = pure T.«unsigned_cond_code»
  t161 : Interp.termOf p 161 = pure T.«trap_code_division_by_zero»
  t162 : Interp.termOf p 162 = pure T.«trap_code_integer_overflow»
  t164 : Interp.termOf p 164 = pure T.«value_reg»
  t166 : Interp.termOf p 166 = pure T.«value_regs»
  t169 : Interp.termOf p 169 = pure T.«output_none»
  t170 : Interp.termOf p 170 = pure T.«output»
  t172 : Interp.termOf p 172 = pure T.«output_reg»
  r172 : p.rulesOf 172 =
    [rule_prelude_lower_105]
  t174 : Interp.termOf p 174 = pure T.«output_vec»
  t175 : Interp.termOf p 175 = pure T.«temp_writable_reg»
  t178 : Interp.termOf p 178 = pure T.«invalid_reg»
  t181 : Interp.termOf p 181 = pure T.«opportunistic_def»
  t182 : Interp.termOf p 182 = pure T.«put_in_reg»
  t183 : Interp.termOf p 183 = pure T.«put_in_regs»
  t184 : Interp.termOf p 184 = pure T.«put_in_regs_vec»
  t185 : Interp.termOf p 185 = pure T.«value_regs_get»
  t190 : Interp.termOf p 190 = pure T.«single_target»
  t191 : Interp.termOf p 191 = pure T.«two_targets»
  t192 : Interp.termOf p 192 = pure T.«jump_table_targets»
  t193 : Interp.termOf p 193 = pure T.«jump_table_size»
  t194 : Interp.termOf p 194 = pure T.«value_list_slice»
  t201 : Interp.termOf p 201 = pure T.«writable_reg_to_reg»
  t205 : Interp.termOf p 205 = pure T.«first_result»
  t207 : Interp.termOf p 207 = pure T.«is_second_result»
  t209 : Interp.termOf p 209 = pure T.«inst_data_value»
  t219 : Interp.termOf p 219 = pure T.«i64_from_iconst»
  t221 : Interp.termOf p 221 = pure T.«is_sinkable_inst»
  t222 : Interp.termOf p 222 = pure T.«maybe_uextend»
  t235 : Interp.termOf p 235 = pure T.«emit»
  t236 : Interp.termOf p 236 = pure T.«sink_inst»
  t242 : Interp.termOf p 242 = pure T.«emit_side_effect»
  r242 : p.rulesOf 242 =
    [rule_prelude_lower_522, rule_prelude_lower_524, rule_prelude_lower_527]
  t243 : Interp.termOf p 243 = pure T.«side_effect»
  r243 : p.rulesOf 243 =
    [rule_prelude_lower_535]
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
  t256 : Interp.termOf p 256 = pure T.«with_flags_side_effect»
  r256 : p.rulesOf 256 =
    [rule_prelude_lower_1000, rule_prelude_lower_1006, rule_prelude_lower_1016, rule_prelude_lower_1023, rule_prelude_lower_1030, rule_prelude_lower_1035, rule_prelude_lower_1040, rule_prelude_lower_1045, rule_prelude_lower_1050]
  t264 : Interp.termOf p 264 = pure T.«box_external_name»
  t265 : Interp.termOf p 265 = pure T.«func_ref_data»
  t267 : Interp.termOf p 267 = pure T.«symbol_value_data»
  t278 : Interp.termOf p 278 = pure T.«abi_sig»
  t286 : Interp.termOf p 286 = pure T.«abi_stackslot_addr»
  t287 : Interp.termOf p 287 = pure T.«abi_stackslot_offset_into_slot_region»
  t294 : Interp.termOf p 294 = pure T.«lower_return»
  r294 : p.rulesOf 294 =
    [rule_prelude_lower_1493]
  t295 : Interp.termOf p 295 = pure T.«gen_return»
  t296 : Interp.termOf p 296 = pure T.«gen_call_output»
  t297 : Interp.termOf p 297 = pure T.«gen_call_args»
  t299 : Interp.termOf p 299 = pure T.«gen_call_rets»
  t303 : Interp.termOf p 303 = pure T.«try_call_none»
  t304 : Interp.termOf p 304 = pure T.«safe_divisor_from_imm64»
  t305 : Interp.termOf p 305 = pure T.«operand_size»
  r305 : p.rulesOf 305 =
    [rule_inst_1592, rule_inst_1593]
  t306 : Interp.termOf p 306 = pure T.«diff_from_32»
  r306 : p.rulesOf 306 =
    [rule_inst_1599, rule_inst_1600]
  t307 : Interp.termOf p 307 = pure T.«scalar_size»
  r307 : p.rulesOf 307 =
    [rule_inst_1623, rule_inst_1624, rule_inst_1625, rule_inst_1626, rule_inst_1627, rule_inst_1629, rule_inst_1630, rule_inst_1631]
  t310 : Interp.termOf p 310 = pure T.«vector_size»
  r310 : p.rulesOf 310 =
    [rule_inst_1690, rule_inst_1691, rule_inst_1692, rule_inst_1693, rule_inst_1694, rule_inst_1695, rule_inst_1696, rule_inst_1697, rule_inst_1698, rule_inst_1699, rule_inst_1700, rule_inst_1701, rule_inst_1702, rule_inst_1703]
  t316 : Interp.termOf p 316 = pure T.«use_fp16»
  t318 : Interp.termOf p 318 = pure T.«move_wide_const_from_u64»
  t319 : Interp.termOf p 319 = pure T.«move_wide_const_from_inverted_u64»
  t320 : Interp.termOf p 320 = pure T.«imm_logic_from_u64»
  t321 : Interp.termOf p 321 = pure T.«imm_size_from_type»
  t322 : Interp.termOf p 322 = pure T.«imm_logic_from_imm64»
  t323 : Interp.termOf p 323 = pure T.«imm_shift_from_imm64»
  t324 : Interp.termOf p 324 = pure T.«imm_shift_from_u8»
  t325 : Interp.termOf p 325 = pure T.«imm12_from_u64»
  t326 : Interp.termOf p 326 = pure T.«u8_into_uimm5»
  t327 : Interp.termOf p 327 = pure T.«u8_into_imm12»
  t328 : Interp.termOf p 328 = pure T.«u64_into_imm_logic»
  t329 : Interp.termOf p 329 = pure T.«branch_target»
  t330 : Interp.termOf p 330 = pure T.«targets_jt_space»
  t336 : Interp.termOf p 336 = pure T.«lshl_from_imm64»
  t338 : Interp.termOf p 338 = pure T.«ashr_from_u64»
  t339 : Interp.termOf p 339 = pure T.«integral_ty»
  t344 : Interp.termOf p 344 = pure T.«imm12_from_negated_value»
  r344 : p.rulesOf 344 =
    [rule_inst_2404]
  t345 : Interp.termOf p 345 = pure T.«extended_value_from_value»
  t346 : Interp.termOf p 346 = pure T.«put_extended_in_reg»
  t347 : Interp.termOf p 347 = pure T.«get_extended_op»
  t348 : Interp.termOf p 348 = pure T.«nzcv»
  t349 : Interp.termOf p 349 = pure T.«cond_br_zero»
  t350 : Interp.termOf p 350 = pure T.«cond_br_not_zero»
  t351 : Interp.termOf p 351 = pure T.«cond_br_cond»
  t352 : Interp.termOf p 352 = pure T.«zero_reg»
  t356 : Interp.termOf p 356 = pure T.«writable_zero_reg»
  t358 : Interp.termOf p 358 = pure T.«movz»
  r358 : p.rulesOf 358 =
    [rule_inst_2513]
  t359 : Interp.termOf p 359 = pure T.«movn»
  r359 : p.rulesOf 359 =
    [rule_inst_2521]
  t360 : Interp.termOf p 360 = pure T.«alu_rr_imm_logic»
  r360 : p.rulesOf 360 =
    [rule_inst_2529]
  t361 : Interp.termOf p 361 = pure T.«alu_rr_imm_shift»
  r361 : p.rulesOf 361 =
    [rule_inst_2537]
  t362 : Interp.termOf p 362 = pure T.«alu_rrr»
  r362 : p.rulesOf 362 =
    [rule_inst_2545]
  t363 : Interp.termOf p 363 = pure T.«vec_rrr»
  r363 : p.rulesOf 363 =
    [rule_inst_2552]
  t370 : Interp.termOf p 370 = pure T.«fpu_cmp»
  r370 : p.rulesOf 370 =
    [rule_inst_2606]
  t371 : Interp.termOf p 371 = pure T.«vec_lanes»
  r371 : p.rulesOf 371 =
    [rule_inst_2612]
  t376 : Interp.termOf p 376 = pure T.«alu_rr_imm12»
  r376 : p.rulesOf 376 =
    [rule_inst_2648]
  t377 : Interp.termOf p 377 = pure T.«alu_rrr_shift»
  r377 : p.rulesOf 377 =
    [rule_inst_2656]
  t379 : Interp.termOf p 379 = pure T.«cmp_rr_shift_asr»
  r379 : p.rulesOf 379 =
    [rule_inst_2675]
  t380 : Interp.termOf p 380 = pure T.«alu_rrr_extend»
  r380 : p.rulesOf 380 =
    [rule_inst_2684]
  t381 : Interp.termOf p 381 = pure T.«alu_rr_extend_reg»
  r381 : p.rulesOf 381 =
    [rule_inst_2693]
  t382 : Interp.termOf p 382 = pure T.«alu_rrrr»
  r382 : p.rulesOf 382 =
    [rule_inst_2701]
  t383 : Interp.termOf p 383 = pure T.«alu_rrr_with_flags_paired»
  r383 : p.rulesOf 383 =
    [rule_inst_2709]
  t385 : Interp.termOf p 385 = pure T.«sbcs_side_effect»
  r385 : p.rulesOf 385 =
    [rule_inst_2726]
  t386 : Interp.termOf p 386 = pure T.«bit_rr»
  r386 : p.rulesOf 386 =
    [rule_inst_2733]
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
  t395 : Interp.termOf p 395 = pure T.«vec_misc»
  r395 : p.rulesOf 395 =
    [rule_inst_2802]
  t406 : Interp.termOf p 406 = pure T.«fpu_csel»
  r406 : p.rulesOf 406 =
    [rule_inst_2891, rule_inst_2888, rule_inst_2898, rule_inst_2904]
  t407 : Interp.termOf p 407 = pure T.«vec_csel»
  r407 : p.rulesOf 407 =
    [rule_inst_2912]
  t409 : Interp.termOf p 409 = pure T.«mov_to_fpu»
  r409 : p.rulesOf 409 =
    [rule_inst_2930]
  t410 : Interp.termOf p 410 = pure T.«size_for_mov_to_fpu»
  r410 : p.rulesOf 410 =
    [rule_inst_2941, rule_inst_2938]
  t414 : Interp.termOf p 414 = pure T.«mov_from_vec»
  r414 : p.rulesOf 414 =
    [rule_inst_2970]
  t417 : Interp.termOf p 417 = pure T.«extend»
  r417 : p.rulesOf 417 =
    [rule_inst_2991]
  t418 : Interp.termOf p 418 = pure T.«bitfield_move»
  r418 : p.rulesOf 418 =
    [rule_inst_2999]
  t424 : Interp.termOf p 424 = pure T.«tst_imm»
  r424 : p.rulesOf 424 =
    [rule_inst_3044]
  t425 : Interp.termOf p 425 = pure T.«csel»
  r425 : p.rulesOf 425 =
    [rule_inst_3059]
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
  t434 : Interp.termOf p 434 = pure T.«add_extend»
  r434 : p.rulesOf 434 =
    [rule_inst_3126]
  t435 : Interp.termOf p 435 = pure T.«add_shift»
  r435 : p.rulesOf 435 =
    [rule_inst_3130]
  t437 : Interp.termOf p 437 = pure T.«sub»
  r437 : p.rulesOf 437 =
    [rule_inst_3138]
  t438 : Interp.termOf p 438 = pure T.«sub_imm»
  r438 : p.rulesOf 438 =
    [rule_inst_3142]
  t439 : Interp.termOf p 439 = pure T.«sub_extend»
  r439 : p.rulesOf 439 =
    [rule_inst_3146]
  t440 : Interp.termOf p 440 = pure T.«sub_shift»
  r440 : p.rulesOf 440 =
    [rule_inst_3150]
  t443 : Interp.termOf p 443 = pure T.«madd»
  r443 : p.rulesOf 443 =
    [rule_inst_3177]
  t444 : Interp.termOf p 444 = pure T.«msub»
  r444 : p.rulesOf 444 =
    [rule_inst_3182]
  t451 : Interp.termOf p 451 = pure T.«umulh»
  r451 : p.rulesOf 451 =
    [rule_inst_3213]
  t452 : Interp.termOf p 452 = pure T.«smulh»
  r452 : p.rulesOf 452 =
    [rule_inst_3218]
  t469 : Interp.termOf p 469 = pure T.«addp»
  r469 : p.rulesOf 469 =
    [rule_inst_3290]
  t473 : Interp.termOf p 473 = pure T.«addv»
  r473 : p.rulesOf 473 =
    [rule_inst_3311]
  t487 : Interp.termOf p 487 = pure T.«asr_imm»
  r487 : p.rulesOf 487 =
    [rule_inst_3366]
  t488 : Interp.termOf p 488 = pure T.«lsr»
  r488 : p.rulesOf 488 =
    [rule_inst_3371]
  t489 : Interp.termOf p 489 = pure T.«lsr_imm»
  r489 : p.rulesOf 489 =
    [rule_inst_3375]
  t490 : Interp.termOf p 490 = pure T.«lsl»
  r490 : p.rulesOf 490 =
    [rule_inst_3380]
  t491 : Interp.termOf p 491 = pure T.«lsl_imm»
  r491 : p.rulesOf 491 =
    [rule_inst_3384]
  t492 : Interp.termOf p 492 = pure T.«a64_udiv»
  r492 : p.rulesOf 492 =
    [rule_inst_3389]
  t493 : Interp.termOf p 493 = pure T.«a64_sdiv»
  r493 : p.rulesOf 493 =
    [rule_inst_3394]
  t495 : Interp.termOf p 495 = pure T.«orr_not»
  r495 : p.rulesOf 495 =
    [rule_inst_3403]
  t496 : Interp.termOf p 496 = pure T.«orr_not_shift»
  r496 : p.rulesOf 496 =
    [rule_inst_3407]
  t497 : Interp.termOf p 497 = pure T.«orr»
  r497 : p.rulesOf 497 =
    [rule_inst_3412]
  t498 : Interp.termOf p 498 = pure T.«orr_imm»
  r498 : p.rulesOf 498 =
    [rule_inst_3416]
  t501 : Interp.termOf p 501 = pure T.«and_reg»
  r501 : p.rulesOf 501 =
    [rule_inst_3427]
  t502 : Interp.termOf p 502 = pure T.«and_imm»
  r502 : p.rulesOf 502 =
    [rule_inst_3431]
  t513 : Interp.termOf p 513 = pure T.«a64_rotr»
  r513 : p.rulesOf 513 =
    [rule_inst_3478]
  t514 : Interp.termOf p 514 = pure T.«a64_rotr_imm»
  r514 : p.rulesOf 514 =
    [rule_inst_3482]
  t515 : Interp.termOf p 515 = pure T.«a64_extr»
  r515 : p.rulesOf 515 =
    [rule_inst_3487]
  t516 : Interp.termOf p 516 = pure T.«a64_extr_imm»
  t517 : Interp.termOf p 517 = pure T.«rbit»
  r517 : p.rulesOf 517 =
    [rule_inst_3512]
  t518 : Interp.termOf p 518 = pure T.«a64_clz»
  r518 : p.rulesOf 518 =
    [rule_inst_3517]
  t520 : Interp.termOf p 520 = pure T.«a64_rev16»
  r520 : p.rulesOf 520 =
    [rule_inst_3527]
  t521 : Interp.termOf p 521 = pure T.«a64_rev32»
  r521 : p.rulesOf 521 =
    [rule_inst_3531]
  t522 : Interp.termOf p 522 = pure T.«a64_rev64»
  r522 : p.rulesOf 522 =
    [rule_inst_3535]
  t524 : Interp.termOf p 524 = pure T.«vec_cnt»
  r524 : p.rulesOf 524 =
    [rule_inst_3545]
  t528 : Interp.termOf p 528 = pure T.«udf»
  r528 : p.rulesOf 528 =
    [rule_inst_3569]
  t529 : Interp.termOf p 529 = pure T.«aarch64_uload8»
  r529 : p.rulesOf 529 =
    [rule_inst_3576]
  t530 : Interp.termOf p 530 = pure T.«aarch64_sload8»
  r530 : p.rulesOf 530 =
    [rule_inst_3583]
  t531 : Interp.termOf p 531 = pure T.«aarch64_uload16»
  r531 : p.rulesOf 531 =
    [rule_inst_3590]
  t532 : Interp.termOf p 532 = pure T.«aarch64_sload16»
  r532 : p.rulesOf 532 =
    [rule_inst_3597]
  t533 : Interp.termOf p 533 = pure T.«aarch64_uload32»
  r533 : p.rulesOf 533 =
    [rule_inst_3605]
  t534 : Interp.termOf p 534 = pure T.«aarch64_sload32»
  r534 : p.rulesOf 534 =
    [rule_inst_3612]
  t535 : Interp.termOf p 535 = pure T.«aarch64_uload64»
  r535 : p.rulesOf 535 =
    [rule_inst_3620]
  t541 : Interp.termOf p 541 = pure T.«aarch64_store8»
  r541 : p.rulesOf 541 =
    [rule_inst_3660]
  t542 : Interp.termOf p 542 = pure T.«aarch64_store16»
  r542 : p.rulesOf 542 =
    [rule_inst_3666]
  t543 : Interp.termOf p 543 = pure T.«aarch64_store32»
  r543 : p.rulesOf 543 =
    [rule_inst_3672]
  t544 : Interp.termOf p 544 = pure T.«aarch64_store64»
  r544 : p.rulesOf 544 =
    [rule_inst_3678]
  t553 : Interp.termOf p 553 = pure T.«imm»
  r553 : p.rulesOf 553 =
    [rule_inst_3742, rule_inst_3745, rule_inst_3751, rule_inst_3786, rule_inst_3790]
  t554 : Interp.termOf p 554 = pure T.«load_constant_full»
  t555 : Interp.termOf p 555 = pure T.«put_in_reg_sext32»
  r555 : p.rulesOf 555 =
    [rule_inst_3803, rule_inst_3804, rule_inst_3799]
  t556 : Interp.termOf p 556 = pure T.«put_in_reg_zext32»
  r556 : p.rulesOf 556 =
    [rule_inst_3813, rule_inst_3814, rule_inst_3809]
  t557 : Interp.termOf p 557 = pure T.«put_in_reg_sext64»
  r557 : p.rulesOf 557 =
    [rule_inst_3819, rule_inst_3823]
  t558 : Interp.termOf p 558 = pure T.«put_in_reg_zext64»
  r558 : p.rulesOf 558 =
    [rule_inst_3829, rule_inst_3833]
  t559 : Interp.termOf p 559 = pure T.«trap_if_zero_divisor»
  r559 : p.rulesOf 559 =
    [rule_inst_3838]
  t560 : Interp.termOf p 560 = pure T.«size_from_ty»
  r560 : p.rulesOf 560 =
    [rule_inst_3852, rule_inst_3853]
  t561 : Interp.termOf p 561 = pure T.«trap_if_div_overflow»
  r561 : p.rulesOf 561 =
    [rule_inst_3861]
  t562 : Interp.termOf p 562 = pure T.«intmin_check»
  r562 : p.rulesOf 562 =
    [rule_inst_3888, rule_inst_3892]
  t565 : Interp.termOf p 565 = pure T.«alu_rs_imm_logic_commutative»
  r565 : p.rulesOf 565 =
    [rule_inst_3923, rule_inst_3931, rule_inst_3920, rule_inst_3928, rule_inst_3916]
  t566 : Interp.termOf p 566 = pure T.«alu_rs_imm_logic»
  r566 : p.rulesOf 566 =
    [rule_inst_3941, rule_inst_3944, rule_inst_3939]
  t569 : Interp.termOf p 569 = pure T.«is_pic»
  t570 : Interp.termOf p 570 = pure T.«load_ext_name»
  r570 : p.rulesOf 570 =
    [rule_inst_3986, rule_inst_3991, rule_inst_3996, rule_inst_3983]
  t571 : Interp.termOf p 571 = pure T.«load_ext_name_got»
  r571 : p.rulesOf 571 =
    [rule_inst_4002]
  t572 : Interp.termOf p 572 = pure T.«load_ext_name_near»
  r572 : p.rulesOf 572 =
    [rule_inst_4009]
  t573 : Interp.termOf p 573 = pure T.«load_ext_name_far»
  r573 : p.rulesOf 573 =
    [rule_inst_4016]
  t574 : Interp.termOf p 574 = pure T.«amode»
  r574 : p.rulesOf 574 =
    [rule_inst_4047, rule_inst_4043, rule_inst_4040, rule_inst_4038]
  t575 : Interp.termOf p 575 = pure T.«amode_no_more_iconst»
  r575 : p.rulesOf 575 =
    [rule_inst_4103, rule_inst_4096, rule_inst_4093, rule_inst_4081, rule_inst_4083, rule_inst_4077, rule_inst_4079, rule_inst_4075, rule_inst_4064, rule_inst_4061, rule_inst_4056]
  t576 : Interp.termOf p 576 = pure T.«amode_reg_scaled»
  r576 : p.rulesOf 576 =
    [rule_inst_4111, rule_inst_4113, rule_inst_4109]
  t577 : Interp.termOf p 577 = pure T.«amode_add»
  r577 : p.rulesOf 577 =
    [rule_inst_4125, rule_inst_4122, rule_inst_4120]
  t580 : Interp.termOf p 580 = pure T.«uimm12_scaled_from_i64»
  t581 : Interp.termOf p 581 = pure T.«uimm12_scaled_nonzero_from_i64»
  t582 : Interp.termOf p 582 = pure T.«simm9_from_i64»
  t592 : Interp.termOf p 592 = pure T.«cond_code»
  t593 : Interp.termOf p 593 = pure T.«invert_cond»
  t634 : Interp.termOf p 634 = pure T.«gen_call_info»
  t635 : Interp.termOf p 635 = pure T.«gen_call_ind_info»
  t638 : Interp.termOf p 638 = pure T.«call_impl»
  r638 : p.rulesOf 638 =
    [rule_inst_4780]
  t639 : Interp.termOf p 639 = pure T.«call_ind_impl»
  r639 : p.rulesOf 639 =
    [rule_inst_4786]
  t643 : Interp.termOf p 643 = pure T.«compute_stack_addr»
  r643 : p.rulesOf 643 =
    [rule_inst_4810]
  t649 : Interp.termOf p 649 = pure T.«cond_result_invert»
  r649 : p.rulesOf 649 =
    [rule_inst_4954, rule_inst_4955, rule_inst_4956, rule_inst_4957, rule_inst_4959]
  t650 : Interp.termOf p 650 = pure T.«is_nonzero_cmp»
  r650 : p.rulesOf 650 =
    [rule_inst_4965, rule_inst_4966, rule_inst_4967]
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
  t655 : Interp.termOf p 655 = pure T.«emit_fcmp»
  r655 : p.rulesOf 655 =
    [rule_inst_5216, rule_inst_5219, rule_inst_5210]
  t656 : Interp.termOf p 656 = pure T.«fp_cond_code»
  r656 : p.rulesOf 656 =
    [rule_inst_5232, rule_inst_5235, rule_inst_5237, rule_inst_5239, rule_inst_5241, rule_inst_5243, rule_inst_5245, rule_inst_5247, rule_inst_5249, rule_inst_5251, rule_inst_5253, rule_inst_5255]
  t657 : Interp.termOf p 657 = pure T.«lower_extend_op»
  r657 : p.rulesOf 657 =
    [rule_inst_5264, rule_inst_5265, rule_inst_5266, rule_inst_5267]
  t659 : Interp.termOf p 659 = pure T.«lower_select»
  r659 : p.rulesOf 659 =
    [rule_inst_5320, rule_inst_5322, rule_inst_5324, rule_inst_5331]
  t660 : Interp.termOf p 660 = pure T.«lower_select_cond»
  r660 : p.rulesOf 660 =
    [rule_inst_5343, rule_inst_5350, rule_inst_5345, rule_inst_5341, rule_inst_5364, rule_inst_5347]
  t661 : Interp.termOf p 661 = pure T.«aarch64_jump»
  r661 : p.rulesOf 661 =
    [rule_inst_5371]
  t662 : Interp.termOf p 662 = pure T.«jt_sequence»
  r662 : p.rulesOf 662 =
    [rule_inst_5394]
  t663 : Interp.termOf p 663 = pure T.«a64_br_cond»
  r663 : p.rulesOf 663 =
    [rule_inst_5406]
  t664 : Interp.termOf p 664 = pure T.«a64_br_zero»
  r664 : p.rulesOf 664 =
    [rule_inst_5412]
  t665 : Interp.termOf p 665 = pure T.«a64_br_not_zero»
  r665 : p.rulesOf 665 =
    [rule_inst_5418]
  t666 : Interp.termOf p 666 = pure T.«test_branch»
  r666 : p.rulesOf 666 =
    [rule_inst_5425]
  t667 : Interp.termOf p 667 = pure T.«tbnz»
  r667 : p.rulesOf 667 =
    [rule_inst_5431]
  t668 : Interp.termOf p 668 = pure T.«tbz»
  r668 : p.rulesOf 668 =
    [rule_inst_5437]
  t669 : Interp.termOf p 669 = pure T.«emit_island»
  r669 : p.rulesOf 669 =
    [rule_inst_5443]
  t670 : Interp.termOf p 670 = pure T.«br_table_impl»
  r670 : p.rulesOf 670 =
    [rule_inst_5450, rule_inst_5454]
  t686 : Interp.termOf p 686 = pure T.«lower»
  r686 : p.rulesOf 686 =
    [rule_lower_419, rule_lower_402, rule_lower_1444, rule_lower_1481, rule_lower_116, rule_lower_125, rule_lower_1442, rule_lower_1479, rule_lower_2779, rule_lower_120, rule_lower_128, rule_lower_165, rule_lower_1439, rule_lower_1476, rule_lower_2784, rule_lower_93, rule_lower_167, rule_lower_1437, rule_lower_1474, rule_lower_1501, rule_lower_1507, rule_lower_2789, rule_lower_3091, rule_lower_3155, rule_lower_90, rule_lower_169, rule_lower_1435, rule_lower_1472, rule_lower_1540, rule_lower_2152, rule_lower_2793, rule_lower_3097, rule_lower_3161, rule_lower_102, rule_lower_171, rule_lower_1408, rule_lower_1434, rule_lower_1471, rule_lower_1539, rule_lower_2158, rule_lower_2185, rule_lower_2798, rule_lower_2828, rule_lower_3008, rule_lower_3101, rule_lower_3165, rule_lower_98, rule_lower_190, rule_lower_437, rule_lower_609, rule_lower_810, rule_lower_861, rule_lower_1163, rule_lower_1222, rule_lower_1224, rule_lower_1226, rule_lower_1228, rule_lower_1406, rule_lower_1431, rule_lower_1468, rule_lower_1536, rule_lower_2120, rule_lower_2164, rule_lower_2191, rule_lower_2386, rule_lower_2404, rule_lower_2419, rule_lower_2435, rule_lower_2815, rule_lower_3018, rule_lower_3036, rule_lower_3056, rule_lower_3076, rule_lower_3126, rule_lower_3140, rule_lower_3190, rule_lower_3204, rule_lower_111, rule_lower_203, rule_lower_205, rule_lower_207, rule_lower_209, rule_lower_211, rule_lower_213, rule_lower_215, rule_lower_217, rule_lower_222, rule_lower_224, rule_lower_226, rule_lower_228, rule_lower_230, rule_lower_232, rule_lower_240, rule_lower_242, rule_lower_244, rule_lower_246, rule_lower_248, rule_lower_250, rule_lower_260, rule_lower_262, rule_lower_264, rule_lower_266, rule_lower_268, rule_lower_270, rule_lower_294, rule_lower_300, rule_lower_440, rule_lower_608, rule_lower_693, rule_lower_699, rule_lower_707, rule_lower_713, rule_lower_730, rule_lower_733, rule_lower_750, rule_lower_753, rule_lower_767, rule_lower_773, rule_lower_787, rule_lower_793, rule_lower_816, rule_lower_857, rule_lower_1056, rule_lower_1068, rule_lower_1116, rule_lower_1167, rule_lower_1236, rule_lower_1242, rule_lower_1248, rule_lower_1254, rule_lower_1266, rule_lower_1272, rule_lower_1281, rule_lower_1283, rule_lower_1401, rule_lower_1429, rule_lower_1466, rule_lower_1534, rule_lower_1704, rule_lower_1707, rule_lower_1803, rule_lower_1808, rule_lower_2138, rule_lower_2170, rule_lower_2197, rule_lower_2288, rule_lower_2328, rule_lower_2331, rule_lower_2334, rule_lower_2337, rule_lower_2340, rule_lower_2343, rule_lower_2346, rule_lower_2349, rule_lower_2352, rule_lower_2381, rule_lower_2400, rule_lower_2415, rule_lower_2431, rule_lower_2451, rule_lower_2466, rule_lower_2508, rule_lower_2580, rule_lower_2803, rule_lower_2822, rule_lower_2837, rule_lower_3014, rule_lower_3031, rule_lower_3051, rule_lower_3071, rule_lower_3110, rule_lower_3174, rule_lower_53, rule_lower_58, rule_lower_63, rule_lower_68, rule_lower_73, rule_lower_78, rule_lower_108, rule_lower_132, rule_lower_273, rule_lower_279, rule_lower_284, rule_lower_308, rule_lower_313, rule_lower_316, rule_lower_336, rule_lower_342, rule_lower_368, rule_lower_375, rule_lower_379, rule_lower_383, rule_lower_387, rule_lower_450, rule_lower_463, rule_lower_477, rule_lower_485, rule_lower_493, rule_lower_501, rule_lower_509, rule_lower_517, rule_lower_525, rule_lower_533, rule_lower_541, rule_lower_549, rule_lower_554, rule_lower_559, rule_lower_567, rule_lower_570, rule_lower_578, rule_lower_581, rule_lower_589, rule_lower_592, rule_lower_600, rule_lower_603, rule_lower_685, rule_lower_690, rule_lower_696, rule_lower_704, rule_lower_710, rule_lower_724, rule_lower_727, rule_lower_744, rule_lower_747, rule_lower_764, rule_lower_770, rule_lower_784, rule_lower_790, rule_lower_805, rule_lower_836, rule_lower_841, rule_lower_846, rule_lower_851, rule_lower_865, rule_lower_906, rule_lower_914, rule_lower_995, rule_lower_1000, rule_lower_1005, rule_lower_1010, rule_lower_1015, rule_lower_1020, rule_lower_1025, rule_lower_1030, rule_lower_1035, rule_lower_1040, rule_lower_1045, rule_lower_1050, rule_lower_1059, rule_lower_1071, rule_lower_1119, rule_lower_1145, rule_lower_1190, rule_lower_1204, rule_lower_1233, rule_lower_1239, rule_lower_1245, rule_lower_1251, rule_lower_1294, rule_lower_1300, rule_lower_1339, rule_lower_1359, rule_lower_1391, rule_lower_1424, rule_lower_1461, rule_lower_1528, rule_lower_1549, rule_lower_1553, rule_lower_1642, rule_lower_1646, rule_lower_1699, rule_lower_1720, rule_lower_1791, rule_lower_1797, rule_lower_1827, rule_lower_1857, rule_lower_1862, rule_lower_1916, rule_lower_1931, rule_lower_1937, rule_lower_1940, rule_lower_1951, rule_lower_1955, rule_lower_1958, rule_lower_1982, rule_lower_1986, rule_lower_1989, rule_lower_2000, rule_lower_2004, rule_lower_2016, rule_lower_2035, rule_lower_2038, rule_lower_2041, rule_lower_2044, rule_lower_2052, rule_lower_2074, rule_lower_2080, rule_lower_2086, rule_lower_2092, rule_lower_2099, rule_lower_2108, rule_lower_2113, rule_lower_2146, rule_lower_2176, rule_lower_2203, rule_lower_2237, rule_lower_2242, rule_lower_2262, rule_lower_2267, rule_lower_2280, rule_lower_2285, rule_lower_2301, rule_lower_2304, rule_lower_2307, rule_lower_2310, rule_lower_2316, rule_lower_2321, rule_lower_2357, rule_lower_2359, rule_lower_2361, rule_lower_2363, rule_lower_2365, rule_lower_2367, rule_lower_2369, rule_lower_2371, rule_lower_2373, rule_lower_2375, rule_lower_2377, rule_lower_2390, rule_lower_2395, rule_lower_2408, rule_lower_2423, rule_lower_2439, rule_lower_2446, rule_lower_2454, rule_lower_2461, rule_lower_2469, rule_lower_2476, rule_lower_2481, rule_lower_2486, rule_lower_2491, rule_lower_2496, rule_lower_2499, rule_lower_2502, rule_lower_2518, rule_lower_2529, rule_lower_2574, rule_lower_2587, rule_lower_2595, rule_lower_2604, rule_lower_2607, rule_lower_2610, rule_lower_2613, rule_lower_2619, rule_lower_2647, rule_lower_2650, rule_lower_2653, rule_lower_2656, rule_lower_2659, rule_lower_2662, rule_lower_2666, rule_lower_2672, rule_lower_2678, rule_lower_2684, rule_lower_2690, rule_lower_2696, rule_lower_2705, rule_lower_2709, rule_lower_2713, rule_lower_2717, rule_lower_2722, rule_lower_2726, rule_lower_2730, rule_lower_2735, rule_lower_2770, rule_lower_2773, rule_lower_2809, rule_lower_2818, rule_lower_2842, rule_lower_2849, rule_lower_2863, rule_lower_2887, rule_lower_2900, rule_lower_2913, rule_lower_2927, rule_lower_3022, rule_lower_3042, rule_lower_3062, rule_lower_3082, rule_lower_3217, rule_lower_3220, rule_lower_3225, rule_lower_3286, rule_lower_3292, rule_lower_dynamic_neon_81, rule_lower_dynamic_neon_87, rule_lower_86, rule_lower_319, rule_lower_359, rule_lower_390, rule_lower_434, rule_lower_472, rule_lower_482, rule_lower_490, rule_lower_498, rule_lower_506, rule_lower_514, rule_lower_522, rule_lower_530, rule_lower_538, rule_lower_546, rule_lower_564, rule_lower_575, rule_lower_586, rule_lower_597, rule_lower_718, rule_lower_721, rule_lower_738, rule_lower_741, rule_lower_758, rule_lower_761, rule_lower_778, rule_lower_781, rule_lower_831, rule_lower_876, rule_lower_956, rule_lower_1153, rule_lower_1197, rule_lower_1211, rule_lower_1289, rule_lower_1349, rule_lower_1387, rule_lower_1421, rule_lower_1458, rule_lower_1525, rule_lower_1545, rule_lower_1638, rule_lower_1736, rule_lower_1778, rule_lower_1844, rule_lower_1848, rule_lower_1946, rule_lower_1961, rule_lower_1995, rule_lower_2030, rule_lower_2179, rule_lower_2209, rule_lower_2294, rule_lower_2622, rule_lower_2742, rule_lower_dynamic_neon_43, rule_lower_dynamic_neon_57, rule_lower_dynamic_neon_71, rule_lower_dynamic_neon_92, rule_lower_dynamic_neon_97, rule_lower_137, rule_lower_322, rule_lower_826, rule_lower_924, rule_lower_1261, rule_lower_1329, rule_lower_1385, rule_lower_1419, rule_lower_1456, rule_lower_1523, rule_lower_1588, rule_lower_1661, rule_lower_1734, rule_lower_1772, rule_lower_1852, rule_lower_2215, rule_lower_2298, rule_lower_2625, rule_lower_2746, rule_lower_dynamic_neon_15, rule_lower_dynamic_neon_19, rule_lower_dynamic_neon_23, rule_lower_dynamic_neon_27, rule_lower_dynamic_neon_31, rule_lower_dynamic_neon_35, rule_lower_dynamic_neon_39, rule_lower_dynamic_neon_53, rule_lower_dynamic_neon_67, rule_lower_142, rule_lower_821, rule_lower_871, rule_lower_1320, rule_lower_1381, rule_lower_1452, rule_lower_1519, rule_lower_1583, rule_lower_1659, rule_lower_1729, rule_lower_1840, rule_lower_2628, rule_lower_2750, rule_lower_dynamic_neon_47, rule_lower_dynamic_neon_61, rule_lower_dynamic_neon_75, rule_lower_801, rule_lower_1315, rule_lower_1377, rule_lower_1415, rule_lower_1449, rule_lower_1516, rule_lower_1654, rule_lower_1695, rule_lower_2633, rule_lower_2754, rule_lower_dynamic_neon_3, rule_lower_dynamic_neon_11, rule_lower_1412, rule_lower_2638, rule_lower_2759, rule_lower_dynamic_neon_7, rule_lower_2643, rule_lower_2763]
  t687 : Interp.termOf p 687 = pure T.«lower_branch»
  r687 : p.rulesOf 687 =
    [rule_lower_2542, rule_lower_3251, rule_lower_3257, rule_lower_2551, rule_lower_2561, rule_lower_3231, rule_lower_3270, rule_lower_3277]
  t698 : Interp.termOf p 698 = pure T.«put_nonzero_in_reg»
  r698 : p.rulesOf 698 =
    [rule_lower_1097, rule_lower_1101, rule_lower_1104, rule_lower_1107, rule_lower_1110]
  t699 : Interp.termOf p 699 = pure T.«aarch64_uload»
  r699 : p.rulesOf 699 =
    [rule_lower_1307, rule_lower_1308, rule_lower_1309]
  t700 : Interp.termOf p 700 = pure T.«aarch64_sload»
  r700 : p.rulesOf 700 =
    [rule_lower_1366, rule_lower_1367, rule_lower_1368]
  t702 : Interp.termOf p 702 = pure T.«shift_masked_imm»
  t703 : Interp.termOf p 703 = pure T.«do_shift»
  r703 : p.rulesOf 703 =
    [rule_lower_1631, rule_lower_1622, rule_lower_1623, rule_lower_1612]
  t704 : Interp.termOf p 704 = pure T.«shift_mask»
  t706 : Interp.termOf p 706 = pure T.«bfm_immr»
  t707 : Interp.termOf p 707 = pure T.«bfm_imms»
  t709 : Interp.termOf p 709 = pure T.«negate_imm_shift»
  t710 : Interp.termOf p 710 = pure T.«small_rotr»
  r710 : p.rulesOf 710 =
    [rule_lower_1879]
  t711 : Interp.termOf p 711 = pure T.«rotr_mask»
  t712 : Interp.termOf p 712 = pure T.«small_rotr_imm»
  r712 : p.rulesOf 712 =
    [rule_lower_1902]
  t713 : Interp.termOf p 713 = pure T.«rotr_opposite_amount»
  t715 : Interp.termOf p 715 = pure T.«lower_cond_result_bool»
  r715 : p.rulesOf 715 =
    [rule_lower_2222, rule_lower_2224, rule_lower_2226, rule_lower_2228, rule_lower_2231]
  t722 : Interp.termOf p 722 = pure T.«br_cond_result»
  r722 : p.rulesOf 722 =
    [rule_lower_3236, rule_lower_3238, rule_lower_3240, rule_lower_3247]
  t723 : Interp.termOf p 723 = pure T.«test_and_compare_bit_const»
  t978 : Interp.termOf p 978 = pure T.«i32_checked_add»
  t1154 : Interp.termOf p 1154 = pure T.«i64_checked_neg»
  t1157 : Interp.termOf p 1157 = pure T.«u64_eq»
  t1161 : Interp.termOf p 1161 = pure T.«u64_gt»
  t1164 : Interp.termOf p 1164 = pure T.«u64_wrapping_add»
  t1167 : Interp.termOf p 1167 = pure T.«u64_wrapping_sub»
  t1182 : Interp.termOf p 1182 = pure T.«u64_wrapping_shl»
  t1199 : Interp.termOf p 1199 = pure T.«u64_is_odd»
  t1378 : Interp.termOf p 1378 = pure T.«u8_into_u32»
  t1382 : Interp.termOf p 1382 = pure T.«u8_into_u64»
  t1431 : Interp.termOf p 1431 = pure T.«u16_into_u64»
  t1455 : Interp.termOf p 1455 = pure T.«i32_into_i64»
  t1485 : Interp.termOf p 1485 = pure T.«u32_into_u64»
  t1508 : Interp.termOf p 1508 = pure T.«i32_from_i64»
  t1514 : Interp.termOf p 1514 = pure T.«i64_cast_unsigned»
  t1527 : Interp.termOf p 1527 = pure T.«u8_from_u64»
  t1614 : Interp.termOf p 1614 = pure T.«value_array_2»
  t1615 : Interp.termOf p 1615 = pure T.«value_array_3»
  t1616 : Interp.termOf p 1616 = pure T.«block_array_2»
  t1785 : Interp.termOf p 1785 = pure T.«RelocDistance.Near»
  t1786 : Interp.termOf p 1786 = pure T.«RelocDistance.Far»
  t1787 : Interp.termOf p 1787 = pure T.«SideEffectNoResult.Inst»
  t1788 : Interp.termOf p 1788 = pure T.«SideEffectNoResult.Inst2»
  t1789 : Interp.termOf p 1789 = pure T.«SideEffectNoResult.Inst3»
  t1790 : Interp.termOf p 1790 = pure T.«ProducesFlags.AlreadyExistingFlags»
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
  t1827 : Interp.termOf p 1827 = pure T.«MInst.BitRR»
  t1828 : Interp.termOf p 1828 = pure T.«MInst.ULoad8»
  t1829 : Interp.termOf p 1829 = pure T.«MInst.SLoad8»
  t1830 : Interp.termOf p 1830 = pure T.«MInst.ULoad16»
  t1831 : Interp.termOf p 1831 = pure T.«MInst.SLoad16»
  t1832 : Interp.termOf p 1832 = pure T.«MInst.ULoad32»
  t1833 : Interp.termOf p 1833 = pure T.«MInst.SLoad32»
  t1834 : Interp.termOf p 1834 = pure T.«MInst.ULoad64»
  t1835 : Interp.termOf p 1835 = pure T.«MInst.Store8»
  t1836 : Interp.termOf p 1836 = pure T.«MInst.Store16»
  t1837 : Interp.termOf p 1837 = pure T.«MInst.Store32»
  t1838 : Interp.termOf p 1838 = pure T.«MInst.Store64»
  t1844 : Interp.termOf p 1844 = pure T.«MInst.MovWide»
  t1846 : Interp.termOf p 1846 = pure T.«MInst.Extend»
  t1847 : Interp.termOf p 1847 = pure T.«MInst.BitfieldMove»
  t1849 : Interp.termOf p 1849 = pure T.«MInst.CSel»
  t1851 : Interp.termOf p 1851 = pure T.«MInst.CSet»
  t1853 : Interp.termOf p 1853 = pure T.«MInst.CCmp»
  t1854 : Interp.termOf p 1854 = pure T.«MInst.CCmpImm»
  t1874 : Interp.termOf p 1874 = pure T.«MInst.FpuCmp»
  t1889 : Interp.termOf p 1889 = pure T.«MInst.FpuCSel16»
  t1890 : Interp.termOf p 1890 = pure T.«MInst.FpuCSel32»
  t1891 : Interp.termOf p 1891 = pure T.«MInst.FpuCSel64»
  t1893 : Interp.termOf p 1893 = pure T.«MInst.MovToFpu»
  t1896 : Interp.termOf p 1896 = pure T.«MInst.MovFromVec»
  t1911 : Interp.termOf p 1911 = pure T.«MInst.VecRRR»
  t1914 : Interp.termOf p 1914 = pure T.«MInst.VecMisc»
  t1915 : Interp.termOf p 1915 = pure T.«MInst.VecLanes»
  t1924 : Interp.termOf p 1924 = pure T.«MInst.VecCSel»
  t1927 : Interp.termOf p 1927 = pure T.«MInst.Call»
  t1928 : Interp.termOf p 1928 = pure T.«MInst.CallInd»
  t1935 : Interp.termOf p 1935 = pure T.«MInst.Jump»
  t1936 : Interp.termOf p 1936 = pure T.«MInst.CondBr»
  t1937 : Interp.termOf p 1937 = pure T.«MInst.TestBitAndBranch»
  t1938 : Interp.termOf p 1938 = pure T.«MInst.TrapIf»
  t1941 : Interp.termOf p 1941 = pure T.«MInst.Udf»
  t1946 : Interp.termOf p 1946 = pure T.«MInst.JTSequence»
  t1947 : Interp.termOf p 1947 = pure T.«MInst.LoadExtNameGot»
  t1948 : Interp.termOf p 1948 = pure T.«MInst.LoadExtNameNear»
  t1949 : Interp.termOf p 1949 = pure T.«MInst.LoadExtNameFar»
  t1954 : Interp.termOf p 1954 = pure T.«MInst.EmitIsland»
  t1962 : Interp.termOf p 1962 = pure T.«ALUOp.Add»
  t1963 : Interp.termOf p 1963 = pure T.«ALUOp.Sub»
  t1964 : Interp.termOf p 1964 = pure T.«ALUOp.Orr»
  t1965 : Interp.termOf p 1965 = pure T.«ALUOp.OrrNot»
  t1966 : Interp.termOf p 1966 = pure T.«ALUOp.And»
  t1967 : Interp.termOf p 1967 = pure T.«ALUOp.AndS»
  t1968 : Interp.termOf p 1968 = pure T.«ALUOp.AndNot»
  t1969 : Interp.termOf p 1969 = pure T.«ALUOp.Eor»
  t1970 : Interp.termOf p 1970 = pure T.«ALUOp.EorNot»
  t1971 : Interp.termOf p 1971 = pure T.«ALUOp.AddS»
  t1972 : Interp.termOf p 1972 = pure T.«ALUOp.SubS»
  t1973 : Interp.termOf p 1973 = pure T.«ALUOp.SMulH»
  t1974 : Interp.termOf p 1974 = pure T.«ALUOp.UMulH»
  t1975 : Interp.termOf p 1975 = pure T.«ALUOp.SDiv»
  t1976 : Interp.termOf p 1976 = pure T.«ALUOp.UDiv»
  t1977 : Interp.termOf p 1977 = pure T.«ALUOp.Extr»
  t1978 : Interp.termOf p 1978 = pure T.«ALUOp.Lsr»
  t1979 : Interp.termOf p 1979 = pure T.«ALUOp.Asr»
  t1980 : Interp.termOf p 1980 = pure T.«ALUOp.Lsl»
  t1984 : Interp.termOf p 1984 = pure T.«ALUOp.SbcS»
  t1985 : Interp.termOf p 1985 = pure T.«ALUOp3.MAdd»
  t1986 : Interp.termOf p 1986 = pure T.«ALUOp3.MSub»
  t1987 : Interp.termOf p 1987 = pure T.«ALUOp3.UMAddL»
  t1988 : Interp.termOf p 1988 = pure T.«ALUOp3.SMAddL»
  t1989 : Interp.termOf p 1989 = pure T.«MoveWideOp.MovZ»
  t1990 : Interp.termOf p 1990 = pure T.«MoveWideOp.MovN»
  t1991 : Interp.termOf p 1991 = pure T.«BfmOp.UBfm»
  t1992 : Interp.termOf p 1992 = pure T.«BfmOp.SBfm»
  t1996 : Interp.termOf p 1996 = pure T.«ExtendOp.UXTB»
  t1997 : Interp.termOf p 1997 = pure T.«ExtendOp.UXTH»
  t1998 : Interp.termOf p 1998 = pure T.«ExtendOp.UXTW»
  t2000 : Interp.termOf p 2000 = pure T.«ExtendOp.SXTB»
  t2001 : Interp.termOf p 2001 = pure T.«ExtendOp.SXTH»
  t2002 : Interp.termOf p 2002 = pure T.«ExtendOp.SXTW»
  t2004 : Interp.termOf p 2004 = pure T.«BitOp.RBit»
  t2005 : Interp.termOf p 2005 = pure T.«BitOp.Clz»
  t2007 : Interp.termOf p 2007 = pure T.«BitOp.Rev16»
  t2008 : Interp.termOf p 2008 = pure T.«BitOp.Rev32»
  t2009 : Interp.termOf p 2009 = pure T.«BitOp.Rev64»
  t2012 : Interp.termOf p 2012 = pure T.«AMode.RegReg»
  t2013 : Interp.termOf p 2013 = pure T.«AMode.RegScaled»
  t2014 : Interp.termOf p 2014 = pure T.«AMode.RegScaledExtended»
  t2015 : Interp.termOf p 2015 = pure T.«AMode.RegExtended»
  t2016 : Interp.termOf p 2016 = pure T.«AMode.Unscaled»
  t2017 : Interp.termOf p 2017 = pure T.«AMode.UnsignedOffset»
  t2024 : Interp.termOf p 2024 = pure T.«AMode.SlotOffset»
  t2028 : Interp.termOf p 2028 = pure T.«OperandSize.Size32»
  t2029 : Interp.termOf p 2029 = pure T.«OperandSize.Size64»
  t2030 : Interp.termOf p 2030 = pure T.«TestBitAndBranchKind.Z»
  t2031 : Interp.termOf p 2031 = pure T.«TestBitAndBranchKind.NZ»
  t2032 : Interp.termOf p 2032 = pure T.«ScalarSize.Size8»
  t2033 : Interp.termOf p 2033 = pure T.«ScalarSize.Size16»
  t2034 : Interp.termOf p 2034 = pure T.«ScalarSize.Size32»
  t2035 : Interp.termOf p 2035 = pure T.«ScalarSize.Size64»
  t2036 : Interp.termOf p 2036 = pure T.«ScalarSize.Size128»
  t2037 : Interp.termOf p 2037 = pure T.«Cond.Eq»
  t2038 : Interp.termOf p 2038 = pure T.«Cond.Ne»
  t2039 : Interp.termOf p 2039 = pure T.«Cond.Hs»
  t2041 : Interp.termOf p 2041 = pure T.«Cond.Mi»
  t2042 : Interp.termOf p 2042 = pure T.«Cond.Pl»
  t2043 : Interp.termOf p 2043 = pure T.«Cond.Vs»
  t2044 : Interp.termOf p 2044 = pure T.«Cond.Vc»
  t2045 : Interp.termOf p 2045 = pure T.«Cond.Hi»
  t2046 : Interp.termOf p 2046 = pure T.«Cond.Ls»
  t2047 : Interp.termOf p 2047 = pure T.«Cond.Ge»
  t2048 : Interp.termOf p 2048 = pure T.«Cond.Lt»
  t2049 : Interp.termOf p 2049 = pure T.«Cond.Gt»
  t2050 : Interp.termOf p 2050 = pure T.«Cond.Le»
  t2053 : Interp.termOf p 2053 = pure T.«VectorSize.Size8x8»
  t2054 : Interp.termOf p 2054 = pure T.«VectorSize.Size8x16»
  t2055 : Interp.termOf p 2055 = pure T.«VectorSize.Size16x4»
  t2056 : Interp.termOf p 2056 = pure T.«VectorSize.Size16x8»
  t2057 : Interp.termOf p 2057 = pure T.«VectorSize.Size32x2»
  t2058 : Interp.termOf p 2058 = pure T.«VectorSize.Size32x4»
  t2059 : Interp.termOf p 2059 = pure T.«VectorSize.Size64x2»
  t2124 : Interp.termOf p 2124 = pure T.«VecALUOp.Umin»
  t2125 : Interp.termOf p 2125 = pure T.«VecALUOp.Smin»
  t2126 : Interp.termOf p 2126 = pure T.«VecALUOp.Umax»
  t2127 : Interp.termOf p 2127 = pure T.«VecALUOp.Smax»
  t2135 : Interp.termOf p 2135 = pure T.«VecALUOp.Addp»
  t2165 : Interp.termOf p 2165 = pure T.«VecMisc2.Cnt»
  t2200 : Interp.termOf p 2200 = pure T.«VecLanesOp.Addv»
  t2234 : Interp.termOf p 2234 = pure T.«ImmExtend.Sign»
  t2235 : Interp.termOf p 2235 = pure T.«ImmExtend.Zero»
  t2236 : Interp.termOf p 2236 = pure T.«CondResult.Zero»
  t2237 : Interp.termOf p 2237 = pure T.«CondResult.NotZero»
  t2238 : Interp.termOf p 2238 = pure T.«CondResult.Cond»
  t2239 : Interp.termOf p 2239 = pure T.«CondResult.Or»
  t2240 : Interp.termOf p 2240 = pure T.«CondResult.And»
  t2242 : Interp.termOf p 2242 = pure T.«ExtType.Signed»
  t2243 : Interp.termOf p 2243 = pure T.«ExtType.Unsigned»
  t2255 : Interp.termOf p 2255 = pure T.«FloatCC.Equal»
  t2256 : Interp.termOf p 2256 = pure T.«FloatCC.GreaterThan»
  t2257 : Interp.termOf p 2257 = pure T.«FloatCC.GreaterThanOrEqual»
  t2258 : Interp.termOf p 2258 = pure T.«FloatCC.LessThan»
  t2259 : Interp.termOf p 2259 = pure T.«FloatCC.LessThanOrEqual»
  t2260 : Interp.termOf p 2260 = pure T.«FloatCC.NotEqual»
  t2261 : Interp.termOf p 2261 = pure T.«FloatCC.Ordered»
  t2262 : Interp.termOf p 2262 = pure T.«FloatCC.OrderedNotEqual»
  t2263 : Interp.termOf p 2263 = pure T.«FloatCC.Unordered»
  t2264 : Interp.termOf p 2264 = pure T.«FloatCC.UnorderedOrEqual»
  t2265 : Interp.termOf p 2265 = pure T.«FloatCC.UnorderedOrGreaterThan»
  t2266 : Interp.termOf p 2266 = pure T.«FloatCC.UnorderedOrGreaterThanOrEqual»
  t2267 : Interp.termOf p 2267 = pure T.«FloatCC.UnorderedOrLessThan»
  t2268 : Interp.termOf p 2268 = pure T.«FloatCC.UnorderedOrLessThanOrEqual»
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
  t2284 : Interp.termOf p 2284 = pure T.«Opcode.Jump»
  t2285 : Interp.termOf p 2285 = pure T.«Opcode.Brif»
  t2286 : Interp.termOf p 2286 = pure T.«Opcode.BrTable»
  t2288 : Interp.termOf p 2288 = pure T.«Opcode.Trap»
  t2291 : Interp.termOf p 2291 = pure T.«Opcode.Return»
  t2292 : Interp.termOf p 2292 = pure T.«Opcode.Call»
  t2304 : Interp.termOf p 2304 = pure T.«Opcode.Smin»
  t2305 : Interp.termOf p 2305 = pure T.«Opcode.Umin»
  t2306 : Interp.termOf p 2306 = pure T.«Opcode.Smax»
  t2307 : Interp.termOf p 2307 = pure T.«Opcode.Umax»
  t2313 : Interp.termOf p 2313 = pure T.«Opcode.Load»
  t2314 : Interp.termOf p 2314 = pure T.«Opcode.Store»
  t2315 : Interp.termOf p 2315 = pure T.«Opcode.Uload8»
  t2316 : Interp.termOf p 2316 = pure T.«Opcode.Sload8»
  t2317 : Interp.termOf p 2317 = pure T.«Opcode.Istore8»
  t2318 : Interp.termOf p 2318 = pure T.«Opcode.Uload16»
  t2319 : Interp.termOf p 2319 = pure T.«Opcode.Sload16»
  t2320 : Interp.termOf p 2320 = pure T.«Opcode.Istore16»
  t2321 : Interp.termOf p 2321 = pure T.«Opcode.Uload32»
  t2322 : Interp.termOf p 2322 = pure T.«Opcode.Sload32»
  t2323 : Interp.termOf p 2323 = pure T.«Opcode.Istore32»
  t2331 : Interp.termOf p 2331 = pure T.«Opcode.StackAddr»
  t2333 : Interp.termOf p 2333 = pure T.«Opcode.SymbolValue»
  t2341 : Interp.termOf p 2341 = pure T.«Opcode.Iconst»
  t2348 : Interp.termOf p 2348 = pure T.«Opcode.Nop»
  t2349 : Interp.termOf p 2349 = pure T.«Opcode.Select»
  t2356 : Interp.termOf p 2356 = pure T.«Opcode.Icmp»
  t2357 : Interp.termOf p 2357 = pure T.«Opcode.Iadd»
  t2358 : Interp.termOf p 2358 = pure T.«Opcode.Isub»
  t2359 : Interp.termOf p 2359 = pure T.«Opcode.Ineg»
  t2361 : Interp.termOf p 2361 = pure T.«Opcode.Imul»
  t2362 : Interp.termOf p 2362 = pure T.«Opcode.Umulhi»
  t2363 : Interp.termOf p 2363 = pure T.«Opcode.Smulhi»
  t2366 : Interp.termOf p 2366 = pure T.«Opcode.Udiv»
  t2367 : Interp.termOf p 2367 = pure T.«Opcode.Sdiv»
  t2368 : Interp.termOf p 2368 = pure T.«Opcode.Urem»
  t2369 : Interp.termOf p 2369 = pure T.«Opcode.Srem»
  t2372 : Interp.termOf p 2372 = pure T.«Opcode.UaddOverflow»
  t2376 : Interp.termOf p 2376 = pure T.«Opcode.UmulOverflow»
  t2377 : Interp.termOf p 2377 = pure T.«Opcode.SmulOverflow»
  t2381 : Interp.termOf p 2381 = pure T.«Opcode.Band»
  t2382 : Interp.termOf p 2382 = pure T.«Opcode.Bor»
  t2383 : Interp.termOf p 2383 = pure T.«Opcode.Bxor»
  t2384 : Interp.termOf p 2384 = pure T.«Opcode.Bnot»
  t2385 : Interp.termOf p 2385 = pure T.«Opcode.Rotl»
  t2386 : Interp.termOf p 2386 = pure T.«Opcode.Rotr»
  t2387 : Interp.termOf p 2387 = pure T.«Opcode.Ishl»
  t2388 : Interp.termOf p 2388 = pure T.«Opcode.Ushr»
  t2389 : Interp.termOf p 2389 = pure T.«Opcode.Sshr»
  t2390 : Interp.termOf p 2390 = pure T.«Opcode.Bitrev»
  t2391 : Interp.termOf p 2391 = pure T.«Opcode.Clz»
  t2393 : Interp.termOf p 2393 = pure T.«Opcode.Ctz»
  t2394 : Interp.termOf p 2394 = pure T.«Opcode.Bswap»
  t2395 : Interp.termOf p 2395 = pure T.«Opcode.Popcnt»
  t2396 : Interp.termOf p 2396 = pure T.«Opcode.Fcmp»
  t2415 : Interp.termOf p 2415 = pure T.«Opcode.Ireduce»
  t2425 : Interp.termOf p 2425 = pure T.«Opcode.Uextend»
  t2426 : Interp.termOf p 2426 = pure T.«Opcode.Sextend»
  t2449 : Interp.termOf p 2449 = pure T.«InstructionData.Binary»
  t2451 : Interp.termOf p 2451 = pure T.«InstructionData.BranchTable»
  t2452 : Interp.termOf p 2452 = pure T.«InstructionData.Brif»
  t2453 : Interp.termOf p 2453 = pure T.«InstructionData.Call»
  t2458 : Interp.termOf p 2458 = pure T.«InstructionData.FloatCompare»
  t2461 : Interp.termOf p 2461 = pure T.«InstructionData.IntCompare»
  t2462 : Interp.termOf p 2462 = pure T.«InstructionData.Jump»
  t2463 : Interp.termOf p 2463 = pure T.«InstructionData.Load»
  t2465 : Interp.termOf p 2465 = pure T.«InstructionData.MultiAry»
  t2466 : Interp.termOf p 2466 = pure T.«InstructionData.NullAry»
  t2468 : Interp.termOf p 2468 = pure T.«InstructionData.StackAddr»
  t2469 : Interp.termOf p 2469 = pure T.«InstructionData.Store»
  t2471 : Interp.termOf p 2471 = pure T.«InstructionData.Ternary»
  t2473 : Interp.termOf p 2473 = pure T.«InstructionData.Trap»
  t2476 : Interp.termOf p 2476 = pure T.«InstructionData.Unary»
  t2478 : Interp.termOf p 2478 = pure T.«InstructionData.UnaryGlobalValue»
  t2482 : Interp.termOf p 2482 = pure T.«InstructionData.UnaryImm»
  lower : p.termByName? "lower" = some T.lower

/-! ### The facts for `program` (each `rfl`: indexing the flat tables, up to ~2500 deep in
`Meta.whnf`; one declaration each, so each has its own heartbeat budget) -/

set_option maxRecDepth 20000

theorem program_term_1 : Interp.termOf program 1 = pure T.«def_inst» := rfl
theorem program_term_2 : Interp.termOf program 2 = pure T.«value_type» := rfl
theorem program_term_31 : Interp.termOf program 31 = pure T.«i64_sextend_imm64» := rfl
theorem program_term_87 : Interp.termOf program 87 = pure T.«ty_bits» := rfl
theorem program_term_93 : Interp.termOf program 93 = pure T.«ty_bytes» := rfl
theorem program_term_103 : Interp.termOf program 103 = pure T.«little_or_native_endian» := rfl
theorem program_term_110 : Interp.termOf program 110 = pure T.«fits_in_16» := rfl
theorem program_term_111 : Interp.termOf program 111 = pure T.«fits_in_32» := rfl
theorem program_term_113 : Interp.termOf program 113 = pure T.«fits_in_64» := rfl
theorem program_term_118 : Interp.termOf program 118 = pure T.«ty_int_ref_scalar_64» := rfl
theorem program_term_119 : Interp.termOf program 119 = pure T.«ty_int_ref_scalar_64_extract» := rfl
theorem program_term_120 : Interp.termOf program 120 = pure T.«ty_32_or_64» := rfl
theorem program_term_126 : Interp.termOf program 126 = pure T.«ty_int» := rfl
theorem program_term_128 : Interp.termOf program 128 = pure T.«ty_scalar_float» := rfl
theorem program_term_132 : Interp.termOf program 132 = pure T.«ty_vec64» := rfl
theorem program_term_133 : Interp.termOf program 133 = pure T.«ty_vec128» := rfl
theorem program_term_141 : Interp.termOf program 141 = pure T.«not_i64x2» := rfl
theorem program_term_144 : Interp.termOf program 144 = pure T.«u64_from_imm64» := rfl
theorem program_term_145 : Interp.termOf program 145 = pure T.«nonzero_u64_from_imm64» := rfl
theorem program_term_152 : Interp.termOf program 152 = pure T.«multi_lane» := rfl
theorem program_term_153 : Interp.termOf program 153 = pure T.«dynamic_lane» := rfl
theorem program_term_156 : Interp.termOf program 156 = pure T.«offset32_to_i32» := rfl
theorem program_term_157 : Interp.termOf program 157 = pure T.«i32_to_offset32» := rfl
theorem program_term_159 : Interp.termOf program 159 = pure T.«signed_cond_code» := rfl
theorem program_term_160 : Interp.termOf program 160 = pure T.«unsigned_cond_code» := rfl
theorem program_term_161 : Interp.termOf program 161 = pure T.«trap_code_division_by_zero» := rfl
theorem program_term_162 : Interp.termOf program 162 = pure T.«trap_code_integer_overflow» := rfl
theorem program_term_164 : Interp.termOf program 164 = pure T.«value_reg» := rfl
theorem program_term_166 : Interp.termOf program 166 = pure T.«value_regs» := rfl
theorem program_term_169 : Interp.termOf program 169 = pure T.«output_none» := rfl
theorem program_term_170 : Interp.termOf program 170 = pure T.«output» := rfl
theorem program_term_172 : Interp.termOf program 172 = pure T.«output_reg» := rfl
theorem program_rulesOf_172 : program.rulesOf 172 =
    [rule_prelude_lower_105] := rfl
theorem program_term_174 : Interp.termOf program 174 = pure T.«output_vec» := rfl
theorem program_term_175 : Interp.termOf program 175 = pure T.«temp_writable_reg» := rfl
theorem program_term_178 : Interp.termOf program 178 = pure T.«invalid_reg» := rfl
theorem program_term_181 : Interp.termOf program 181 = pure T.«opportunistic_def» := rfl
theorem program_term_182 : Interp.termOf program 182 = pure T.«put_in_reg» := rfl
theorem program_term_183 : Interp.termOf program 183 = pure T.«put_in_regs» := rfl
theorem program_term_184 : Interp.termOf program 184 = pure T.«put_in_regs_vec» := rfl
theorem program_term_185 : Interp.termOf program 185 = pure T.«value_regs_get» := rfl
theorem program_term_190 : Interp.termOf program 190 = pure T.«single_target» := rfl
theorem program_term_191 : Interp.termOf program 191 = pure T.«two_targets» := rfl
theorem program_term_192 : Interp.termOf program 192 = pure T.«jump_table_targets» := rfl
theorem program_term_193 : Interp.termOf program 193 = pure T.«jump_table_size» := rfl
theorem program_term_194 : Interp.termOf program 194 = pure T.«value_list_slice» := rfl
theorem program_term_201 : Interp.termOf program 201 = pure T.«writable_reg_to_reg» := rfl
theorem program_term_205 : Interp.termOf program 205 = pure T.«first_result» := rfl
theorem program_term_207 : Interp.termOf program 207 = pure T.«is_second_result» := rfl
theorem program_term_209 : Interp.termOf program 209 = pure T.«inst_data_value» := rfl
theorem program_term_219 : Interp.termOf program 219 = pure T.«i64_from_iconst» := rfl
theorem program_term_221 : Interp.termOf program 221 = pure T.«is_sinkable_inst» := rfl
theorem program_term_222 : Interp.termOf program 222 = pure T.«maybe_uextend» := rfl
theorem program_term_235 : Interp.termOf program 235 = pure T.«emit» := rfl
theorem program_term_236 : Interp.termOf program 236 = pure T.«sink_inst» := rfl
theorem program_term_242 : Interp.termOf program 242 = pure T.«emit_side_effect» := rfl
theorem program_rulesOf_242 : program.rulesOf 242 =
    [rule_prelude_lower_522, rule_prelude_lower_524, rule_prelude_lower_527] := rfl
theorem program_term_243 : Interp.termOf program 243 = pure T.«side_effect» := rfl
theorem program_rulesOf_243 : program.rulesOf 243 =
    [rule_prelude_lower_535] := rfl
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
theorem program_term_256 : Interp.termOf program 256 = pure T.«with_flags_side_effect» := rfl
theorem program_rulesOf_256 : program.rulesOf 256 =
    [rule_prelude_lower_1000, rule_prelude_lower_1006, rule_prelude_lower_1016, rule_prelude_lower_1023, rule_prelude_lower_1030, rule_prelude_lower_1035, rule_prelude_lower_1040, rule_prelude_lower_1045, rule_prelude_lower_1050] := rfl
theorem program_term_264 : Interp.termOf program 264 = pure T.«box_external_name» := rfl
theorem program_term_265 : Interp.termOf program 265 = pure T.«func_ref_data» := rfl
theorem program_term_267 : Interp.termOf program 267 = pure T.«symbol_value_data» := rfl
theorem program_term_278 : Interp.termOf program 278 = pure T.«abi_sig» := rfl
theorem program_term_286 : Interp.termOf program 286 = pure T.«abi_stackslot_addr» := rfl
theorem program_term_287 : Interp.termOf program 287 = pure T.«abi_stackslot_offset_into_slot_region» := rfl
theorem program_term_294 : Interp.termOf program 294 = pure T.«lower_return» := rfl
theorem program_rulesOf_294 : program.rulesOf 294 =
    [rule_prelude_lower_1493] := rfl
theorem program_term_295 : Interp.termOf program 295 = pure T.«gen_return» := rfl
theorem program_term_296 : Interp.termOf program 296 = pure T.«gen_call_output» := rfl
theorem program_term_297 : Interp.termOf program 297 = pure T.«gen_call_args» := rfl
theorem program_term_299 : Interp.termOf program 299 = pure T.«gen_call_rets» := rfl
theorem program_term_303 : Interp.termOf program 303 = pure T.«try_call_none» := rfl
theorem program_term_304 : Interp.termOf program 304 = pure T.«safe_divisor_from_imm64» := rfl
theorem program_term_305 : Interp.termOf program 305 = pure T.«operand_size» := rfl
theorem program_rulesOf_305 : program.rulesOf 305 =
    [rule_inst_1592, rule_inst_1593] := rfl
theorem program_term_306 : Interp.termOf program 306 = pure T.«diff_from_32» := rfl
theorem program_rulesOf_306 : program.rulesOf 306 =
    [rule_inst_1599, rule_inst_1600] := rfl
theorem program_term_307 : Interp.termOf program 307 = pure T.«scalar_size» := rfl
theorem program_rulesOf_307 : program.rulesOf 307 =
    [rule_inst_1623, rule_inst_1624, rule_inst_1625, rule_inst_1626, rule_inst_1627, rule_inst_1629, rule_inst_1630, rule_inst_1631] := rfl
theorem program_term_310 : Interp.termOf program 310 = pure T.«vector_size» := rfl
theorem program_rulesOf_310 : program.rulesOf 310 =
    [rule_inst_1690, rule_inst_1691, rule_inst_1692, rule_inst_1693, rule_inst_1694, rule_inst_1695, rule_inst_1696, rule_inst_1697, rule_inst_1698, rule_inst_1699, rule_inst_1700, rule_inst_1701, rule_inst_1702, rule_inst_1703] := rfl
theorem program_term_316 : Interp.termOf program 316 = pure T.«use_fp16» := rfl
theorem program_term_318 : Interp.termOf program 318 = pure T.«move_wide_const_from_u64» := rfl
theorem program_term_319 : Interp.termOf program 319 = pure T.«move_wide_const_from_inverted_u64» := rfl
theorem program_term_320 : Interp.termOf program 320 = pure T.«imm_logic_from_u64» := rfl
theorem program_term_321 : Interp.termOf program 321 = pure T.«imm_size_from_type» := rfl
theorem program_term_322 : Interp.termOf program 322 = pure T.«imm_logic_from_imm64» := rfl
theorem program_term_323 : Interp.termOf program 323 = pure T.«imm_shift_from_imm64» := rfl
theorem program_term_324 : Interp.termOf program 324 = pure T.«imm_shift_from_u8» := rfl
theorem program_term_325 : Interp.termOf program 325 = pure T.«imm12_from_u64» := rfl
theorem program_term_326 : Interp.termOf program 326 = pure T.«u8_into_uimm5» := rfl
theorem program_term_327 : Interp.termOf program 327 = pure T.«u8_into_imm12» := rfl
theorem program_term_328 : Interp.termOf program 328 = pure T.«u64_into_imm_logic» := rfl
theorem program_term_329 : Interp.termOf program 329 = pure T.«branch_target» := rfl
theorem program_term_330 : Interp.termOf program 330 = pure T.«targets_jt_space» := rfl
theorem program_term_336 : Interp.termOf program 336 = pure T.«lshl_from_imm64» := rfl
theorem program_term_338 : Interp.termOf program 338 = pure T.«ashr_from_u64» := rfl
theorem program_term_339 : Interp.termOf program 339 = pure T.«integral_ty» := rfl
theorem program_term_344 : Interp.termOf program 344 = pure T.«imm12_from_negated_value» := rfl
theorem program_rulesOf_344 : program.rulesOf 344 =
    [rule_inst_2404] := rfl
theorem program_term_345 : Interp.termOf program 345 = pure T.«extended_value_from_value» := rfl
theorem program_term_346 : Interp.termOf program 346 = pure T.«put_extended_in_reg» := rfl
theorem program_term_347 : Interp.termOf program 347 = pure T.«get_extended_op» := rfl
theorem program_term_348 : Interp.termOf program 348 = pure T.«nzcv» := rfl
theorem program_term_349 : Interp.termOf program 349 = pure T.«cond_br_zero» := rfl
theorem program_term_350 : Interp.termOf program 350 = pure T.«cond_br_not_zero» := rfl
theorem program_term_351 : Interp.termOf program 351 = pure T.«cond_br_cond» := rfl
theorem program_term_352 : Interp.termOf program 352 = pure T.«zero_reg» := rfl
theorem program_term_356 : Interp.termOf program 356 = pure T.«writable_zero_reg» := rfl
theorem program_term_358 : Interp.termOf program 358 = pure T.«movz» := rfl
theorem program_rulesOf_358 : program.rulesOf 358 =
    [rule_inst_2513] := rfl
theorem program_term_359 : Interp.termOf program 359 = pure T.«movn» := rfl
theorem program_rulesOf_359 : program.rulesOf 359 =
    [rule_inst_2521] := rfl
theorem program_term_360 : Interp.termOf program 360 = pure T.«alu_rr_imm_logic» := rfl
theorem program_rulesOf_360 : program.rulesOf 360 =
    [rule_inst_2529] := rfl
theorem program_term_361 : Interp.termOf program 361 = pure T.«alu_rr_imm_shift» := rfl
theorem program_rulesOf_361 : program.rulesOf 361 =
    [rule_inst_2537] := rfl
theorem program_term_362 : Interp.termOf program 362 = pure T.«alu_rrr» := rfl
theorem program_rulesOf_362 : program.rulesOf 362 =
    [rule_inst_2545] := rfl
theorem program_term_363 : Interp.termOf program 363 = pure T.«vec_rrr» := rfl
theorem program_rulesOf_363 : program.rulesOf 363 =
    [rule_inst_2552] := rfl
theorem program_term_370 : Interp.termOf program 370 = pure T.«fpu_cmp» := rfl
theorem program_rulesOf_370 : program.rulesOf 370 =
    [rule_inst_2606] := rfl
theorem program_term_371 : Interp.termOf program 371 = pure T.«vec_lanes» := rfl
theorem program_rulesOf_371 : program.rulesOf 371 =
    [rule_inst_2612] := rfl
theorem program_term_376 : Interp.termOf program 376 = pure T.«alu_rr_imm12» := rfl
theorem program_rulesOf_376 : program.rulesOf 376 =
    [rule_inst_2648] := rfl
theorem program_term_377 : Interp.termOf program 377 = pure T.«alu_rrr_shift» := rfl
theorem program_rulesOf_377 : program.rulesOf 377 =
    [rule_inst_2656] := rfl
theorem program_term_379 : Interp.termOf program 379 = pure T.«cmp_rr_shift_asr» := rfl
theorem program_rulesOf_379 : program.rulesOf 379 =
    [rule_inst_2675] := rfl
theorem program_term_380 : Interp.termOf program 380 = pure T.«alu_rrr_extend» := rfl
theorem program_rulesOf_380 : program.rulesOf 380 =
    [rule_inst_2684] := rfl
theorem program_term_381 : Interp.termOf program 381 = pure T.«alu_rr_extend_reg» := rfl
theorem program_rulesOf_381 : program.rulesOf 381 =
    [rule_inst_2693] := rfl
theorem program_term_382 : Interp.termOf program 382 = pure T.«alu_rrrr» := rfl
theorem program_rulesOf_382 : program.rulesOf 382 =
    [rule_inst_2701] := rfl
theorem program_term_383 : Interp.termOf program 383 = pure T.«alu_rrr_with_flags_paired» := rfl
theorem program_rulesOf_383 : program.rulesOf 383 =
    [rule_inst_2709] := rfl
theorem program_term_385 : Interp.termOf program 385 = pure T.«sbcs_side_effect» := rfl
theorem program_rulesOf_385 : program.rulesOf 385 =
    [rule_inst_2726] := rfl
theorem program_term_386 : Interp.termOf program 386 = pure T.«bit_rr» := rfl
theorem program_rulesOf_386 : program.rulesOf 386 =
    [rule_inst_2733] := rfl
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
theorem program_term_395 : Interp.termOf program 395 = pure T.«vec_misc» := rfl
theorem program_rulesOf_395 : program.rulesOf 395 =
    [rule_inst_2802] := rfl
theorem program_term_406 : Interp.termOf program 406 = pure T.«fpu_csel» := rfl
theorem program_rulesOf_406 : program.rulesOf 406 =
    [rule_inst_2891, rule_inst_2888, rule_inst_2898, rule_inst_2904] := rfl
theorem program_term_407 : Interp.termOf program 407 = pure T.«vec_csel» := rfl
theorem program_rulesOf_407 : program.rulesOf 407 =
    [rule_inst_2912] := rfl
theorem program_term_409 : Interp.termOf program 409 = pure T.«mov_to_fpu» := rfl
theorem program_rulesOf_409 : program.rulesOf 409 =
    [rule_inst_2930] := rfl
theorem program_term_410 : Interp.termOf program 410 = pure T.«size_for_mov_to_fpu» := rfl
theorem program_rulesOf_410 : program.rulesOf 410 =
    [rule_inst_2941, rule_inst_2938] := rfl
theorem program_term_414 : Interp.termOf program 414 = pure T.«mov_from_vec» := rfl
theorem program_rulesOf_414 : program.rulesOf 414 =
    [rule_inst_2970] := rfl
theorem program_term_417 : Interp.termOf program 417 = pure T.«extend» := rfl
theorem program_rulesOf_417 : program.rulesOf 417 =
    [rule_inst_2991] := rfl
theorem program_term_418 : Interp.termOf program 418 = pure T.«bitfield_move» := rfl
theorem program_rulesOf_418 : program.rulesOf 418 =
    [rule_inst_2999] := rfl
theorem program_term_424 : Interp.termOf program 424 = pure T.«tst_imm» := rfl
theorem program_rulesOf_424 : program.rulesOf 424 =
    [rule_inst_3044] := rfl
theorem program_term_425 : Interp.termOf program 425 = pure T.«csel» := rfl
theorem program_rulesOf_425 : program.rulesOf 425 =
    [rule_inst_3059] := rfl
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
theorem program_term_434 : Interp.termOf program 434 = pure T.«add_extend» := rfl
theorem program_rulesOf_434 : program.rulesOf 434 =
    [rule_inst_3126] := rfl
theorem program_term_435 : Interp.termOf program 435 = pure T.«add_shift» := rfl
theorem program_rulesOf_435 : program.rulesOf 435 =
    [rule_inst_3130] := rfl
theorem program_term_437 : Interp.termOf program 437 = pure T.«sub» := rfl
theorem program_rulesOf_437 : program.rulesOf 437 =
    [rule_inst_3138] := rfl
theorem program_term_438 : Interp.termOf program 438 = pure T.«sub_imm» := rfl
theorem program_rulesOf_438 : program.rulesOf 438 =
    [rule_inst_3142] := rfl
theorem program_term_439 : Interp.termOf program 439 = pure T.«sub_extend» := rfl
theorem program_rulesOf_439 : program.rulesOf 439 =
    [rule_inst_3146] := rfl
theorem program_term_440 : Interp.termOf program 440 = pure T.«sub_shift» := rfl
theorem program_rulesOf_440 : program.rulesOf 440 =
    [rule_inst_3150] := rfl
theorem program_term_443 : Interp.termOf program 443 = pure T.«madd» := rfl
theorem program_rulesOf_443 : program.rulesOf 443 =
    [rule_inst_3177] := rfl
theorem program_term_444 : Interp.termOf program 444 = pure T.«msub» := rfl
theorem program_rulesOf_444 : program.rulesOf 444 =
    [rule_inst_3182] := rfl
theorem program_term_451 : Interp.termOf program 451 = pure T.«umulh» := rfl
theorem program_rulesOf_451 : program.rulesOf 451 =
    [rule_inst_3213] := rfl
theorem program_term_452 : Interp.termOf program 452 = pure T.«smulh» := rfl
theorem program_rulesOf_452 : program.rulesOf 452 =
    [rule_inst_3218] := rfl
theorem program_term_469 : Interp.termOf program 469 = pure T.«addp» := rfl
theorem program_rulesOf_469 : program.rulesOf 469 =
    [rule_inst_3290] := rfl
theorem program_term_473 : Interp.termOf program 473 = pure T.«addv» := rfl
theorem program_rulesOf_473 : program.rulesOf 473 =
    [rule_inst_3311] := rfl
theorem program_term_487 : Interp.termOf program 487 = pure T.«asr_imm» := rfl
theorem program_rulesOf_487 : program.rulesOf 487 =
    [rule_inst_3366] := rfl
theorem program_term_488 : Interp.termOf program 488 = pure T.«lsr» := rfl
theorem program_rulesOf_488 : program.rulesOf 488 =
    [rule_inst_3371] := rfl
theorem program_term_489 : Interp.termOf program 489 = pure T.«lsr_imm» := rfl
theorem program_rulesOf_489 : program.rulesOf 489 =
    [rule_inst_3375] := rfl
theorem program_term_490 : Interp.termOf program 490 = pure T.«lsl» := rfl
theorem program_rulesOf_490 : program.rulesOf 490 =
    [rule_inst_3380] := rfl
theorem program_term_491 : Interp.termOf program 491 = pure T.«lsl_imm» := rfl
theorem program_rulesOf_491 : program.rulesOf 491 =
    [rule_inst_3384] := rfl
theorem program_term_492 : Interp.termOf program 492 = pure T.«a64_udiv» := rfl
theorem program_rulesOf_492 : program.rulesOf 492 =
    [rule_inst_3389] := rfl
theorem program_term_493 : Interp.termOf program 493 = pure T.«a64_sdiv» := rfl
theorem program_rulesOf_493 : program.rulesOf 493 =
    [rule_inst_3394] := rfl
theorem program_term_495 : Interp.termOf program 495 = pure T.«orr_not» := rfl
theorem program_rulesOf_495 : program.rulesOf 495 =
    [rule_inst_3403] := rfl
theorem program_term_496 : Interp.termOf program 496 = pure T.«orr_not_shift» := rfl
theorem program_rulesOf_496 : program.rulesOf 496 =
    [rule_inst_3407] := rfl
theorem program_term_497 : Interp.termOf program 497 = pure T.«orr» := rfl
theorem program_rulesOf_497 : program.rulesOf 497 =
    [rule_inst_3412] := rfl
theorem program_term_498 : Interp.termOf program 498 = pure T.«orr_imm» := rfl
theorem program_rulesOf_498 : program.rulesOf 498 =
    [rule_inst_3416] := rfl
theorem program_term_501 : Interp.termOf program 501 = pure T.«and_reg» := rfl
theorem program_rulesOf_501 : program.rulesOf 501 =
    [rule_inst_3427] := rfl
theorem program_term_502 : Interp.termOf program 502 = pure T.«and_imm» := rfl
theorem program_rulesOf_502 : program.rulesOf 502 =
    [rule_inst_3431] := rfl
theorem program_term_513 : Interp.termOf program 513 = pure T.«a64_rotr» := rfl
theorem program_rulesOf_513 : program.rulesOf 513 =
    [rule_inst_3478] := rfl
theorem program_term_514 : Interp.termOf program 514 = pure T.«a64_rotr_imm» := rfl
theorem program_rulesOf_514 : program.rulesOf 514 =
    [rule_inst_3482] := rfl
theorem program_term_515 : Interp.termOf program 515 = pure T.«a64_extr» := rfl
theorem program_rulesOf_515 : program.rulesOf 515 =
    [rule_inst_3487] := rfl
theorem program_term_516 : Interp.termOf program 516 = pure T.«a64_extr_imm» := rfl
theorem program_term_517 : Interp.termOf program 517 = pure T.«rbit» := rfl
theorem program_rulesOf_517 : program.rulesOf 517 =
    [rule_inst_3512] := rfl
theorem program_term_518 : Interp.termOf program 518 = pure T.«a64_clz» := rfl
theorem program_rulesOf_518 : program.rulesOf 518 =
    [rule_inst_3517] := rfl
theorem program_term_520 : Interp.termOf program 520 = pure T.«a64_rev16» := rfl
theorem program_rulesOf_520 : program.rulesOf 520 =
    [rule_inst_3527] := rfl
theorem program_term_521 : Interp.termOf program 521 = pure T.«a64_rev32» := rfl
theorem program_rulesOf_521 : program.rulesOf 521 =
    [rule_inst_3531] := rfl
theorem program_term_522 : Interp.termOf program 522 = pure T.«a64_rev64» := rfl
theorem program_rulesOf_522 : program.rulesOf 522 =
    [rule_inst_3535] := rfl
theorem program_term_524 : Interp.termOf program 524 = pure T.«vec_cnt» := rfl
theorem program_rulesOf_524 : program.rulesOf 524 =
    [rule_inst_3545] := rfl
theorem program_term_528 : Interp.termOf program 528 = pure T.«udf» := rfl
theorem program_rulesOf_528 : program.rulesOf 528 =
    [rule_inst_3569] := rfl
theorem program_term_529 : Interp.termOf program 529 = pure T.«aarch64_uload8» := rfl
theorem program_rulesOf_529 : program.rulesOf 529 =
    [rule_inst_3576] := rfl
theorem program_term_530 : Interp.termOf program 530 = pure T.«aarch64_sload8» := rfl
theorem program_rulesOf_530 : program.rulesOf 530 =
    [rule_inst_3583] := rfl
theorem program_term_531 : Interp.termOf program 531 = pure T.«aarch64_uload16» := rfl
theorem program_rulesOf_531 : program.rulesOf 531 =
    [rule_inst_3590] := rfl
theorem program_term_532 : Interp.termOf program 532 = pure T.«aarch64_sload16» := rfl
theorem program_rulesOf_532 : program.rulesOf 532 =
    [rule_inst_3597] := rfl
theorem program_term_533 : Interp.termOf program 533 = pure T.«aarch64_uload32» := rfl
theorem program_rulesOf_533 : program.rulesOf 533 =
    [rule_inst_3605] := rfl
theorem program_term_534 : Interp.termOf program 534 = pure T.«aarch64_sload32» := rfl
theorem program_rulesOf_534 : program.rulesOf 534 =
    [rule_inst_3612] := rfl
theorem program_term_535 : Interp.termOf program 535 = pure T.«aarch64_uload64» := rfl
theorem program_rulesOf_535 : program.rulesOf 535 =
    [rule_inst_3620] := rfl
theorem program_term_541 : Interp.termOf program 541 = pure T.«aarch64_store8» := rfl
theorem program_rulesOf_541 : program.rulesOf 541 =
    [rule_inst_3660] := rfl
theorem program_term_542 : Interp.termOf program 542 = pure T.«aarch64_store16» := rfl
theorem program_rulesOf_542 : program.rulesOf 542 =
    [rule_inst_3666] := rfl
theorem program_term_543 : Interp.termOf program 543 = pure T.«aarch64_store32» := rfl
theorem program_rulesOf_543 : program.rulesOf 543 =
    [rule_inst_3672] := rfl
theorem program_term_544 : Interp.termOf program 544 = pure T.«aarch64_store64» := rfl
theorem program_rulesOf_544 : program.rulesOf 544 =
    [rule_inst_3678] := rfl
theorem program_term_553 : Interp.termOf program 553 = pure T.«imm» := rfl
theorem program_rulesOf_553 : program.rulesOf 553 =
    [rule_inst_3742, rule_inst_3745, rule_inst_3751, rule_inst_3786, rule_inst_3790] := rfl
theorem program_term_554 : Interp.termOf program 554 = pure T.«load_constant_full» := rfl
theorem program_term_555 : Interp.termOf program 555 = pure T.«put_in_reg_sext32» := rfl
theorem program_rulesOf_555 : program.rulesOf 555 =
    [rule_inst_3803, rule_inst_3804, rule_inst_3799] := rfl
theorem program_term_556 : Interp.termOf program 556 = pure T.«put_in_reg_zext32» := rfl
theorem program_rulesOf_556 : program.rulesOf 556 =
    [rule_inst_3813, rule_inst_3814, rule_inst_3809] := rfl
theorem program_term_557 : Interp.termOf program 557 = pure T.«put_in_reg_sext64» := rfl
theorem program_rulesOf_557 : program.rulesOf 557 =
    [rule_inst_3819, rule_inst_3823] := rfl
theorem program_term_558 : Interp.termOf program 558 = pure T.«put_in_reg_zext64» := rfl
theorem program_rulesOf_558 : program.rulesOf 558 =
    [rule_inst_3829, rule_inst_3833] := rfl
theorem program_term_559 : Interp.termOf program 559 = pure T.«trap_if_zero_divisor» := rfl
theorem program_rulesOf_559 : program.rulesOf 559 =
    [rule_inst_3838] := rfl
theorem program_term_560 : Interp.termOf program 560 = pure T.«size_from_ty» := rfl
theorem program_rulesOf_560 : program.rulesOf 560 =
    [rule_inst_3852, rule_inst_3853] := rfl
theorem program_term_561 : Interp.termOf program 561 = pure T.«trap_if_div_overflow» := rfl
theorem program_rulesOf_561 : program.rulesOf 561 =
    [rule_inst_3861] := rfl
theorem program_term_562 : Interp.termOf program 562 = pure T.«intmin_check» := rfl
theorem program_rulesOf_562 : program.rulesOf 562 =
    [rule_inst_3888, rule_inst_3892] := rfl
theorem program_term_565 : Interp.termOf program 565 = pure T.«alu_rs_imm_logic_commutative» := rfl
theorem program_rulesOf_565 : program.rulesOf 565 =
    [rule_inst_3923, rule_inst_3931, rule_inst_3920, rule_inst_3928, rule_inst_3916] := rfl
theorem program_term_566 : Interp.termOf program 566 = pure T.«alu_rs_imm_logic» := rfl
theorem program_rulesOf_566 : program.rulesOf 566 =
    [rule_inst_3941, rule_inst_3944, rule_inst_3939] := rfl
theorem program_term_569 : Interp.termOf program 569 = pure T.«is_pic» := rfl
theorem program_term_570 : Interp.termOf program 570 = pure T.«load_ext_name» := rfl
theorem program_rulesOf_570 : program.rulesOf 570 =
    [rule_inst_3986, rule_inst_3991, rule_inst_3996, rule_inst_3983] := rfl
theorem program_term_571 : Interp.termOf program 571 = pure T.«load_ext_name_got» := rfl
theorem program_rulesOf_571 : program.rulesOf 571 =
    [rule_inst_4002] := rfl
theorem program_term_572 : Interp.termOf program 572 = pure T.«load_ext_name_near» := rfl
theorem program_rulesOf_572 : program.rulesOf 572 =
    [rule_inst_4009] := rfl
theorem program_term_573 : Interp.termOf program 573 = pure T.«load_ext_name_far» := rfl
theorem program_rulesOf_573 : program.rulesOf 573 =
    [rule_inst_4016] := rfl
theorem program_term_574 : Interp.termOf program 574 = pure T.«amode» := rfl
theorem program_rulesOf_574 : program.rulesOf 574 =
    [rule_inst_4047, rule_inst_4043, rule_inst_4040, rule_inst_4038] := rfl
theorem program_term_575 : Interp.termOf program 575 = pure T.«amode_no_more_iconst» := rfl
theorem program_rulesOf_575 : program.rulesOf 575 =
    [rule_inst_4103, rule_inst_4096, rule_inst_4093, rule_inst_4081, rule_inst_4083, rule_inst_4077, rule_inst_4079, rule_inst_4075, rule_inst_4064, rule_inst_4061, rule_inst_4056] := rfl
theorem program_term_576 : Interp.termOf program 576 = pure T.«amode_reg_scaled» := rfl
theorem program_rulesOf_576 : program.rulesOf 576 =
    [rule_inst_4111, rule_inst_4113, rule_inst_4109] := rfl
theorem program_term_577 : Interp.termOf program 577 = pure T.«amode_add» := rfl
theorem program_rulesOf_577 : program.rulesOf 577 =
    [rule_inst_4125, rule_inst_4122, rule_inst_4120] := rfl
theorem program_term_580 : Interp.termOf program 580 = pure T.«uimm12_scaled_from_i64» := rfl
theorem program_term_581 : Interp.termOf program 581 = pure T.«uimm12_scaled_nonzero_from_i64» := rfl
theorem program_term_582 : Interp.termOf program 582 = pure T.«simm9_from_i64» := rfl
theorem program_term_592 : Interp.termOf program 592 = pure T.«cond_code» := rfl
theorem program_term_593 : Interp.termOf program 593 = pure T.«invert_cond» := rfl
theorem program_term_634 : Interp.termOf program 634 = pure T.«gen_call_info» := rfl
theorem program_term_635 : Interp.termOf program 635 = pure T.«gen_call_ind_info» := rfl
theorem program_term_638 : Interp.termOf program 638 = pure T.«call_impl» := rfl
theorem program_rulesOf_638 : program.rulesOf 638 =
    [rule_inst_4780] := rfl
theorem program_term_639 : Interp.termOf program 639 = pure T.«call_ind_impl» := rfl
theorem program_rulesOf_639 : program.rulesOf 639 =
    [rule_inst_4786] := rfl
theorem program_term_643 : Interp.termOf program 643 = pure T.«compute_stack_addr» := rfl
theorem program_rulesOf_643 : program.rulesOf 643 =
    [rule_inst_4810] := rfl
theorem program_term_649 : Interp.termOf program 649 = pure T.«cond_result_invert» := rfl
theorem program_rulesOf_649 : program.rulesOf 649 =
    [rule_inst_4954, rule_inst_4955, rule_inst_4956, rule_inst_4957, rule_inst_4959] := rfl
theorem program_term_650 : Interp.termOf program 650 = pure T.«is_nonzero_cmp» := rfl
theorem program_rulesOf_650 : program.rulesOf 650 =
    [rule_inst_4965, rule_inst_4966, rule_inst_4967] := rfl
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
theorem program_term_655 : Interp.termOf program 655 = pure T.«emit_fcmp» := rfl
theorem program_rulesOf_655 : program.rulesOf 655 =
    [rule_inst_5216, rule_inst_5219, rule_inst_5210] := rfl
theorem program_term_656 : Interp.termOf program 656 = pure T.«fp_cond_code» := rfl
theorem program_rulesOf_656 : program.rulesOf 656 =
    [rule_inst_5232, rule_inst_5235, rule_inst_5237, rule_inst_5239, rule_inst_5241, rule_inst_5243, rule_inst_5245, rule_inst_5247, rule_inst_5249, rule_inst_5251, rule_inst_5253, rule_inst_5255] := rfl
theorem program_term_657 : Interp.termOf program 657 = pure T.«lower_extend_op» := rfl
theorem program_rulesOf_657 : program.rulesOf 657 =
    [rule_inst_5264, rule_inst_5265, rule_inst_5266, rule_inst_5267] := rfl
theorem program_term_659 : Interp.termOf program 659 = pure T.«lower_select» := rfl
theorem program_rulesOf_659 : program.rulesOf 659 =
    [rule_inst_5320, rule_inst_5322, rule_inst_5324, rule_inst_5331] := rfl
theorem program_term_660 : Interp.termOf program 660 = pure T.«lower_select_cond» := rfl
theorem program_rulesOf_660 : program.rulesOf 660 =
    [rule_inst_5343, rule_inst_5350, rule_inst_5345, rule_inst_5341, rule_inst_5364, rule_inst_5347] := rfl
theorem program_term_661 : Interp.termOf program 661 = pure T.«aarch64_jump» := rfl
theorem program_rulesOf_661 : program.rulesOf 661 =
    [rule_inst_5371] := rfl
theorem program_term_662 : Interp.termOf program 662 = pure T.«jt_sequence» := rfl
theorem program_rulesOf_662 : program.rulesOf 662 =
    [rule_inst_5394] := rfl
theorem program_term_663 : Interp.termOf program 663 = pure T.«a64_br_cond» := rfl
theorem program_rulesOf_663 : program.rulesOf 663 =
    [rule_inst_5406] := rfl
theorem program_term_664 : Interp.termOf program 664 = pure T.«a64_br_zero» := rfl
theorem program_rulesOf_664 : program.rulesOf 664 =
    [rule_inst_5412] := rfl
theorem program_term_665 : Interp.termOf program 665 = pure T.«a64_br_not_zero» := rfl
theorem program_rulesOf_665 : program.rulesOf 665 =
    [rule_inst_5418] := rfl
theorem program_term_666 : Interp.termOf program 666 = pure T.«test_branch» := rfl
theorem program_rulesOf_666 : program.rulesOf 666 =
    [rule_inst_5425] := rfl
theorem program_term_667 : Interp.termOf program 667 = pure T.«tbnz» := rfl
theorem program_rulesOf_667 : program.rulesOf 667 =
    [rule_inst_5431] := rfl
theorem program_term_668 : Interp.termOf program 668 = pure T.«tbz» := rfl
theorem program_rulesOf_668 : program.rulesOf 668 =
    [rule_inst_5437] := rfl
theorem program_term_669 : Interp.termOf program 669 = pure T.«emit_island» := rfl
theorem program_rulesOf_669 : program.rulesOf 669 =
    [rule_inst_5443] := rfl
theorem program_term_670 : Interp.termOf program 670 = pure T.«br_table_impl» := rfl
theorem program_rulesOf_670 : program.rulesOf 670 =
    [rule_inst_5450, rule_inst_5454] := rfl
theorem program_term_686 : Interp.termOf program 686 = pure T.«lower» := rfl
theorem program_rulesOf_686 : program.rulesOf 686 =
    [rule_lower_419, rule_lower_402, rule_lower_1444, rule_lower_1481, rule_lower_116, rule_lower_125, rule_lower_1442, rule_lower_1479, rule_lower_2779, rule_lower_120, rule_lower_128, rule_lower_165, rule_lower_1439, rule_lower_1476, rule_lower_2784, rule_lower_93, rule_lower_167, rule_lower_1437, rule_lower_1474, rule_lower_1501, rule_lower_1507, rule_lower_2789, rule_lower_3091, rule_lower_3155, rule_lower_90, rule_lower_169, rule_lower_1435, rule_lower_1472, rule_lower_1540, rule_lower_2152, rule_lower_2793, rule_lower_3097, rule_lower_3161, rule_lower_102, rule_lower_171, rule_lower_1408, rule_lower_1434, rule_lower_1471, rule_lower_1539, rule_lower_2158, rule_lower_2185, rule_lower_2798, rule_lower_2828, rule_lower_3008, rule_lower_3101, rule_lower_3165, rule_lower_98, rule_lower_190, rule_lower_437, rule_lower_609, rule_lower_810, rule_lower_861, rule_lower_1163, rule_lower_1222, rule_lower_1224, rule_lower_1226, rule_lower_1228, rule_lower_1406, rule_lower_1431, rule_lower_1468, rule_lower_1536, rule_lower_2120, rule_lower_2164, rule_lower_2191, rule_lower_2386, rule_lower_2404, rule_lower_2419, rule_lower_2435, rule_lower_2815, rule_lower_3018, rule_lower_3036, rule_lower_3056, rule_lower_3076, rule_lower_3126, rule_lower_3140, rule_lower_3190, rule_lower_3204, rule_lower_111, rule_lower_203, rule_lower_205, rule_lower_207, rule_lower_209, rule_lower_211, rule_lower_213, rule_lower_215, rule_lower_217, rule_lower_222, rule_lower_224, rule_lower_226, rule_lower_228, rule_lower_230, rule_lower_232, rule_lower_240, rule_lower_242, rule_lower_244, rule_lower_246, rule_lower_248, rule_lower_250, rule_lower_260, rule_lower_262, rule_lower_264, rule_lower_266, rule_lower_268, rule_lower_270, rule_lower_294, rule_lower_300, rule_lower_440, rule_lower_608, rule_lower_693, rule_lower_699, rule_lower_707, rule_lower_713, rule_lower_730, rule_lower_733, rule_lower_750, rule_lower_753, rule_lower_767, rule_lower_773, rule_lower_787, rule_lower_793, rule_lower_816, rule_lower_857, rule_lower_1056, rule_lower_1068, rule_lower_1116, rule_lower_1167, rule_lower_1236, rule_lower_1242, rule_lower_1248, rule_lower_1254, rule_lower_1266, rule_lower_1272, rule_lower_1281, rule_lower_1283, rule_lower_1401, rule_lower_1429, rule_lower_1466, rule_lower_1534, rule_lower_1704, rule_lower_1707, rule_lower_1803, rule_lower_1808, rule_lower_2138, rule_lower_2170, rule_lower_2197, rule_lower_2288, rule_lower_2328, rule_lower_2331, rule_lower_2334, rule_lower_2337, rule_lower_2340, rule_lower_2343, rule_lower_2346, rule_lower_2349, rule_lower_2352, rule_lower_2381, rule_lower_2400, rule_lower_2415, rule_lower_2431, rule_lower_2451, rule_lower_2466, rule_lower_2508, rule_lower_2580, rule_lower_2803, rule_lower_2822, rule_lower_2837, rule_lower_3014, rule_lower_3031, rule_lower_3051, rule_lower_3071, rule_lower_3110, rule_lower_3174, rule_lower_53, rule_lower_58, rule_lower_63, rule_lower_68, rule_lower_73, rule_lower_78, rule_lower_108, rule_lower_132, rule_lower_273, rule_lower_279, rule_lower_284, rule_lower_308, rule_lower_313, rule_lower_316, rule_lower_336, rule_lower_342, rule_lower_368, rule_lower_375, rule_lower_379, rule_lower_383, rule_lower_387, rule_lower_450, rule_lower_463, rule_lower_477, rule_lower_485, rule_lower_493, rule_lower_501, rule_lower_509, rule_lower_517, rule_lower_525, rule_lower_533, rule_lower_541, rule_lower_549, rule_lower_554, rule_lower_559, rule_lower_567, rule_lower_570, rule_lower_578, rule_lower_581, rule_lower_589, rule_lower_592, rule_lower_600, rule_lower_603, rule_lower_685, rule_lower_690, rule_lower_696, rule_lower_704, rule_lower_710, rule_lower_724, rule_lower_727, rule_lower_744, rule_lower_747, rule_lower_764, rule_lower_770, rule_lower_784, rule_lower_790, rule_lower_805, rule_lower_836, rule_lower_841, rule_lower_846, rule_lower_851, rule_lower_865, rule_lower_906, rule_lower_914, rule_lower_995, rule_lower_1000, rule_lower_1005, rule_lower_1010, rule_lower_1015, rule_lower_1020, rule_lower_1025, rule_lower_1030, rule_lower_1035, rule_lower_1040, rule_lower_1045, rule_lower_1050, rule_lower_1059, rule_lower_1071, rule_lower_1119, rule_lower_1145, rule_lower_1190, rule_lower_1204, rule_lower_1233, rule_lower_1239, rule_lower_1245, rule_lower_1251, rule_lower_1294, rule_lower_1300, rule_lower_1339, rule_lower_1359, rule_lower_1391, rule_lower_1424, rule_lower_1461, rule_lower_1528, rule_lower_1549, rule_lower_1553, rule_lower_1642, rule_lower_1646, rule_lower_1699, rule_lower_1720, rule_lower_1791, rule_lower_1797, rule_lower_1827, rule_lower_1857, rule_lower_1862, rule_lower_1916, rule_lower_1931, rule_lower_1937, rule_lower_1940, rule_lower_1951, rule_lower_1955, rule_lower_1958, rule_lower_1982, rule_lower_1986, rule_lower_1989, rule_lower_2000, rule_lower_2004, rule_lower_2016, rule_lower_2035, rule_lower_2038, rule_lower_2041, rule_lower_2044, rule_lower_2052, rule_lower_2074, rule_lower_2080, rule_lower_2086, rule_lower_2092, rule_lower_2099, rule_lower_2108, rule_lower_2113, rule_lower_2146, rule_lower_2176, rule_lower_2203, rule_lower_2237, rule_lower_2242, rule_lower_2262, rule_lower_2267, rule_lower_2280, rule_lower_2285, rule_lower_2301, rule_lower_2304, rule_lower_2307, rule_lower_2310, rule_lower_2316, rule_lower_2321, rule_lower_2357, rule_lower_2359, rule_lower_2361, rule_lower_2363, rule_lower_2365, rule_lower_2367, rule_lower_2369, rule_lower_2371, rule_lower_2373, rule_lower_2375, rule_lower_2377, rule_lower_2390, rule_lower_2395, rule_lower_2408, rule_lower_2423, rule_lower_2439, rule_lower_2446, rule_lower_2454, rule_lower_2461, rule_lower_2469, rule_lower_2476, rule_lower_2481, rule_lower_2486, rule_lower_2491, rule_lower_2496, rule_lower_2499, rule_lower_2502, rule_lower_2518, rule_lower_2529, rule_lower_2574, rule_lower_2587, rule_lower_2595, rule_lower_2604, rule_lower_2607, rule_lower_2610, rule_lower_2613, rule_lower_2619, rule_lower_2647, rule_lower_2650, rule_lower_2653, rule_lower_2656, rule_lower_2659, rule_lower_2662, rule_lower_2666, rule_lower_2672, rule_lower_2678, rule_lower_2684, rule_lower_2690, rule_lower_2696, rule_lower_2705, rule_lower_2709, rule_lower_2713, rule_lower_2717, rule_lower_2722, rule_lower_2726, rule_lower_2730, rule_lower_2735, rule_lower_2770, rule_lower_2773, rule_lower_2809, rule_lower_2818, rule_lower_2842, rule_lower_2849, rule_lower_2863, rule_lower_2887, rule_lower_2900, rule_lower_2913, rule_lower_2927, rule_lower_3022, rule_lower_3042, rule_lower_3062, rule_lower_3082, rule_lower_3217, rule_lower_3220, rule_lower_3225, rule_lower_3286, rule_lower_3292, rule_lower_dynamic_neon_81, rule_lower_dynamic_neon_87, rule_lower_86, rule_lower_319, rule_lower_359, rule_lower_390, rule_lower_434, rule_lower_472, rule_lower_482, rule_lower_490, rule_lower_498, rule_lower_506, rule_lower_514, rule_lower_522, rule_lower_530, rule_lower_538, rule_lower_546, rule_lower_564, rule_lower_575, rule_lower_586, rule_lower_597, rule_lower_718, rule_lower_721, rule_lower_738, rule_lower_741, rule_lower_758, rule_lower_761, rule_lower_778, rule_lower_781, rule_lower_831, rule_lower_876, rule_lower_956, rule_lower_1153, rule_lower_1197, rule_lower_1211, rule_lower_1289, rule_lower_1349, rule_lower_1387, rule_lower_1421, rule_lower_1458, rule_lower_1525, rule_lower_1545, rule_lower_1638, rule_lower_1736, rule_lower_1778, rule_lower_1844, rule_lower_1848, rule_lower_1946, rule_lower_1961, rule_lower_1995, rule_lower_2030, rule_lower_2179, rule_lower_2209, rule_lower_2294, rule_lower_2622, rule_lower_2742, rule_lower_dynamic_neon_43, rule_lower_dynamic_neon_57, rule_lower_dynamic_neon_71, rule_lower_dynamic_neon_92, rule_lower_dynamic_neon_97, rule_lower_137, rule_lower_322, rule_lower_826, rule_lower_924, rule_lower_1261, rule_lower_1329, rule_lower_1385, rule_lower_1419, rule_lower_1456, rule_lower_1523, rule_lower_1588, rule_lower_1661, rule_lower_1734, rule_lower_1772, rule_lower_1852, rule_lower_2215, rule_lower_2298, rule_lower_2625, rule_lower_2746, rule_lower_dynamic_neon_15, rule_lower_dynamic_neon_19, rule_lower_dynamic_neon_23, rule_lower_dynamic_neon_27, rule_lower_dynamic_neon_31, rule_lower_dynamic_neon_35, rule_lower_dynamic_neon_39, rule_lower_dynamic_neon_53, rule_lower_dynamic_neon_67, rule_lower_142, rule_lower_821, rule_lower_871, rule_lower_1320, rule_lower_1381, rule_lower_1452, rule_lower_1519, rule_lower_1583, rule_lower_1659, rule_lower_1729, rule_lower_1840, rule_lower_2628, rule_lower_2750, rule_lower_dynamic_neon_47, rule_lower_dynamic_neon_61, rule_lower_dynamic_neon_75, rule_lower_801, rule_lower_1315, rule_lower_1377, rule_lower_1415, rule_lower_1449, rule_lower_1516, rule_lower_1654, rule_lower_1695, rule_lower_2633, rule_lower_2754, rule_lower_dynamic_neon_3, rule_lower_dynamic_neon_11, rule_lower_1412, rule_lower_2638, rule_lower_2759, rule_lower_dynamic_neon_7, rule_lower_2643, rule_lower_2763] := rfl
theorem program_term_687 : Interp.termOf program 687 = pure T.«lower_branch» := rfl
theorem program_rulesOf_687 : program.rulesOf 687 =
    [rule_lower_2542, rule_lower_3251, rule_lower_3257, rule_lower_2551, rule_lower_2561, rule_lower_3231, rule_lower_3270, rule_lower_3277] := rfl
theorem program_term_698 : Interp.termOf program 698 = pure T.«put_nonzero_in_reg» := rfl
theorem program_rulesOf_698 : program.rulesOf 698 =
    [rule_lower_1097, rule_lower_1101, rule_lower_1104, rule_lower_1107, rule_lower_1110] := rfl
theorem program_term_699 : Interp.termOf program 699 = pure T.«aarch64_uload» := rfl
theorem program_rulesOf_699 : program.rulesOf 699 =
    [rule_lower_1307, rule_lower_1308, rule_lower_1309] := rfl
theorem program_term_700 : Interp.termOf program 700 = pure T.«aarch64_sload» := rfl
theorem program_rulesOf_700 : program.rulesOf 700 =
    [rule_lower_1366, rule_lower_1367, rule_lower_1368] := rfl
theorem program_term_702 : Interp.termOf program 702 = pure T.«shift_masked_imm» := rfl
theorem program_term_703 : Interp.termOf program 703 = pure T.«do_shift» := rfl
theorem program_rulesOf_703 : program.rulesOf 703 =
    [rule_lower_1631, rule_lower_1622, rule_lower_1623, rule_lower_1612] := rfl
theorem program_term_704 : Interp.termOf program 704 = pure T.«shift_mask» := rfl
theorem program_term_706 : Interp.termOf program 706 = pure T.«bfm_immr» := rfl
theorem program_term_707 : Interp.termOf program 707 = pure T.«bfm_imms» := rfl
theorem program_term_709 : Interp.termOf program 709 = pure T.«negate_imm_shift» := rfl
theorem program_term_710 : Interp.termOf program 710 = pure T.«small_rotr» := rfl
theorem program_rulesOf_710 : program.rulesOf 710 =
    [rule_lower_1879] := rfl
theorem program_term_711 : Interp.termOf program 711 = pure T.«rotr_mask» := rfl
theorem program_term_712 : Interp.termOf program 712 = pure T.«small_rotr_imm» := rfl
theorem program_rulesOf_712 : program.rulesOf 712 =
    [rule_lower_1902] := rfl
theorem program_term_713 : Interp.termOf program 713 = pure T.«rotr_opposite_amount» := rfl
theorem program_term_715 : Interp.termOf program 715 = pure T.«lower_cond_result_bool» := rfl
theorem program_rulesOf_715 : program.rulesOf 715 =
    [rule_lower_2222, rule_lower_2224, rule_lower_2226, rule_lower_2228, rule_lower_2231] := rfl
theorem program_term_722 : Interp.termOf program 722 = pure T.«br_cond_result» := rfl
theorem program_rulesOf_722 : program.rulesOf 722 =
    [rule_lower_3236, rule_lower_3238, rule_lower_3240, rule_lower_3247] := rfl
theorem program_term_723 : Interp.termOf program 723 = pure T.«test_and_compare_bit_const» := rfl
theorem program_term_978 : Interp.termOf program 978 = pure T.«i32_checked_add» := rfl
theorem program_term_1154 : Interp.termOf program 1154 = pure T.«i64_checked_neg» := rfl
theorem program_term_1157 : Interp.termOf program 1157 = pure T.«u64_eq» := rfl
theorem program_term_1161 : Interp.termOf program 1161 = pure T.«u64_gt» := rfl
theorem program_term_1164 : Interp.termOf program 1164 = pure T.«u64_wrapping_add» := rfl
theorem program_term_1167 : Interp.termOf program 1167 = pure T.«u64_wrapping_sub» := rfl
theorem program_term_1182 : Interp.termOf program 1182 = pure T.«u64_wrapping_shl» := rfl
theorem program_term_1199 : Interp.termOf program 1199 = pure T.«u64_is_odd» := rfl
theorem program_term_1378 : Interp.termOf program 1378 = pure T.«u8_into_u32» := rfl
theorem program_term_1382 : Interp.termOf program 1382 = pure T.«u8_into_u64» := rfl
theorem program_term_1431 : Interp.termOf program 1431 = pure T.«u16_into_u64» := rfl
theorem program_term_1455 : Interp.termOf program 1455 = pure T.«i32_into_i64» := rfl
theorem program_term_1485 : Interp.termOf program 1485 = pure T.«u32_into_u64» := rfl
theorem program_term_1508 : Interp.termOf program 1508 = pure T.«i32_from_i64» := rfl
theorem program_term_1514 : Interp.termOf program 1514 = pure T.«i64_cast_unsigned» := rfl
theorem program_term_1527 : Interp.termOf program 1527 = pure T.«u8_from_u64» := rfl
theorem program_term_1614 : Interp.termOf program 1614 = pure T.«value_array_2» := rfl
theorem program_term_1615 : Interp.termOf program 1615 = pure T.«value_array_3» := rfl
theorem program_term_1616 : Interp.termOf program 1616 = pure T.«block_array_2» := rfl
theorem program_term_1785 : Interp.termOf program 1785 = pure T.«RelocDistance.Near» := rfl
theorem program_term_1786 : Interp.termOf program 1786 = pure T.«RelocDistance.Far» := rfl
theorem program_term_1787 : Interp.termOf program 1787 = pure T.«SideEffectNoResult.Inst» := rfl
theorem program_term_1788 : Interp.termOf program 1788 = pure T.«SideEffectNoResult.Inst2» := rfl
theorem program_term_1789 : Interp.termOf program 1789 = pure T.«SideEffectNoResult.Inst3» := rfl
theorem program_term_1790 : Interp.termOf program 1790 = pure T.«ProducesFlags.AlreadyExistingFlags» := rfl
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
theorem program_term_1827 : Interp.termOf program 1827 = pure T.«MInst.BitRR» := rfl
theorem program_term_1828 : Interp.termOf program 1828 = pure T.«MInst.ULoad8» := rfl
theorem program_term_1829 : Interp.termOf program 1829 = pure T.«MInst.SLoad8» := rfl
theorem program_term_1830 : Interp.termOf program 1830 = pure T.«MInst.ULoad16» := rfl
theorem program_term_1831 : Interp.termOf program 1831 = pure T.«MInst.SLoad16» := rfl
theorem program_term_1832 : Interp.termOf program 1832 = pure T.«MInst.ULoad32» := rfl
theorem program_term_1833 : Interp.termOf program 1833 = pure T.«MInst.SLoad32» := rfl
theorem program_term_1834 : Interp.termOf program 1834 = pure T.«MInst.ULoad64» := rfl
theorem program_term_1835 : Interp.termOf program 1835 = pure T.«MInst.Store8» := rfl
theorem program_term_1836 : Interp.termOf program 1836 = pure T.«MInst.Store16» := rfl
theorem program_term_1837 : Interp.termOf program 1837 = pure T.«MInst.Store32» := rfl
theorem program_term_1838 : Interp.termOf program 1838 = pure T.«MInst.Store64» := rfl
theorem program_term_1844 : Interp.termOf program 1844 = pure T.«MInst.MovWide» := rfl
theorem program_term_1846 : Interp.termOf program 1846 = pure T.«MInst.Extend» := rfl
theorem program_term_1847 : Interp.termOf program 1847 = pure T.«MInst.BitfieldMove» := rfl
theorem program_term_1849 : Interp.termOf program 1849 = pure T.«MInst.CSel» := rfl
theorem program_term_1851 : Interp.termOf program 1851 = pure T.«MInst.CSet» := rfl
theorem program_term_1853 : Interp.termOf program 1853 = pure T.«MInst.CCmp» := rfl
theorem program_term_1854 : Interp.termOf program 1854 = pure T.«MInst.CCmpImm» := rfl
theorem program_term_1874 : Interp.termOf program 1874 = pure T.«MInst.FpuCmp» := rfl
theorem program_term_1889 : Interp.termOf program 1889 = pure T.«MInst.FpuCSel16» := rfl
theorem program_term_1890 : Interp.termOf program 1890 = pure T.«MInst.FpuCSel32» := rfl
theorem program_term_1891 : Interp.termOf program 1891 = pure T.«MInst.FpuCSel64» := rfl
theorem program_term_1893 : Interp.termOf program 1893 = pure T.«MInst.MovToFpu» := rfl
theorem program_term_1896 : Interp.termOf program 1896 = pure T.«MInst.MovFromVec» := rfl
theorem program_term_1911 : Interp.termOf program 1911 = pure T.«MInst.VecRRR» := rfl
theorem program_term_1914 : Interp.termOf program 1914 = pure T.«MInst.VecMisc» := rfl
theorem program_term_1915 : Interp.termOf program 1915 = pure T.«MInst.VecLanes» := rfl
theorem program_term_1924 : Interp.termOf program 1924 = pure T.«MInst.VecCSel» := rfl
theorem program_term_1927 : Interp.termOf program 1927 = pure T.«MInst.Call» := rfl
theorem program_term_1928 : Interp.termOf program 1928 = pure T.«MInst.CallInd» := rfl
theorem program_term_1935 : Interp.termOf program 1935 = pure T.«MInst.Jump» := rfl
theorem program_term_1936 : Interp.termOf program 1936 = pure T.«MInst.CondBr» := rfl
theorem program_term_1937 : Interp.termOf program 1937 = pure T.«MInst.TestBitAndBranch» := rfl
theorem program_term_1938 : Interp.termOf program 1938 = pure T.«MInst.TrapIf» := rfl
theorem program_term_1941 : Interp.termOf program 1941 = pure T.«MInst.Udf» := rfl
theorem program_term_1946 : Interp.termOf program 1946 = pure T.«MInst.JTSequence» := rfl
theorem program_term_1947 : Interp.termOf program 1947 = pure T.«MInst.LoadExtNameGot» := rfl
theorem program_term_1948 : Interp.termOf program 1948 = pure T.«MInst.LoadExtNameNear» := rfl
theorem program_term_1949 : Interp.termOf program 1949 = pure T.«MInst.LoadExtNameFar» := rfl
theorem program_term_1954 : Interp.termOf program 1954 = pure T.«MInst.EmitIsland» := rfl
theorem program_term_1962 : Interp.termOf program 1962 = pure T.«ALUOp.Add» := rfl
theorem program_term_1963 : Interp.termOf program 1963 = pure T.«ALUOp.Sub» := rfl
theorem program_term_1964 : Interp.termOf program 1964 = pure T.«ALUOp.Orr» := rfl
theorem program_term_1965 : Interp.termOf program 1965 = pure T.«ALUOp.OrrNot» := rfl
theorem program_term_1966 : Interp.termOf program 1966 = pure T.«ALUOp.And» := rfl
theorem program_term_1967 : Interp.termOf program 1967 = pure T.«ALUOp.AndS» := rfl
theorem program_term_1968 : Interp.termOf program 1968 = pure T.«ALUOp.AndNot» := rfl
theorem program_term_1969 : Interp.termOf program 1969 = pure T.«ALUOp.Eor» := rfl
theorem program_term_1970 : Interp.termOf program 1970 = pure T.«ALUOp.EorNot» := rfl
theorem program_term_1971 : Interp.termOf program 1971 = pure T.«ALUOp.AddS» := rfl
theorem program_term_1972 : Interp.termOf program 1972 = pure T.«ALUOp.SubS» := rfl
theorem program_term_1973 : Interp.termOf program 1973 = pure T.«ALUOp.SMulH» := rfl
theorem program_term_1974 : Interp.termOf program 1974 = pure T.«ALUOp.UMulH» := rfl
theorem program_term_1975 : Interp.termOf program 1975 = pure T.«ALUOp.SDiv» := rfl
theorem program_term_1976 : Interp.termOf program 1976 = pure T.«ALUOp.UDiv» := rfl
theorem program_term_1977 : Interp.termOf program 1977 = pure T.«ALUOp.Extr» := rfl
theorem program_term_1978 : Interp.termOf program 1978 = pure T.«ALUOp.Lsr» := rfl
theorem program_term_1979 : Interp.termOf program 1979 = pure T.«ALUOp.Asr» := rfl
theorem program_term_1980 : Interp.termOf program 1980 = pure T.«ALUOp.Lsl» := rfl
theorem program_term_1984 : Interp.termOf program 1984 = pure T.«ALUOp.SbcS» := rfl
theorem program_term_1985 : Interp.termOf program 1985 = pure T.«ALUOp3.MAdd» := rfl
theorem program_term_1986 : Interp.termOf program 1986 = pure T.«ALUOp3.MSub» := rfl
theorem program_term_1987 : Interp.termOf program 1987 = pure T.«ALUOp3.UMAddL» := rfl
theorem program_term_1988 : Interp.termOf program 1988 = pure T.«ALUOp3.SMAddL» := rfl
theorem program_term_1989 : Interp.termOf program 1989 = pure T.«MoveWideOp.MovZ» := rfl
theorem program_term_1990 : Interp.termOf program 1990 = pure T.«MoveWideOp.MovN» := rfl
theorem program_term_1991 : Interp.termOf program 1991 = pure T.«BfmOp.UBfm» := rfl
theorem program_term_1992 : Interp.termOf program 1992 = pure T.«BfmOp.SBfm» := rfl
theorem program_term_1996 : Interp.termOf program 1996 = pure T.«ExtendOp.UXTB» := rfl
theorem program_term_1997 : Interp.termOf program 1997 = pure T.«ExtendOp.UXTH» := rfl
theorem program_term_1998 : Interp.termOf program 1998 = pure T.«ExtendOp.UXTW» := rfl
theorem program_term_2000 : Interp.termOf program 2000 = pure T.«ExtendOp.SXTB» := rfl
theorem program_term_2001 : Interp.termOf program 2001 = pure T.«ExtendOp.SXTH» := rfl
theorem program_term_2002 : Interp.termOf program 2002 = pure T.«ExtendOp.SXTW» := rfl
theorem program_term_2004 : Interp.termOf program 2004 = pure T.«BitOp.RBit» := rfl
theorem program_term_2005 : Interp.termOf program 2005 = pure T.«BitOp.Clz» := rfl
theorem program_term_2007 : Interp.termOf program 2007 = pure T.«BitOp.Rev16» := rfl
theorem program_term_2008 : Interp.termOf program 2008 = pure T.«BitOp.Rev32» := rfl
theorem program_term_2009 : Interp.termOf program 2009 = pure T.«BitOp.Rev64» := rfl
theorem program_term_2012 : Interp.termOf program 2012 = pure T.«AMode.RegReg» := rfl
theorem program_term_2013 : Interp.termOf program 2013 = pure T.«AMode.RegScaled» := rfl
theorem program_term_2014 : Interp.termOf program 2014 = pure T.«AMode.RegScaledExtended» := rfl
theorem program_term_2015 : Interp.termOf program 2015 = pure T.«AMode.RegExtended» := rfl
theorem program_term_2016 : Interp.termOf program 2016 = pure T.«AMode.Unscaled» := rfl
theorem program_term_2017 : Interp.termOf program 2017 = pure T.«AMode.UnsignedOffset» := rfl
theorem program_term_2024 : Interp.termOf program 2024 = pure T.«AMode.SlotOffset» := rfl
theorem program_term_2028 : Interp.termOf program 2028 = pure T.«OperandSize.Size32» := rfl
theorem program_term_2029 : Interp.termOf program 2029 = pure T.«OperandSize.Size64» := rfl
theorem program_term_2030 : Interp.termOf program 2030 = pure T.«TestBitAndBranchKind.Z» := rfl
theorem program_term_2031 : Interp.termOf program 2031 = pure T.«TestBitAndBranchKind.NZ» := rfl
theorem program_term_2032 : Interp.termOf program 2032 = pure T.«ScalarSize.Size8» := rfl
theorem program_term_2033 : Interp.termOf program 2033 = pure T.«ScalarSize.Size16» := rfl
theorem program_term_2034 : Interp.termOf program 2034 = pure T.«ScalarSize.Size32» := rfl
theorem program_term_2035 : Interp.termOf program 2035 = pure T.«ScalarSize.Size64» := rfl
theorem program_term_2036 : Interp.termOf program 2036 = pure T.«ScalarSize.Size128» := rfl
theorem program_term_2037 : Interp.termOf program 2037 = pure T.«Cond.Eq» := rfl
theorem program_term_2038 : Interp.termOf program 2038 = pure T.«Cond.Ne» := rfl
theorem program_term_2039 : Interp.termOf program 2039 = pure T.«Cond.Hs» := rfl
theorem program_term_2041 : Interp.termOf program 2041 = pure T.«Cond.Mi» := rfl
theorem program_term_2042 : Interp.termOf program 2042 = pure T.«Cond.Pl» := rfl
theorem program_term_2043 : Interp.termOf program 2043 = pure T.«Cond.Vs» := rfl
theorem program_term_2044 : Interp.termOf program 2044 = pure T.«Cond.Vc» := rfl
theorem program_term_2045 : Interp.termOf program 2045 = pure T.«Cond.Hi» := rfl
theorem program_term_2046 : Interp.termOf program 2046 = pure T.«Cond.Ls» := rfl
theorem program_term_2047 : Interp.termOf program 2047 = pure T.«Cond.Ge» := rfl
theorem program_term_2048 : Interp.termOf program 2048 = pure T.«Cond.Lt» := rfl
theorem program_term_2049 : Interp.termOf program 2049 = pure T.«Cond.Gt» := rfl
theorem program_term_2050 : Interp.termOf program 2050 = pure T.«Cond.Le» := rfl
theorem program_term_2053 : Interp.termOf program 2053 = pure T.«VectorSize.Size8x8» := rfl
theorem program_term_2054 : Interp.termOf program 2054 = pure T.«VectorSize.Size8x16» := rfl
theorem program_term_2055 : Interp.termOf program 2055 = pure T.«VectorSize.Size16x4» := rfl
theorem program_term_2056 : Interp.termOf program 2056 = pure T.«VectorSize.Size16x8» := rfl
theorem program_term_2057 : Interp.termOf program 2057 = pure T.«VectorSize.Size32x2» := rfl
theorem program_term_2058 : Interp.termOf program 2058 = pure T.«VectorSize.Size32x4» := rfl
theorem program_term_2059 : Interp.termOf program 2059 = pure T.«VectorSize.Size64x2» := rfl
theorem program_term_2124 : Interp.termOf program 2124 = pure T.«VecALUOp.Umin» := rfl
theorem program_term_2125 : Interp.termOf program 2125 = pure T.«VecALUOp.Smin» := rfl
theorem program_term_2126 : Interp.termOf program 2126 = pure T.«VecALUOp.Umax» := rfl
theorem program_term_2127 : Interp.termOf program 2127 = pure T.«VecALUOp.Smax» := rfl
theorem program_term_2135 : Interp.termOf program 2135 = pure T.«VecALUOp.Addp» := rfl
theorem program_term_2165 : Interp.termOf program 2165 = pure T.«VecMisc2.Cnt» := rfl
theorem program_term_2200 : Interp.termOf program 2200 = pure T.«VecLanesOp.Addv» := rfl
theorem program_term_2234 : Interp.termOf program 2234 = pure T.«ImmExtend.Sign» := rfl
theorem program_term_2235 : Interp.termOf program 2235 = pure T.«ImmExtend.Zero» := rfl
theorem program_term_2236 : Interp.termOf program 2236 = pure T.«CondResult.Zero» := rfl
theorem program_term_2237 : Interp.termOf program 2237 = pure T.«CondResult.NotZero» := rfl
theorem program_term_2238 : Interp.termOf program 2238 = pure T.«CondResult.Cond» := rfl
theorem program_term_2239 : Interp.termOf program 2239 = pure T.«CondResult.Or» := rfl
theorem program_term_2240 : Interp.termOf program 2240 = pure T.«CondResult.And» := rfl
theorem program_term_2242 : Interp.termOf program 2242 = pure T.«ExtType.Signed» := rfl
theorem program_term_2243 : Interp.termOf program 2243 = pure T.«ExtType.Unsigned» := rfl
theorem program_term_2255 : Interp.termOf program 2255 = pure T.«FloatCC.Equal» := rfl
theorem program_term_2256 : Interp.termOf program 2256 = pure T.«FloatCC.GreaterThan» := rfl
theorem program_term_2257 : Interp.termOf program 2257 = pure T.«FloatCC.GreaterThanOrEqual» := rfl
theorem program_term_2258 : Interp.termOf program 2258 = pure T.«FloatCC.LessThan» := rfl
theorem program_term_2259 : Interp.termOf program 2259 = pure T.«FloatCC.LessThanOrEqual» := rfl
theorem program_term_2260 : Interp.termOf program 2260 = pure T.«FloatCC.NotEqual» := rfl
theorem program_term_2261 : Interp.termOf program 2261 = pure T.«FloatCC.Ordered» := rfl
theorem program_term_2262 : Interp.termOf program 2262 = pure T.«FloatCC.OrderedNotEqual» := rfl
theorem program_term_2263 : Interp.termOf program 2263 = pure T.«FloatCC.Unordered» := rfl
theorem program_term_2264 : Interp.termOf program 2264 = pure T.«FloatCC.UnorderedOrEqual» := rfl
theorem program_term_2265 : Interp.termOf program 2265 = pure T.«FloatCC.UnorderedOrGreaterThan» := rfl
theorem program_term_2266 : Interp.termOf program 2266 = pure T.«FloatCC.UnorderedOrGreaterThanOrEqual» := rfl
theorem program_term_2267 : Interp.termOf program 2267 = pure T.«FloatCC.UnorderedOrLessThan» := rfl
theorem program_term_2268 : Interp.termOf program 2268 = pure T.«FloatCC.UnorderedOrLessThanOrEqual» := rfl
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
theorem program_term_2284 : Interp.termOf program 2284 = pure T.«Opcode.Jump» := rfl
theorem program_term_2285 : Interp.termOf program 2285 = pure T.«Opcode.Brif» := rfl
theorem program_term_2286 : Interp.termOf program 2286 = pure T.«Opcode.BrTable» := rfl
theorem program_term_2288 : Interp.termOf program 2288 = pure T.«Opcode.Trap» := rfl
theorem program_term_2291 : Interp.termOf program 2291 = pure T.«Opcode.Return» := rfl
theorem program_term_2292 : Interp.termOf program 2292 = pure T.«Opcode.Call» := rfl
theorem program_term_2304 : Interp.termOf program 2304 = pure T.«Opcode.Smin» := rfl
theorem program_term_2305 : Interp.termOf program 2305 = pure T.«Opcode.Umin» := rfl
theorem program_term_2306 : Interp.termOf program 2306 = pure T.«Opcode.Smax» := rfl
theorem program_term_2307 : Interp.termOf program 2307 = pure T.«Opcode.Umax» := rfl
theorem program_term_2313 : Interp.termOf program 2313 = pure T.«Opcode.Load» := rfl
theorem program_term_2314 : Interp.termOf program 2314 = pure T.«Opcode.Store» := rfl
theorem program_term_2315 : Interp.termOf program 2315 = pure T.«Opcode.Uload8» := rfl
theorem program_term_2316 : Interp.termOf program 2316 = pure T.«Opcode.Sload8» := rfl
theorem program_term_2317 : Interp.termOf program 2317 = pure T.«Opcode.Istore8» := rfl
theorem program_term_2318 : Interp.termOf program 2318 = pure T.«Opcode.Uload16» := rfl
theorem program_term_2319 : Interp.termOf program 2319 = pure T.«Opcode.Sload16» := rfl
theorem program_term_2320 : Interp.termOf program 2320 = pure T.«Opcode.Istore16» := rfl
theorem program_term_2321 : Interp.termOf program 2321 = pure T.«Opcode.Uload32» := rfl
theorem program_term_2322 : Interp.termOf program 2322 = pure T.«Opcode.Sload32» := rfl
theorem program_term_2323 : Interp.termOf program 2323 = pure T.«Opcode.Istore32» := rfl
theorem program_term_2331 : Interp.termOf program 2331 = pure T.«Opcode.StackAddr» := rfl
theorem program_term_2333 : Interp.termOf program 2333 = pure T.«Opcode.SymbolValue» := rfl
theorem program_term_2341 : Interp.termOf program 2341 = pure T.«Opcode.Iconst» := rfl
theorem program_term_2348 : Interp.termOf program 2348 = pure T.«Opcode.Nop» := rfl
theorem program_term_2349 : Interp.termOf program 2349 = pure T.«Opcode.Select» := rfl
theorem program_term_2356 : Interp.termOf program 2356 = pure T.«Opcode.Icmp» := rfl
theorem program_term_2357 : Interp.termOf program 2357 = pure T.«Opcode.Iadd» := rfl
theorem program_term_2358 : Interp.termOf program 2358 = pure T.«Opcode.Isub» := rfl
theorem program_term_2359 : Interp.termOf program 2359 = pure T.«Opcode.Ineg» := rfl
theorem program_term_2361 : Interp.termOf program 2361 = pure T.«Opcode.Imul» := rfl
theorem program_term_2362 : Interp.termOf program 2362 = pure T.«Opcode.Umulhi» := rfl
theorem program_term_2363 : Interp.termOf program 2363 = pure T.«Opcode.Smulhi» := rfl
theorem program_term_2366 : Interp.termOf program 2366 = pure T.«Opcode.Udiv» := rfl
theorem program_term_2367 : Interp.termOf program 2367 = pure T.«Opcode.Sdiv» := rfl
theorem program_term_2368 : Interp.termOf program 2368 = pure T.«Opcode.Urem» := rfl
theorem program_term_2369 : Interp.termOf program 2369 = pure T.«Opcode.Srem» := rfl
theorem program_term_2372 : Interp.termOf program 2372 = pure T.«Opcode.UaddOverflow» := rfl
theorem program_term_2376 : Interp.termOf program 2376 = pure T.«Opcode.UmulOverflow» := rfl
theorem program_term_2377 : Interp.termOf program 2377 = pure T.«Opcode.SmulOverflow» := rfl
theorem program_term_2381 : Interp.termOf program 2381 = pure T.«Opcode.Band» := rfl
theorem program_term_2382 : Interp.termOf program 2382 = pure T.«Opcode.Bor» := rfl
theorem program_term_2383 : Interp.termOf program 2383 = pure T.«Opcode.Bxor» := rfl
theorem program_term_2384 : Interp.termOf program 2384 = pure T.«Opcode.Bnot» := rfl
theorem program_term_2385 : Interp.termOf program 2385 = pure T.«Opcode.Rotl» := rfl
theorem program_term_2386 : Interp.termOf program 2386 = pure T.«Opcode.Rotr» := rfl
theorem program_term_2387 : Interp.termOf program 2387 = pure T.«Opcode.Ishl» := rfl
theorem program_term_2388 : Interp.termOf program 2388 = pure T.«Opcode.Ushr» := rfl
theorem program_term_2389 : Interp.termOf program 2389 = pure T.«Opcode.Sshr» := rfl
theorem program_term_2390 : Interp.termOf program 2390 = pure T.«Opcode.Bitrev» := rfl
theorem program_term_2391 : Interp.termOf program 2391 = pure T.«Opcode.Clz» := rfl
theorem program_term_2393 : Interp.termOf program 2393 = pure T.«Opcode.Ctz» := rfl
theorem program_term_2394 : Interp.termOf program 2394 = pure T.«Opcode.Bswap» := rfl
theorem program_term_2395 : Interp.termOf program 2395 = pure T.«Opcode.Popcnt» := rfl
theorem program_term_2396 : Interp.termOf program 2396 = pure T.«Opcode.Fcmp» := rfl
theorem program_term_2415 : Interp.termOf program 2415 = pure T.«Opcode.Ireduce» := rfl
theorem program_term_2425 : Interp.termOf program 2425 = pure T.«Opcode.Uextend» := rfl
theorem program_term_2426 : Interp.termOf program 2426 = pure T.«Opcode.Sextend» := rfl
theorem program_term_2449 : Interp.termOf program 2449 = pure T.«InstructionData.Binary» := rfl
theorem program_term_2451 : Interp.termOf program 2451 = pure T.«InstructionData.BranchTable» := rfl
theorem program_term_2452 : Interp.termOf program 2452 = pure T.«InstructionData.Brif» := rfl
theorem program_term_2453 : Interp.termOf program 2453 = pure T.«InstructionData.Call» := rfl
theorem program_term_2458 : Interp.termOf program 2458 = pure T.«InstructionData.FloatCompare» := rfl
theorem program_term_2461 : Interp.termOf program 2461 = pure T.«InstructionData.IntCompare» := rfl
theorem program_term_2462 : Interp.termOf program 2462 = pure T.«InstructionData.Jump» := rfl
theorem program_term_2463 : Interp.termOf program 2463 = pure T.«InstructionData.Load» := rfl
theorem program_term_2465 : Interp.termOf program 2465 = pure T.«InstructionData.MultiAry» := rfl
theorem program_term_2466 : Interp.termOf program 2466 = pure T.«InstructionData.NullAry» := rfl
theorem program_term_2468 : Interp.termOf program 2468 = pure T.«InstructionData.StackAddr» := rfl
theorem program_term_2469 : Interp.termOf program 2469 = pure T.«InstructionData.Store» := rfl
theorem program_term_2471 : Interp.termOf program 2471 = pure T.«InstructionData.Ternary» := rfl
theorem program_term_2473 : Interp.termOf program 2473 = pure T.«InstructionData.Trap» := rfl
theorem program_term_2476 : Interp.termOf program 2476 = pure T.«InstructionData.Unary» := rfl
theorem program_term_2478 : Interp.termOf program 2478 = pure T.«InstructionData.UnaryGlobalValue» := rfl
theorem program_term_2482 : Interp.termOf program 2482 = pure T.«InstructionData.UnaryImm» := rfl

theorem program_termByName_lower : program.termByName? "lower" = some T.lower := by
  decide +kernel

theorem data_program : Data program where
  t1 := program_term_1
  t2 := program_term_2
  t31 := program_term_31
  t87 := program_term_87
  t93 := program_term_93
  t103 := program_term_103
  t110 := program_term_110
  t111 := program_term_111
  t113 := program_term_113
  t118 := program_term_118
  t119 := program_term_119
  t120 := program_term_120
  t126 := program_term_126
  t128 := program_term_128
  t132 := program_term_132
  t133 := program_term_133
  t141 := program_term_141
  t144 := program_term_144
  t145 := program_term_145
  t152 := program_term_152
  t153 := program_term_153
  t156 := program_term_156
  t157 := program_term_157
  t159 := program_term_159
  t160 := program_term_160
  t161 := program_term_161
  t162 := program_term_162
  t164 := program_term_164
  t166 := program_term_166
  t169 := program_term_169
  t170 := program_term_170
  t172 := program_term_172
  r172 := program_rulesOf_172
  t174 := program_term_174
  t175 := program_term_175
  t178 := program_term_178
  t181 := program_term_181
  t182 := program_term_182
  t183 := program_term_183
  t184 := program_term_184
  t185 := program_term_185
  t190 := program_term_190
  t191 := program_term_191
  t192 := program_term_192
  t193 := program_term_193
  t194 := program_term_194
  t201 := program_term_201
  t205 := program_term_205
  t207 := program_term_207
  t209 := program_term_209
  t219 := program_term_219
  t221 := program_term_221
  t222 := program_term_222
  t235 := program_term_235
  t236 := program_term_236
  t242 := program_term_242
  r242 := program_rulesOf_242
  t243 := program_term_243
  r243 := program_rulesOf_243
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
  t256 := program_term_256
  r256 := program_rulesOf_256
  t264 := program_term_264
  t265 := program_term_265
  t267 := program_term_267
  t278 := program_term_278
  t286 := program_term_286
  t287 := program_term_287
  t294 := program_term_294
  r294 := program_rulesOf_294
  t295 := program_term_295
  t296 := program_term_296
  t297 := program_term_297
  t299 := program_term_299
  t303 := program_term_303
  t304 := program_term_304
  t305 := program_term_305
  r305 := program_rulesOf_305
  t306 := program_term_306
  r306 := program_rulesOf_306
  t307 := program_term_307
  r307 := program_rulesOf_307
  t310 := program_term_310
  r310 := program_rulesOf_310
  t316 := program_term_316
  t318 := program_term_318
  t319 := program_term_319
  t320 := program_term_320
  t321 := program_term_321
  t322 := program_term_322
  t323 := program_term_323
  t324 := program_term_324
  t325 := program_term_325
  t326 := program_term_326
  t327 := program_term_327
  t328 := program_term_328
  t329 := program_term_329
  t330 := program_term_330
  t336 := program_term_336
  t338 := program_term_338
  t339 := program_term_339
  t344 := program_term_344
  r344 := program_rulesOf_344
  t345 := program_term_345
  t346 := program_term_346
  t347 := program_term_347
  t348 := program_term_348
  t349 := program_term_349
  t350 := program_term_350
  t351 := program_term_351
  t352 := program_term_352
  t356 := program_term_356
  t358 := program_term_358
  r358 := program_rulesOf_358
  t359 := program_term_359
  r359 := program_rulesOf_359
  t360 := program_term_360
  r360 := program_rulesOf_360
  t361 := program_term_361
  r361 := program_rulesOf_361
  t362 := program_term_362
  r362 := program_rulesOf_362
  t363 := program_term_363
  r363 := program_rulesOf_363
  t370 := program_term_370
  r370 := program_rulesOf_370
  t371 := program_term_371
  r371 := program_rulesOf_371
  t376 := program_term_376
  r376 := program_rulesOf_376
  t377 := program_term_377
  r377 := program_rulesOf_377
  t379 := program_term_379
  r379 := program_rulesOf_379
  t380 := program_term_380
  r380 := program_rulesOf_380
  t381 := program_term_381
  r381 := program_rulesOf_381
  t382 := program_term_382
  r382 := program_rulesOf_382
  t383 := program_term_383
  r383 := program_rulesOf_383
  t385 := program_term_385
  r385 := program_rulesOf_385
  t386 := program_term_386
  r386 := program_rulesOf_386
  t390 := program_term_390
  r390 := program_rulesOf_390
  t391 := program_term_391
  r391 := program_rulesOf_391
  t392 := program_term_392
  r392 := program_rulesOf_392
  t393 := program_term_393
  r393 := program_rulesOf_393
  t395 := program_term_395
  r395 := program_rulesOf_395
  t406 := program_term_406
  r406 := program_rulesOf_406
  t407 := program_term_407
  r407 := program_rulesOf_407
  t409 := program_term_409
  r409 := program_rulesOf_409
  t410 := program_term_410
  r410 := program_rulesOf_410
  t414 := program_term_414
  r414 := program_rulesOf_414
  t417 := program_term_417
  r417 := program_rulesOf_417
  t418 := program_term_418
  r418 := program_rulesOf_418
  t424 := program_term_424
  r424 := program_rulesOf_424
  t425 := program_term_425
  r425 := program_rulesOf_425
  t426 := program_term_426
  r426 := program_rulesOf_426
  t430 := program_term_430
  r430 := program_rulesOf_430
  t432 := program_term_432
  r432 := program_rulesOf_432
  t433 := program_term_433
  r433 := program_rulesOf_433
  t434 := program_term_434
  r434 := program_rulesOf_434
  t435 := program_term_435
  r435 := program_rulesOf_435
  t437 := program_term_437
  r437 := program_rulesOf_437
  t438 := program_term_438
  r438 := program_rulesOf_438
  t439 := program_term_439
  r439 := program_rulesOf_439
  t440 := program_term_440
  r440 := program_rulesOf_440
  t443 := program_term_443
  r443 := program_rulesOf_443
  t444 := program_term_444
  r444 := program_rulesOf_444
  t451 := program_term_451
  r451 := program_rulesOf_451
  t452 := program_term_452
  r452 := program_rulesOf_452
  t469 := program_term_469
  r469 := program_rulesOf_469
  t473 := program_term_473
  r473 := program_rulesOf_473
  t487 := program_term_487
  r487 := program_rulesOf_487
  t488 := program_term_488
  r488 := program_rulesOf_488
  t489 := program_term_489
  r489 := program_rulesOf_489
  t490 := program_term_490
  r490 := program_rulesOf_490
  t491 := program_term_491
  r491 := program_rulesOf_491
  t492 := program_term_492
  r492 := program_rulesOf_492
  t493 := program_term_493
  r493 := program_rulesOf_493
  t495 := program_term_495
  r495 := program_rulesOf_495
  t496 := program_term_496
  r496 := program_rulesOf_496
  t497 := program_term_497
  r497 := program_rulesOf_497
  t498 := program_term_498
  r498 := program_rulesOf_498
  t501 := program_term_501
  r501 := program_rulesOf_501
  t502 := program_term_502
  r502 := program_rulesOf_502
  t513 := program_term_513
  r513 := program_rulesOf_513
  t514 := program_term_514
  r514 := program_rulesOf_514
  t515 := program_term_515
  r515 := program_rulesOf_515
  t516 := program_term_516
  t517 := program_term_517
  r517 := program_rulesOf_517
  t518 := program_term_518
  r518 := program_rulesOf_518
  t520 := program_term_520
  r520 := program_rulesOf_520
  t521 := program_term_521
  r521 := program_rulesOf_521
  t522 := program_term_522
  r522 := program_rulesOf_522
  t524 := program_term_524
  r524 := program_rulesOf_524
  t528 := program_term_528
  r528 := program_rulesOf_528
  t529 := program_term_529
  r529 := program_rulesOf_529
  t530 := program_term_530
  r530 := program_rulesOf_530
  t531 := program_term_531
  r531 := program_rulesOf_531
  t532 := program_term_532
  r532 := program_rulesOf_532
  t533 := program_term_533
  r533 := program_rulesOf_533
  t534 := program_term_534
  r534 := program_rulesOf_534
  t535 := program_term_535
  r535 := program_rulesOf_535
  t541 := program_term_541
  r541 := program_rulesOf_541
  t542 := program_term_542
  r542 := program_rulesOf_542
  t543 := program_term_543
  r543 := program_rulesOf_543
  t544 := program_term_544
  r544 := program_rulesOf_544
  t553 := program_term_553
  r553 := program_rulesOf_553
  t554 := program_term_554
  t555 := program_term_555
  r555 := program_rulesOf_555
  t556 := program_term_556
  r556 := program_rulesOf_556
  t557 := program_term_557
  r557 := program_rulesOf_557
  t558 := program_term_558
  r558 := program_rulesOf_558
  t559 := program_term_559
  r559 := program_rulesOf_559
  t560 := program_term_560
  r560 := program_rulesOf_560
  t561 := program_term_561
  r561 := program_rulesOf_561
  t562 := program_term_562
  r562 := program_rulesOf_562
  t565 := program_term_565
  r565 := program_rulesOf_565
  t566 := program_term_566
  r566 := program_rulesOf_566
  t569 := program_term_569
  t570 := program_term_570
  r570 := program_rulesOf_570
  t571 := program_term_571
  r571 := program_rulesOf_571
  t572 := program_term_572
  r572 := program_rulesOf_572
  t573 := program_term_573
  r573 := program_rulesOf_573
  t574 := program_term_574
  r574 := program_rulesOf_574
  t575 := program_term_575
  r575 := program_rulesOf_575
  t576 := program_term_576
  r576 := program_rulesOf_576
  t577 := program_term_577
  r577 := program_rulesOf_577
  t580 := program_term_580
  t581 := program_term_581
  t582 := program_term_582
  t592 := program_term_592
  t593 := program_term_593
  t634 := program_term_634
  t635 := program_term_635
  t638 := program_term_638
  r638 := program_rulesOf_638
  t639 := program_term_639
  r639 := program_rulesOf_639
  t643 := program_term_643
  r643 := program_rulesOf_643
  t649 := program_term_649
  r649 := program_rulesOf_649
  t650 := program_term_650
  r650 := program_rulesOf_650
  t651 := program_term_651
  r651 := program_rulesOf_651
  t652 := program_term_652
  r652 := program_rulesOf_652
  t653 := program_term_653
  r653 := program_rulesOf_653
  t654 := program_term_654
  r654 := program_rulesOf_654
  t655 := program_term_655
  r655 := program_rulesOf_655
  t656 := program_term_656
  r656 := program_rulesOf_656
  t657 := program_term_657
  r657 := program_rulesOf_657
  t659 := program_term_659
  r659 := program_rulesOf_659
  t660 := program_term_660
  r660 := program_rulesOf_660
  t661 := program_term_661
  r661 := program_rulesOf_661
  t662 := program_term_662
  r662 := program_rulesOf_662
  t663 := program_term_663
  r663 := program_rulesOf_663
  t664 := program_term_664
  r664 := program_rulesOf_664
  t665 := program_term_665
  r665 := program_rulesOf_665
  t666 := program_term_666
  r666 := program_rulesOf_666
  t667 := program_term_667
  r667 := program_rulesOf_667
  t668 := program_term_668
  r668 := program_rulesOf_668
  t669 := program_term_669
  r669 := program_rulesOf_669
  t670 := program_term_670
  r670 := program_rulesOf_670
  t686 := program_term_686
  r686 := program_rulesOf_686
  t687 := program_term_687
  r687 := program_rulesOf_687
  t698 := program_term_698
  r698 := program_rulesOf_698
  t699 := program_term_699
  r699 := program_rulesOf_699
  t700 := program_term_700
  r700 := program_rulesOf_700
  t702 := program_term_702
  t703 := program_term_703
  r703 := program_rulesOf_703
  t704 := program_term_704
  t706 := program_term_706
  t707 := program_term_707
  t709 := program_term_709
  t710 := program_term_710
  r710 := program_rulesOf_710
  t711 := program_term_711
  t712 := program_term_712
  r712 := program_rulesOf_712
  t713 := program_term_713
  t715 := program_term_715
  r715 := program_rulesOf_715
  t722 := program_term_722
  r722 := program_rulesOf_722
  t723 := program_term_723
  t978 := program_term_978
  t1154 := program_term_1154
  t1157 := program_term_1157
  t1161 := program_term_1161
  t1164 := program_term_1164
  t1167 := program_term_1167
  t1182 := program_term_1182
  t1199 := program_term_1199
  t1378 := program_term_1378
  t1382 := program_term_1382
  t1431 := program_term_1431
  t1455 := program_term_1455
  t1485 := program_term_1485
  t1508 := program_term_1508
  t1514 := program_term_1514
  t1527 := program_term_1527
  t1614 := program_term_1614
  t1615 := program_term_1615
  t1616 := program_term_1616
  t1785 := program_term_1785
  t1786 := program_term_1786
  t1787 := program_term_1787
  t1788 := program_term_1788
  t1789 := program_term_1789
  t1790 := program_term_1790
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
  t1827 := program_term_1827
  t1828 := program_term_1828
  t1829 := program_term_1829
  t1830 := program_term_1830
  t1831 := program_term_1831
  t1832 := program_term_1832
  t1833 := program_term_1833
  t1834 := program_term_1834
  t1835 := program_term_1835
  t1836 := program_term_1836
  t1837 := program_term_1837
  t1838 := program_term_1838
  t1844 := program_term_1844
  t1846 := program_term_1846
  t1847 := program_term_1847
  t1849 := program_term_1849
  t1851 := program_term_1851
  t1853 := program_term_1853
  t1854 := program_term_1854
  t1874 := program_term_1874
  t1889 := program_term_1889
  t1890 := program_term_1890
  t1891 := program_term_1891
  t1893 := program_term_1893
  t1896 := program_term_1896
  t1911 := program_term_1911
  t1914 := program_term_1914
  t1915 := program_term_1915
  t1924 := program_term_1924
  t1927 := program_term_1927
  t1928 := program_term_1928
  t1935 := program_term_1935
  t1936 := program_term_1936
  t1937 := program_term_1937
  t1938 := program_term_1938
  t1941 := program_term_1941
  t1946 := program_term_1946
  t1947 := program_term_1947
  t1948 := program_term_1948
  t1949 := program_term_1949
  t1954 := program_term_1954
  t1962 := program_term_1962
  t1963 := program_term_1963
  t1964 := program_term_1964
  t1965 := program_term_1965
  t1966 := program_term_1966
  t1967 := program_term_1967
  t1968 := program_term_1968
  t1969 := program_term_1969
  t1970 := program_term_1970
  t1971 := program_term_1971
  t1972 := program_term_1972
  t1973 := program_term_1973
  t1974 := program_term_1974
  t1975 := program_term_1975
  t1976 := program_term_1976
  t1977 := program_term_1977
  t1978 := program_term_1978
  t1979 := program_term_1979
  t1980 := program_term_1980
  t1984 := program_term_1984
  t1985 := program_term_1985
  t1986 := program_term_1986
  t1987 := program_term_1987
  t1988 := program_term_1988
  t1989 := program_term_1989
  t1990 := program_term_1990
  t1991 := program_term_1991
  t1992 := program_term_1992
  t1996 := program_term_1996
  t1997 := program_term_1997
  t1998 := program_term_1998
  t2000 := program_term_2000
  t2001 := program_term_2001
  t2002 := program_term_2002
  t2004 := program_term_2004
  t2005 := program_term_2005
  t2007 := program_term_2007
  t2008 := program_term_2008
  t2009 := program_term_2009
  t2012 := program_term_2012
  t2013 := program_term_2013
  t2014 := program_term_2014
  t2015 := program_term_2015
  t2016 := program_term_2016
  t2017 := program_term_2017
  t2024 := program_term_2024
  t2028 := program_term_2028
  t2029 := program_term_2029
  t2030 := program_term_2030
  t2031 := program_term_2031
  t2032 := program_term_2032
  t2033 := program_term_2033
  t2034 := program_term_2034
  t2035 := program_term_2035
  t2036 := program_term_2036
  t2037 := program_term_2037
  t2038 := program_term_2038
  t2039 := program_term_2039
  t2041 := program_term_2041
  t2042 := program_term_2042
  t2043 := program_term_2043
  t2044 := program_term_2044
  t2045 := program_term_2045
  t2046 := program_term_2046
  t2047 := program_term_2047
  t2048 := program_term_2048
  t2049 := program_term_2049
  t2050 := program_term_2050
  t2053 := program_term_2053
  t2054 := program_term_2054
  t2055 := program_term_2055
  t2056 := program_term_2056
  t2057 := program_term_2057
  t2058 := program_term_2058
  t2059 := program_term_2059
  t2124 := program_term_2124
  t2125 := program_term_2125
  t2126 := program_term_2126
  t2127 := program_term_2127
  t2135 := program_term_2135
  t2165 := program_term_2165
  t2200 := program_term_2200
  t2234 := program_term_2234
  t2235 := program_term_2235
  t2236 := program_term_2236
  t2237 := program_term_2237
  t2238 := program_term_2238
  t2239 := program_term_2239
  t2240 := program_term_2240
  t2242 := program_term_2242
  t2243 := program_term_2243
  t2255 := program_term_2255
  t2256 := program_term_2256
  t2257 := program_term_2257
  t2258 := program_term_2258
  t2259 := program_term_2259
  t2260 := program_term_2260
  t2261 := program_term_2261
  t2262 := program_term_2262
  t2263 := program_term_2263
  t2264 := program_term_2264
  t2265 := program_term_2265
  t2266 := program_term_2266
  t2267 := program_term_2267
  t2268 := program_term_2268
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
  t2284 := program_term_2284
  t2285 := program_term_2285
  t2286 := program_term_2286
  t2288 := program_term_2288
  t2291 := program_term_2291
  t2292 := program_term_2292
  t2304 := program_term_2304
  t2305 := program_term_2305
  t2306 := program_term_2306
  t2307 := program_term_2307
  t2313 := program_term_2313
  t2314 := program_term_2314
  t2315 := program_term_2315
  t2316 := program_term_2316
  t2317 := program_term_2317
  t2318 := program_term_2318
  t2319 := program_term_2319
  t2320 := program_term_2320
  t2321 := program_term_2321
  t2322 := program_term_2322
  t2323 := program_term_2323
  t2331 := program_term_2331
  t2333 := program_term_2333
  t2341 := program_term_2341
  t2348 := program_term_2348
  t2349 := program_term_2349
  t2356 := program_term_2356
  t2357 := program_term_2357
  t2358 := program_term_2358
  t2359 := program_term_2359
  t2361 := program_term_2361
  t2362 := program_term_2362
  t2363 := program_term_2363
  t2366 := program_term_2366
  t2367 := program_term_2367
  t2368 := program_term_2368
  t2369 := program_term_2369
  t2372 := program_term_2372
  t2376 := program_term_2376
  t2377 := program_term_2377
  t2381 := program_term_2381
  t2382 := program_term_2382
  t2383 := program_term_2383
  t2384 := program_term_2384
  t2385 := program_term_2385
  t2386 := program_term_2386
  t2387 := program_term_2387
  t2388 := program_term_2388
  t2389 := program_term_2389
  t2390 := program_term_2390
  t2391 := program_term_2391
  t2393 := program_term_2393
  t2394 := program_term_2394
  t2395 := program_term_2395
  t2396 := program_term_2396
  t2415 := program_term_2415
  t2425 := program_term_2425
  t2426 := program_term_2426
  t2449 := program_term_2449
  t2451 := program_term_2451
  t2452 := program_term_2452
  t2453 := program_term_2453
  t2458 := program_term_2458
  t2461 := program_term_2461
  t2462 := program_term_2462
  t2463 := program_term_2463
  t2465 := program_term_2465
  t2466 := program_term_2466
  t2468 := program_term_2468
  t2469 := program_term_2469
  t2471 := program_term_2471
  t2473 := program_term_2473
  t2476 := program_term_2476
  t2478 := program_term_2478
  t2482 := program_term_2482
  lower := program_termByName_lower

/-! ### Integer literals (`normInt`), type ids -/

@[isel_data] theorem normInt_4_0 : normInt 4 (0) = 0 := rfl
@[isel_data] theorem normInt_6_0 : normInt 6 (0) = 0 := rfl
@[isel_data] theorem normInt_1_24 : normInt 1 (24) = 24 := rfl
@[isel_data] theorem normInt_1_16 : normInt 1 (16) = 16 := rfl
@[isel_data] theorem normInt_4_8388608 : normInt 4 (8388608) = 8388608 := rfl
@[isel_data] theorem normInt_4_32768 : normInt 4 (32768) = 32768 := rfl
@[isel_data] theorem normInt_1_0 : normInt 1 (0) = 0 := rfl
@[isel_data] theorem normInt_10_0 : normInt 10 (0) = 0 := rfl
@[isel_data] theorem normInt_3_8 : normInt 3 (8) = 8 := rfl
@[isel_data] theorem normInt_3_16 : normInt 3 (16) = 16 := rfl
@[isel_data] theorem normInt_3_4 : normInt 3 (4) = 4 := rfl
@[isel_data] theorem normInt_3_32 : normInt 3 (32) = 32 := rfl
@[isel_data] theorem normInt_3_2 : normInt 3 (2) = 2 := rfl
@[isel_data] theorem normInt_3_64 : normInt 3 (64) = 64 := rfl
@[isel_data] theorem normInt_1_32 : normInt 1 (32) = 32 := rfl
@[isel_data] theorem normInt_1_64 : normInt 1 (64) = 64 := rfl
@[isel_data] theorem normInt_1_1 : normInt 1 (1) = 1 := rfl
@[isel_data] theorem normInt_4_1 : normInt 4 (1) = 1 := rfl
@[isel_data] theorem normInt_9_0 : normInt 9 (0) = 0 := rfl
@[isel_data] theorem normInt_4_63 : normInt 4 (63) = 63 := rfl
@[isel_data] theorem normInt_4_255 : normInt 4 (255) = 255 := rfl
@[isel_data] theorem normInt_6_1 : normInt 6 (1) = 1 := rfl
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
@[isel_data] theorem normInt_4_32 : normInt 4 (32) = 32 := rfl
@[isel_data] theorem normInt_1_63 : normInt 1 (63) = 63 := rfl
@[isel_data] theorem normInt_4_128 : normInt 4 (128) = 128 := rfl
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
