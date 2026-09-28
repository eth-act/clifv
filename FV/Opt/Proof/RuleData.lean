import FV.Isle.Opt.Simplify
import FV.Opt.Proof.RuleAttr

/-!
# ISLE data facts for the mid-end rule proofs (generated, do not edit)

Regenerate: `lake env lean --run FVTest/Opt/Proof/GenData.lean > FV/Opt/Proof/RuleData.lean`.

Roots: the 1193 closure root rules of `simplify`/`simplify_skeleton`
(`Isle.Opt.Closure`); 291 terms reachable from them, of which the internal
constructors (other than the roots) have 164 rules.

`Data p` bundles `Interp.termOf p t = .ok T.x` and `p.rulesOf t = [...]`. Rule proofs are
stated for an abstract `p` with `Data p`, so the kernel never unfolds the program while
checking them; `data_program : Data program` proves every field by `rfl`.
-/

namespace Opt.Proof

open Isle Isle.Opt

/-! ### Term kinds (`rfl`) -/

@[opt_data] theorem term_2_kind : T.«value_type».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "value_type" true))) := rfl
@[opt_data] theorem term_7_kind : T.«imm64_sdiv».kind = (.decl ⟨true, false, true, false⟩ (some (.external "imm64_sdiv")) none) := rfl
@[opt_data] theorem term_8_kind : T.«imm64_udiv».kind = (.decl ⟨true, false, true, false⟩ (some (.external "imm64_udiv")) none) := rfl
@[opt_data] theorem term_9_kind : T.«imm64_srem».kind = (.decl ⟨true, false, true, false⟩ (some (.external "imm64_srem")) none) := rfl
@[opt_data] theorem term_10_kind : T.«imm64_urem».kind = (.decl ⟨true, false, true, false⟩ (some (.external "imm64_urem")) none) := rfl
@[opt_data] theorem term_11_kind : T.«imm64_add».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64_add")) none) := rfl
@[opt_data] theorem term_12_kind : T.«imm64_sub».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64_sub")) none) := rfl
@[opt_data] theorem term_13_kind : T.«imm64_mul».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64_mul")) none) := rfl
@[opt_data] theorem term_14_kind : T.«imm64_and».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64_and")) none) := rfl
@[opt_data] theorem term_15_kind : T.«imm64_or».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64_or")) none) := rfl
@[opt_data] theorem term_16_kind : T.«imm64_xor».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64_xor")) none) := rfl
@[opt_data] theorem term_17_kind : T.«imm64_not».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64_not")) none) := rfl
@[opt_data] theorem term_18_kind : T.«imm64_neg».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64_neg")) none) := rfl
@[opt_data] theorem term_21_kind : T.«imm64_umin».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64_umin")) none) := rfl
@[opt_data] theorem term_22_kind : T.«imm64_umax».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64_umax")) none) := rfl
@[opt_data] theorem term_23_kind : T.«imm64_smin».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64_smin")) none) := rfl
@[opt_data] theorem term_24_kind : T.«imm64_smax».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64_smax")) none) := rfl
@[opt_data] theorem term_25_kind : T.«imm64_shl».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64_shl")) none) := rfl
@[opt_data] theorem term_26_kind : T.«imm64_ushr».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64_ushr")) none) := rfl
@[opt_data] theorem term_27_kind : T.«imm64_sshr».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64_sshr")) none) := rfl
@[opt_data] theorem term_28_kind : T.«imm64_rotl».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64_rotl")) none) := rfl
@[opt_data] theorem term_29_kind : T.«imm64_rotr».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64_rotr")) none) := rfl
@[opt_data] theorem term_30_kind : T.«i64_sextend_u64».kind = (.decl ⟨true, false, false, false⟩ (some (.external "i64_sextend_u64")) none) := rfl
@[opt_data] theorem term_33_kind : T.«imm64_icmp».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64_icmp")) none) := rfl
@[opt_data] theorem term_34_kind : T.«imm64_clz».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64_clz")) none) := rfl
@[opt_data] theorem term_35_kind : T.«imm64_ctz».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64_ctz")) none) := rfl
@[opt_data] theorem term_84_kind : T.«ty_umax».kind = (.decl ⟨true, false, false, false⟩ (some (.external "ty_umax")) none) := rfl
@[opt_data] theorem term_85_kind : T.«ty_smin».kind = (.decl ⟨true, false, false, false⟩ (some (.external "ty_smin")) none) := rfl
@[opt_data] theorem term_86_kind : T.«ty_smax».kind = (.decl ⟨true, false, false, false⟩ (some (.external "ty_smax")) none) := rfl
@[opt_data] theorem term_87_kind : T.«ty_bits».kind = (.decl ⟨true, false, false, false⟩ (some (.external "ty_bits")) none) := rfl
@[opt_data] theorem term_89_kind : T.«ty_bits_u64».kind = (.decl ⟨true, false, false, false⟩ (some (.external "ty_bits_u64")) none) := rfl
@[opt_data] theorem term_90_kind : T.«ty_mask».kind = (.decl ⟨true, false, false, false⟩ (some (.external "ty_mask")) none) := rfl
@[opt_data] theorem term_94_kind : T.«lane_type».kind = (.decl ⟨true, false, false, false⟩ (some (.external "lane_type")) none) := rfl
@[opt_data] theorem term_96_kind : T.«ty_half_width».kind = (.decl ⟨true, false, true, false⟩ (some (.external "ty_half_width")) none) := rfl
@[opt_data] theorem term_97_kind : T.«ty_shift_mask».kind = (.decl ⟨true, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_98_kind : T.«ty_equal».kind = (.decl ⟨true, false, false, false⟩ (some (.external "ty_equal")) none) := rfl
@[opt_data] theorem term_104_kind : T.«intcc_swap_args».kind = (.decl ⟨false, false, false, false⟩ (some (.external "intcc_swap_args")) none) := rfl
@[opt_data] theorem term_105_kind : T.«intcc_complement».kind = (.decl ⟨false, false, false, false⟩ (some (.external "intcc_complement")) none) := rfl
@[opt_data] theorem term_113_kind : T.«fits_in_64».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "fits_in_64" false))) := rfl
@[opt_data] theorem term_119_kind : T.«ty_int_ref_scalar_64_extract».kind = (.decl ⟨true, false, true, false⟩ none (some (.external "ty_int_ref_scalar_64_extract" false))) := rfl
@[opt_data] theorem term_126_kind : T.«ty_int».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "ty_int" false))) := rfl
@[opt_data] theorem term_133_kind : T.«ty_vec128».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "ty_vec128" false))) := rfl
@[opt_data] theorem term_144_kind : T.«u64_from_imm64».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "u64_from_imm64" true))) := rfl
@[opt_data] theorem term_146_kind : T.«imm64_power_of_two».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "imm64_power_of_two" false))) := rfl
@[opt_data] theorem term_147_kind : T.«imm64».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64")) none) := rfl
@[opt_data] theorem term_148_kind : T.«imm64_masked».kind = (.decl ⟨true, false, false, false⟩ (some (.external "imm64_masked")) none) := rfl
@[opt_data] theorem term_159_kind : T.«signed_cond_code».kind = (.decl ⟨true, false, true, false⟩ (some (.external "signed_cond_code")) none) := rfl
@[opt_data] theorem term_164_kind : T.«zero_constant».kind = (.decl ⟨false, false, false, false⟩ (some (.external "zero_constant")) none) := rfl
@[opt_data] theorem term_165_kind : T.«inst_data_value».kind = (.decl ⟨false, true, false, false⟩ none (some (.external "inst_data_value_etor" false))) := rfl
@[opt_data] theorem term_166_kind : T.«inst_data».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "inst_data_etor" false))) := rfl
@[opt_data] theorem term_167_kind : T.«inst_data_value_tupled».kind = (.decl ⟨false, true, false, false⟩ none (some (.external "inst_data_value_tupled_etor" false))) := rfl
@[opt_data] theorem term_168_kind : T.«make_inst».kind = (.decl ⟨false, false, false, false⟩ (some (.external "make_inst_ctor")) none) := rfl
@[opt_data] theorem term_169_kind : T.«make_skeleton_inst».kind = (.decl ⟨false, false, false, false⟩ (some (.external "make_skeleton_inst_ctor")) none) := rfl
@[opt_data] theorem term_170_kind : T.«value_array_2_ctor».kind = (.decl ⟨false, false, false, false⟩ (some (.external "value_array_2_ctor")) none) := rfl
@[opt_data] theorem term_171_kind : T.«value_array_3_ctor».kind = (.decl ⟨false, false, false, false⟩ (some (.external "value_array_3_ctor")) none) := rfl
@[opt_data] theorem term_172_kind : T.«resolve_jump_table_entry».kind = (.decl ⟨true, false, false, false⟩ (some (.external "resolve_jump_table_entry")) none) := rfl
@[opt_data] theorem term_173_kind : T.«block_call_block».kind = (.decl ⟨true, false, false, false⟩ (some (.external "block_call_block")) none) := rfl
@[opt_data] theorem term_174_kind : T.«just_trap_block».kind = (.decl ⟨true, false, true, false⟩ (some (.external "just_trap_block")) none) := rfl
@[opt_data] theorem term_178_kind : T.«inst_to_skeleton_inst_simplification».kind = (.decl ⟨true, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_179_kind : T.«value_to_skeleton_inst_simplification».kind = (.decl ⟨true, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_180_kind : T.«remove_inst».kind = (.decl ⟨true, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_182_kind : T.«replace_branch_cond».kind = (.decl ⟨true, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_183_kind : T.«replace_with_two».kind = (.decl ⟨true, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_185_kind : T.«remat».kind = (.decl ⟨false, false, false, false⟩ (some (.external "remat")) none) := rfl
@[opt_data] theorem term_186_kind : T.«subsume».kind = (.decl ⟨false, false, false, false⟩ (some (.external "subsume")) none) := rfl
@[opt_data] theorem term_187_kind : T.«iconst_sextend_etor».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "iconst_sextend_etor" false))) := rfl
@[opt_data] theorem term_191_kind : T.«uextend_maybe_etor».kind = (.decl ⟨false, true, false, false⟩ none (some (.external "uextend_maybe_etor" true))) := rfl
@[opt_data] theorem term_204_kind : T.«i64_is_negative_power_of_two».kind = (.decl ⟨true, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_205_kind : T.«i64_is_any_sign_power_of_two».kind = (.decl ⟨true, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_206_kind : T.«div_const_magic_u32».kind = (.decl ⟨false, false, false, false⟩ (some (.external "div_const_magic_u32")) none) := rfl
@[opt_data] theorem term_207_kind : T.«div_const_magic_u64».kind = (.decl ⟨false, false, false, false⟩ (some (.external "div_const_magic_u64")) none) := rfl
@[opt_data] theorem term_208_kind : T.«div_const_magic_s32».kind = (.decl ⟨false, false, false, false⟩ (some (.external "div_const_magic_s32")) none) := rfl
@[opt_data] theorem term_209_kind : T.«div_const_magic_s64».kind = (.decl ⟨false, false, false, false⟩ (some (.external "div_const_magic_s64")) none) := rfl
@[opt_data] theorem term_210_kind : T.«apply_div_const_magic_u32».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_211_kind : T.«apply_div_const_magic_u32_inner».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_212_kind : T.«apply_div_const_magic_u32_maybe_add».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_213_kind : T.«apply_div_const_magic_u32_maybe_shift».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_214_kind : T.«apply_div_const_magic_u32_finish».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_215_kind : T.«apply_div_const_magic_u64».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_216_kind : T.«apply_div_const_magic_u64_inner».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_217_kind : T.«apply_div_const_magic_u64_maybe_add».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_218_kind : T.«apply_div_const_magic_u64_maybe_shift».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_219_kind : T.«apply_div_const_magic_u64_finish».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_220_kind : T.«apply_div_const_magic_s32».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_221_kind : T.«apply_div_const_magic_s32_inner».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_222_kind : T.«apply_div_const_magic_s32_add_sub».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_223_kind : T.«apply_div_const_magic_s32_shift».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_224_kind : T.«apply_div_const_magic_s32_finish».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_225_kind : T.«apply_div_const_magic_s64».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_226_kind : T.«apply_div_const_magic_s64_inner».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_227_kind : T.«apply_div_const_magic_s64_add_sub».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_228_kind : T.«apply_div_const_magic_s64_shift».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_229_kind : T.«apply_div_const_magic_s64_finish».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_230_kind : T.«cmp_true».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_231_kind : T.«all_zero_etor».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "all_zero_etor" false))) := rfl
@[opt_data] theorem term_232_kind : T.«f16_zero».kind = (.decl ⟨false, false, false, false⟩ (some (.external "f16_zero")) none) := rfl
@[opt_data] theorem term_233_kind : T.«ty_vector».kind = (.decl ⟨false, false, false, false⟩ none (some (.external "ty_vector" false))) := rfl
@[opt_data] theorem term_235_kind : T.«truthy».kind = (.decl ⟨true, true, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_241_kind : T.«f32_from_uint».kind = (.decl ⟨false, false, false, false⟩ (some (.external "f32_from_uint")) none) := rfl
@[opt_data] theorem term_242_kind : T.«f64_from_uint».kind = (.decl ⟨false, false, false, false⟩ (some (.external "f64_from_uint")) none) := rfl
@[opt_data] theorem term_245_kind : T.«u64_bswap16».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_bswap16")) none) := rfl
@[opt_data] theorem term_246_kind : T.«u64_bswap32».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_bswap32")) none) := rfl
@[opt_data] theorem term_247_kind : T.«u64_bswap64».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_bswap64")) none) := rfl
@[opt_data] theorem term_249_kind : T.«intcc_comparable».kind = (.decl ⟨true, false, true, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_250_kind : T.«decompose_intcc».kind = (.decl ⟨true, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_251_kind : T.«compose_icmp».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_252_kind : T.«intcc_class».kind = (.decl ⟨true, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_253_kind : T.«shift_amt_to_type».kind = (.decl ⟨true, false, true, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_254_kind : T.«iadd_uextend».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_255_kind : T.«isub_uextend».kind = (.decl ⟨false, false, false, false⟩ (some .internal) none) := rfl
@[opt_data] theorem term_506_kind : T.«i32_lt».kind = (.decl ⟨true, false, false, false⟩ (some (.external "i32_lt")) none) := rfl
@[opt_data] theorem term_508_kind : T.«i32_gt».kind = (.decl ⟨true, false, false, false⟩ (some (.external "i32_gt")) none) := rfl
@[opt_data] theorem term_567_kind : T.«u32_lt».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u32_lt")) none) := rfl
@[opt_data] theorem term_576_kind : T.«u32_sub».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u32_sub")) none) := rfl
@[opt_data] theorem term_603_kind : T.«u32_matches_non_zero».kind = (.decl ⟨true, false, false, false⟩ none (some (.external "u32_matches_non_zero" false))) := rfl
@[opt_data] theorem term_623_kind : T.«u32_is_power_of_two».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u32_is_power_of_two")) none) := rfl
@[opt_data] theorem term_628_kind : T.«i64_eq».kind = (.decl ⟨true, false, false, false⟩ (some (.external "i64_eq")) none) := rfl
@[opt_data] theorem term_629_kind : T.«i64_ne».kind = (.decl ⟨true, false, false, false⟩ (some (.external "i64_ne")) none) := rfl
@[opt_data] theorem term_630_kind : T.«i64_lt».kind = (.decl ⟨true, false, false, false⟩ (some (.external "i64_lt")) none) := rfl
@[opt_data] theorem term_632_kind : T.«i64_gt».kind = (.decl ⟨true, false, false, false⟩ (some (.external "i64_gt")) none) := rfl
@[opt_data] theorem term_633_kind : T.«i64_gt_eq».kind = (.decl ⟨true, false, false, false⟩ (some (.external "i64_gt_eq")) none) := rfl
@[opt_data] theorem term_654_kind : T.«i64_shl».kind = (.decl ⟨true, false, false, false⟩ (some (.external "i64_shl")) none) := rfl
@[opt_data] theorem term_666_kind : T.«i64_matches_non_zero».kind = (.decl ⟨true, false, false, false⟩ none (some (.external "i64_matches_non_zero" false))) := rfl
@[opt_data] theorem term_682_kind : T.«i64_trailing_zeros».kind = (.decl ⟨true, false, false, false⟩ (some (.external "i64_trailing_zeros")) none) := rfl
@[opt_data] theorem term_687_kind : T.«i64_wrapping_neg».kind = (.decl ⟨true, false, false, false⟩ (some (.external "i64_wrapping_neg")) none) := rfl
@[opt_data] theorem term_689_kind : T.«u64_eq».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_eq")) none) := rfl
@[opt_data] theorem term_691_kind : T.«u64_lt».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_lt")) none) := rfl
@[opt_data] theorem term_692_kind : T.«u64_lt_eq».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_lt_eq")) none) := rfl
@[opt_data] theorem term_693_kind : T.«u64_gt».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_gt")) none) := rfl
@[opt_data] theorem term_696_kind : T.«u64_wrapping_add».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_wrapping_add")) none) := rfl
@[opt_data] theorem term_699_kind : T.«u64_wrapping_sub».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_wrapping_sub")) none) := rfl
@[opt_data] theorem term_700_kind : T.«u64_sub».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_sub")) none) := rfl
@[opt_data] theorem term_706_kind : T.«u64_div».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_div")) none) := rfl
@[opt_data] theorem term_707_kind : T.«u64_checked_rem».kind = (.decl ⟨true, false, true, false⟩ (some (.external "u64_checked_rem")) none) := rfl
@[opt_data] theorem term_708_kind : T.«u64_rem».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_rem")) none) := rfl
@[opt_data] theorem term_709_kind : T.«u64_and».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_and")) none) := rfl
@[opt_data] theorem term_710_kind : T.«u64_or».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_or")) none) := rfl
@[opt_data] theorem term_712_kind : T.«u64_not».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_not")) none) := rfl
@[opt_data] theorem term_715_kind : T.«u64_shl».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_shl")) none) := rfl
@[opt_data] theorem term_727_kind : T.«u64_matches_non_zero».kind = (.decl ⟨true, false, false, false⟩ none (some (.external "u64_matches_non_zero" false))) := rfl
@[opt_data] theorem term_742_kind : T.«u64_ilog2».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_ilog2")) none) := rfl
@[opt_data] theorem term_743_kind : T.«u64_trailing_zeros».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_trailing_zeros")) none) := rfl
@[opt_data] theorem term_747_kind : T.«u64_is_power_of_two».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u64_is_power_of_two")) none) := rfl
@[opt_data] theorem term_748_kind : T.«u64_matches_power_of_two».kind = (.decl ⟨true, false, false, false⟩ none (some (.external "u64_matches_power_of_two" false))) := rfl
@[opt_data] theorem term_910_kind : T.«u8_into_u32».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u8_into_u32")) none) := rfl
@[opt_data] theorem term_914_kind : T.«u8_into_u64».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u8_into_u64")) none) := rfl
@[opt_data] theorem term_987_kind : T.«i32_into_i64».kind = (.decl ⟨true, false, false, false⟩ (some (.external "i32_into_i64")) none) := rfl
@[opt_data] theorem term_1015_kind : T.«u32_into_i64».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u32_into_i64")) none) := rfl
@[opt_data] theorem term_1017_kind : T.«u32_into_u64».kind = (.decl ⟨true, false, false, false⟩ (some (.external "u32_into_u64")) none) := rfl
@[opt_data] theorem term_1040_kind : T.«i32_from_i64».kind = (.decl ⟨true, false, false, false⟩ none (some (.external "i64_from_i32" false))) := rfl
@[opt_data] theorem term_1046_kind : T.«i64_cast_unsigned».kind = (.decl ⟨true, false, false, false⟩ (some (.external "i64_cast_unsigned")) none) := rfl
@[opt_data] theorem term_1073_kind : T.«u32_from_u64».kind = (.decl ⟨true, false, false, false⟩ none (some (.external "u64_from_u32" false))) := rfl
@[opt_data] theorem term_1146_kind : T.«value_array_2».kind = (.decl ⟨false, false, false, false⟩ (some (.external "pack_value_array_2")) (some (.external "unpack_value_array_2" true))) := rfl
@[opt_data] theorem term_1147_kind : T.«value_array_3».kind = (.decl ⟨false, false, false, false⟩ (some (.external "pack_value_array_3")) (some (.external "unpack_value_array_3" true))) := rfl
@[opt_data] theorem term_1148_kind : T.«block_array_2».kind = (.decl ⟨false, false, false, false⟩ (some (.external "pack_block_array_2")) (some (.external "unpack_block_array_2" true))) := rfl
@[opt_data] theorem term_1305_kind : T.«SkeletonInstSimplification.Remove».kind = (.enumVariant 0) := rfl
@[opt_data] theorem term_1306_kind : T.«SkeletonInstSimplification.RemoveWithVal».kind = (.enumVariant 1) := rfl
@[opt_data] theorem term_1307_kind : T.«SkeletonInstSimplification.Replace».kind = (.enumVariant 2) := rfl
@[opt_data] theorem term_1309_kind : T.«SkeletonInstSimplification.ReplaceBranchCond».kind = (.enumVariant 4) := rfl
@[opt_data] theorem term_1310_kind : T.«SkeletonInstSimplification.ReplaceWithTwo».kind = (.enumVariant 5) := rfl
@[opt_data] theorem term_1312_kind : T.«DivConstMagicU32.U32».kind = (.enumVariant 0) := rfl
@[opt_data] theorem term_1313_kind : T.«DivConstMagicU64.U64».kind = (.enumVariant 0) := rfl
@[opt_data] theorem term_1314_kind : T.«DivConstMagicS32.S32».kind = (.enumVariant 0) := rfl
@[opt_data] theorem term_1315_kind : T.«DivConstMagicS64.S64».kind = (.enumVariant 0) := rfl
@[opt_data] theorem term_1341_kind : T.«IntCC.Equal».kind = (.enumVariant 0) := rfl
@[opt_data] theorem term_1342_kind : T.«IntCC.NotEqual».kind = (.enumVariant 1) := rfl
@[opt_data] theorem term_1343_kind : T.«IntCC.SignedGreaterThan».kind = (.enumVariant 2) := rfl
@[opt_data] theorem term_1344_kind : T.«IntCC.SignedGreaterThanOrEqual».kind = (.enumVariant 3) := rfl
@[opt_data] theorem term_1345_kind : T.«IntCC.SignedLessThan».kind = (.enumVariant 4) := rfl
@[opt_data] theorem term_1346_kind : T.«IntCC.SignedLessThanOrEqual».kind = (.enumVariant 5) := rfl
@[opt_data] theorem term_1347_kind : T.«IntCC.UnsignedGreaterThan».kind = (.enumVariant 6) := rfl
@[opt_data] theorem term_1348_kind : T.«IntCC.UnsignedGreaterThanOrEqual».kind = (.enumVariant 7) := rfl
@[opt_data] theorem term_1349_kind : T.«IntCC.UnsignedLessThan».kind = (.enumVariant 8) := rfl
@[opt_data] theorem term_1350_kind : T.«IntCC.UnsignedLessThanOrEqual».kind = (.enumVariant 9) := rfl
@[opt_data] theorem term_1356_kind : T.«Opcode.Jump».kind = (.enumVariant 0) := rfl
@[opt_data] theorem term_1357_kind : T.«Opcode.Brif».kind = (.enumVariant 1) := rfl
@[opt_data] theorem term_1358_kind : T.«Opcode.BrTable».kind = (.enumVariant 2) := rfl
@[opt_data] theorem term_1361_kind : T.«Opcode.Trapz».kind = (.enumVariant 5) := rfl
@[opt_data] theorem term_1362_kind : T.«Opcode.Trapnz».kind = (.enumVariant 6) := rfl
@[opt_data] theorem term_1371_kind : T.«Opcode.Splat».kind = (.enumVariant 15) := rfl
@[opt_data] theorem term_1376_kind : T.«Opcode.Smin».kind = (.enumVariant 20) := rfl
@[opt_data] theorem term_1377_kind : T.«Opcode.Umin».kind = (.enumVariant 21) := rfl
@[opt_data] theorem term_1378_kind : T.«Opcode.Smax».kind = (.enumVariant 22) := rfl
@[opt_data] theorem term_1379_kind : T.«Opcode.Umax».kind = (.enumVariant 23) := rfl
@[opt_data] theorem term_1413_kind : T.«Opcode.Iconst».kind = (.enumVariant 57) := rfl
@[opt_data] theorem term_1414_kind : T.«Opcode.F16const».kind = (.enumVariant 58) := rfl
@[opt_data] theorem term_1415_kind : T.«Opcode.F32const».kind = (.enumVariant 59) := rfl
@[opt_data] theorem term_1416_kind : T.«Opcode.F64const».kind = (.enumVariant 60) := rfl
@[opt_data] theorem term_1417_kind : T.«Opcode.F128const».kind = (.enumVariant 61) := rfl
@[opt_data] theorem term_1418_kind : T.«Opcode.Vconst».kind = (.enumVariant 62) := rfl
@[opt_data] theorem term_1421_kind : T.«Opcode.Select».kind = (.enumVariant 65) := rfl
@[opt_data] theorem term_1428_kind : T.«Opcode.Icmp».kind = (.enumVariant 72) := rfl
@[opt_data] theorem term_1429_kind : T.«Opcode.Iadd».kind = (.enumVariant 73) := rfl
@[opt_data] theorem term_1430_kind : T.«Opcode.Isub».kind = (.enumVariant 74) := rfl
@[opt_data] theorem term_1431_kind : T.«Opcode.Ineg».kind = (.enumVariant 75) := rfl
@[opt_data] theorem term_1432_kind : T.«Opcode.Iabs».kind = (.enumVariant 76) := rfl
@[opt_data] theorem term_1433_kind : T.«Opcode.Imul».kind = (.enumVariant 77) := rfl
@[opt_data] theorem term_1434_kind : T.«Opcode.Umulhi».kind = (.enumVariant 78) := rfl
@[opt_data] theorem term_1435_kind : T.«Opcode.Smulhi».kind = (.enumVariant 79) := rfl
@[opt_data] theorem term_1438_kind : T.«Opcode.Udiv».kind = (.enumVariant 82) := rfl
@[opt_data] theorem term_1439_kind : T.«Opcode.Sdiv».kind = (.enumVariant 83) := rfl
@[opt_data] theorem term_1440_kind : T.«Opcode.Urem».kind = (.enumVariant 84) := rfl
@[opt_data] theorem term_1441_kind : T.«Opcode.Srem».kind = (.enumVariant 85) := rfl
@[opt_data] theorem term_1453_kind : T.«Opcode.Band».kind = (.enumVariant 97) := rfl
@[opt_data] theorem term_1454_kind : T.«Opcode.Bor».kind = (.enumVariant 98) := rfl
@[opt_data] theorem term_1455_kind : T.«Opcode.Bxor».kind = (.enumVariant 99) := rfl
@[opt_data] theorem term_1456_kind : T.«Opcode.Bnot».kind = (.enumVariant 100) := rfl
@[opt_data] theorem term_1457_kind : T.«Opcode.Rotl».kind = (.enumVariant 101) := rfl
@[opt_data] theorem term_1458_kind : T.«Opcode.Rotr».kind = (.enumVariant 102) := rfl
@[opt_data] theorem term_1459_kind : T.«Opcode.Ishl».kind = (.enumVariant 103) := rfl
@[opt_data] theorem term_1460_kind : T.«Opcode.Ushr».kind = (.enumVariant 104) := rfl
@[opt_data] theorem term_1461_kind : T.«Opcode.Sshr».kind = (.enumVariant 105) := rfl
@[opt_data] theorem term_1462_kind : T.«Opcode.Bitrev».kind = (.enumVariant 106) := rfl
@[opt_data] theorem term_1463_kind : T.«Opcode.Clz».kind = (.enumVariant 107) := rfl
@[opt_data] theorem term_1465_kind : T.«Opcode.Ctz».kind = (.enumVariant 109) := rfl
@[opt_data] theorem term_1466_kind : T.«Opcode.Bswap».kind = (.enumVariant 110) := rfl
@[opt_data] theorem term_1467_kind : T.«Opcode.Popcnt».kind = (.enumVariant 111) := rfl
@[opt_data] theorem term_1486_kind : T.«Opcode.Bmask».kind = (.enumVariant 130) := rfl
@[opt_data] theorem term_1487_kind : T.«Opcode.Ireduce».kind = (.enumVariant 131) := rfl
@[opt_data] theorem term_1497_kind : T.«Opcode.Uextend».kind = (.enumVariant 141) := rfl
@[opt_data] theorem term_1498_kind : T.«Opcode.Sextend».kind = (.enumVariant 142) := rfl
@[opt_data] theorem term_1511_kind : T.«Opcode.Iconcat».kind = (.enumVariant 155) := rfl
@[opt_data] theorem term_1521_kind : T.«InstructionData.Binary».kind = (.enumVariant 2) := rfl
@[opt_data] theorem term_1523_kind : T.«InstructionData.BranchTable».kind = (.enumVariant 4) := rfl
@[opt_data] theorem term_1524_kind : T.«InstructionData.Brif».kind = (.enumVariant 5) := rfl
@[opt_data] theorem term_1527_kind : T.«InstructionData.CondTrap».kind = (.enumVariant 8) := rfl
@[opt_data] theorem term_1533_kind : T.«InstructionData.IntCompare».kind = (.enumVariant 14) := rfl
@[opt_data] theorem term_1534_kind : T.«InstructionData.Jump».kind = (.enumVariant 15) := rfl
@[opt_data] theorem term_1543_kind : T.«InstructionData.Ternary».kind = (.enumVariant 24) := rfl
@[opt_data] theorem term_1548_kind : T.«InstructionData.Unary».kind = (.enumVariant 29) := rfl
@[opt_data] theorem term_1549_kind : T.«InstructionData.UnaryConst».kind = (.enumVariant 30) := rfl
@[opt_data] theorem term_1551_kind : T.«InstructionData.UnaryIeee16».kind = (.enumVariant 32) := rfl
@[opt_data] theorem term_1552_kind : T.«InstructionData.UnaryIeee32».kind = (.enumVariant 33) := rfl
@[opt_data] theorem term_1553_kind : T.«InstructionData.UnaryIeee64».kind = (.enumVariant 34) := rfl
@[opt_data] theorem term_1554_kind : T.«InstructionData.UnaryImm».kind = (.enumVariant 35) := rfl

/-- The facts about the exported program that the rule proofs use. -/
structure Data (p : Program) : Prop where
  t2 : Interp.termOf p 2 = .ok T.«value_type»
  t7 : Interp.termOf p 7 = .ok T.«imm64_sdiv»
  t8 : Interp.termOf p 8 = .ok T.«imm64_udiv»
  t9 : Interp.termOf p 9 = .ok T.«imm64_srem»
  t10 : Interp.termOf p 10 = .ok T.«imm64_urem»
  t11 : Interp.termOf p 11 = .ok T.«imm64_add»
  t12 : Interp.termOf p 12 = .ok T.«imm64_sub»
  t13 : Interp.termOf p 13 = .ok T.«imm64_mul»
  t14 : Interp.termOf p 14 = .ok T.«imm64_and»
  t15 : Interp.termOf p 15 = .ok T.«imm64_or»
  t16 : Interp.termOf p 16 = .ok T.«imm64_xor»
  t17 : Interp.termOf p 17 = .ok T.«imm64_not»
  t18 : Interp.termOf p 18 = .ok T.«imm64_neg»
  t21 : Interp.termOf p 21 = .ok T.«imm64_umin»
  t22 : Interp.termOf p 22 = .ok T.«imm64_umax»
  t23 : Interp.termOf p 23 = .ok T.«imm64_smin»
  t24 : Interp.termOf p 24 = .ok T.«imm64_smax»
  t25 : Interp.termOf p 25 = .ok T.«imm64_shl»
  t26 : Interp.termOf p 26 = .ok T.«imm64_ushr»
  t27 : Interp.termOf p 27 = .ok T.«imm64_sshr»
  t28 : Interp.termOf p 28 = .ok T.«imm64_rotl»
  t29 : Interp.termOf p 29 = .ok T.«imm64_rotr»
  t30 : Interp.termOf p 30 = .ok T.«i64_sextend_u64»
  t33 : Interp.termOf p 33 = .ok T.«imm64_icmp»
  t34 : Interp.termOf p 34 = .ok T.«imm64_clz»
  t35 : Interp.termOf p 35 = .ok T.«imm64_ctz»
  t84 : Interp.termOf p 84 = .ok T.«ty_umax»
  t85 : Interp.termOf p 85 = .ok T.«ty_smin»
  t86 : Interp.termOf p 86 = .ok T.«ty_smax»
  t87 : Interp.termOf p 87 = .ok T.«ty_bits»
  t89 : Interp.termOf p 89 = .ok T.«ty_bits_u64»
  t90 : Interp.termOf p 90 = .ok T.«ty_mask»
  t94 : Interp.termOf p 94 = .ok T.«lane_type»
  t96 : Interp.termOf p 96 = .ok T.«ty_half_width»
  t97 : Interp.termOf p 97 = .ok T.«ty_shift_mask»
  r97 : p.rulesOf 97 = [rule_prelude_343]
  t98 : Interp.termOf p 98 = .ok T.«ty_equal»
  t104 : Interp.termOf p 104 = .ok T.«intcc_swap_args»
  t105 : Interp.termOf p 105 = .ok T.«intcc_complement»
  t113 : Interp.termOf p 113 = .ok T.«fits_in_64»
  t119 : Interp.termOf p 119 = .ok T.«ty_int_ref_scalar_64_extract»
  t126 : Interp.termOf p 126 = .ok T.«ty_int»
  t133 : Interp.termOf p 133 = .ok T.«ty_vec128»
  t144 : Interp.termOf p 144 = .ok T.«u64_from_imm64»
  t146 : Interp.termOf p 146 = .ok T.«imm64_power_of_two»
  t147 : Interp.termOf p 147 = .ok T.«imm64»
  t148 : Interp.termOf p 148 = .ok T.«imm64_masked»
  t159 : Interp.termOf p 159 = .ok T.«signed_cond_code»
  t164 : Interp.termOf p 164 = .ok T.«zero_constant»
  t165 : Interp.termOf p 165 = .ok T.«inst_data_value»
  t166 : Interp.termOf p 166 = .ok T.«inst_data»
  t167 : Interp.termOf p 167 = .ok T.«inst_data_value_tupled»
  t168 : Interp.termOf p 168 = .ok T.«make_inst»
  t169 : Interp.termOf p 169 = .ok T.«make_skeleton_inst»
  t170 : Interp.termOf p 170 = .ok T.«value_array_2_ctor»
  t171 : Interp.termOf p 171 = .ok T.«value_array_3_ctor»
  t172 : Interp.termOf p 172 = .ok T.«resolve_jump_table_entry»
  t173 : Interp.termOf p 173 = .ok T.«block_call_block»
  t174 : Interp.termOf p 174 = .ok T.«just_trap_block»
  t175 : Interp.termOf p 175 = .ok T.«spaceship_s»
  r175 : p.rulesOf 175 = [rule_prelude_opt_74]
  t176 : Interp.termOf p 176 = .ok T.«spaceship_u»
  r176 : p.rulesOf 176 = [rule_prelude_opt_77]
  t178 : Interp.termOf p 178 = .ok T.«inst_to_skeleton_inst_simplification»
  r178 : p.rulesOf 178 = [rule_prelude_opt_136]
  t179 : Interp.termOf p 179 = .ok T.«value_to_skeleton_inst_simplification»
  r179 : p.rulesOf 179 = [rule_prelude_opt_140]
  t180 : Interp.termOf p 180 = .ok T.«remove_inst»
  r180 : p.rulesOf 180 = [rule_prelude_opt_144]
  t182 : Interp.termOf p 182 = .ok T.«replace_branch_cond»
  r182 : p.rulesOf 182 = [rule_prelude_opt_150]
  t183 : Interp.termOf p 183 = .ok T.«replace_with_two»
  r183 : p.rulesOf 183 = [rule_prelude_opt_154]
  t185 : Interp.termOf p 185 = .ok T.«remat»
  t186 : Interp.termOf p 186 = .ok T.«subsume»
  t187 : Interp.termOf p 187 = .ok T.«iconst_sextend_etor»
  t188 : Interp.termOf p 188 = .ok T.«iconst_s»
  r188 : p.rulesOf 188 = [rule_prelude_opt_208, rule_prelude_opt_207, rule_prelude_opt_201]
  t189 : Interp.termOf p 189 = .ok T.«iconst_u»
  r189 : p.rulesOf 189 = [rule_prelude_opt_225, rule_prelude_opt_224, rule_prelude_opt_221]
  t191 : Interp.termOf p 191 = .ok T.«uextend_maybe_etor»
  t192 : Interp.termOf p 192 = .ok T.«uextend_maybe»
  r192 : p.rulesOf 192 = [rule_prelude_opt_246, rule_prelude_opt_245]
  t193 : Interp.termOf p 193 = .ok T.«sextend_maybe»
  r193 : p.rulesOf 193 = [rule_prelude_opt_252, rule_prelude_opt_251]
  t194 : Interp.termOf p 194 = .ok T.«eq»
  r194 : p.rulesOf 194 = [rule_prelude_opt_61]
  t195 : Interp.termOf p 195 = .ok T.«ne»
  r195 : p.rulesOf 195 = [rule_prelude_opt_62]
  t196 : Interp.termOf p 196 = .ok T.«ult»
  r196 : p.rulesOf 196 = [rule_prelude_opt_63]
  t197 : Interp.termOf p 197 = .ok T.«ule»
  r197 : p.rulesOf 197 = [rule_prelude_opt_64]
  t198 : Interp.termOf p 198 = .ok T.«ugt»
  r198 : p.rulesOf 198 = [rule_prelude_opt_65]
  t199 : Interp.termOf p 199 = .ok T.«uge»
  r199 : p.rulesOf 199 = [rule_prelude_opt_66]
  t200 : Interp.termOf p 200 = .ok T.«slt»
  r200 : p.rulesOf 200 = [rule_prelude_opt_67]
  t201 : Interp.termOf p 201 = .ok T.«sle»
  r201 : p.rulesOf 201 = [rule_prelude_opt_68]
  t202 : Interp.termOf p 202 = .ok T.«sgt»
  r202 : p.rulesOf 202 = [rule_prelude_opt_69]
  t203 : Interp.termOf p 203 = .ok T.«sge»
  r203 : p.rulesOf 203 = [rule_prelude_opt_70]
  t204 : Interp.termOf p 204 = .ok T.«i64_is_negative_power_of_two»
  r204 : p.rulesOf 204 = [rule_prelude_opt_289]
  t205 : Interp.termOf p 205 = .ok T.«i64_is_any_sign_power_of_two»
  r205 : p.rulesOf 205 = [rule_prelude_opt_293, rule_prelude_opt_296, rule_prelude_opt_299]
  t206 : Interp.termOf p 206 = .ok T.«div_const_magic_u32»
  t207 : Interp.termOf p 207 = .ok T.«div_const_magic_u64»
  t208 : Interp.termOf p 208 = .ok T.«div_const_magic_s32»
  t209 : Interp.termOf p 209 = .ok T.«div_const_magic_s64»
  t210 : Interp.termOf p 210 = .ok T.«apply_div_const_magic_u32»
  r210 : p.rulesOf 210 = [rule_prelude_opt_328]
  t211 : Interp.termOf p 211 = .ok T.«apply_div_const_magic_u32_inner»
  r211 : p.rulesOf 211 = [rule_prelude_opt_333]
  t212 : Interp.termOf p 212 = .ok T.«apply_div_const_magic_u32_maybe_add»
  r212 : p.rulesOf 212 = [rule_prelude_opt_349, rule_prelude_opt_358]
  t213 : Interp.termOf p 213 = .ok T.«apply_div_const_magic_u32_maybe_shift»
  r213 : p.rulesOf 213 = [rule_prelude_opt_372, rule_prelude_opt_378]
  t214 : Interp.termOf p 214 = .ok T.«apply_div_const_magic_u32_finish»
  r214 : p.rulesOf 214 = [rule_prelude_opt_398, rule_prelude_opt_399]
  t215 : Interp.termOf p 215 = .ok T.«apply_div_const_magic_u64»
  r215 : p.rulesOf 215 = [rule_prelude_opt_405]
  t216 : Interp.termOf p 216 = .ok T.«apply_div_const_magic_u64_inner»
  r216 : p.rulesOf 216 = [rule_prelude_opt_410]
  t217 : Interp.termOf p 217 = .ok T.«apply_div_const_magic_u64_maybe_add»
  r217 : p.rulesOf 217 = [rule_prelude_opt_426, rule_prelude_opt_435]
  t218 : Interp.termOf p 218 = .ok T.«apply_div_const_magic_u64_maybe_shift»
  r218 : p.rulesOf 218 = [rule_prelude_opt_449, rule_prelude_opt_455]
  t219 : Interp.termOf p 219 = .ok T.«apply_div_const_magic_u64_finish»
  r219 : p.rulesOf 219 = [rule_prelude_opt_475, rule_prelude_opt_476]
  t220 : Interp.termOf p 220 = .ok T.«apply_div_const_magic_s32»
  r220 : p.rulesOf 220 = [rule_prelude_opt_483]
  t221 : Interp.termOf p 221 = .ok T.«apply_div_const_magic_s32_inner»
  r221 : p.rulesOf 221 = [rule_prelude_opt_489]
  t222 : Interp.termOf p 222 = .ok T.«apply_div_const_magic_s32_add_sub»
  r222 : p.rulesOf 222 = [rule_prelude_opt_505, rule_prelude_opt_514, rule_prelude_opt_523]
  t223 : Interp.termOf p 223 = .ok T.«apply_div_const_magic_s32_shift»
  r223 : p.rulesOf 223 = [rule_prelude_opt_534]
  t224 : Interp.termOf p 224 = .ok T.«apply_div_const_magic_s32_finish»
  r224 : p.rulesOf 224 = [rule_prelude_opt_555, rule_prelude_opt_558]
  t225 : Interp.termOf p 225 = .ok T.«apply_div_const_magic_s64»
  r225 : p.rulesOf 225 = [rule_prelude_opt_564]
  t226 : Interp.termOf p 226 = .ok T.«apply_div_const_magic_s64_inner»
  r226 : p.rulesOf 226 = [rule_prelude_opt_570]
  t227 : Interp.termOf p 227 = .ok T.«apply_div_const_magic_s64_add_sub»
  r227 : p.rulesOf 227 = [rule_prelude_opt_586, rule_prelude_opt_595, rule_prelude_opt_604]
  t228 : Interp.termOf p 228 = .ok T.«apply_div_const_magic_s64_shift»
  r228 : p.rulesOf 228 = [rule_prelude_opt_615]
  t229 : Interp.termOf p 229 = .ok T.«apply_div_const_magic_s64_finish»
  r229 : p.rulesOf 229 = [rule_prelude_opt_636, rule_prelude_opt_639]
  t230 : Interp.termOf p 230 = .ok T.«cmp_true»
  r230 : p.rulesOf 230 = [rule_arithmetic_401, rule_arithmetic_400]
  t231 : Interp.termOf p 231 = .ok T.«all_zero_etor»
  t232 : Interp.termOf p 232 = .ok T.«f16_zero»
  t233 : Interp.termOf p 233 = .ok T.«ty_vector»
  t234 : Interp.termOf p 234 = .ok T.«all_zero»
  r234 : p.rulesOf 234 = [rule_bitops_18, rule_bitops_17, rule_bitops_16, rule_bitops_15, rule_bitops_14, rule_bitops_13]
  t235 : Interp.termOf p 235 = .ok T.«truthy»
  r235 : p.rulesOf 235 = [rule_bitops_111, rule_bitops_112, rule_bitops_113, rule_bitops_114, rule_bitops_115, rule_bitops_116, rule_bitops_117, rule_bitops_118, rule_bitops_119, rule_bitops_120, rule_bitops_122]
  t241 : Interp.termOf p 241 = .ok T.«f32_from_uint»
  t242 : Interp.termOf p 242 = .ok T.«f64_from_uint»
  t245 : Interp.termOf p 245 = .ok T.«u64_bswap16»
  t246 : Interp.termOf p 246 = .ok T.«u64_bswap32»
  t247 : Interp.termOf p 247 = .ok T.«u64_bswap64»
  t249 : Interp.termOf p 249 = .ok T.«intcc_comparable»
  r249 : p.rulesOf 249 = [rule_icmp_209]
  t250 : Interp.termOf p 250 = .ok T.«decompose_intcc»
  r250 : p.rulesOf 250 = [rule_icmp_214, rule_icmp_215, rule_icmp_216, rule_icmp_217, rule_icmp_218, rule_icmp_219, rule_icmp_220, rule_icmp_221, rule_icmp_222, rule_icmp_223]
  t251 : Interp.termOf p 251 = .ok T.«compose_icmp»
  r251 : p.rulesOf 251 = [rule_icmp_226, rule_icmp_227, rule_icmp_228, rule_icmp_229, rule_icmp_230, rule_icmp_231, rule_icmp_232, rule_icmp_233, rule_icmp_234, rule_icmp_235, rule_icmp_236, rule_icmp_237]
  t252 : Interp.termOf p 252 = .ok T.«intcc_class»
  r252 : p.rulesOf 252 = [rule_icmp_240, rule_icmp_241, rule_icmp_242, rule_icmp_243, rule_icmp_244, rule_icmp_245, rule_icmp_246, rule_icmp_247, rule_icmp_248, rule_icmp_249]
  t253 : Interp.termOf p 253 = .ok T.«shift_amt_to_type»
  r253 : p.rulesOf 253 = [rule_shifts_94, rule_shifts_95, rule_shifts_96]
  t254 : Interp.termOf p 254 = .ok T.«iadd_uextend»
  r254 : p.rulesOf 254 = [rule_shifts_215, rule_shifts_212, rule_shifts_210]
  t255 : Interp.termOf p 255 = .ok T.«isub_uextend»
  r255 : p.rulesOf 255 = [rule_shifts_227, rule_shifts_224, rule_shifts_222]
  t506 : Interp.termOf p 506 = .ok T.«i32_lt»
  t508 : Interp.termOf p 508 = .ok T.«i32_gt»
  t567 : Interp.termOf p 567 = .ok T.«u32_lt»
  t576 : Interp.termOf p 576 = .ok T.«u32_sub»
  t603 : Interp.termOf p 603 = .ok T.«u32_matches_non_zero»
  t623 : Interp.termOf p 623 = .ok T.«u32_is_power_of_two»
  t628 : Interp.termOf p 628 = .ok T.«i64_eq»
  t629 : Interp.termOf p 629 = .ok T.«i64_ne»
  t630 : Interp.termOf p 630 = .ok T.«i64_lt»
  t632 : Interp.termOf p 632 = .ok T.«i64_gt»
  t633 : Interp.termOf p 633 = .ok T.«i64_gt_eq»
  t654 : Interp.termOf p 654 = .ok T.«i64_shl»
  t666 : Interp.termOf p 666 = .ok T.«i64_matches_non_zero»
  t682 : Interp.termOf p 682 = .ok T.«i64_trailing_zeros»
  t687 : Interp.termOf p 687 = .ok T.«i64_wrapping_neg»
  t689 : Interp.termOf p 689 = .ok T.«u64_eq»
  t691 : Interp.termOf p 691 = .ok T.«u64_lt»
  t692 : Interp.termOf p 692 = .ok T.«u64_lt_eq»
  t693 : Interp.termOf p 693 = .ok T.«u64_gt»
  t696 : Interp.termOf p 696 = .ok T.«u64_wrapping_add»
  t699 : Interp.termOf p 699 = .ok T.«u64_wrapping_sub»
  t700 : Interp.termOf p 700 = .ok T.«u64_sub»
  t706 : Interp.termOf p 706 = .ok T.«u64_div»
  t707 : Interp.termOf p 707 = .ok T.«u64_checked_rem»
  t708 : Interp.termOf p 708 = .ok T.«u64_rem»
  t709 : Interp.termOf p 709 = .ok T.«u64_and»
  t710 : Interp.termOf p 710 = .ok T.«u64_or»
  t712 : Interp.termOf p 712 = .ok T.«u64_not»
  t715 : Interp.termOf p 715 = .ok T.«u64_shl»
  t727 : Interp.termOf p 727 = .ok T.«u64_matches_non_zero»
  t742 : Interp.termOf p 742 = .ok T.«u64_ilog2»
  t743 : Interp.termOf p 743 = .ok T.«u64_trailing_zeros»
  t747 : Interp.termOf p 747 = .ok T.«u64_is_power_of_two»
  t748 : Interp.termOf p 748 = .ok T.«u64_matches_power_of_two»
  t910 : Interp.termOf p 910 = .ok T.«u8_into_u32»
  t914 : Interp.termOf p 914 = .ok T.«u8_into_u64»
  t987 : Interp.termOf p 987 = .ok T.«i32_into_i64»
  t1015 : Interp.termOf p 1015 = .ok T.«u32_into_i64»
  t1017 : Interp.termOf p 1017 = .ok T.«u32_into_u64»
  t1040 : Interp.termOf p 1040 = .ok T.«i32_from_i64»
  t1046 : Interp.termOf p 1046 = .ok T.«i64_cast_unsigned»
  t1073 : Interp.termOf p 1073 = .ok T.«u32_from_u64»
  t1146 : Interp.termOf p 1146 = .ok T.«value_array_2»
  t1147 : Interp.termOf p 1147 = .ok T.«value_array_3»
  t1148 : Interp.termOf p 1148 = .ok T.«block_array_2»
  t1149 : Interp.termOf p 1149 = .ok T.«jump»
  r1149 : p.rulesOf 1149 = [rule_clif_opt_342]
  t1154 : Interp.termOf p 1154 = .ok T.«trapz»
  r1154 : p.rulesOf 1154 = [rule_clif_opt_387]
  t1155 : Interp.termOf p 1155 = .ok T.«trapnz»
  r1155 : p.rulesOf 1155 = [rule_clif_opt_396]
  t1157 : Interp.termOf p 1157 = .ok T.«splat»
  r1157 : p.rulesOf 1157 = [rule_clif_opt_414]
  t1162 : Interp.termOf p 1162 = .ok T.«smin»
  r1162 : p.rulesOf 1162 = [rule_clif_opt_459]
  t1163 : Interp.termOf p 1163 = .ok T.«umin»
  r1163 : p.rulesOf 1163 = [rule_clif_opt_468]
  t1164 : Interp.termOf p 1164 = .ok T.«smax»
  r1164 : p.rulesOf 1164 = [rule_clif_opt_477]
  t1165 : Interp.termOf p 1165 = .ok T.«umax»
  r1165 : p.rulesOf 1165 = [rule_clif_opt_486]
  t1199 : Interp.termOf p 1199 = .ok T.«iconst»
  r1199 : p.rulesOf 1199 = [rule_clif_opt_792]
  t1200 : Interp.termOf p 1200 = .ok T.«f16const»
  r1200 : p.rulesOf 1200 = [rule_clif_opt_801]
  t1201 : Interp.termOf p 1201 = .ok T.«f32const»
  r1201 : p.rulesOf 1201 = [rule_clif_opt_810]
  t1202 : Interp.termOf p 1202 = .ok T.«f64const»
  r1202 : p.rulesOf 1202 = [rule_clif_opt_819]
  t1203 : Interp.termOf p 1203 = .ok T.«f128const»
  r1203 : p.rulesOf 1203 = [rule_clif_opt_828]
  t1204 : Interp.termOf p 1204 = .ok T.«vconst»
  r1204 : p.rulesOf 1204 = [rule_clif_opt_837]
  t1207 : Interp.termOf p 1207 = .ok T.«select»
  r1207 : p.rulesOf 1207 = [rule_clif_opt_864]
  t1214 : Interp.termOf p 1214 = .ok T.«icmp»
  r1214 : p.rulesOf 1214 = [rule_clif_opt_927]
  t1215 : Interp.termOf p 1215 = .ok T.«iadd»
  r1215 : p.rulesOf 1215 = [rule_clif_opt_936]
  t1216 : Interp.termOf p 1216 = .ok T.«isub»
  r1216 : p.rulesOf 1216 = [rule_clif_opt_945]
  t1217 : Interp.termOf p 1217 = .ok T.«ineg»
  r1217 : p.rulesOf 1217 = [rule_clif_opt_954]
  t1218 : Interp.termOf p 1218 = .ok T.«iabs»
  r1218 : p.rulesOf 1218 = [rule_clif_opt_963]
  t1219 : Interp.termOf p 1219 = .ok T.«imul»
  r1219 : p.rulesOf 1219 = [rule_clif_opt_972]
  t1220 : Interp.termOf p 1220 = .ok T.«umulhi»
  r1220 : p.rulesOf 1220 = [rule_clif_opt_981]
  t1221 : Interp.termOf p 1221 = .ok T.«smulhi»
  r1221 : p.rulesOf 1221 = [rule_clif_opt_990]
  t1239 : Interp.termOf p 1239 = .ok T.«band»
  r1239 : p.rulesOf 1239 = [rule_clif_opt_1152]
  t1240 : Interp.termOf p 1240 = .ok T.«bor»
  r1240 : p.rulesOf 1240 = [rule_clif_opt_1161]
  t1241 : Interp.termOf p 1241 = .ok T.«bxor»
  r1241 : p.rulesOf 1241 = [rule_clif_opt_1170]
  t1242 : Interp.termOf p 1242 = .ok T.«bnot»
  r1242 : p.rulesOf 1242 = [rule_clif_opt_1179]
  t1243 : Interp.termOf p 1243 = .ok T.«rotl»
  r1243 : p.rulesOf 1243 = [rule_clif_opt_1188]
  t1244 : Interp.termOf p 1244 = .ok T.«rotr»
  r1244 : p.rulesOf 1244 = [rule_clif_opt_1197]
  t1245 : Interp.termOf p 1245 = .ok T.«ishl»
  r1245 : p.rulesOf 1245 = [rule_clif_opt_1206]
  t1246 : Interp.termOf p 1246 = .ok T.«ushr»
  r1246 : p.rulesOf 1246 = [rule_clif_opt_1215]
  t1247 : Interp.termOf p 1247 = .ok T.«sshr»
  r1247 : p.rulesOf 1247 = [rule_clif_opt_1224]
  t1252 : Interp.termOf p 1252 = .ok T.«bswap»
  r1252 : p.rulesOf 1252 = [rule_clif_opt_1269]
  t1253 : Interp.termOf p 1253 = .ok T.«popcnt»
  r1253 : p.rulesOf 1253 = [rule_clif_opt_1278]
  t1272 : Interp.termOf p 1272 = .ok T.«bmask»
  r1272 : p.rulesOf 1272 = [rule_clif_opt_1449]
  t1273 : Interp.termOf p 1273 = .ok T.«ireduce»
  r1273 : p.rulesOf 1273 = [rule_clif_opt_1458]
  t1283 : Interp.termOf p 1283 = .ok T.«uextend»
  r1283 : p.rulesOf 1283 = [rule_clif_opt_1548]
  t1284 : Interp.termOf p 1284 = .ok T.«sextend»
  r1284 : p.rulesOf 1284 = [rule_clif_opt_1557]
  t1297 : Interp.termOf p 1297 = .ok T.«iconcat»
  r1297 : p.rulesOf 1297 = [rule_clif_opt_1674]
  t1305 : Interp.termOf p 1305 = .ok T.«SkeletonInstSimplification.Remove»
  t1306 : Interp.termOf p 1306 = .ok T.«SkeletonInstSimplification.RemoveWithVal»
  t1307 : Interp.termOf p 1307 = .ok T.«SkeletonInstSimplification.Replace»
  t1309 : Interp.termOf p 1309 = .ok T.«SkeletonInstSimplification.ReplaceBranchCond»
  t1310 : Interp.termOf p 1310 = .ok T.«SkeletonInstSimplification.ReplaceWithTwo»
  t1312 : Interp.termOf p 1312 = .ok T.«DivConstMagicU32.U32»
  t1313 : Interp.termOf p 1313 = .ok T.«DivConstMagicU64.U64»
  t1314 : Interp.termOf p 1314 = .ok T.«DivConstMagicS32.S32»
  t1315 : Interp.termOf p 1315 = .ok T.«DivConstMagicS64.S64»
  t1341 : Interp.termOf p 1341 = .ok T.«IntCC.Equal»
  t1342 : Interp.termOf p 1342 = .ok T.«IntCC.NotEqual»
  t1343 : Interp.termOf p 1343 = .ok T.«IntCC.SignedGreaterThan»
  t1344 : Interp.termOf p 1344 = .ok T.«IntCC.SignedGreaterThanOrEqual»
  t1345 : Interp.termOf p 1345 = .ok T.«IntCC.SignedLessThan»
  t1346 : Interp.termOf p 1346 = .ok T.«IntCC.SignedLessThanOrEqual»
  t1347 : Interp.termOf p 1347 = .ok T.«IntCC.UnsignedGreaterThan»
  t1348 : Interp.termOf p 1348 = .ok T.«IntCC.UnsignedGreaterThanOrEqual»
  t1349 : Interp.termOf p 1349 = .ok T.«IntCC.UnsignedLessThan»
  t1350 : Interp.termOf p 1350 = .ok T.«IntCC.UnsignedLessThanOrEqual»
  t1356 : Interp.termOf p 1356 = .ok T.«Opcode.Jump»
  t1357 : Interp.termOf p 1357 = .ok T.«Opcode.Brif»
  t1358 : Interp.termOf p 1358 = .ok T.«Opcode.BrTable»
  t1361 : Interp.termOf p 1361 = .ok T.«Opcode.Trapz»
  t1362 : Interp.termOf p 1362 = .ok T.«Opcode.Trapnz»
  t1371 : Interp.termOf p 1371 = .ok T.«Opcode.Splat»
  t1376 : Interp.termOf p 1376 = .ok T.«Opcode.Smin»
  t1377 : Interp.termOf p 1377 = .ok T.«Opcode.Umin»
  t1378 : Interp.termOf p 1378 = .ok T.«Opcode.Smax»
  t1379 : Interp.termOf p 1379 = .ok T.«Opcode.Umax»
  t1413 : Interp.termOf p 1413 = .ok T.«Opcode.Iconst»
  t1414 : Interp.termOf p 1414 = .ok T.«Opcode.F16const»
  t1415 : Interp.termOf p 1415 = .ok T.«Opcode.F32const»
  t1416 : Interp.termOf p 1416 = .ok T.«Opcode.F64const»
  t1417 : Interp.termOf p 1417 = .ok T.«Opcode.F128const»
  t1418 : Interp.termOf p 1418 = .ok T.«Opcode.Vconst»
  t1421 : Interp.termOf p 1421 = .ok T.«Opcode.Select»
  t1428 : Interp.termOf p 1428 = .ok T.«Opcode.Icmp»
  t1429 : Interp.termOf p 1429 = .ok T.«Opcode.Iadd»
  t1430 : Interp.termOf p 1430 = .ok T.«Opcode.Isub»
  t1431 : Interp.termOf p 1431 = .ok T.«Opcode.Ineg»
  t1432 : Interp.termOf p 1432 = .ok T.«Opcode.Iabs»
  t1433 : Interp.termOf p 1433 = .ok T.«Opcode.Imul»
  t1434 : Interp.termOf p 1434 = .ok T.«Opcode.Umulhi»
  t1435 : Interp.termOf p 1435 = .ok T.«Opcode.Smulhi»
  t1438 : Interp.termOf p 1438 = .ok T.«Opcode.Udiv»
  t1439 : Interp.termOf p 1439 = .ok T.«Opcode.Sdiv»
  t1440 : Interp.termOf p 1440 = .ok T.«Opcode.Urem»
  t1441 : Interp.termOf p 1441 = .ok T.«Opcode.Srem»
  t1453 : Interp.termOf p 1453 = .ok T.«Opcode.Band»
  t1454 : Interp.termOf p 1454 = .ok T.«Opcode.Bor»
  t1455 : Interp.termOf p 1455 = .ok T.«Opcode.Bxor»
  t1456 : Interp.termOf p 1456 = .ok T.«Opcode.Bnot»
  t1457 : Interp.termOf p 1457 = .ok T.«Opcode.Rotl»
  t1458 : Interp.termOf p 1458 = .ok T.«Opcode.Rotr»
  t1459 : Interp.termOf p 1459 = .ok T.«Opcode.Ishl»
  t1460 : Interp.termOf p 1460 = .ok T.«Opcode.Ushr»
  t1461 : Interp.termOf p 1461 = .ok T.«Opcode.Sshr»
  t1462 : Interp.termOf p 1462 = .ok T.«Opcode.Bitrev»
  t1463 : Interp.termOf p 1463 = .ok T.«Opcode.Clz»
  t1465 : Interp.termOf p 1465 = .ok T.«Opcode.Ctz»
  t1466 : Interp.termOf p 1466 = .ok T.«Opcode.Bswap»
  t1467 : Interp.termOf p 1467 = .ok T.«Opcode.Popcnt»
  t1486 : Interp.termOf p 1486 = .ok T.«Opcode.Bmask»
  t1487 : Interp.termOf p 1487 = .ok T.«Opcode.Ireduce»
  t1497 : Interp.termOf p 1497 = .ok T.«Opcode.Uextend»
  t1498 : Interp.termOf p 1498 = .ok T.«Opcode.Sextend»
  t1511 : Interp.termOf p 1511 = .ok T.«Opcode.Iconcat»
  t1521 : Interp.termOf p 1521 = .ok T.«InstructionData.Binary»
  t1523 : Interp.termOf p 1523 = .ok T.«InstructionData.BranchTable»
  t1524 : Interp.termOf p 1524 = .ok T.«InstructionData.Brif»
  t1527 : Interp.termOf p 1527 = .ok T.«InstructionData.CondTrap»
  t1533 : Interp.termOf p 1533 = .ok T.«InstructionData.IntCompare»
  t1534 : Interp.termOf p 1534 = .ok T.«InstructionData.Jump»
  t1543 : Interp.termOf p 1543 = .ok T.«InstructionData.Ternary»
  t1548 : Interp.termOf p 1548 = .ok T.«InstructionData.Unary»
  t1549 : Interp.termOf p 1549 = .ok T.«InstructionData.UnaryConst»
  t1551 : Interp.termOf p 1551 = .ok T.«InstructionData.UnaryIeee16»
  t1552 : Interp.termOf p 1552 = .ok T.«InstructionData.UnaryIeee32»
  t1553 : Interp.termOf p 1553 = .ok T.«InstructionData.UnaryIeee64»
  t1554 : Interp.termOf p 1554 = .ok T.«InstructionData.UnaryImm»

/-! ### The fields as conditional simp lemmas (`simp [opt_data]` discharges `Data p` from the
context) -/

@[opt_data] theorem Data.term_2 {p : Program} (hd : Data p) : Interp.termOf p 2 = .ok T.«value_type» := hd.t2
@[opt_data] theorem Data.term_7 {p : Program} (hd : Data p) : Interp.termOf p 7 = .ok T.«imm64_sdiv» := hd.t7
@[opt_data] theorem Data.term_8 {p : Program} (hd : Data p) : Interp.termOf p 8 = .ok T.«imm64_udiv» := hd.t8
@[opt_data] theorem Data.term_9 {p : Program} (hd : Data p) : Interp.termOf p 9 = .ok T.«imm64_srem» := hd.t9
@[opt_data] theorem Data.term_10 {p : Program} (hd : Data p) : Interp.termOf p 10 = .ok T.«imm64_urem» := hd.t10
@[opt_data] theorem Data.term_11 {p : Program} (hd : Data p) : Interp.termOf p 11 = .ok T.«imm64_add» := hd.t11
@[opt_data] theorem Data.term_12 {p : Program} (hd : Data p) : Interp.termOf p 12 = .ok T.«imm64_sub» := hd.t12
@[opt_data] theorem Data.term_13 {p : Program} (hd : Data p) : Interp.termOf p 13 = .ok T.«imm64_mul» := hd.t13
@[opt_data] theorem Data.term_14 {p : Program} (hd : Data p) : Interp.termOf p 14 = .ok T.«imm64_and» := hd.t14
@[opt_data] theorem Data.term_15 {p : Program} (hd : Data p) : Interp.termOf p 15 = .ok T.«imm64_or» := hd.t15
@[opt_data] theorem Data.term_16 {p : Program} (hd : Data p) : Interp.termOf p 16 = .ok T.«imm64_xor» := hd.t16
@[opt_data] theorem Data.term_17 {p : Program} (hd : Data p) : Interp.termOf p 17 = .ok T.«imm64_not» := hd.t17
@[opt_data] theorem Data.term_18 {p : Program} (hd : Data p) : Interp.termOf p 18 = .ok T.«imm64_neg» := hd.t18
@[opt_data] theorem Data.term_21 {p : Program} (hd : Data p) : Interp.termOf p 21 = .ok T.«imm64_umin» := hd.t21
@[opt_data] theorem Data.term_22 {p : Program} (hd : Data p) : Interp.termOf p 22 = .ok T.«imm64_umax» := hd.t22
@[opt_data] theorem Data.term_23 {p : Program} (hd : Data p) : Interp.termOf p 23 = .ok T.«imm64_smin» := hd.t23
@[opt_data] theorem Data.term_24 {p : Program} (hd : Data p) : Interp.termOf p 24 = .ok T.«imm64_smax» := hd.t24
@[opt_data] theorem Data.term_25 {p : Program} (hd : Data p) : Interp.termOf p 25 = .ok T.«imm64_shl» := hd.t25
@[opt_data] theorem Data.term_26 {p : Program} (hd : Data p) : Interp.termOf p 26 = .ok T.«imm64_ushr» := hd.t26
@[opt_data] theorem Data.term_27 {p : Program} (hd : Data p) : Interp.termOf p 27 = .ok T.«imm64_sshr» := hd.t27
@[opt_data] theorem Data.term_28 {p : Program} (hd : Data p) : Interp.termOf p 28 = .ok T.«imm64_rotl» := hd.t28
@[opt_data] theorem Data.term_29 {p : Program} (hd : Data p) : Interp.termOf p 29 = .ok T.«imm64_rotr» := hd.t29
@[opt_data] theorem Data.term_30 {p : Program} (hd : Data p) : Interp.termOf p 30 = .ok T.«i64_sextend_u64» := hd.t30
@[opt_data] theorem Data.term_33 {p : Program} (hd : Data p) : Interp.termOf p 33 = .ok T.«imm64_icmp» := hd.t33
@[opt_data] theorem Data.term_34 {p : Program} (hd : Data p) : Interp.termOf p 34 = .ok T.«imm64_clz» := hd.t34
@[opt_data] theorem Data.term_35 {p : Program} (hd : Data p) : Interp.termOf p 35 = .ok T.«imm64_ctz» := hd.t35
@[opt_data] theorem Data.term_84 {p : Program} (hd : Data p) : Interp.termOf p 84 = .ok T.«ty_umax» := hd.t84
@[opt_data] theorem Data.term_85 {p : Program} (hd : Data p) : Interp.termOf p 85 = .ok T.«ty_smin» := hd.t85
@[opt_data] theorem Data.term_86 {p : Program} (hd : Data p) : Interp.termOf p 86 = .ok T.«ty_smax» := hd.t86
@[opt_data] theorem Data.term_87 {p : Program} (hd : Data p) : Interp.termOf p 87 = .ok T.«ty_bits» := hd.t87
@[opt_data] theorem Data.term_89 {p : Program} (hd : Data p) : Interp.termOf p 89 = .ok T.«ty_bits_u64» := hd.t89
@[opt_data] theorem Data.term_90 {p : Program} (hd : Data p) : Interp.termOf p 90 = .ok T.«ty_mask» := hd.t90
@[opt_data] theorem Data.term_94 {p : Program} (hd : Data p) : Interp.termOf p 94 = .ok T.«lane_type» := hd.t94
@[opt_data] theorem Data.term_96 {p : Program} (hd : Data p) : Interp.termOf p 96 = .ok T.«ty_half_width» := hd.t96
@[opt_data] theorem Data.term_97 {p : Program} (hd : Data p) : Interp.termOf p 97 = .ok T.«ty_shift_mask» := hd.t97
@[opt_data] theorem Data.rules_97 {p : Program} (hd : Data p) : p.rulesOf 97 = [rule_prelude_343] := hd.r97
@[opt_data] theorem Data.term_98 {p : Program} (hd : Data p) : Interp.termOf p 98 = .ok T.«ty_equal» := hd.t98
@[opt_data] theorem Data.term_104 {p : Program} (hd : Data p) : Interp.termOf p 104 = .ok T.«intcc_swap_args» := hd.t104
@[opt_data] theorem Data.term_105 {p : Program} (hd : Data p) : Interp.termOf p 105 = .ok T.«intcc_complement» := hd.t105
@[opt_data] theorem Data.term_113 {p : Program} (hd : Data p) : Interp.termOf p 113 = .ok T.«fits_in_64» := hd.t113
@[opt_data] theorem Data.term_119 {p : Program} (hd : Data p) : Interp.termOf p 119 = .ok T.«ty_int_ref_scalar_64_extract» := hd.t119
@[opt_data] theorem Data.term_126 {p : Program} (hd : Data p) : Interp.termOf p 126 = .ok T.«ty_int» := hd.t126
@[opt_data] theorem Data.term_133 {p : Program} (hd : Data p) : Interp.termOf p 133 = .ok T.«ty_vec128» := hd.t133
@[opt_data] theorem Data.term_144 {p : Program} (hd : Data p) : Interp.termOf p 144 = .ok T.«u64_from_imm64» := hd.t144
@[opt_data] theorem Data.term_146 {p : Program} (hd : Data p) : Interp.termOf p 146 = .ok T.«imm64_power_of_two» := hd.t146
@[opt_data] theorem Data.term_147 {p : Program} (hd : Data p) : Interp.termOf p 147 = .ok T.«imm64» := hd.t147
@[opt_data] theorem Data.term_148 {p : Program} (hd : Data p) : Interp.termOf p 148 = .ok T.«imm64_masked» := hd.t148
@[opt_data] theorem Data.term_159 {p : Program} (hd : Data p) : Interp.termOf p 159 = .ok T.«signed_cond_code» := hd.t159
@[opt_data] theorem Data.term_164 {p : Program} (hd : Data p) : Interp.termOf p 164 = .ok T.«zero_constant» := hd.t164
@[opt_data] theorem Data.term_165 {p : Program} (hd : Data p) : Interp.termOf p 165 = .ok T.«inst_data_value» := hd.t165
@[opt_data] theorem Data.term_166 {p : Program} (hd : Data p) : Interp.termOf p 166 = .ok T.«inst_data» := hd.t166
@[opt_data] theorem Data.term_167 {p : Program} (hd : Data p) : Interp.termOf p 167 = .ok T.«inst_data_value_tupled» := hd.t167
@[opt_data] theorem Data.term_168 {p : Program} (hd : Data p) : Interp.termOf p 168 = .ok T.«make_inst» := hd.t168
@[opt_data] theorem Data.term_169 {p : Program} (hd : Data p) : Interp.termOf p 169 = .ok T.«make_skeleton_inst» := hd.t169
@[opt_data] theorem Data.term_170 {p : Program} (hd : Data p) : Interp.termOf p 170 = .ok T.«value_array_2_ctor» := hd.t170
@[opt_data] theorem Data.term_171 {p : Program} (hd : Data p) : Interp.termOf p 171 = .ok T.«value_array_3_ctor» := hd.t171
@[opt_data] theorem Data.term_172 {p : Program} (hd : Data p) : Interp.termOf p 172 = .ok T.«resolve_jump_table_entry» := hd.t172
@[opt_data] theorem Data.term_173 {p : Program} (hd : Data p) : Interp.termOf p 173 = .ok T.«block_call_block» := hd.t173
@[opt_data] theorem Data.term_174 {p : Program} (hd : Data p) : Interp.termOf p 174 = .ok T.«just_trap_block» := hd.t174
@[opt_data] theorem Data.term_175 {p : Program} (hd : Data p) : Interp.termOf p 175 = .ok T.«spaceship_s» := hd.t175
@[opt_data] theorem Data.rules_175 {p : Program} (hd : Data p) : p.rulesOf 175 = [rule_prelude_opt_74] := hd.r175
@[opt_data] theorem Data.term_176 {p : Program} (hd : Data p) : Interp.termOf p 176 = .ok T.«spaceship_u» := hd.t176
@[opt_data] theorem Data.rules_176 {p : Program} (hd : Data p) : p.rulesOf 176 = [rule_prelude_opt_77] := hd.r176
@[opt_data] theorem Data.term_178 {p : Program} (hd : Data p) : Interp.termOf p 178 = .ok T.«inst_to_skeleton_inst_simplification» := hd.t178
@[opt_data] theorem Data.rules_178 {p : Program} (hd : Data p) : p.rulesOf 178 = [rule_prelude_opt_136] := hd.r178
@[opt_data] theorem Data.term_179 {p : Program} (hd : Data p) : Interp.termOf p 179 = .ok T.«value_to_skeleton_inst_simplification» := hd.t179
@[opt_data] theorem Data.rules_179 {p : Program} (hd : Data p) : p.rulesOf 179 = [rule_prelude_opt_140] := hd.r179
@[opt_data] theorem Data.term_180 {p : Program} (hd : Data p) : Interp.termOf p 180 = .ok T.«remove_inst» := hd.t180
@[opt_data] theorem Data.rules_180 {p : Program} (hd : Data p) : p.rulesOf 180 = [rule_prelude_opt_144] := hd.r180
@[opt_data] theorem Data.term_182 {p : Program} (hd : Data p) : Interp.termOf p 182 = .ok T.«replace_branch_cond» := hd.t182
@[opt_data] theorem Data.rules_182 {p : Program} (hd : Data p) : p.rulesOf 182 = [rule_prelude_opt_150] := hd.r182
@[opt_data] theorem Data.term_183 {p : Program} (hd : Data p) : Interp.termOf p 183 = .ok T.«replace_with_two» := hd.t183
@[opt_data] theorem Data.rules_183 {p : Program} (hd : Data p) : p.rulesOf 183 = [rule_prelude_opt_154] := hd.r183
@[opt_data] theorem Data.term_185 {p : Program} (hd : Data p) : Interp.termOf p 185 = .ok T.«remat» := hd.t185
@[opt_data] theorem Data.term_186 {p : Program} (hd : Data p) : Interp.termOf p 186 = .ok T.«subsume» := hd.t186
@[opt_data] theorem Data.term_187 {p : Program} (hd : Data p) : Interp.termOf p 187 = .ok T.«iconst_sextend_etor» := hd.t187
@[opt_data] theorem Data.term_188 {p : Program} (hd : Data p) : Interp.termOf p 188 = .ok T.«iconst_s» := hd.t188
@[opt_data] theorem Data.rules_188 {p : Program} (hd : Data p) : p.rulesOf 188 = [rule_prelude_opt_208, rule_prelude_opt_207, rule_prelude_opt_201] := hd.r188
@[opt_data] theorem Data.term_189 {p : Program} (hd : Data p) : Interp.termOf p 189 = .ok T.«iconst_u» := hd.t189
@[opt_data] theorem Data.rules_189 {p : Program} (hd : Data p) : p.rulesOf 189 = [rule_prelude_opt_225, rule_prelude_opt_224, rule_prelude_opt_221] := hd.r189
@[opt_data] theorem Data.term_191 {p : Program} (hd : Data p) : Interp.termOf p 191 = .ok T.«uextend_maybe_etor» := hd.t191
@[opt_data] theorem Data.term_192 {p : Program} (hd : Data p) : Interp.termOf p 192 = .ok T.«uextend_maybe» := hd.t192
@[opt_data] theorem Data.rules_192 {p : Program} (hd : Data p) : p.rulesOf 192 = [rule_prelude_opt_246, rule_prelude_opt_245] := hd.r192
@[opt_data] theorem Data.term_193 {p : Program} (hd : Data p) : Interp.termOf p 193 = .ok T.«sextend_maybe» := hd.t193
@[opt_data] theorem Data.rules_193 {p : Program} (hd : Data p) : p.rulesOf 193 = [rule_prelude_opt_252, rule_prelude_opt_251] := hd.r193
@[opt_data] theorem Data.term_194 {p : Program} (hd : Data p) : Interp.termOf p 194 = .ok T.«eq» := hd.t194
@[opt_data] theorem Data.rules_194 {p : Program} (hd : Data p) : p.rulesOf 194 = [rule_prelude_opt_61] := hd.r194
@[opt_data] theorem Data.term_195 {p : Program} (hd : Data p) : Interp.termOf p 195 = .ok T.«ne» := hd.t195
@[opt_data] theorem Data.rules_195 {p : Program} (hd : Data p) : p.rulesOf 195 = [rule_prelude_opt_62] := hd.r195
@[opt_data] theorem Data.term_196 {p : Program} (hd : Data p) : Interp.termOf p 196 = .ok T.«ult» := hd.t196
@[opt_data] theorem Data.rules_196 {p : Program} (hd : Data p) : p.rulesOf 196 = [rule_prelude_opt_63] := hd.r196
@[opt_data] theorem Data.term_197 {p : Program} (hd : Data p) : Interp.termOf p 197 = .ok T.«ule» := hd.t197
@[opt_data] theorem Data.rules_197 {p : Program} (hd : Data p) : p.rulesOf 197 = [rule_prelude_opt_64] := hd.r197
@[opt_data] theorem Data.term_198 {p : Program} (hd : Data p) : Interp.termOf p 198 = .ok T.«ugt» := hd.t198
@[opt_data] theorem Data.rules_198 {p : Program} (hd : Data p) : p.rulesOf 198 = [rule_prelude_opt_65] := hd.r198
@[opt_data] theorem Data.term_199 {p : Program} (hd : Data p) : Interp.termOf p 199 = .ok T.«uge» := hd.t199
@[opt_data] theorem Data.rules_199 {p : Program} (hd : Data p) : p.rulesOf 199 = [rule_prelude_opt_66] := hd.r199
@[opt_data] theorem Data.term_200 {p : Program} (hd : Data p) : Interp.termOf p 200 = .ok T.«slt» := hd.t200
@[opt_data] theorem Data.rules_200 {p : Program} (hd : Data p) : p.rulesOf 200 = [rule_prelude_opt_67] := hd.r200
@[opt_data] theorem Data.term_201 {p : Program} (hd : Data p) : Interp.termOf p 201 = .ok T.«sle» := hd.t201
@[opt_data] theorem Data.rules_201 {p : Program} (hd : Data p) : p.rulesOf 201 = [rule_prelude_opt_68] := hd.r201
@[opt_data] theorem Data.term_202 {p : Program} (hd : Data p) : Interp.termOf p 202 = .ok T.«sgt» := hd.t202
@[opt_data] theorem Data.rules_202 {p : Program} (hd : Data p) : p.rulesOf 202 = [rule_prelude_opt_69] := hd.r202
@[opt_data] theorem Data.term_203 {p : Program} (hd : Data p) : Interp.termOf p 203 = .ok T.«sge» := hd.t203
@[opt_data] theorem Data.rules_203 {p : Program} (hd : Data p) : p.rulesOf 203 = [rule_prelude_opt_70] := hd.r203
@[opt_data] theorem Data.term_204 {p : Program} (hd : Data p) : Interp.termOf p 204 = .ok T.«i64_is_negative_power_of_two» := hd.t204
@[opt_data] theorem Data.rules_204 {p : Program} (hd : Data p) : p.rulesOf 204 = [rule_prelude_opt_289] := hd.r204
@[opt_data] theorem Data.term_205 {p : Program} (hd : Data p) : Interp.termOf p 205 = .ok T.«i64_is_any_sign_power_of_two» := hd.t205
@[opt_data] theorem Data.rules_205 {p : Program} (hd : Data p) : p.rulesOf 205 = [rule_prelude_opt_293, rule_prelude_opt_296, rule_prelude_opt_299] := hd.r205
@[opt_data] theorem Data.term_206 {p : Program} (hd : Data p) : Interp.termOf p 206 = .ok T.«div_const_magic_u32» := hd.t206
@[opt_data] theorem Data.term_207 {p : Program} (hd : Data p) : Interp.termOf p 207 = .ok T.«div_const_magic_u64» := hd.t207
@[opt_data] theorem Data.term_208 {p : Program} (hd : Data p) : Interp.termOf p 208 = .ok T.«div_const_magic_s32» := hd.t208
@[opt_data] theorem Data.term_209 {p : Program} (hd : Data p) : Interp.termOf p 209 = .ok T.«div_const_magic_s64» := hd.t209
@[opt_data] theorem Data.term_210 {p : Program} (hd : Data p) : Interp.termOf p 210 = .ok T.«apply_div_const_magic_u32» := hd.t210
@[opt_data] theorem Data.rules_210 {p : Program} (hd : Data p) : p.rulesOf 210 = [rule_prelude_opt_328] := hd.r210
@[opt_data] theorem Data.term_211 {p : Program} (hd : Data p) : Interp.termOf p 211 = .ok T.«apply_div_const_magic_u32_inner» := hd.t211
@[opt_data] theorem Data.rules_211 {p : Program} (hd : Data p) : p.rulesOf 211 = [rule_prelude_opt_333] := hd.r211
@[opt_data] theorem Data.term_212 {p : Program} (hd : Data p) : Interp.termOf p 212 = .ok T.«apply_div_const_magic_u32_maybe_add» := hd.t212
@[opt_data] theorem Data.rules_212 {p : Program} (hd : Data p) : p.rulesOf 212 = [rule_prelude_opt_349, rule_prelude_opt_358] := hd.r212
@[opt_data] theorem Data.term_213 {p : Program} (hd : Data p) : Interp.termOf p 213 = .ok T.«apply_div_const_magic_u32_maybe_shift» := hd.t213
@[opt_data] theorem Data.rules_213 {p : Program} (hd : Data p) : p.rulesOf 213 = [rule_prelude_opt_372, rule_prelude_opt_378] := hd.r213
@[opt_data] theorem Data.term_214 {p : Program} (hd : Data p) : Interp.termOf p 214 = .ok T.«apply_div_const_magic_u32_finish» := hd.t214
@[opt_data] theorem Data.rules_214 {p : Program} (hd : Data p) : p.rulesOf 214 = [rule_prelude_opt_398, rule_prelude_opt_399] := hd.r214
@[opt_data] theorem Data.term_215 {p : Program} (hd : Data p) : Interp.termOf p 215 = .ok T.«apply_div_const_magic_u64» := hd.t215
@[opt_data] theorem Data.rules_215 {p : Program} (hd : Data p) : p.rulesOf 215 = [rule_prelude_opt_405] := hd.r215
@[opt_data] theorem Data.term_216 {p : Program} (hd : Data p) : Interp.termOf p 216 = .ok T.«apply_div_const_magic_u64_inner» := hd.t216
@[opt_data] theorem Data.rules_216 {p : Program} (hd : Data p) : p.rulesOf 216 = [rule_prelude_opt_410] := hd.r216
@[opt_data] theorem Data.term_217 {p : Program} (hd : Data p) : Interp.termOf p 217 = .ok T.«apply_div_const_magic_u64_maybe_add» := hd.t217
@[opt_data] theorem Data.rules_217 {p : Program} (hd : Data p) : p.rulesOf 217 = [rule_prelude_opt_426, rule_prelude_opt_435] := hd.r217
@[opt_data] theorem Data.term_218 {p : Program} (hd : Data p) : Interp.termOf p 218 = .ok T.«apply_div_const_magic_u64_maybe_shift» := hd.t218
@[opt_data] theorem Data.rules_218 {p : Program} (hd : Data p) : p.rulesOf 218 = [rule_prelude_opt_449, rule_prelude_opt_455] := hd.r218
@[opt_data] theorem Data.term_219 {p : Program} (hd : Data p) : Interp.termOf p 219 = .ok T.«apply_div_const_magic_u64_finish» := hd.t219
@[opt_data] theorem Data.rules_219 {p : Program} (hd : Data p) : p.rulesOf 219 = [rule_prelude_opt_475, rule_prelude_opt_476] := hd.r219
@[opt_data] theorem Data.term_220 {p : Program} (hd : Data p) : Interp.termOf p 220 = .ok T.«apply_div_const_magic_s32» := hd.t220
@[opt_data] theorem Data.rules_220 {p : Program} (hd : Data p) : p.rulesOf 220 = [rule_prelude_opt_483] := hd.r220
@[opt_data] theorem Data.term_221 {p : Program} (hd : Data p) : Interp.termOf p 221 = .ok T.«apply_div_const_magic_s32_inner» := hd.t221
@[opt_data] theorem Data.rules_221 {p : Program} (hd : Data p) : p.rulesOf 221 = [rule_prelude_opt_489] := hd.r221
@[opt_data] theorem Data.term_222 {p : Program} (hd : Data p) : Interp.termOf p 222 = .ok T.«apply_div_const_magic_s32_add_sub» := hd.t222
@[opt_data] theorem Data.rules_222 {p : Program} (hd : Data p) : p.rulesOf 222 = [rule_prelude_opt_505, rule_prelude_opt_514, rule_prelude_opt_523] := hd.r222
@[opt_data] theorem Data.term_223 {p : Program} (hd : Data p) : Interp.termOf p 223 = .ok T.«apply_div_const_magic_s32_shift» := hd.t223
@[opt_data] theorem Data.rules_223 {p : Program} (hd : Data p) : p.rulesOf 223 = [rule_prelude_opt_534] := hd.r223
@[opt_data] theorem Data.term_224 {p : Program} (hd : Data p) : Interp.termOf p 224 = .ok T.«apply_div_const_magic_s32_finish» := hd.t224
@[opt_data] theorem Data.rules_224 {p : Program} (hd : Data p) : p.rulesOf 224 = [rule_prelude_opt_555, rule_prelude_opt_558] := hd.r224
@[opt_data] theorem Data.term_225 {p : Program} (hd : Data p) : Interp.termOf p 225 = .ok T.«apply_div_const_magic_s64» := hd.t225
@[opt_data] theorem Data.rules_225 {p : Program} (hd : Data p) : p.rulesOf 225 = [rule_prelude_opt_564] := hd.r225
@[opt_data] theorem Data.term_226 {p : Program} (hd : Data p) : Interp.termOf p 226 = .ok T.«apply_div_const_magic_s64_inner» := hd.t226
@[opt_data] theorem Data.rules_226 {p : Program} (hd : Data p) : p.rulesOf 226 = [rule_prelude_opt_570] := hd.r226
@[opt_data] theorem Data.term_227 {p : Program} (hd : Data p) : Interp.termOf p 227 = .ok T.«apply_div_const_magic_s64_add_sub» := hd.t227
@[opt_data] theorem Data.rules_227 {p : Program} (hd : Data p) : p.rulesOf 227 = [rule_prelude_opt_586, rule_prelude_opt_595, rule_prelude_opt_604] := hd.r227
@[opt_data] theorem Data.term_228 {p : Program} (hd : Data p) : Interp.termOf p 228 = .ok T.«apply_div_const_magic_s64_shift» := hd.t228
@[opt_data] theorem Data.rules_228 {p : Program} (hd : Data p) : p.rulesOf 228 = [rule_prelude_opt_615] := hd.r228
@[opt_data] theorem Data.term_229 {p : Program} (hd : Data p) : Interp.termOf p 229 = .ok T.«apply_div_const_magic_s64_finish» := hd.t229
@[opt_data] theorem Data.rules_229 {p : Program} (hd : Data p) : p.rulesOf 229 = [rule_prelude_opt_636, rule_prelude_opt_639] := hd.r229
@[opt_data] theorem Data.term_230 {p : Program} (hd : Data p) : Interp.termOf p 230 = .ok T.«cmp_true» := hd.t230
@[opt_data] theorem Data.rules_230 {p : Program} (hd : Data p) : p.rulesOf 230 = [rule_arithmetic_401, rule_arithmetic_400] := hd.r230
@[opt_data] theorem Data.term_231 {p : Program} (hd : Data p) : Interp.termOf p 231 = .ok T.«all_zero_etor» := hd.t231
@[opt_data] theorem Data.term_232 {p : Program} (hd : Data p) : Interp.termOf p 232 = .ok T.«f16_zero» := hd.t232
@[opt_data] theorem Data.term_233 {p : Program} (hd : Data p) : Interp.termOf p 233 = .ok T.«ty_vector» := hd.t233
@[opt_data] theorem Data.term_234 {p : Program} (hd : Data p) : Interp.termOf p 234 = .ok T.«all_zero» := hd.t234
@[opt_data] theorem Data.rules_234 {p : Program} (hd : Data p) : p.rulesOf 234 = [rule_bitops_18, rule_bitops_17, rule_bitops_16, rule_bitops_15, rule_bitops_14, rule_bitops_13] := hd.r234
@[opt_data] theorem Data.term_235 {p : Program} (hd : Data p) : Interp.termOf p 235 = .ok T.«truthy» := hd.t235
@[opt_data] theorem Data.rules_235 {p : Program} (hd : Data p) : p.rulesOf 235 = [rule_bitops_111, rule_bitops_112, rule_bitops_113, rule_bitops_114, rule_bitops_115, rule_bitops_116, rule_bitops_117, rule_bitops_118, rule_bitops_119, rule_bitops_120, rule_bitops_122] := hd.r235
@[opt_data] theorem Data.term_241 {p : Program} (hd : Data p) : Interp.termOf p 241 = .ok T.«f32_from_uint» := hd.t241
@[opt_data] theorem Data.term_242 {p : Program} (hd : Data p) : Interp.termOf p 242 = .ok T.«f64_from_uint» := hd.t242
@[opt_data] theorem Data.term_245 {p : Program} (hd : Data p) : Interp.termOf p 245 = .ok T.«u64_bswap16» := hd.t245
@[opt_data] theorem Data.term_246 {p : Program} (hd : Data p) : Interp.termOf p 246 = .ok T.«u64_bswap32» := hd.t246
@[opt_data] theorem Data.term_247 {p : Program} (hd : Data p) : Interp.termOf p 247 = .ok T.«u64_bswap64» := hd.t247
@[opt_data] theorem Data.term_249 {p : Program} (hd : Data p) : Interp.termOf p 249 = .ok T.«intcc_comparable» := hd.t249
@[opt_data] theorem Data.rules_249 {p : Program} (hd : Data p) : p.rulesOf 249 = [rule_icmp_209] := hd.r249
@[opt_data] theorem Data.term_250 {p : Program} (hd : Data p) : Interp.termOf p 250 = .ok T.«decompose_intcc» := hd.t250
@[opt_data] theorem Data.rules_250 {p : Program} (hd : Data p) : p.rulesOf 250 = [rule_icmp_214, rule_icmp_215, rule_icmp_216, rule_icmp_217, rule_icmp_218, rule_icmp_219, rule_icmp_220, rule_icmp_221, rule_icmp_222, rule_icmp_223] := hd.r250
@[opt_data] theorem Data.term_251 {p : Program} (hd : Data p) : Interp.termOf p 251 = .ok T.«compose_icmp» := hd.t251
@[opt_data] theorem Data.rules_251 {p : Program} (hd : Data p) : p.rulesOf 251 = [rule_icmp_226, rule_icmp_227, rule_icmp_228, rule_icmp_229, rule_icmp_230, rule_icmp_231, rule_icmp_232, rule_icmp_233, rule_icmp_234, rule_icmp_235, rule_icmp_236, rule_icmp_237] := hd.r251
@[opt_data] theorem Data.term_252 {p : Program} (hd : Data p) : Interp.termOf p 252 = .ok T.«intcc_class» := hd.t252
@[opt_data] theorem Data.rules_252 {p : Program} (hd : Data p) : p.rulesOf 252 = [rule_icmp_240, rule_icmp_241, rule_icmp_242, rule_icmp_243, rule_icmp_244, rule_icmp_245, rule_icmp_246, rule_icmp_247, rule_icmp_248, rule_icmp_249] := hd.r252
@[opt_data] theorem Data.term_253 {p : Program} (hd : Data p) : Interp.termOf p 253 = .ok T.«shift_amt_to_type» := hd.t253
@[opt_data] theorem Data.rules_253 {p : Program} (hd : Data p) : p.rulesOf 253 = [rule_shifts_94, rule_shifts_95, rule_shifts_96] := hd.r253
@[opt_data] theorem Data.term_254 {p : Program} (hd : Data p) : Interp.termOf p 254 = .ok T.«iadd_uextend» := hd.t254
@[opt_data] theorem Data.rules_254 {p : Program} (hd : Data p) : p.rulesOf 254 = [rule_shifts_215, rule_shifts_212, rule_shifts_210] := hd.r254
@[opt_data] theorem Data.term_255 {p : Program} (hd : Data p) : Interp.termOf p 255 = .ok T.«isub_uextend» := hd.t255
@[opt_data] theorem Data.rules_255 {p : Program} (hd : Data p) : p.rulesOf 255 = [rule_shifts_227, rule_shifts_224, rule_shifts_222] := hd.r255
@[opt_data] theorem Data.term_506 {p : Program} (hd : Data p) : Interp.termOf p 506 = .ok T.«i32_lt» := hd.t506
@[opt_data] theorem Data.term_508 {p : Program} (hd : Data p) : Interp.termOf p 508 = .ok T.«i32_gt» := hd.t508
@[opt_data] theorem Data.term_567 {p : Program} (hd : Data p) : Interp.termOf p 567 = .ok T.«u32_lt» := hd.t567
@[opt_data] theorem Data.term_576 {p : Program} (hd : Data p) : Interp.termOf p 576 = .ok T.«u32_sub» := hd.t576
@[opt_data] theorem Data.term_603 {p : Program} (hd : Data p) : Interp.termOf p 603 = .ok T.«u32_matches_non_zero» := hd.t603
@[opt_data] theorem Data.term_623 {p : Program} (hd : Data p) : Interp.termOf p 623 = .ok T.«u32_is_power_of_two» := hd.t623
@[opt_data] theorem Data.term_628 {p : Program} (hd : Data p) : Interp.termOf p 628 = .ok T.«i64_eq» := hd.t628
@[opt_data] theorem Data.term_629 {p : Program} (hd : Data p) : Interp.termOf p 629 = .ok T.«i64_ne» := hd.t629
@[opt_data] theorem Data.term_630 {p : Program} (hd : Data p) : Interp.termOf p 630 = .ok T.«i64_lt» := hd.t630
@[opt_data] theorem Data.term_632 {p : Program} (hd : Data p) : Interp.termOf p 632 = .ok T.«i64_gt» := hd.t632
@[opt_data] theorem Data.term_633 {p : Program} (hd : Data p) : Interp.termOf p 633 = .ok T.«i64_gt_eq» := hd.t633
@[opt_data] theorem Data.term_654 {p : Program} (hd : Data p) : Interp.termOf p 654 = .ok T.«i64_shl» := hd.t654
@[opt_data] theorem Data.term_666 {p : Program} (hd : Data p) : Interp.termOf p 666 = .ok T.«i64_matches_non_zero» := hd.t666
@[opt_data] theorem Data.term_682 {p : Program} (hd : Data p) : Interp.termOf p 682 = .ok T.«i64_trailing_zeros» := hd.t682
@[opt_data] theorem Data.term_687 {p : Program} (hd : Data p) : Interp.termOf p 687 = .ok T.«i64_wrapping_neg» := hd.t687
@[opt_data] theorem Data.term_689 {p : Program} (hd : Data p) : Interp.termOf p 689 = .ok T.«u64_eq» := hd.t689
@[opt_data] theorem Data.term_691 {p : Program} (hd : Data p) : Interp.termOf p 691 = .ok T.«u64_lt» := hd.t691
@[opt_data] theorem Data.term_692 {p : Program} (hd : Data p) : Interp.termOf p 692 = .ok T.«u64_lt_eq» := hd.t692
@[opt_data] theorem Data.term_693 {p : Program} (hd : Data p) : Interp.termOf p 693 = .ok T.«u64_gt» := hd.t693
@[opt_data] theorem Data.term_696 {p : Program} (hd : Data p) : Interp.termOf p 696 = .ok T.«u64_wrapping_add» := hd.t696
@[opt_data] theorem Data.term_699 {p : Program} (hd : Data p) : Interp.termOf p 699 = .ok T.«u64_wrapping_sub» := hd.t699
@[opt_data] theorem Data.term_700 {p : Program} (hd : Data p) : Interp.termOf p 700 = .ok T.«u64_sub» := hd.t700
@[opt_data] theorem Data.term_706 {p : Program} (hd : Data p) : Interp.termOf p 706 = .ok T.«u64_div» := hd.t706
@[opt_data] theorem Data.term_707 {p : Program} (hd : Data p) : Interp.termOf p 707 = .ok T.«u64_checked_rem» := hd.t707
@[opt_data] theorem Data.term_708 {p : Program} (hd : Data p) : Interp.termOf p 708 = .ok T.«u64_rem» := hd.t708
@[opt_data] theorem Data.term_709 {p : Program} (hd : Data p) : Interp.termOf p 709 = .ok T.«u64_and» := hd.t709
@[opt_data] theorem Data.term_710 {p : Program} (hd : Data p) : Interp.termOf p 710 = .ok T.«u64_or» := hd.t710
@[opt_data] theorem Data.term_712 {p : Program} (hd : Data p) : Interp.termOf p 712 = .ok T.«u64_not» := hd.t712
@[opt_data] theorem Data.term_715 {p : Program} (hd : Data p) : Interp.termOf p 715 = .ok T.«u64_shl» := hd.t715
@[opt_data] theorem Data.term_727 {p : Program} (hd : Data p) : Interp.termOf p 727 = .ok T.«u64_matches_non_zero» := hd.t727
@[opt_data] theorem Data.term_742 {p : Program} (hd : Data p) : Interp.termOf p 742 = .ok T.«u64_ilog2» := hd.t742
@[opt_data] theorem Data.term_743 {p : Program} (hd : Data p) : Interp.termOf p 743 = .ok T.«u64_trailing_zeros» := hd.t743
@[opt_data] theorem Data.term_747 {p : Program} (hd : Data p) : Interp.termOf p 747 = .ok T.«u64_is_power_of_two» := hd.t747
@[opt_data] theorem Data.term_748 {p : Program} (hd : Data p) : Interp.termOf p 748 = .ok T.«u64_matches_power_of_two» := hd.t748
@[opt_data] theorem Data.term_910 {p : Program} (hd : Data p) : Interp.termOf p 910 = .ok T.«u8_into_u32» := hd.t910
@[opt_data] theorem Data.term_914 {p : Program} (hd : Data p) : Interp.termOf p 914 = .ok T.«u8_into_u64» := hd.t914
@[opt_data] theorem Data.term_987 {p : Program} (hd : Data p) : Interp.termOf p 987 = .ok T.«i32_into_i64» := hd.t987
@[opt_data] theorem Data.term_1015 {p : Program} (hd : Data p) : Interp.termOf p 1015 = .ok T.«u32_into_i64» := hd.t1015
@[opt_data] theorem Data.term_1017 {p : Program} (hd : Data p) : Interp.termOf p 1017 = .ok T.«u32_into_u64» := hd.t1017
@[opt_data] theorem Data.term_1040 {p : Program} (hd : Data p) : Interp.termOf p 1040 = .ok T.«i32_from_i64» := hd.t1040
@[opt_data] theorem Data.term_1046 {p : Program} (hd : Data p) : Interp.termOf p 1046 = .ok T.«i64_cast_unsigned» := hd.t1046
@[opt_data] theorem Data.term_1073 {p : Program} (hd : Data p) : Interp.termOf p 1073 = .ok T.«u32_from_u64» := hd.t1073
@[opt_data] theorem Data.term_1146 {p : Program} (hd : Data p) : Interp.termOf p 1146 = .ok T.«value_array_2» := hd.t1146
@[opt_data] theorem Data.term_1147 {p : Program} (hd : Data p) : Interp.termOf p 1147 = .ok T.«value_array_3» := hd.t1147
@[opt_data] theorem Data.term_1148 {p : Program} (hd : Data p) : Interp.termOf p 1148 = .ok T.«block_array_2» := hd.t1148
@[opt_data] theorem Data.term_1149 {p : Program} (hd : Data p) : Interp.termOf p 1149 = .ok T.«jump» := hd.t1149
@[opt_data] theorem Data.rules_1149 {p : Program} (hd : Data p) : p.rulesOf 1149 = [rule_clif_opt_342] := hd.r1149
@[opt_data] theorem Data.term_1154 {p : Program} (hd : Data p) : Interp.termOf p 1154 = .ok T.«trapz» := hd.t1154
@[opt_data] theorem Data.rules_1154 {p : Program} (hd : Data p) : p.rulesOf 1154 = [rule_clif_opt_387] := hd.r1154
@[opt_data] theorem Data.term_1155 {p : Program} (hd : Data p) : Interp.termOf p 1155 = .ok T.«trapnz» := hd.t1155
@[opt_data] theorem Data.rules_1155 {p : Program} (hd : Data p) : p.rulesOf 1155 = [rule_clif_opt_396] := hd.r1155
@[opt_data] theorem Data.term_1157 {p : Program} (hd : Data p) : Interp.termOf p 1157 = .ok T.«splat» := hd.t1157
@[opt_data] theorem Data.rules_1157 {p : Program} (hd : Data p) : p.rulesOf 1157 = [rule_clif_opt_414] := hd.r1157
@[opt_data] theorem Data.term_1162 {p : Program} (hd : Data p) : Interp.termOf p 1162 = .ok T.«smin» := hd.t1162
@[opt_data] theorem Data.rules_1162 {p : Program} (hd : Data p) : p.rulesOf 1162 = [rule_clif_opt_459] := hd.r1162
@[opt_data] theorem Data.term_1163 {p : Program} (hd : Data p) : Interp.termOf p 1163 = .ok T.«umin» := hd.t1163
@[opt_data] theorem Data.rules_1163 {p : Program} (hd : Data p) : p.rulesOf 1163 = [rule_clif_opt_468] := hd.r1163
@[opt_data] theorem Data.term_1164 {p : Program} (hd : Data p) : Interp.termOf p 1164 = .ok T.«smax» := hd.t1164
@[opt_data] theorem Data.rules_1164 {p : Program} (hd : Data p) : p.rulesOf 1164 = [rule_clif_opt_477] := hd.r1164
@[opt_data] theorem Data.term_1165 {p : Program} (hd : Data p) : Interp.termOf p 1165 = .ok T.«umax» := hd.t1165
@[opt_data] theorem Data.rules_1165 {p : Program} (hd : Data p) : p.rulesOf 1165 = [rule_clif_opt_486] := hd.r1165
@[opt_data] theorem Data.term_1199 {p : Program} (hd : Data p) : Interp.termOf p 1199 = .ok T.«iconst» := hd.t1199
@[opt_data] theorem Data.rules_1199 {p : Program} (hd : Data p) : p.rulesOf 1199 = [rule_clif_opt_792] := hd.r1199
@[opt_data] theorem Data.term_1200 {p : Program} (hd : Data p) : Interp.termOf p 1200 = .ok T.«f16const» := hd.t1200
@[opt_data] theorem Data.rules_1200 {p : Program} (hd : Data p) : p.rulesOf 1200 = [rule_clif_opt_801] := hd.r1200
@[opt_data] theorem Data.term_1201 {p : Program} (hd : Data p) : Interp.termOf p 1201 = .ok T.«f32const» := hd.t1201
@[opt_data] theorem Data.rules_1201 {p : Program} (hd : Data p) : p.rulesOf 1201 = [rule_clif_opt_810] := hd.r1201
@[opt_data] theorem Data.term_1202 {p : Program} (hd : Data p) : Interp.termOf p 1202 = .ok T.«f64const» := hd.t1202
@[opt_data] theorem Data.rules_1202 {p : Program} (hd : Data p) : p.rulesOf 1202 = [rule_clif_opt_819] := hd.r1202
@[opt_data] theorem Data.term_1203 {p : Program} (hd : Data p) : Interp.termOf p 1203 = .ok T.«f128const» := hd.t1203
@[opt_data] theorem Data.rules_1203 {p : Program} (hd : Data p) : p.rulesOf 1203 = [rule_clif_opt_828] := hd.r1203
@[opt_data] theorem Data.term_1204 {p : Program} (hd : Data p) : Interp.termOf p 1204 = .ok T.«vconst» := hd.t1204
@[opt_data] theorem Data.rules_1204 {p : Program} (hd : Data p) : p.rulesOf 1204 = [rule_clif_opt_837] := hd.r1204
@[opt_data] theorem Data.term_1207 {p : Program} (hd : Data p) : Interp.termOf p 1207 = .ok T.«select» := hd.t1207
@[opt_data] theorem Data.rules_1207 {p : Program} (hd : Data p) : p.rulesOf 1207 = [rule_clif_opt_864] := hd.r1207
@[opt_data] theorem Data.term_1214 {p : Program} (hd : Data p) : Interp.termOf p 1214 = .ok T.«icmp» := hd.t1214
@[opt_data] theorem Data.rules_1214 {p : Program} (hd : Data p) : p.rulesOf 1214 = [rule_clif_opt_927] := hd.r1214
@[opt_data] theorem Data.term_1215 {p : Program} (hd : Data p) : Interp.termOf p 1215 = .ok T.«iadd» := hd.t1215
@[opt_data] theorem Data.rules_1215 {p : Program} (hd : Data p) : p.rulesOf 1215 = [rule_clif_opt_936] := hd.r1215
@[opt_data] theorem Data.term_1216 {p : Program} (hd : Data p) : Interp.termOf p 1216 = .ok T.«isub» := hd.t1216
@[opt_data] theorem Data.rules_1216 {p : Program} (hd : Data p) : p.rulesOf 1216 = [rule_clif_opt_945] := hd.r1216
@[opt_data] theorem Data.term_1217 {p : Program} (hd : Data p) : Interp.termOf p 1217 = .ok T.«ineg» := hd.t1217
@[opt_data] theorem Data.rules_1217 {p : Program} (hd : Data p) : p.rulesOf 1217 = [rule_clif_opt_954] := hd.r1217
@[opt_data] theorem Data.term_1218 {p : Program} (hd : Data p) : Interp.termOf p 1218 = .ok T.«iabs» := hd.t1218
@[opt_data] theorem Data.rules_1218 {p : Program} (hd : Data p) : p.rulesOf 1218 = [rule_clif_opt_963] := hd.r1218
@[opt_data] theorem Data.term_1219 {p : Program} (hd : Data p) : Interp.termOf p 1219 = .ok T.«imul» := hd.t1219
@[opt_data] theorem Data.rules_1219 {p : Program} (hd : Data p) : p.rulesOf 1219 = [rule_clif_opt_972] := hd.r1219
@[opt_data] theorem Data.term_1220 {p : Program} (hd : Data p) : Interp.termOf p 1220 = .ok T.«umulhi» := hd.t1220
@[opt_data] theorem Data.rules_1220 {p : Program} (hd : Data p) : p.rulesOf 1220 = [rule_clif_opt_981] := hd.r1220
@[opt_data] theorem Data.term_1221 {p : Program} (hd : Data p) : Interp.termOf p 1221 = .ok T.«smulhi» := hd.t1221
@[opt_data] theorem Data.rules_1221 {p : Program} (hd : Data p) : p.rulesOf 1221 = [rule_clif_opt_990] := hd.r1221
@[opt_data] theorem Data.term_1239 {p : Program} (hd : Data p) : Interp.termOf p 1239 = .ok T.«band» := hd.t1239
@[opt_data] theorem Data.rules_1239 {p : Program} (hd : Data p) : p.rulesOf 1239 = [rule_clif_opt_1152] := hd.r1239
@[opt_data] theorem Data.term_1240 {p : Program} (hd : Data p) : Interp.termOf p 1240 = .ok T.«bor» := hd.t1240
@[opt_data] theorem Data.rules_1240 {p : Program} (hd : Data p) : p.rulesOf 1240 = [rule_clif_opt_1161] := hd.r1240
@[opt_data] theorem Data.term_1241 {p : Program} (hd : Data p) : Interp.termOf p 1241 = .ok T.«bxor» := hd.t1241
@[opt_data] theorem Data.rules_1241 {p : Program} (hd : Data p) : p.rulesOf 1241 = [rule_clif_opt_1170] := hd.r1241
@[opt_data] theorem Data.term_1242 {p : Program} (hd : Data p) : Interp.termOf p 1242 = .ok T.«bnot» := hd.t1242
@[opt_data] theorem Data.rules_1242 {p : Program} (hd : Data p) : p.rulesOf 1242 = [rule_clif_opt_1179] := hd.r1242
@[opt_data] theorem Data.term_1243 {p : Program} (hd : Data p) : Interp.termOf p 1243 = .ok T.«rotl» := hd.t1243
@[opt_data] theorem Data.rules_1243 {p : Program} (hd : Data p) : p.rulesOf 1243 = [rule_clif_opt_1188] := hd.r1243
@[opt_data] theorem Data.term_1244 {p : Program} (hd : Data p) : Interp.termOf p 1244 = .ok T.«rotr» := hd.t1244
@[opt_data] theorem Data.rules_1244 {p : Program} (hd : Data p) : p.rulesOf 1244 = [rule_clif_opt_1197] := hd.r1244
@[opt_data] theorem Data.term_1245 {p : Program} (hd : Data p) : Interp.termOf p 1245 = .ok T.«ishl» := hd.t1245
@[opt_data] theorem Data.rules_1245 {p : Program} (hd : Data p) : p.rulesOf 1245 = [rule_clif_opt_1206] := hd.r1245
@[opt_data] theorem Data.term_1246 {p : Program} (hd : Data p) : Interp.termOf p 1246 = .ok T.«ushr» := hd.t1246
@[opt_data] theorem Data.rules_1246 {p : Program} (hd : Data p) : p.rulesOf 1246 = [rule_clif_opt_1215] := hd.r1246
@[opt_data] theorem Data.term_1247 {p : Program} (hd : Data p) : Interp.termOf p 1247 = .ok T.«sshr» := hd.t1247
@[opt_data] theorem Data.rules_1247 {p : Program} (hd : Data p) : p.rulesOf 1247 = [rule_clif_opt_1224] := hd.r1247
@[opt_data] theorem Data.term_1252 {p : Program} (hd : Data p) : Interp.termOf p 1252 = .ok T.«bswap» := hd.t1252
@[opt_data] theorem Data.rules_1252 {p : Program} (hd : Data p) : p.rulesOf 1252 = [rule_clif_opt_1269] := hd.r1252
@[opt_data] theorem Data.term_1253 {p : Program} (hd : Data p) : Interp.termOf p 1253 = .ok T.«popcnt» := hd.t1253
@[opt_data] theorem Data.rules_1253 {p : Program} (hd : Data p) : p.rulesOf 1253 = [rule_clif_opt_1278] := hd.r1253
@[opt_data] theorem Data.term_1272 {p : Program} (hd : Data p) : Interp.termOf p 1272 = .ok T.«bmask» := hd.t1272
@[opt_data] theorem Data.rules_1272 {p : Program} (hd : Data p) : p.rulesOf 1272 = [rule_clif_opt_1449] := hd.r1272
@[opt_data] theorem Data.term_1273 {p : Program} (hd : Data p) : Interp.termOf p 1273 = .ok T.«ireduce» := hd.t1273
@[opt_data] theorem Data.rules_1273 {p : Program} (hd : Data p) : p.rulesOf 1273 = [rule_clif_opt_1458] := hd.r1273
@[opt_data] theorem Data.term_1283 {p : Program} (hd : Data p) : Interp.termOf p 1283 = .ok T.«uextend» := hd.t1283
@[opt_data] theorem Data.rules_1283 {p : Program} (hd : Data p) : p.rulesOf 1283 = [rule_clif_opt_1548] := hd.r1283
@[opt_data] theorem Data.term_1284 {p : Program} (hd : Data p) : Interp.termOf p 1284 = .ok T.«sextend» := hd.t1284
@[opt_data] theorem Data.rules_1284 {p : Program} (hd : Data p) : p.rulesOf 1284 = [rule_clif_opt_1557] := hd.r1284
@[opt_data] theorem Data.term_1297 {p : Program} (hd : Data p) : Interp.termOf p 1297 = .ok T.«iconcat» := hd.t1297
@[opt_data] theorem Data.rules_1297 {p : Program} (hd : Data p) : p.rulesOf 1297 = [rule_clif_opt_1674] := hd.r1297
@[opt_data] theorem Data.term_1305 {p : Program} (hd : Data p) : Interp.termOf p 1305 = .ok T.«SkeletonInstSimplification.Remove» := hd.t1305
@[opt_data] theorem Data.term_1306 {p : Program} (hd : Data p) : Interp.termOf p 1306 = .ok T.«SkeletonInstSimplification.RemoveWithVal» := hd.t1306
@[opt_data] theorem Data.term_1307 {p : Program} (hd : Data p) : Interp.termOf p 1307 = .ok T.«SkeletonInstSimplification.Replace» := hd.t1307
@[opt_data] theorem Data.term_1309 {p : Program} (hd : Data p) : Interp.termOf p 1309 = .ok T.«SkeletonInstSimplification.ReplaceBranchCond» := hd.t1309
@[opt_data] theorem Data.term_1310 {p : Program} (hd : Data p) : Interp.termOf p 1310 = .ok T.«SkeletonInstSimplification.ReplaceWithTwo» := hd.t1310
@[opt_data] theorem Data.term_1312 {p : Program} (hd : Data p) : Interp.termOf p 1312 = .ok T.«DivConstMagicU32.U32» := hd.t1312
@[opt_data] theorem Data.term_1313 {p : Program} (hd : Data p) : Interp.termOf p 1313 = .ok T.«DivConstMagicU64.U64» := hd.t1313
@[opt_data] theorem Data.term_1314 {p : Program} (hd : Data p) : Interp.termOf p 1314 = .ok T.«DivConstMagicS32.S32» := hd.t1314
@[opt_data] theorem Data.term_1315 {p : Program} (hd : Data p) : Interp.termOf p 1315 = .ok T.«DivConstMagicS64.S64» := hd.t1315
@[opt_data] theorem Data.term_1341 {p : Program} (hd : Data p) : Interp.termOf p 1341 = .ok T.«IntCC.Equal» := hd.t1341
@[opt_data] theorem Data.term_1342 {p : Program} (hd : Data p) : Interp.termOf p 1342 = .ok T.«IntCC.NotEqual» := hd.t1342
@[opt_data] theorem Data.term_1343 {p : Program} (hd : Data p) : Interp.termOf p 1343 = .ok T.«IntCC.SignedGreaterThan» := hd.t1343
@[opt_data] theorem Data.term_1344 {p : Program} (hd : Data p) : Interp.termOf p 1344 = .ok T.«IntCC.SignedGreaterThanOrEqual» := hd.t1344
@[opt_data] theorem Data.term_1345 {p : Program} (hd : Data p) : Interp.termOf p 1345 = .ok T.«IntCC.SignedLessThan» := hd.t1345
@[opt_data] theorem Data.term_1346 {p : Program} (hd : Data p) : Interp.termOf p 1346 = .ok T.«IntCC.SignedLessThanOrEqual» := hd.t1346
@[opt_data] theorem Data.term_1347 {p : Program} (hd : Data p) : Interp.termOf p 1347 = .ok T.«IntCC.UnsignedGreaterThan» := hd.t1347
@[opt_data] theorem Data.term_1348 {p : Program} (hd : Data p) : Interp.termOf p 1348 = .ok T.«IntCC.UnsignedGreaterThanOrEqual» := hd.t1348
@[opt_data] theorem Data.term_1349 {p : Program} (hd : Data p) : Interp.termOf p 1349 = .ok T.«IntCC.UnsignedLessThan» := hd.t1349
@[opt_data] theorem Data.term_1350 {p : Program} (hd : Data p) : Interp.termOf p 1350 = .ok T.«IntCC.UnsignedLessThanOrEqual» := hd.t1350
@[opt_data] theorem Data.term_1356 {p : Program} (hd : Data p) : Interp.termOf p 1356 = .ok T.«Opcode.Jump» := hd.t1356
@[opt_data] theorem Data.term_1357 {p : Program} (hd : Data p) : Interp.termOf p 1357 = .ok T.«Opcode.Brif» := hd.t1357
@[opt_data] theorem Data.term_1358 {p : Program} (hd : Data p) : Interp.termOf p 1358 = .ok T.«Opcode.BrTable» := hd.t1358
@[opt_data] theorem Data.term_1361 {p : Program} (hd : Data p) : Interp.termOf p 1361 = .ok T.«Opcode.Trapz» := hd.t1361
@[opt_data] theorem Data.term_1362 {p : Program} (hd : Data p) : Interp.termOf p 1362 = .ok T.«Opcode.Trapnz» := hd.t1362
@[opt_data] theorem Data.term_1371 {p : Program} (hd : Data p) : Interp.termOf p 1371 = .ok T.«Opcode.Splat» := hd.t1371
@[opt_data] theorem Data.term_1376 {p : Program} (hd : Data p) : Interp.termOf p 1376 = .ok T.«Opcode.Smin» := hd.t1376
@[opt_data] theorem Data.term_1377 {p : Program} (hd : Data p) : Interp.termOf p 1377 = .ok T.«Opcode.Umin» := hd.t1377
@[opt_data] theorem Data.term_1378 {p : Program} (hd : Data p) : Interp.termOf p 1378 = .ok T.«Opcode.Smax» := hd.t1378
@[opt_data] theorem Data.term_1379 {p : Program} (hd : Data p) : Interp.termOf p 1379 = .ok T.«Opcode.Umax» := hd.t1379
@[opt_data] theorem Data.term_1413 {p : Program} (hd : Data p) : Interp.termOf p 1413 = .ok T.«Opcode.Iconst» := hd.t1413
@[opt_data] theorem Data.term_1414 {p : Program} (hd : Data p) : Interp.termOf p 1414 = .ok T.«Opcode.F16const» := hd.t1414
@[opt_data] theorem Data.term_1415 {p : Program} (hd : Data p) : Interp.termOf p 1415 = .ok T.«Opcode.F32const» := hd.t1415
@[opt_data] theorem Data.term_1416 {p : Program} (hd : Data p) : Interp.termOf p 1416 = .ok T.«Opcode.F64const» := hd.t1416
@[opt_data] theorem Data.term_1417 {p : Program} (hd : Data p) : Interp.termOf p 1417 = .ok T.«Opcode.F128const» := hd.t1417
@[opt_data] theorem Data.term_1418 {p : Program} (hd : Data p) : Interp.termOf p 1418 = .ok T.«Opcode.Vconst» := hd.t1418
@[opt_data] theorem Data.term_1421 {p : Program} (hd : Data p) : Interp.termOf p 1421 = .ok T.«Opcode.Select» := hd.t1421
@[opt_data] theorem Data.term_1428 {p : Program} (hd : Data p) : Interp.termOf p 1428 = .ok T.«Opcode.Icmp» := hd.t1428
@[opt_data] theorem Data.term_1429 {p : Program} (hd : Data p) : Interp.termOf p 1429 = .ok T.«Opcode.Iadd» := hd.t1429
@[opt_data] theorem Data.term_1430 {p : Program} (hd : Data p) : Interp.termOf p 1430 = .ok T.«Opcode.Isub» := hd.t1430
@[opt_data] theorem Data.term_1431 {p : Program} (hd : Data p) : Interp.termOf p 1431 = .ok T.«Opcode.Ineg» := hd.t1431
@[opt_data] theorem Data.term_1432 {p : Program} (hd : Data p) : Interp.termOf p 1432 = .ok T.«Opcode.Iabs» := hd.t1432
@[opt_data] theorem Data.term_1433 {p : Program} (hd : Data p) : Interp.termOf p 1433 = .ok T.«Opcode.Imul» := hd.t1433
@[opt_data] theorem Data.term_1434 {p : Program} (hd : Data p) : Interp.termOf p 1434 = .ok T.«Opcode.Umulhi» := hd.t1434
@[opt_data] theorem Data.term_1435 {p : Program} (hd : Data p) : Interp.termOf p 1435 = .ok T.«Opcode.Smulhi» := hd.t1435
@[opt_data] theorem Data.term_1438 {p : Program} (hd : Data p) : Interp.termOf p 1438 = .ok T.«Opcode.Udiv» := hd.t1438
@[opt_data] theorem Data.term_1439 {p : Program} (hd : Data p) : Interp.termOf p 1439 = .ok T.«Opcode.Sdiv» := hd.t1439
@[opt_data] theorem Data.term_1440 {p : Program} (hd : Data p) : Interp.termOf p 1440 = .ok T.«Opcode.Urem» := hd.t1440
@[opt_data] theorem Data.term_1441 {p : Program} (hd : Data p) : Interp.termOf p 1441 = .ok T.«Opcode.Srem» := hd.t1441
@[opt_data] theorem Data.term_1453 {p : Program} (hd : Data p) : Interp.termOf p 1453 = .ok T.«Opcode.Band» := hd.t1453
@[opt_data] theorem Data.term_1454 {p : Program} (hd : Data p) : Interp.termOf p 1454 = .ok T.«Opcode.Bor» := hd.t1454
@[opt_data] theorem Data.term_1455 {p : Program} (hd : Data p) : Interp.termOf p 1455 = .ok T.«Opcode.Bxor» := hd.t1455
@[opt_data] theorem Data.term_1456 {p : Program} (hd : Data p) : Interp.termOf p 1456 = .ok T.«Opcode.Bnot» := hd.t1456
@[opt_data] theorem Data.term_1457 {p : Program} (hd : Data p) : Interp.termOf p 1457 = .ok T.«Opcode.Rotl» := hd.t1457
@[opt_data] theorem Data.term_1458 {p : Program} (hd : Data p) : Interp.termOf p 1458 = .ok T.«Opcode.Rotr» := hd.t1458
@[opt_data] theorem Data.term_1459 {p : Program} (hd : Data p) : Interp.termOf p 1459 = .ok T.«Opcode.Ishl» := hd.t1459
@[opt_data] theorem Data.term_1460 {p : Program} (hd : Data p) : Interp.termOf p 1460 = .ok T.«Opcode.Ushr» := hd.t1460
@[opt_data] theorem Data.term_1461 {p : Program} (hd : Data p) : Interp.termOf p 1461 = .ok T.«Opcode.Sshr» := hd.t1461
@[opt_data] theorem Data.term_1462 {p : Program} (hd : Data p) : Interp.termOf p 1462 = .ok T.«Opcode.Bitrev» := hd.t1462
@[opt_data] theorem Data.term_1463 {p : Program} (hd : Data p) : Interp.termOf p 1463 = .ok T.«Opcode.Clz» := hd.t1463
@[opt_data] theorem Data.term_1465 {p : Program} (hd : Data p) : Interp.termOf p 1465 = .ok T.«Opcode.Ctz» := hd.t1465
@[opt_data] theorem Data.term_1466 {p : Program} (hd : Data p) : Interp.termOf p 1466 = .ok T.«Opcode.Bswap» := hd.t1466
@[opt_data] theorem Data.term_1467 {p : Program} (hd : Data p) : Interp.termOf p 1467 = .ok T.«Opcode.Popcnt» := hd.t1467
@[opt_data] theorem Data.term_1486 {p : Program} (hd : Data p) : Interp.termOf p 1486 = .ok T.«Opcode.Bmask» := hd.t1486
@[opt_data] theorem Data.term_1487 {p : Program} (hd : Data p) : Interp.termOf p 1487 = .ok T.«Opcode.Ireduce» := hd.t1487
@[opt_data] theorem Data.term_1497 {p : Program} (hd : Data p) : Interp.termOf p 1497 = .ok T.«Opcode.Uextend» := hd.t1497
@[opt_data] theorem Data.term_1498 {p : Program} (hd : Data p) : Interp.termOf p 1498 = .ok T.«Opcode.Sextend» := hd.t1498
@[opt_data] theorem Data.term_1511 {p : Program} (hd : Data p) : Interp.termOf p 1511 = .ok T.«Opcode.Iconcat» := hd.t1511
@[opt_data] theorem Data.term_1521 {p : Program} (hd : Data p) : Interp.termOf p 1521 = .ok T.«InstructionData.Binary» := hd.t1521
@[opt_data] theorem Data.term_1523 {p : Program} (hd : Data p) : Interp.termOf p 1523 = .ok T.«InstructionData.BranchTable» := hd.t1523
@[opt_data] theorem Data.term_1524 {p : Program} (hd : Data p) : Interp.termOf p 1524 = .ok T.«InstructionData.Brif» := hd.t1524
@[opt_data] theorem Data.term_1527 {p : Program} (hd : Data p) : Interp.termOf p 1527 = .ok T.«InstructionData.CondTrap» := hd.t1527
@[opt_data] theorem Data.term_1533 {p : Program} (hd : Data p) : Interp.termOf p 1533 = .ok T.«InstructionData.IntCompare» := hd.t1533
@[opt_data] theorem Data.term_1534 {p : Program} (hd : Data p) : Interp.termOf p 1534 = .ok T.«InstructionData.Jump» := hd.t1534
@[opt_data] theorem Data.term_1543 {p : Program} (hd : Data p) : Interp.termOf p 1543 = .ok T.«InstructionData.Ternary» := hd.t1543
@[opt_data] theorem Data.term_1548 {p : Program} (hd : Data p) : Interp.termOf p 1548 = .ok T.«InstructionData.Unary» := hd.t1548
@[opt_data] theorem Data.term_1549 {p : Program} (hd : Data p) : Interp.termOf p 1549 = .ok T.«InstructionData.UnaryConst» := hd.t1549
@[opt_data] theorem Data.term_1551 {p : Program} (hd : Data p) : Interp.termOf p 1551 = .ok T.«InstructionData.UnaryIeee16» := hd.t1551
@[opt_data] theorem Data.term_1552 {p : Program} (hd : Data p) : Interp.termOf p 1552 = .ok T.«InstructionData.UnaryIeee32» := hd.t1552
@[opt_data] theorem Data.term_1553 {p : Program} (hd : Data p) : Interp.termOf p 1553 = .ok T.«InstructionData.UnaryIeee64» := hd.t1553
@[opt_data] theorem Data.term_1554 {p : Program} (hd : Data p) : Interp.termOf p 1554 = .ok T.«InstructionData.UnaryImm» := hd.t1554

/-! ### The facts for `program` (`rfl`) -/

set_option maxRecDepth 20000

theorem program_term_2 : Interp.termOf program 2 = .ok T.«value_type» := rfl
theorem program_term_7 : Interp.termOf program 7 = .ok T.«imm64_sdiv» := rfl
theorem program_term_8 : Interp.termOf program 8 = .ok T.«imm64_udiv» := rfl
theorem program_term_9 : Interp.termOf program 9 = .ok T.«imm64_srem» := rfl
theorem program_term_10 : Interp.termOf program 10 = .ok T.«imm64_urem» := rfl
theorem program_term_11 : Interp.termOf program 11 = .ok T.«imm64_add» := rfl
theorem program_term_12 : Interp.termOf program 12 = .ok T.«imm64_sub» := rfl
theorem program_term_13 : Interp.termOf program 13 = .ok T.«imm64_mul» := rfl
theorem program_term_14 : Interp.termOf program 14 = .ok T.«imm64_and» := rfl
theorem program_term_15 : Interp.termOf program 15 = .ok T.«imm64_or» := rfl
theorem program_term_16 : Interp.termOf program 16 = .ok T.«imm64_xor» := rfl
theorem program_term_17 : Interp.termOf program 17 = .ok T.«imm64_not» := rfl
theorem program_term_18 : Interp.termOf program 18 = .ok T.«imm64_neg» := rfl
theorem program_term_21 : Interp.termOf program 21 = .ok T.«imm64_umin» := rfl
theorem program_term_22 : Interp.termOf program 22 = .ok T.«imm64_umax» := rfl
theorem program_term_23 : Interp.termOf program 23 = .ok T.«imm64_smin» := rfl
theorem program_term_24 : Interp.termOf program 24 = .ok T.«imm64_smax» := rfl
theorem program_term_25 : Interp.termOf program 25 = .ok T.«imm64_shl» := rfl
theorem program_term_26 : Interp.termOf program 26 = .ok T.«imm64_ushr» := rfl
theorem program_term_27 : Interp.termOf program 27 = .ok T.«imm64_sshr» := rfl
theorem program_term_28 : Interp.termOf program 28 = .ok T.«imm64_rotl» := rfl
theorem program_term_29 : Interp.termOf program 29 = .ok T.«imm64_rotr» := rfl
theorem program_term_30 : Interp.termOf program 30 = .ok T.«i64_sextend_u64» := rfl
theorem program_term_33 : Interp.termOf program 33 = .ok T.«imm64_icmp» := rfl
theorem program_term_34 : Interp.termOf program 34 = .ok T.«imm64_clz» := rfl
theorem program_term_35 : Interp.termOf program 35 = .ok T.«imm64_ctz» := rfl
theorem program_term_84 : Interp.termOf program 84 = .ok T.«ty_umax» := rfl
theorem program_term_85 : Interp.termOf program 85 = .ok T.«ty_smin» := rfl
theorem program_term_86 : Interp.termOf program 86 = .ok T.«ty_smax» := rfl
theorem program_term_87 : Interp.termOf program 87 = .ok T.«ty_bits» := rfl
theorem program_term_89 : Interp.termOf program 89 = .ok T.«ty_bits_u64» := rfl
theorem program_term_90 : Interp.termOf program 90 = .ok T.«ty_mask» := rfl
theorem program_term_94 : Interp.termOf program 94 = .ok T.«lane_type» := rfl
theorem program_term_96 : Interp.termOf program 96 = .ok T.«ty_half_width» := rfl
theorem program_term_97 : Interp.termOf program 97 = .ok T.«ty_shift_mask» := rfl
theorem program_rulesOf_97 : program.rulesOf 97 = [rule_prelude_343] := rfl
theorem program_term_98 : Interp.termOf program 98 = .ok T.«ty_equal» := rfl
theorem program_term_104 : Interp.termOf program 104 = .ok T.«intcc_swap_args» := rfl
theorem program_term_105 : Interp.termOf program 105 = .ok T.«intcc_complement» := rfl
theorem program_term_113 : Interp.termOf program 113 = .ok T.«fits_in_64» := rfl
theorem program_term_119 : Interp.termOf program 119 = .ok T.«ty_int_ref_scalar_64_extract» := rfl
theorem program_term_126 : Interp.termOf program 126 = .ok T.«ty_int» := rfl
theorem program_term_133 : Interp.termOf program 133 = .ok T.«ty_vec128» := rfl
theorem program_term_144 : Interp.termOf program 144 = .ok T.«u64_from_imm64» := rfl
theorem program_term_146 : Interp.termOf program 146 = .ok T.«imm64_power_of_two» := rfl
theorem program_term_147 : Interp.termOf program 147 = .ok T.«imm64» := rfl
theorem program_term_148 : Interp.termOf program 148 = .ok T.«imm64_masked» := rfl
theorem program_term_159 : Interp.termOf program 159 = .ok T.«signed_cond_code» := rfl
theorem program_term_164 : Interp.termOf program 164 = .ok T.«zero_constant» := rfl
theorem program_term_165 : Interp.termOf program 165 = .ok T.«inst_data_value» := rfl
theorem program_term_166 : Interp.termOf program 166 = .ok T.«inst_data» := rfl
theorem program_term_167 : Interp.termOf program 167 = .ok T.«inst_data_value_tupled» := rfl
theorem program_term_168 : Interp.termOf program 168 = .ok T.«make_inst» := rfl
theorem program_term_169 : Interp.termOf program 169 = .ok T.«make_skeleton_inst» := rfl
theorem program_term_170 : Interp.termOf program 170 = .ok T.«value_array_2_ctor» := rfl
theorem program_term_171 : Interp.termOf program 171 = .ok T.«value_array_3_ctor» := rfl
theorem program_term_172 : Interp.termOf program 172 = .ok T.«resolve_jump_table_entry» := rfl
theorem program_term_173 : Interp.termOf program 173 = .ok T.«block_call_block» := rfl
theorem program_term_174 : Interp.termOf program 174 = .ok T.«just_trap_block» := rfl
theorem program_term_175 : Interp.termOf program 175 = .ok T.«spaceship_s» := rfl
theorem program_rulesOf_175 : program.rulesOf 175 = [rule_prelude_opt_74] := rfl
theorem program_term_176 : Interp.termOf program 176 = .ok T.«spaceship_u» := rfl
theorem program_rulesOf_176 : program.rulesOf 176 = [rule_prelude_opt_77] := rfl
theorem program_term_178 : Interp.termOf program 178 = .ok T.«inst_to_skeleton_inst_simplification» := rfl
theorem program_rulesOf_178 : program.rulesOf 178 = [rule_prelude_opt_136] := rfl
theorem program_term_179 : Interp.termOf program 179 = .ok T.«value_to_skeleton_inst_simplification» := rfl
theorem program_rulesOf_179 : program.rulesOf 179 = [rule_prelude_opt_140] := rfl
theorem program_term_180 : Interp.termOf program 180 = .ok T.«remove_inst» := rfl
theorem program_rulesOf_180 : program.rulesOf 180 = [rule_prelude_opt_144] := rfl
theorem program_term_182 : Interp.termOf program 182 = .ok T.«replace_branch_cond» := rfl
theorem program_rulesOf_182 : program.rulesOf 182 = [rule_prelude_opt_150] := rfl
theorem program_term_183 : Interp.termOf program 183 = .ok T.«replace_with_two» := rfl
theorem program_rulesOf_183 : program.rulesOf 183 = [rule_prelude_opt_154] := rfl
theorem program_term_185 : Interp.termOf program 185 = .ok T.«remat» := rfl
theorem program_term_186 : Interp.termOf program 186 = .ok T.«subsume» := rfl
theorem program_term_187 : Interp.termOf program 187 = .ok T.«iconst_sextend_etor» := rfl
theorem program_term_188 : Interp.termOf program 188 = .ok T.«iconst_s» := rfl
theorem program_rulesOf_188 : program.rulesOf 188 = [rule_prelude_opt_208, rule_prelude_opt_207, rule_prelude_opt_201] := rfl
theorem program_term_189 : Interp.termOf program 189 = .ok T.«iconst_u» := rfl
theorem program_rulesOf_189 : program.rulesOf 189 = [rule_prelude_opt_225, rule_prelude_opt_224, rule_prelude_opt_221] := rfl
theorem program_term_191 : Interp.termOf program 191 = .ok T.«uextend_maybe_etor» := rfl
theorem program_term_192 : Interp.termOf program 192 = .ok T.«uextend_maybe» := rfl
theorem program_rulesOf_192 : program.rulesOf 192 = [rule_prelude_opt_246, rule_prelude_opt_245] := rfl
theorem program_term_193 : Interp.termOf program 193 = .ok T.«sextend_maybe» := rfl
theorem program_rulesOf_193 : program.rulesOf 193 = [rule_prelude_opt_252, rule_prelude_opt_251] := rfl
theorem program_term_194 : Interp.termOf program 194 = .ok T.«eq» := rfl
theorem program_rulesOf_194 : program.rulesOf 194 = [rule_prelude_opt_61] := rfl
theorem program_term_195 : Interp.termOf program 195 = .ok T.«ne» := rfl
theorem program_rulesOf_195 : program.rulesOf 195 = [rule_prelude_opt_62] := rfl
theorem program_term_196 : Interp.termOf program 196 = .ok T.«ult» := rfl
theorem program_rulesOf_196 : program.rulesOf 196 = [rule_prelude_opt_63] := rfl
theorem program_term_197 : Interp.termOf program 197 = .ok T.«ule» := rfl
theorem program_rulesOf_197 : program.rulesOf 197 = [rule_prelude_opt_64] := rfl
theorem program_term_198 : Interp.termOf program 198 = .ok T.«ugt» := rfl
theorem program_rulesOf_198 : program.rulesOf 198 = [rule_prelude_opt_65] := rfl
theorem program_term_199 : Interp.termOf program 199 = .ok T.«uge» := rfl
theorem program_rulesOf_199 : program.rulesOf 199 = [rule_prelude_opt_66] := rfl
theorem program_term_200 : Interp.termOf program 200 = .ok T.«slt» := rfl
theorem program_rulesOf_200 : program.rulesOf 200 = [rule_prelude_opt_67] := rfl
theorem program_term_201 : Interp.termOf program 201 = .ok T.«sle» := rfl
theorem program_rulesOf_201 : program.rulesOf 201 = [rule_prelude_opt_68] := rfl
theorem program_term_202 : Interp.termOf program 202 = .ok T.«sgt» := rfl
theorem program_rulesOf_202 : program.rulesOf 202 = [rule_prelude_opt_69] := rfl
theorem program_term_203 : Interp.termOf program 203 = .ok T.«sge» := rfl
theorem program_rulesOf_203 : program.rulesOf 203 = [rule_prelude_opt_70] := rfl
theorem program_term_204 : Interp.termOf program 204 = .ok T.«i64_is_negative_power_of_two» := rfl
theorem program_rulesOf_204 : program.rulesOf 204 = [rule_prelude_opt_289] := rfl
theorem program_term_205 : Interp.termOf program 205 = .ok T.«i64_is_any_sign_power_of_two» := rfl
theorem program_rulesOf_205 : program.rulesOf 205 = [rule_prelude_opt_293, rule_prelude_opt_296, rule_prelude_opt_299] := rfl
theorem program_term_206 : Interp.termOf program 206 = .ok T.«div_const_magic_u32» := rfl
theorem program_term_207 : Interp.termOf program 207 = .ok T.«div_const_magic_u64» := rfl
theorem program_term_208 : Interp.termOf program 208 = .ok T.«div_const_magic_s32» := rfl
theorem program_term_209 : Interp.termOf program 209 = .ok T.«div_const_magic_s64» := rfl
theorem program_term_210 : Interp.termOf program 210 = .ok T.«apply_div_const_magic_u32» := rfl
theorem program_rulesOf_210 : program.rulesOf 210 = [rule_prelude_opt_328] := rfl
theorem program_term_211 : Interp.termOf program 211 = .ok T.«apply_div_const_magic_u32_inner» := rfl
theorem program_rulesOf_211 : program.rulesOf 211 = [rule_prelude_opt_333] := rfl
theorem program_term_212 : Interp.termOf program 212 = .ok T.«apply_div_const_magic_u32_maybe_add» := rfl
theorem program_rulesOf_212 : program.rulesOf 212 = [rule_prelude_opt_349, rule_prelude_opt_358] := rfl
theorem program_term_213 : Interp.termOf program 213 = .ok T.«apply_div_const_magic_u32_maybe_shift» := rfl
theorem program_rulesOf_213 : program.rulesOf 213 = [rule_prelude_opt_372, rule_prelude_opt_378] := rfl
theorem program_term_214 : Interp.termOf program 214 = .ok T.«apply_div_const_magic_u32_finish» := rfl
theorem program_rulesOf_214 : program.rulesOf 214 = [rule_prelude_opt_398, rule_prelude_opt_399] := rfl
theorem program_term_215 : Interp.termOf program 215 = .ok T.«apply_div_const_magic_u64» := rfl
theorem program_rulesOf_215 : program.rulesOf 215 = [rule_prelude_opt_405] := rfl
theorem program_term_216 : Interp.termOf program 216 = .ok T.«apply_div_const_magic_u64_inner» := rfl
theorem program_rulesOf_216 : program.rulesOf 216 = [rule_prelude_opt_410] := rfl
theorem program_term_217 : Interp.termOf program 217 = .ok T.«apply_div_const_magic_u64_maybe_add» := rfl
theorem program_rulesOf_217 : program.rulesOf 217 = [rule_prelude_opt_426, rule_prelude_opt_435] := rfl
theorem program_term_218 : Interp.termOf program 218 = .ok T.«apply_div_const_magic_u64_maybe_shift» := rfl
theorem program_rulesOf_218 : program.rulesOf 218 = [rule_prelude_opt_449, rule_prelude_opt_455] := rfl
theorem program_term_219 : Interp.termOf program 219 = .ok T.«apply_div_const_magic_u64_finish» := rfl
theorem program_rulesOf_219 : program.rulesOf 219 = [rule_prelude_opt_475, rule_prelude_opt_476] := rfl
theorem program_term_220 : Interp.termOf program 220 = .ok T.«apply_div_const_magic_s32» := rfl
theorem program_rulesOf_220 : program.rulesOf 220 = [rule_prelude_opt_483] := rfl
theorem program_term_221 : Interp.termOf program 221 = .ok T.«apply_div_const_magic_s32_inner» := rfl
theorem program_rulesOf_221 : program.rulesOf 221 = [rule_prelude_opt_489] := rfl
theorem program_term_222 : Interp.termOf program 222 = .ok T.«apply_div_const_magic_s32_add_sub» := rfl
theorem program_rulesOf_222 : program.rulesOf 222 = [rule_prelude_opt_505, rule_prelude_opt_514, rule_prelude_opt_523] := rfl
theorem program_term_223 : Interp.termOf program 223 = .ok T.«apply_div_const_magic_s32_shift» := rfl
theorem program_rulesOf_223 : program.rulesOf 223 = [rule_prelude_opt_534] := rfl
theorem program_term_224 : Interp.termOf program 224 = .ok T.«apply_div_const_magic_s32_finish» := rfl
theorem program_rulesOf_224 : program.rulesOf 224 = [rule_prelude_opt_555, rule_prelude_opt_558] := rfl
theorem program_term_225 : Interp.termOf program 225 = .ok T.«apply_div_const_magic_s64» := rfl
theorem program_rulesOf_225 : program.rulesOf 225 = [rule_prelude_opt_564] := rfl
theorem program_term_226 : Interp.termOf program 226 = .ok T.«apply_div_const_magic_s64_inner» := rfl
theorem program_rulesOf_226 : program.rulesOf 226 = [rule_prelude_opt_570] := rfl
theorem program_term_227 : Interp.termOf program 227 = .ok T.«apply_div_const_magic_s64_add_sub» := rfl
theorem program_rulesOf_227 : program.rulesOf 227 = [rule_prelude_opt_586, rule_prelude_opt_595, rule_prelude_opt_604] := rfl
theorem program_term_228 : Interp.termOf program 228 = .ok T.«apply_div_const_magic_s64_shift» := rfl
theorem program_rulesOf_228 : program.rulesOf 228 = [rule_prelude_opt_615] := rfl
theorem program_term_229 : Interp.termOf program 229 = .ok T.«apply_div_const_magic_s64_finish» := rfl
theorem program_rulesOf_229 : program.rulesOf 229 = [rule_prelude_opt_636, rule_prelude_opt_639] := rfl
theorem program_term_230 : Interp.termOf program 230 = .ok T.«cmp_true» := rfl
theorem program_rulesOf_230 : program.rulesOf 230 = [rule_arithmetic_401, rule_arithmetic_400] := rfl
theorem program_term_231 : Interp.termOf program 231 = .ok T.«all_zero_etor» := rfl
theorem program_term_232 : Interp.termOf program 232 = .ok T.«f16_zero» := rfl
theorem program_term_233 : Interp.termOf program 233 = .ok T.«ty_vector» := rfl
theorem program_term_234 : Interp.termOf program 234 = .ok T.«all_zero» := rfl
theorem program_rulesOf_234 : program.rulesOf 234 = [rule_bitops_18, rule_bitops_17, rule_bitops_16, rule_bitops_15, rule_bitops_14, rule_bitops_13] := rfl
theorem program_term_235 : Interp.termOf program 235 = .ok T.«truthy» := rfl
theorem program_rulesOf_235 : program.rulesOf 235 = [rule_bitops_111, rule_bitops_112, rule_bitops_113, rule_bitops_114, rule_bitops_115, rule_bitops_116, rule_bitops_117, rule_bitops_118, rule_bitops_119, rule_bitops_120, rule_bitops_122] := rfl
theorem program_term_241 : Interp.termOf program 241 = .ok T.«f32_from_uint» := rfl
theorem program_term_242 : Interp.termOf program 242 = .ok T.«f64_from_uint» := rfl
theorem program_term_245 : Interp.termOf program 245 = .ok T.«u64_bswap16» := rfl
theorem program_term_246 : Interp.termOf program 246 = .ok T.«u64_bswap32» := rfl
theorem program_term_247 : Interp.termOf program 247 = .ok T.«u64_bswap64» := rfl
theorem program_term_249 : Interp.termOf program 249 = .ok T.«intcc_comparable» := rfl
theorem program_rulesOf_249 : program.rulesOf 249 = [rule_icmp_209] := rfl
theorem program_term_250 : Interp.termOf program 250 = .ok T.«decompose_intcc» := rfl
theorem program_rulesOf_250 : program.rulesOf 250 = [rule_icmp_214, rule_icmp_215, rule_icmp_216, rule_icmp_217, rule_icmp_218, rule_icmp_219, rule_icmp_220, rule_icmp_221, rule_icmp_222, rule_icmp_223] := rfl
theorem program_term_251 : Interp.termOf program 251 = .ok T.«compose_icmp» := rfl
theorem program_rulesOf_251 : program.rulesOf 251 = [rule_icmp_226, rule_icmp_227, rule_icmp_228, rule_icmp_229, rule_icmp_230, rule_icmp_231, rule_icmp_232, rule_icmp_233, rule_icmp_234, rule_icmp_235, rule_icmp_236, rule_icmp_237] := rfl
theorem program_term_252 : Interp.termOf program 252 = .ok T.«intcc_class» := rfl
theorem program_rulesOf_252 : program.rulesOf 252 = [rule_icmp_240, rule_icmp_241, rule_icmp_242, rule_icmp_243, rule_icmp_244, rule_icmp_245, rule_icmp_246, rule_icmp_247, rule_icmp_248, rule_icmp_249] := rfl
theorem program_term_253 : Interp.termOf program 253 = .ok T.«shift_amt_to_type» := rfl
theorem program_rulesOf_253 : program.rulesOf 253 = [rule_shifts_94, rule_shifts_95, rule_shifts_96] := rfl
theorem program_term_254 : Interp.termOf program 254 = .ok T.«iadd_uextend» := rfl
theorem program_rulesOf_254 : program.rulesOf 254 = [rule_shifts_215, rule_shifts_212, rule_shifts_210] := rfl
theorem program_term_255 : Interp.termOf program 255 = .ok T.«isub_uextend» := rfl
theorem program_rulesOf_255 : program.rulesOf 255 = [rule_shifts_227, rule_shifts_224, rule_shifts_222] := rfl
theorem program_term_506 : Interp.termOf program 506 = .ok T.«i32_lt» := rfl
theorem program_term_508 : Interp.termOf program 508 = .ok T.«i32_gt» := rfl
theorem program_term_567 : Interp.termOf program 567 = .ok T.«u32_lt» := rfl
theorem program_term_576 : Interp.termOf program 576 = .ok T.«u32_sub» := rfl
theorem program_term_603 : Interp.termOf program 603 = .ok T.«u32_matches_non_zero» := rfl
theorem program_term_623 : Interp.termOf program 623 = .ok T.«u32_is_power_of_two» := rfl
theorem program_term_628 : Interp.termOf program 628 = .ok T.«i64_eq» := rfl
theorem program_term_629 : Interp.termOf program 629 = .ok T.«i64_ne» := rfl
theorem program_term_630 : Interp.termOf program 630 = .ok T.«i64_lt» := rfl
theorem program_term_632 : Interp.termOf program 632 = .ok T.«i64_gt» := rfl
theorem program_term_633 : Interp.termOf program 633 = .ok T.«i64_gt_eq» := rfl
theorem program_term_654 : Interp.termOf program 654 = .ok T.«i64_shl» := rfl
theorem program_term_666 : Interp.termOf program 666 = .ok T.«i64_matches_non_zero» := rfl
theorem program_term_682 : Interp.termOf program 682 = .ok T.«i64_trailing_zeros» := rfl
theorem program_term_687 : Interp.termOf program 687 = .ok T.«i64_wrapping_neg» := rfl
theorem program_term_689 : Interp.termOf program 689 = .ok T.«u64_eq» := rfl
theorem program_term_691 : Interp.termOf program 691 = .ok T.«u64_lt» := rfl
theorem program_term_692 : Interp.termOf program 692 = .ok T.«u64_lt_eq» := rfl
theorem program_term_693 : Interp.termOf program 693 = .ok T.«u64_gt» := rfl
theorem program_term_696 : Interp.termOf program 696 = .ok T.«u64_wrapping_add» := rfl
theorem program_term_699 : Interp.termOf program 699 = .ok T.«u64_wrapping_sub» := rfl
theorem program_term_700 : Interp.termOf program 700 = .ok T.«u64_sub» := rfl
theorem program_term_706 : Interp.termOf program 706 = .ok T.«u64_div» := rfl
theorem program_term_707 : Interp.termOf program 707 = .ok T.«u64_checked_rem» := rfl
theorem program_term_708 : Interp.termOf program 708 = .ok T.«u64_rem» := rfl
theorem program_term_709 : Interp.termOf program 709 = .ok T.«u64_and» := rfl
theorem program_term_710 : Interp.termOf program 710 = .ok T.«u64_or» := rfl
theorem program_term_712 : Interp.termOf program 712 = .ok T.«u64_not» := rfl
theorem program_term_715 : Interp.termOf program 715 = .ok T.«u64_shl» := rfl
theorem program_term_727 : Interp.termOf program 727 = .ok T.«u64_matches_non_zero» := rfl
theorem program_term_742 : Interp.termOf program 742 = .ok T.«u64_ilog2» := rfl
theorem program_term_743 : Interp.termOf program 743 = .ok T.«u64_trailing_zeros» := rfl
theorem program_term_747 : Interp.termOf program 747 = .ok T.«u64_is_power_of_two» := rfl
theorem program_term_748 : Interp.termOf program 748 = .ok T.«u64_matches_power_of_two» := rfl
theorem program_term_910 : Interp.termOf program 910 = .ok T.«u8_into_u32» := rfl
theorem program_term_914 : Interp.termOf program 914 = .ok T.«u8_into_u64» := rfl
theorem program_term_987 : Interp.termOf program 987 = .ok T.«i32_into_i64» := rfl
theorem program_term_1015 : Interp.termOf program 1015 = .ok T.«u32_into_i64» := rfl
theorem program_term_1017 : Interp.termOf program 1017 = .ok T.«u32_into_u64» := rfl
theorem program_term_1040 : Interp.termOf program 1040 = .ok T.«i32_from_i64» := rfl
theorem program_term_1046 : Interp.termOf program 1046 = .ok T.«i64_cast_unsigned» := rfl
theorem program_term_1073 : Interp.termOf program 1073 = .ok T.«u32_from_u64» := rfl
theorem program_term_1146 : Interp.termOf program 1146 = .ok T.«value_array_2» := rfl
theorem program_term_1147 : Interp.termOf program 1147 = .ok T.«value_array_3» := rfl
theorem program_term_1148 : Interp.termOf program 1148 = .ok T.«block_array_2» := rfl
theorem program_term_1149 : Interp.termOf program 1149 = .ok T.«jump» := rfl
theorem program_rulesOf_1149 : program.rulesOf 1149 = [rule_clif_opt_342] := rfl
theorem program_term_1154 : Interp.termOf program 1154 = .ok T.«trapz» := rfl
theorem program_rulesOf_1154 : program.rulesOf 1154 = [rule_clif_opt_387] := rfl
theorem program_term_1155 : Interp.termOf program 1155 = .ok T.«trapnz» := rfl
theorem program_rulesOf_1155 : program.rulesOf 1155 = [rule_clif_opt_396] := rfl
theorem program_term_1157 : Interp.termOf program 1157 = .ok T.«splat» := rfl
theorem program_rulesOf_1157 : program.rulesOf 1157 = [rule_clif_opt_414] := rfl
theorem program_term_1162 : Interp.termOf program 1162 = .ok T.«smin» := rfl
theorem program_rulesOf_1162 : program.rulesOf 1162 = [rule_clif_opt_459] := rfl
theorem program_term_1163 : Interp.termOf program 1163 = .ok T.«umin» := rfl
theorem program_rulesOf_1163 : program.rulesOf 1163 = [rule_clif_opt_468] := rfl
theorem program_term_1164 : Interp.termOf program 1164 = .ok T.«smax» := rfl
theorem program_rulesOf_1164 : program.rulesOf 1164 = [rule_clif_opt_477] := rfl
theorem program_term_1165 : Interp.termOf program 1165 = .ok T.«umax» := rfl
theorem program_rulesOf_1165 : program.rulesOf 1165 = [rule_clif_opt_486] := rfl
theorem program_term_1199 : Interp.termOf program 1199 = .ok T.«iconst» := rfl
theorem program_rulesOf_1199 : program.rulesOf 1199 = [rule_clif_opt_792] := rfl
theorem program_term_1200 : Interp.termOf program 1200 = .ok T.«f16const» := rfl
theorem program_rulesOf_1200 : program.rulesOf 1200 = [rule_clif_opt_801] := rfl
theorem program_term_1201 : Interp.termOf program 1201 = .ok T.«f32const» := rfl
theorem program_rulesOf_1201 : program.rulesOf 1201 = [rule_clif_opt_810] := rfl
theorem program_term_1202 : Interp.termOf program 1202 = .ok T.«f64const» := rfl
theorem program_rulesOf_1202 : program.rulesOf 1202 = [rule_clif_opt_819] := rfl
theorem program_term_1203 : Interp.termOf program 1203 = .ok T.«f128const» := rfl
theorem program_rulesOf_1203 : program.rulesOf 1203 = [rule_clif_opt_828] := rfl
theorem program_term_1204 : Interp.termOf program 1204 = .ok T.«vconst» := rfl
theorem program_rulesOf_1204 : program.rulesOf 1204 = [rule_clif_opt_837] := rfl
theorem program_term_1207 : Interp.termOf program 1207 = .ok T.«select» := rfl
theorem program_rulesOf_1207 : program.rulesOf 1207 = [rule_clif_opt_864] := rfl
theorem program_term_1214 : Interp.termOf program 1214 = .ok T.«icmp» := rfl
theorem program_rulesOf_1214 : program.rulesOf 1214 = [rule_clif_opt_927] := rfl
theorem program_term_1215 : Interp.termOf program 1215 = .ok T.«iadd» := rfl
theorem program_rulesOf_1215 : program.rulesOf 1215 = [rule_clif_opt_936] := rfl
theorem program_term_1216 : Interp.termOf program 1216 = .ok T.«isub» := rfl
theorem program_rulesOf_1216 : program.rulesOf 1216 = [rule_clif_opt_945] := rfl
theorem program_term_1217 : Interp.termOf program 1217 = .ok T.«ineg» := rfl
theorem program_rulesOf_1217 : program.rulesOf 1217 = [rule_clif_opt_954] := rfl
theorem program_term_1218 : Interp.termOf program 1218 = .ok T.«iabs» := rfl
theorem program_rulesOf_1218 : program.rulesOf 1218 = [rule_clif_opt_963] := rfl
theorem program_term_1219 : Interp.termOf program 1219 = .ok T.«imul» := rfl
theorem program_rulesOf_1219 : program.rulesOf 1219 = [rule_clif_opt_972] := rfl
theorem program_term_1220 : Interp.termOf program 1220 = .ok T.«umulhi» := rfl
theorem program_rulesOf_1220 : program.rulesOf 1220 = [rule_clif_opt_981] := rfl
theorem program_term_1221 : Interp.termOf program 1221 = .ok T.«smulhi» := rfl
theorem program_rulesOf_1221 : program.rulesOf 1221 = [rule_clif_opt_990] := rfl
theorem program_term_1239 : Interp.termOf program 1239 = .ok T.«band» := rfl
theorem program_rulesOf_1239 : program.rulesOf 1239 = [rule_clif_opt_1152] := rfl
theorem program_term_1240 : Interp.termOf program 1240 = .ok T.«bor» := rfl
theorem program_rulesOf_1240 : program.rulesOf 1240 = [rule_clif_opt_1161] := rfl
theorem program_term_1241 : Interp.termOf program 1241 = .ok T.«bxor» := rfl
theorem program_rulesOf_1241 : program.rulesOf 1241 = [rule_clif_opt_1170] := rfl
theorem program_term_1242 : Interp.termOf program 1242 = .ok T.«bnot» := rfl
theorem program_rulesOf_1242 : program.rulesOf 1242 = [rule_clif_opt_1179] := rfl
theorem program_term_1243 : Interp.termOf program 1243 = .ok T.«rotl» := rfl
theorem program_rulesOf_1243 : program.rulesOf 1243 = [rule_clif_opt_1188] := rfl
theorem program_term_1244 : Interp.termOf program 1244 = .ok T.«rotr» := rfl
theorem program_rulesOf_1244 : program.rulesOf 1244 = [rule_clif_opt_1197] := rfl
theorem program_term_1245 : Interp.termOf program 1245 = .ok T.«ishl» := rfl
theorem program_rulesOf_1245 : program.rulesOf 1245 = [rule_clif_opt_1206] := rfl
theorem program_term_1246 : Interp.termOf program 1246 = .ok T.«ushr» := rfl
theorem program_rulesOf_1246 : program.rulesOf 1246 = [rule_clif_opt_1215] := rfl
theorem program_term_1247 : Interp.termOf program 1247 = .ok T.«sshr» := rfl
theorem program_rulesOf_1247 : program.rulesOf 1247 = [rule_clif_opt_1224] := rfl
theorem program_term_1252 : Interp.termOf program 1252 = .ok T.«bswap» := rfl
theorem program_rulesOf_1252 : program.rulesOf 1252 = [rule_clif_opt_1269] := rfl
theorem program_term_1253 : Interp.termOf program 1253 = .ok T.«popcnt» := rfl
theorem program_rulesOf_1253 : program.rulesOf 1253 = [rule_clif_opt_1278] := rfl
theorem program_term_1272 : Interp.termOf program 1272 = .ok T.«bmask» := rfl
theorem program_rulesOf_1272 : program.rulesOf 1272 = [rule_clif_opt_1449] := rfl
theorem program_term_1273 : Interp.termOf program 1273 = .ok T.«ireduce» := rfl
theorem program_rulesOf_1273 : program.rulesOf 1273 = [rule_clif_opt_1458] := rfl
theorem program_term_1283 : Interp.termOf program 1283 = .ok T.«uextend» := rfl
theorem program_rulesOf_1283 : program.rulesOf 1283 = [rule_clif_opt_1548] := rfl
theorem program_term_1284 : Interp.termOf program 1284 = .ok T.«sextend» := rfl
theorem program_rulesOf_1284 : program.rulesOf 1284 = [rule_clif_opt_1557] := rfl
theorem program_term_1297 : Interp.termOf program 1297 = .ok T.«iconcat» := rfl
theorem program_rulesOf_1297 : program.rulesOf 1297 = [rule_clif_opt_1674] := rfl
theorem program_term_1305 : Interp.termOf program 1305 = .ok T.«SkeletonInstSimplification.Remove» := rfl
theorem program_term_1306 : Interp.termOf program 1306 = .ok T.«SkeletonInstSimplification.RemoveWithVal» := rfl
theorem program_term_1307 : Interp.termOf program 1307 = .ok T.«SkeletonInstSimplification.Replace» := rfl
theorem program_term_1309 : Interp.termOf program 1309 = .ok T.«SkeletonInstSimplification.ReplaceBranchCond» := rfl
theorem program_term_1310 : Interp.termOf program 1310 = .ok T.«SkeletonInstSimplification.ReplaceWithTwo» := rfl
theorem program_term_1312 : Interp.termOf program 1312 = .ok T.«DivConstMagicU32.U32» := rfl
theorem program_term_1313 : Interp.termOf program 1313 = .ok T.«DivConstMagicU64.U64» := rfl
theorem program_term_1314 : Interp.termOf program 1314 = .ok T.«DivConstMagicS32.S32» := rfl
theorem program_term_1315 : Interp.termOf program 1315 = .ok T.«DivConstMagicS64.S64» := rfl
theorem program_term_1341 : Interp.termOf program 1341 = .ok T.«IntCC.Equal» := rfl
theorem program_term_1342 : Interp.termOf program 1342 = .ok T.«IntCC.NotEqual» := rfl
theorem program_term_1343 : Interp.termOf program 1343 = .ok T.«IntCC.SignedGreaterThan» := rfl
theorem program_term_1344 : Interp.termOf program 1344 = .ok T.«IntCC.SignedGreaterThanOrEqual» := rfl
theorem program_term_1345 : Interp.termOf program 1345 = .ok T.«IntCC.SignedLessThan» := rfl
theorem program_term_1346 : Interp.termOf program 1346 = .ok T.«IntCC.SignedLessThanOrEqual» := rfl
theorem program_term_1347 : Interp.termOf program 1347 = .ok T.«IntCC.UnsignedGreaterThan» := rfl
theorem program_term_1348 : Interp.termOf program 1348 = .ok T.«IntCC.UnsignedGreaterThanOrEqual» := rfl
theorem program_term_1349 : Interp.termOf program 1349 = .ok T.«IntCC.UnsignedLessThan» := rfl
theorem program_term_1350 : Interp.termOf program 1350 = .ok T.«IntCC.UnsignedLessThanOrEqual» := rfl
theorem program_term_1356 : Interp.termOf program 1356 = .ok T.«Opcode.Jump» := rfl
theorem program_term_1357 : Interp.termOf program 1357 = .ok T.«Opcode.Brif» := rfl
theorem program_term_1358 : Interp.termOf program 1358 = .ok T.«Opcode.BrTable» := rfl
theorem program_term_1361 : Interp.termOf program 1361 = .ok T.«Opcode.Trapz» := rfl
theorem program_term_1362 : Interp.termOf program 1362 = .ok T.«Opcode.Trapnz» := rfl
theorem program_term_1371 : Interp.termOf program 1371 = .ok T.«Opcode.Splat» := rfl
theorem program_term_1376 : Interp.termOf program 1376 = .ok T.«Opcode.Smin» := rfl
theorem program_term_1377 : Interp.termOf program 1377 = .ok T.«Opcode.Umin» := rfl
theorem program_term_1378 : Interp.termOf program 1378 = .ok T.«Opcode.Smax» := rfl
theorem program_term_1379 : Interp.termOf program 1379 = .ok T.«Opcode.Umax» := rfl
theorem program_term_1413 : Interp.termOf program 1413 = .ok T.«Opcode.Iconst» := rfl
theorem program_term_1414 : Interp.termOf program 1414 = .ok T.«Opcode.F16const» := rfl
theorem program_term_1415 : Interp.termOf program 1415 = .ok T.«Opcode.F32const» := rfl
theorem program_term_1416 : Interp.termOf program 1416 = .ok T.«Opcode.F64const» := rfl
theorem program_term_1417 : Interp.termOf program 1417 = .ok T.«Opcode.F128const» := rfl
theorem program_term_1418 : Interp.termOf program 1418 = .ok T.«Opcode.Vconst» := rfl
theorem program_term_1421 : Interp.termOf program 1421 = .ok T.«Opcode.Select» := rfl
theorem program_term_1428 : Interp.termOf program 1428 = .ok T.«Opcode.Icmp» := rfl
theorem program_term_1429 : Interp.termOf program 1429 = .ok T.«Opcode.Iadd» := rfl
theorem program_term_1430 : Interp.termOf program 1430 = .ok T.«Opcode.Isub» := rfl
theorem program_term_1431 : Interp.termOf program 1431 = .ok T.«Opcode.Ineg» := rfl
theorem program_term_1432 : Interp.termOf program 1432 = .ok T.«Opcode.Iabs» := rfl
theorem program_term_1433 : Interp.termOf program 1433 = .ok T.«Opcode.Imul» := rfl
theorem program_term_1434 : Interp.termOf program 1434 = .ok T.«Opcode.Umulhi» := rfl
theorem program_term_1435 : Interp.termOf program 1435 = .ok T.«Opcode.Smulhi» := rfl
theorem program_term_1438 : Interp.termOf program 1438 = .ok T.«Opcode.Udiv» := rfl
theorem program_term_1439 : Interp.termOf program 1439 = .ok T.«Opcode.Sdiv» := rfl
theorem program_term_1440 : Interp.termOf program 1440 = .ok T.«Opcode.Urem» := rfl
theorem program_term_1441 : Interp.termOf program 1441 = .ok T.«Opcode.Srem» := rfl
theorem program_term_1453 : Interp.termOf program 1453 = .ok T.«Opcode.Band» := rfl
theorem program_term_1454 : Interp.termOf program 1454 = .ok T.«Opcode.Bor» := rfl
theorem program_term_1455 : Interp.termOf program 1455 = .ok T.«Opcode.Bxor» := rfl
theorem program_term_1456 : Interp.termOf program 1456 = .ok T.«Opcode.Bnot» := rfl
theorem program_term_1457 : Interp.termOf program 1457 = .ok T.«Opcode.Rotl» := rfl
theorem program_term_1458 : Interp.termOf program 1458 = .ok T.«Opcode.Rotr» := rfl
theorem program_term_1459 : Interp.termOf program 1459 = .ok T.«Opcode.Ishl» := rfl
theorem program_term_1460 : Interp.termOf program 1460 = .ok T.«Opcode.Ushr» := rfl
theorem program_term_1461 : Interp.termOf program 1461 = .ok T.«Opcode.Sshr» := rfl
theorem program_term_1462 : Interp.termOf program 1462 = .ok T.«Opcode.Bitrev» := rfl
theorem program_term_1463 : Interp.termOf program 1463 = .ok T.«Opcode.Clz» := rfl
theorem program_term_1465 : Interp.termOf program 1465 = .ok T.«Opcode.Ctz» := rfl
theorem program_term_1466 : Interp.termOf program 1466 = .ok T.«Opcode.Bswap» := rfl
theorem program_term_1467 : Interp.termOf program 1467 = .ok T.«Opcode.Popcnt» := rfl
theorem program_term_1486 : Interp.termOf program 1486 = .ok T.«Opcode.Bmask» := rfl
theorem program_term_1487 : Interp.termOf program 1487 = .ok T.«Opcode.Ireduce» := rfl
theorem program_term_1497 : Interp.termOf program 1497 = .ok T.«Opcode.Uextend» := rfl
theorem program_term_1498 : Interp.termOf program 1498 = .ok T.«Opcode.Sextend» := rfl
theorem program_term_1511 : Interp.termOf program 1511 = .ok T.«Opcode.Iconcat» := rfl
theorem program_term_1521 : Interp.termOf program 1521 = .ok T.«InstructionData.Binary» := rfl
theorem program_term_1523 : Interp.termOf program 1523 = .ok T.«InstructionData.BranchTable» := rfl
theorem program_term_1524 : Interp.termOf program 1524 = .ok T.«InstructionData.Brif» := rfl
theorem program_term_1527 : Interp.termOf program 1527 = .ok T.«InstructionData.CondTrap» := rfl
theorem program_term_1533 : Interp.termOf program 1533 = .ok T.«InstructionData.IntCompare» := rfl
theorem program_term_1534 : Interp.termOf program 1534 = .ok T.«InstructionData.Jump» := rfl
theorem program_term_1543 : Interp.termOf program 1543 = .ok T.«InstructionData.Ternary» := rfl
theorem program_term_1548 : Interp.termOf program 1548 = .ok T.«InstructionData.Unary» := rfl
theorem program_term_1549 : Interp.termOf program 1549 = .ok T.«InstructionData.UnaryConst» := rfl
theorem program_term_1551 : Interp.termOf program 1551 = .ok T.«InstructionData.UnaryIeee16» := rfl
theorem program_term_1552 : Interp.termOf program 1552 = .ok T.«InstructionData.UnaryIeee32» := rfl
theorem program_term_1553 : Interp.termOf program 1553 = .ok T.«InstructionData.UnaryIeee64» := rfl
theorem program_term_1554 : Interp.termOf program 1554 = .ok T.«InstructionData.UnaryImm» := rfl

theorem data_program : Data program where
  t2 := program_term_2
  t7 := program_term_7
  t8 := program_term_8
  t9 := program_term_9
  t10 := program_term_10
  t11 := program_term_11
  t12 := program_term_12
  t13 := program_term_13
  t14 := program_term_14
  t15 := program_term_15
  t16 := program_term_16
  t17 := program_term_17
  t18 := program_term_18
  t21 := program_term_21
  t22 := program_term_22
  t23 := program_term_23
  t24 := program_term_24
  t25 := program_term_25
  t26 := program_term_26
  t27 := program_term_27
  t28 := program_term_28
  t29 := program_term_29
  t30 := program_term_30
  t33 := program_term_33
  t34 := program_term_34
  t35 := program_term_35
  t84 := program_term_84
  t85 := program_term_85
  t86 := program_term_86
  t87 := program_term_87
  t89 := program_term_89
  t90 := program_term_90
  t94 := program_term_94
  t96 := program_term_96
  t97 := program_term_97
  r97 := program_rulesOf_97
  t98 := program_term_98
  t104 := program_term_104
  t105 := program_term_105
  t113 := program_term_113
  t119 := program_term_119
  t126 := program_term_126
  t133 := program_term_133
  t144 := program_term_144
  t146 := program_term_146
  t147 := program_term_147
  t148 := program_term_148
  t159 := program_term_159
  t164 := program_term_164
  t165 := program_term_165
  t166 := program_term_166
  t167 := program_term_167
  t168 := program_term_168
  t169 := program_term_169
  t170 := program_term_170
  t171 := program_term_171
  t172 := program_term_172
  t173 := program_term_173
  t174 := program_term_174
  t175 := program_term_175
  r175 := program_rulesOf_175
  t176 := program_term_176
  r176 := program_rulesOf_176
  t178 := program_term_178
  r178 := program_rulesOf_178
  t179 := program_term_179
  r179 := program_rulesOf_179
  t180 := program_term_180
  r180 := program_rulesOf_180
  t182 := program_term_182
  r182 := program_rulesOf_182
  t183 := program_term_183
  r183 := program_rulesOf_183
  t185 := program_term_185
  t186 := program_term_186
  t187 := program_term_187
  t188 := program_term_188
  r188 := program_rulesOf_188
  t189 := program_term_189
  r189 := program_rulesOf_189
  t191 := program_term_191
  t192 := program_term_192
  r192 := program_rulesOf_192
  t193 := program_term_193
  r193 := program_rulesOf_193
  t194 := program_term_194
  r194 := program_rulesOf_194
  t195 := program_term_195
  r195 := program_rulesOf_195
  t196 := program_term_196
  r196 := program_rulesOf_196
  t197 := program_term_197
  r197 := program_rulesOf_197
  t198 := program_term_198
  r198 := program_rulesOf_198
  t199 := program_term_199
  r199 := program_rulesOf_199
  t200 := program_term_200
  r200 := program_rulesOf_200
  t201 := program_term_201
  r201 := program_rulesOf_201
  t202 := program_term_202
  r202 := program_rulesOf_202
  t203 := program_term_203
  r203 := program_rulesOf_203
  t204 := program_term_204
  r204 := program_rulesOf_204
  t205 := program_term_205
  r205 := program_rulesOf_205
  t206 := program_term_206
  t207 := program_term_207
  t208 := program_term_208
  t209 := program_term_209
  t210 := program_term_210
  r210 := program_rulesOf_210
  t211 := program_term_211
  r211 := program_rulesOf_211
  t212 := program_term_212
  r212 := program_rulesOf_212
  t213 := program_term_213
  r213 := program_rulesOf_213
  t214 := program_term_214
  r214 := program_rulesOf_214
  t215 := program_term_215
  r215 := program_rulesOf_215
  t216 := program_term_216
  r216 := program_rulesOf_216
  t217 := program_term_217
  r217 := program_rulesOf_217
  t218 := program_term_218
  r218 := program_rulesOf_218
  t219 := program_term_219
  r219 := program_rulesOf_219
  t220 := program_term_220
  r220 := program_rulesOf_220
  t221 := program_term_221
  r221 := program_rulesOf_221
  t222 := program_term_222
  r222 := program_rulesOf_222
  t223 := program_term_223
  r223 := program_rulesOf_223
  t224 := program_term_224
  r224 := program_rulesOf_224
  t225 := program_term_225
  r225 := program_rulesOf_225
  t226 := program_term_226
  r226 := program_rulesOf_226
  t227 := program_term_227
  r227 := program_rulesOf_227
  t228 := program_term_228
  r228 := program_rulesOf_228
  t229 := program_term_229
  r229 := program_rulesOf_229
  t230 := program_term_230
  r230 := program_rulesOf_230
  t231 := program_term_231
  t232 := program_term_232
  t233 := program_term_233
  t234 := program_term_234
  r234 := program_rulesOf_234
  t235 := program_term_235
  r235 := program_rulesOf_235
  t241 := program_term_241
  t242 := program_term_242
  t245 := program_term_245
  t246 := program_term_246
  t247 := program_term_247
  t249 := program_term_249
  r249 := program_rulesOf_249
  t250 := program_term_250
  r250 := program_rulesOf_250
  t251 := program_term_251
  r251 := program_rulesOf_251
  t252 := program_term_252
  r252 := program_rulesOf_252
  t253 := program_term_253
  r253 := program_rulesOf_253
  t254 := program_term_254
  r254 := program_rulesOf_254
  t255 := program_term_255
  r255 := program_rulesOf_255
  t506 := program_term_506
  t508 := program_term_508
  t567 := program_term_567
  t576 := program_term_576
  t603 := program_term_603
  t623 := program_term_623
  t628 := program_term_628
  t629 := program_term_629
  t630 := program_term_630
  t632 := program_term_632
  t633 := program_term_633
  t654 := program_term_654
  t666 := program_term_666
  t682 := program_term_682
  t687 := program_term_687
  t689 := program_term_689
  t691 := program_term_691
  t692 := program_term_692
  t693 := program_term_693
  t696 := program_term_696
  t699 := program_term_699
  t700 := program_term_700
  t706 := program_term_706
  t707 := program_term_707
  t708 := program_term_708
  t709 := program_term_709
  t710 := program_term_710
  t712 := program_term_712
  t715 := program_term_715
  t727 := program_term_727
  t742 := program_term_742
  t743 := program_term_743
  t747 := program_term_747
  t748 := program_term_748
  t910 := program_term_910
  t914 := program_term_914
  t987 := program_term_987
  t1015 := program_term_1015
  t1017 := program_term_1017
  t1040 := program_term_1040
  t1046 := program_term_1046
  t1073 := program_term_1073
  t1146 := program_term_1146
  t1147 := program_term_1147
  t1148 := program_term_1148
  t1149 := program_term_1149
  r1149 := program_rulesOf_1149
  t1154 := program_term_1154
  r1154 := program_rulesOf_1154
  t1155 := program_term_1155
  r1155 := program_rulesOf_1155
  t1157 := program_term_1157
  r1157 := program_rulesOf_1157
  t1162 := program_term_1162
  r1162 := program_rulesOf_1162
  t1163 := program_term_1163
  r1163 := program_rulesOf_1163
  t1164 := program_term_1164
  r1164 := program_rulesOf_1164
  t1165 := program_term_1165
  r1165 := program_rulesOf_1165
  t1199 := program_term_1199
  r1199 := program_rulesOf_1199
  t1200 := program_term_1200
  r1200 := program_rulesOf_1200
  t1201 := program_term_1201
  r1201 := program_rulesOf_1201
  t1202 := program_term_1202
  r1202 := program_rulesOf_1202
  t1203 := program_term_1203
  r1203 := program_rulesOf_1203
  t1204 := program_term_1204
  r1204 := program_rulesOf_1204
  t1207 := program_term_1207
  r1207 := program_rulesOf_1207
  t1214 := program_term_1214
  r1214 := program_rulesOf_1214
  t1215 := program_term_1215
  r1215 := program_rulesOf_1215
  t1216 := program_term_1216
  r1216 := program_rulesOf_1216
  t1217 := program_term_1217
  r1217 := program_rulesOf_1217
  t1218 := program_term_1218
  r1218 := program_rulesOf_1218
  t1219 := program_term_1219
  r1219 := program_rulesOf_1219
  t1220 := program_term_1220
  r1220 := program_rulesOf_1220
  t1221 := program_term_1221
  r1221 := program_rulesOf_1221
  t1239 := program_term_1239
  r1239 := program_rulesOf_1239
  t1240 := program_term_1240
  r1240 := program_rulesOf_1240
  t1241 := program_term_1241
  r1241 := program_rulesOf_1241
  t1242 := program_term_1242
  r1242 := program_rulesOf_1242
  t1243 := program_term_1243
  r1243 := program_rulesOf_1243
  t1244 := program_term_1244
  r1244 := program_rulesOf_1244
  t1245 := program_term_1245
  r1245 := program_rulesOf_1245
  t1246 := program_term_1246
  r1246 := program_rulesOf_1246
  t1247 := program_term_1247
  r1247 := program_rulesOf_1247
  t1252 := program_term_1252
  r1252 := program_rulesOf_1252
  t1253 := program_term_1253
  r1253 := program_rulesOf_1253
  t1272 := program_term_1272
  r1272 := program_rulesOf_1272
  t1273 := program_term_1273
  r1273 := program_rulesOf_1273
  t1283 := program_term_1283
  r1283 := program_rulesOf_1283
  t1284 := program_term_1284
  r1284 := program_rulesOf_1284
  t1297 := program_term_1297
  r1297 := program_rulesOf_1297
  t1305 := program_term_1305
  t1306 := program_term_1306
  t1307 := program_term_1307
  t1309 := program_term_1309
  t1310 := program_term_1310
  t1312 := program_term_1312
  t1313 := program_term_1313
  t1314 := program_term_1314
  t1315 := program_term_1315
  t1341 := program_term_1341
  t1342 := program_term_1342
  t1343 := program_term_1343
  t1344 := program_term_1344
  t1345 := program_term_1345
  t1346 := program_term_1346
  t1347 := program_term_1347
  t1348 := program_term_1348
  t1349 := program_term_1349
  t1350 := program_term_1350
  t1356 := program_term_1356
  t1357 := program_term_1357
  t1358 := program_term_1358
  t1361 := program_term_1361
  t1362 := program_term_1362
  t1371 := program_term_1371
  t1376 := program_term_1376
  t1377 := program_term_1377
  t1378 := program_term_1378
  t1379 := program_term_1379
  t1413 := program_term_1413
  t1414 := program_term_1414
  t1415 := program_term_1415
  t1416 := program_term_1416
  t1417 := program_term_1417
  t1418 := program_term_1418
  t1421 := program_term_1421
  t1428 := program_term_1428
  t1429 := program_term_1429
  t1430 := program_term_1430
  t1431 := program_term_1431
  t1432 := program_term_1432
  t1433 := program_term_1433
  t1434 := program_term_1434
  t1435 := program_term_1435
  t1438 := program_term_1438
  t1439 := program_term_1439
  t1440 := program_term_1440
  t1441 := program_term_1441
  t1453 := program_term_1453
  t1454 := program_term_1454
  t1455 := program_term_1455
  t1456 := program_term_1456
  t1457 := program_term_1457
  t1458 := program_term_1458
  t1459 := program_term_1459
  t1460 := program_term_1460
  t1461 := program_term_1461
  t1462 := program_term_1462
  t1463 := program_term_1463
  t1465 := program_term_1465
  t1466 := program_term_1466
  t1467 := program_term_1467
  t1486 := program_term_1486
  t1487 := program_term_1487
  t1497 := program_term_1497
  t1498 := program_term_1498
  t1511 := program_term_1511
  t1521 := program_term_1521
  t1523 := program_term_1523
  t1524 := program_term_1524
  t1527 := program_term_1527
  t1533 := program_term_1533
  t1534 := program_term_1534
  t1543 := program_term_1543
  t1548 := program_term_1548
  t1549 := program_term_1549
  t1551 := program_term_1551
  t1552 := program_term_1552
  t1553 := program_term_1553
  t1554 := program_term_1554

end Opt.Proof
