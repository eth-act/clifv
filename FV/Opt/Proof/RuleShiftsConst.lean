import FV.Opt.Proof.RuleRestEmbedSshr
import FV.Opt.Proof.RuleRestEmbedRotl
import FV.Opt.Proof.RuleRestEmbedRotr
import FV.Opt.Proof.RuleInfraConst
import FV.Opt.Proof.RuleShiftsConstSem
import FV.Opt.Proof.RuleInfraIcmp
import FV.Opt.Proof.RuleIntRetry

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option Elab.async false

namespace Opt.Proof
open Isle Isle.Opt Clif
attribute [local implicit_reducible] Ty.width

-- Keep all three types symbolic while evaluating the original guards. In
-- particular the constant presentation excludes i128 only for the two amounts. The made
-- constant's type is split on `isInt` on demand (`RuleIntRetry.lean`): at a float type
-- `iconst_u` has no rule.
set_option hygiene false in
local macro "shifts_const_prefix " r:ident : tactic => `(tactic| (
  rule_intro $r
  rule_lhs_g hG
  all_goals try opt_den_subst
  all_goals try opt_val_ty_subst
  opt_cases_val
  all_goals (try simp only [Val.ty, Val.bits] at *; subst_vars)
  all_goals simp (disch := assumption) only [asU64_imm64OfBits] at *
  all_goals rule_iflets_c [shifts_const_mask, shifts_const_sum,
    Interp.matchAll.eq_1, Interp.matchAll.eq_2]
  all_goals simp only [Option.map_some, except_ok_bind', toExt_ok_some,
    ExtResult.ok.injEq, Prod.mk.injEq, V.beq_int, beq_iff_eq,
    beq_true, decide_eq_true_eq, ofClif_bits, Int.ofNat_lt, Int.ofNat_le] at *
  opt_destruct
  all_goals subst_vars
  all_goals simp only [Sem.shift, Option.some.injEq] at *
  all_goals subst_vars
  all_goals opt_split_i128
  all_goals try contradiction
  all_goals opt_int_retry
    rule_rhs_w [Interp.matchAll.eq_1, Interp.matchAll.eq_2, tyInt_ofClif_notInt]
  all_goals opt_some_subst
  all_goals try opt_den_subst
  all_goals (apply GraphOk.make_val hG (by opt_P); opt_node_x)
  all_goals try decide
  all_goals try (show _ < _; assumption)
  all_goals first | apply some_val_congr | apply val_congr | skip
  all_goals simp (disch := assumption) only [ofInt_asI64_low, Sem.binary,
    Sem.uextend, Sem.sextend, BitVec.setWidth_zero,
    BitVec.ofInt_ofNat, shifts_const_mask, shifts_const_sum]
  all_goals first
    | (symm; apply shifts_const_ushr; assumption)
    | (apply shifts_const_ushr; assumption)
    | (symm; apply shifts_const_sshr; assumption)
    | (apply shifts_const_sshr; assumption)
    | (symm; apply shifts_const_ishl_zero; assumption)
    | (apply shifts_const_ishl_zero; assumption)
    | (symm; apply shifts_const_ushr_zero; assumption)
    | (apply shifts_const_ushr_zero; assumption)))

/-- `shifts.isle:161`: repeated logical right shifts below the width. -/
theorem ok_rule_shifts_161 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_161 := by
  shifts_const_prefix rule_shifts_161

/-- `shifts.isle:170`: repeated arithmetic right shifts below the width. -/
theorem ok_rule_shifts_170 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_170 := by
  shifts_const_prefix rule_shifts_170

/-- `shifts.isle:184`: repeated left shifts reaching the width are zero. -/
theorem ok_rule_shifts_184 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_184 := by
  shifts_const_prefix rule_shifts_184

/-- `shifts.isle:193`: repeated logical right shifts reaching the width are zero. -/
theorem ok_rule_shifts_193 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_193 := by
  shifts_const_prefix rule_shifts_193

-- Joint-premise witnesses retain the actual unsigned immediate cast, both
-- presented amount constants, masked wrapping addition, guard and conclusion.
example : ofInst (.iconst .i8 (248#8)) ≠ none ∧
    ofInst (.iconst .i16 (65528#16)) ≠ none ∧
    Rust.asU64 (Rust.band64 (Rust.asU64 (imm64OfBits (248#8))) 7 +
      Rust.band64 (Rust.asU64 (imm64OfBits (65528#16))) 7) = 0 ∧
    (0 : Int) < 8 ∧
    Sem.ushr (Sem.ushr (255#8) (248#8)) (65528#16) = Sem.ushr (255#8) (0#8) := by decide

example : ofInst (.iconst .i8 (255#8)) ≠ none ∧
    ofInst (.iconst .i64 (0x8000000000000000#64)) ≠ none ∧
    Rust.asU64 (Rust.band64 (Rust.asU64 (imm64OfBits (255#8))) 127 +
      Rust.band64 (Rust.asU64 (imm64OfBits (0x8000000000000000#64))) 127) = 127 ∧
    (127 : Int) < 128 ∧
    Sem.sshr (Sem.sshr (0x80000000000000000000000000000000#128) (255#8))
      (0x8000000000000000#64) =
        Sem.sshr (0x80000000000000000000000000000000#128) (127#8) := by decide

example : ofInst (.iconst .i8 (255#8)) ≠ none ∧
    ofInst (.iconst .i16 (129#16)) ≠ none ∧
    Rust.asU64 (Rust.band64 (Rust.asU64 (imm64OfBits (255#8))) 127 +
      Rust.band64 (Rust.asU64 (imm64OfBits (129#16))) 127) = 128 ∧
    (128 : Int) ≤ 128 ∧
    Sem.ishl (Sem.ishl (0xffffffffffffffffffffffffffffffff#128) (255#8)) (129#16) =
      Sem.uextend 128 (0#64) := by decide

example : ofInst (.iconst .i8 (255#8)) ≠ none ∧
    ofInst (.iconst .i64 (0xffffffffffffffff#64)) ≠ none ∧
    Rust.asU64 (Rust.band64 (Rust.asU64 (imm64OfBits (255#8))) 127 +
      Rust.band64 (Rust.asU64 (imm64OfBits (0xffffffffffffffff#64))) 127) = 254 ∧
    (128 : Int) ≤ 254 ∧
    Sem.ushr (Sem.ushr (0xffffffffffffffffffffffffffffffff#128) (255#8))
      (0xffffffffffffffff#64) = Sem.uextend 128 (0#64) := by decide

end Opt.Proof
