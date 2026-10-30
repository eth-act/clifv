import FV.Opt.Proof.RuleIcmpEmbed2

/-!
# `opts/icmp.isle` (part 2): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleIcmpEmbed.lean`, `RuleIcmpEmbed2.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- A `select` condition extended to a wider type is truthy iff the original is
(`uextend` keeps the value). -/
theorem select_uextend_of_lt {v u w : Nat} (h : v < u) (c : BitVec v) (x y : BitVec w) :
    Clif.Sem.select (Clif.Sem.uextend u c) x y = Clif.Sem.select c x y := by
  have hz : (c.zeroExtend u != 0#u) = (c != 0#v) := by
    have hlt : c.toNat < 2 ^ u := Nat.lt_of_lt_of_le c.isLt (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt h))
    have he : (BitVec.setWidth u c == 0#u) = (c == 0#v) := by
      rw [Bool.eq_iff_iff]
      simp only [beq_iff_eq, BitVec.toNat_eq, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
        Nat.zero_mod, Nat.mod_eq_of_lt hlt]
    simp only [bne, BitVec.zeroExtend_eq_setWidth, he]
  have ht : Clif.Sem.truthy (Clif.Sem.uextend u c) = Clif.Sem.truthy c := hz
  unfold Clif.Sem.select
  rw [ht]

/-- `rule_bits` with `select_uextend_of_lt` tried before the type split. Without it, `icmp.isle:84`
splits every `Ty`/`IntCC` variable (2,940 goals, all this identity) and `kbv` searches each one:
93 G heartbeats, an hour, not counted in `maxHeartbeats`; with it, 0.42 G. -/
macro "rule_bits_su" : tactic => `(tactic| (
  try simp (disch := assumption) only [asU64_imm64OfBits, Int.natCast_eq_zero, Int.natCast_inj,
    toNat_eq_iff_ofNat, ofInt_imm64OfBits, bne_iff_ne, ne_eq, toNat_eq_zero_iff] at *
  opt_destruct
  all_goals subst_vars
  all_goals first
    | (simp only [val_some_eq, val_mk_same]; done)
    | rfl
    | (first | apply some_val_congr | apply val_congr | skip
       first
         | (exact select_uextend_of_lt (by assumption) _ _ _)
         | (simp only [Clif.Sem.binary, Clif.Sem.unary, Clif.Sem.iadd, Clif.Sem.imul, Clif.Sem.band,
              Clif.Sem.bor, Clif.Sem.bxor]
            ac_rfl)
         | (opt_cases_ty <;> opt_widths <;> (try sem_simp) <;>
             first | ac_rfl | kbv))))

set_option hygiene false in
/-- `rule_auto` with `rule_bits_su`. -/
macro "rule_auto_su " r:ident : tactic => `(tactic| (
  rule_intro $r
  rule_no_iflets
  rule_lhs hG
  all_goals (rule_rhs []; first
    | (try dsimp only
       apply Valuation.le_trans hle1 hle3
       opt_rw_lhs
       rule_bits_su)
    | (try dsimp only
       apply GraphOk.make_val hG (by opt_P)
       opt_node
       all_goals rule_bits_su))))

/-- `icmp.isle:33`. -/
theorem ok_rule_icmp_33 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_33 := by
  first | rule_auto_c rule_icmp_33 | rule_auto_ci rule_icmp_33

/-- `icmp.isle:35`. -/
theorem ok_rule_icmp_35 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_35 := by
  first | rule_auto_c rule_icmp_35 | rule_auto_ci rule_icmp_35

/-- `icmp.isle:41`. -/
theorem ok_rule_icmp_41 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_41 := by
  first | rule_auto rule_icmp_41 | rule_auto_b rule_icmp_41 | rule_auto_i rule_icmp_41 | rule_auto_z rule_icmp_41

/-- `icmp.isle:43`. -/
theorem ok_rule_icmp_43 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_43 := by
  first | rule_auto rule_icmp_43 | rule_auto_b rule_icmp_43 | rule_auto_i rule_icmp_43 | rule_auto_z rule_icmp_43

/-- `icmp.isle:84`. -/
theorem ok_rule_icmp_84 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_84 := by
  rule_auto_su rule_icmp_84

/-- `icmp.isle:96`. -/
theorem ok_rule_icmp_96 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_96 := by
  first | rule_auto rule_icmp_96 | rule_auto_b rule_icmp_96 | rule_auto_i rule_icmp_96 | rule_auto_z rule_icmp_96

/-- `icmp.isle:104`. -/
theorem ok_rule_icmp_104 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_104 := by
  first | rule_auto rule_icmp_104 | rule_auto_b rule_icmp_104 | rule_auto_i rule_icmp_104 | rule_auto_z rule_icmp_104

/-- `icmp.isle:108`. -/
theorem ok_rule_icmp_108 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_108 := by
  first | rule_auto rule_icmp_108 | rule_auto_b rule_icmp_108 | rule_auto_i rule_icmp_108 | rule_auto_z rule_icmp_108

/-- `icmp.isle:112`. -/
theorem ok_rule_icmp_112 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_112 := by
  first | rule_auto rule_icmp_112 | rule_auto_b rule_icmp_112 | rule_auto_i rule_icmp_112 | rule_auto_z rule_icmp_112

/-- `icmp.isle:116`. -/
theorem ok_rule_icmp_116 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_116 := by
  first | rule_auto rule_icmp_116 | rule_auto_b rule_icmp_116 | rule_auto_i rule_icmp_116 | rule_auto_z rule_icmp_116

/-- `icmp.isle:120`. -/
theorem ok_rule_icmp_120 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_120 := by
  first | rule_auto_d rule_icmp_120 [tySmin_ofClif, tySmax_ofClif] | rule_auto_di rule_icmp_120 [tySmin_ofClif, tySmax_ofClif]

end Opt.Proof
