import FV.Opt.Proof.RuleSpaceshipInfra

/-! Select-shaped signed and unsigned three-way comparisons. -/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace Opt.Proof
open Isle Isle.Opt Clif
attribute [local implicit_reducible] Ty.width

set_option hygiene false in
macro "spaceship_rule_prefix " r:ident rhs:ident : tactic => `(tactic| (
  rule_intro $r:ident
  rule_no_iflets
  rule_lhs_g hG
  all_goals try opt_den_subst
  all_goals (
    have hs := $rhs:ident hd G P den fr mem hG s3 _ _ _ _ _ _ _ hP3
      n tr3 ws s4 tr4 hev (by opt_den) (by opt_den) m hm
    rw [hs]
    apply some_val_congr)
  all_goals opt_cases_ty
  all_goals try contradiction
  all_goals try simp (disch := decide) only [Ty.width, toInt_eq_iff_ofInt] at *
  all_goals opt_destruct
  all_goals subst_vars
  all_goals symm))

macro "spaceship_math " h:term : tactic => `(tactic|
  simpa (disch := decide) only [Sem.unary, Sem.ineg, Sem.uextend, Sem.sextend,
    BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_eq, BitVec.ofInt_neg,
    BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat, BitVec.natCast_eq_ofNat,
    BitVec.neg_one_eq_allOnes] using $h:term)

macro "spaceship_select_rule " r:ident rhs:ident h:ident : tactic => `(tactic| (
  spaceship_rule_prefix $r:ident $rhs:ident
  all_goals first
    | spaceship_math ($h:ident 8 _ _)
    | spaceship_math ($h:ident 16 _ _)
    | spaceship_math ($h:ident 32 _ _)
    | spaceship_math ($h:ident 64 _ _)
    | spaceship_math ($h:ident 128 _ _)))

-- Negation preserves the i8 comparison result, so these four forms have i8 outputs.
macro "spaceship_narrow_rule " r:ident rhs:ident h:ident : tactic => `(tactic| (
  spaceship_rule_prefix $r:ident $rhs:ident
  all_goals spaceship_math ($h:ident _ _)))

/-- `spaceship.isle:13`: unsigned three-way comparison. -/
theorem ok_rule_spaceship_13 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_13 := by
  spaceship_noinfo
    spaceship_select_rule rule_spaceship_13 spaceship_rhs_unsigned spaceship_select_13

/-- `spaceship.isle:19`: unsigned three-way comparison. -/
theorem ok_rule_spaceship_19 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_19 := by
  spaceship_noinfo
    spaceship_select_rule rule_spaceship_19 spaceship_rhs_unsigned spaceship_select_19

/-- `spaceship.isle:25`: unsigned three-way comparison. -/
theorem ok_rule_spaceship_25 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_25 := by
  spaceship_noinfo
    spaceship_select_rule rule_spaceship_25 spaceship_rhs_unsigned spaceship_select_25

/-- `spaceship.isle:32`: unsigned three-way comparison. -/
theorem ok_rule_spaceship_32 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_32 := by
  spaceship_noinfo
    spaceship_select_rule rule_spaceship_32 spaceship_rhs_unsigned spaceship_select_32

/-- `spaceship.isle:39`: unsigned three-way comparison. -/
theorem ok_rule_spaceship_39 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_39 := by
  spaceship_noinfo
    spaceship_select_rule rule_spaceship_39 spaceship_rhs_unsigned spaceship_select_39

/-- `spaceship.isle:46`: unsigned three-way comparison. -/
theorem ok_rule_spaceship_46 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_46 := by
  spaceship_noinfo
    spaceship_select_rule rule_spaceship_46 spaceship_rhs_unsigned spaceship_select_46

/-- `spaceship.isle:55`: unsigned three-way comparison. -/
theorem ok_rule_spaceship_55 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_55 := by
  spaceship_noinfo
    spaceship_narrow_rule rule_spaceship_55 spaceship_rhs_unsigned spaceship_select_55

/-- `spaceship.isle:59`: unsigned three-way comparison. -/
theorem ok_rule_spaceship_59 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_59 := by
  spaceship_noinfo
    spaceship_select_rule rule_spaceship_59 spaceship_rhs_unsigned spaceship_select_59

/-- `spaceship.isle:65`: unsigned three-way comparison. -/
theorem ok_rule_spaceship_65 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_65 := by
  spaceship_noinfo
    spaceship_narrow_rule rule_spaceship_65 spaceship_rhs_unsigned spaceship_select_65

/-- `spaceship.isle:69`: unsigned three-way comparison. -/
theorem ok_rule_spaceship_69 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_69 := by
  spaceship_noinfo
    spaceship_select_rule rule_spaceship_69 spaceship_rhs_unsigned spaceship_select_69

/-- `spaceship.isle:78`: signed three-way comparison. -/
theorem ok_rule_spaceship_78 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_78 := by
  spaceship_noinfo
    spaceship_select_rule rule_spaceship_78 spaceship_rhs_signed spaceship_select_78

/-- `spaceship.isle:84`: signed three-way comparison. -/
theorem ok_rule_spaceship_84 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_84 := by
  spaceship_noinfo
    spaceship_select_rule rule_spaceship_84 spaceship_rhs_signed spaceship_select_84

/-- `spaceship.isle:90`: signed three-way comparison. -/
theorem ok_rule_spaceship_90 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_90 := by
  spaceship_noinfo
    spaceship_select_rule rule_spaceship_90 spaceship_rhs_signed spaceship_select_90

/-- `spaceship.isle:97`: signed three-way comparison. -/
theorem ok_rule_spaceship_97 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_97 := by
  spaceship_noinfo
    spaceship_select_rule rule_spaceship_97 spaceship_rhs_signed spaceship_select_97

/-- `spaceship.isle:104`: signed three-way comparison. -/
theorem ok_rule_spaceship_104 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_104 := by
  spaceship_noinfo
    spaceship_select_rule rule_spaceship_104 spaceship_rhs_signed spaceship_select_104

/-- `spaceship.isle:111`: signed three-way comparison. -/
theorem ok_rule_spaceship_111 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_111 := by
  spaceship_noinfo
    spaceship_select_rule rule_spaceship_111 spaceship_rhs_signed spaceship_select_111

/-- `spaceship.isle:120`: signed three-way comparison. -/
theorem ok_rule_spaceship_120 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_120 := by
  spaceship_noinfo
    spaceship_narrow_rule rule_spaceship_120 spaceship_rhs_signed spaceship_select_120

/-- `spaceship.isle:124`: signed three-way comparison. -/
theorem ok_rule_spaceship_124 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_124 := by
  spaceship_noinfo
    spaceship_select_rule rule_spaceship_124 spaceship_rhs_signed spaceship_select_124

/-- `spaceship.isle:130`: signed three-way comparison. -/
theorem ok_rule_spaceship_130 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_130 := by
  spaceship_noinfo
    spaceship_narrow_rule rule_spaceship_130 spaceship_rhs_signed spaceship_select_130

/-- `spaceship.isle:134`: signed three-way comparison. -/
theorem ok_rule_spaceship_134 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_134 := by
  spaceship_noinfo
    spaceship_select_rule rule_spaceship_134 spaceship_rhs_signed spaceship_select_134

end Opt.Proof
