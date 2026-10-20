import FV.Opt.Proof.RuleInfraIcmp
import FV.Opt.Proof.RuleExtEmbed

/-!
# Lifting matching extensions through a select

Selection commutes with any function on the selected bits. The graph proof retains the
source operands' common type and the strict extension-width premise, without splitting
any widths or bit-blasting the distribution identity.
-/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000
set_option Elab.async false

namespace Opt.Proof

open Isle Isle.Opt Clif

/-- Applying one function to both selected alternatives is the same as applying it afterward. -/
theorem selects_extend_distrib {cw sw tw : Nat} (c : BitVec cw)
    (f : BitVec sw → BitVec tw) (a b : BitVec sw) :
    Sem.select c (f a) (f b) = f (Sem.select c a b) := by
  simp only [Sem.select]
  split <;> rfl

open Lean Elab Tactic in
elab "selects_extend_noinfo " t:tacticSeq : tactic =>
  withEnableInfoTree false (evalTactic t)

set_option hygiene false in
macro "rule_selects_extend " r:ident : tactic => `(tactic| (
  rule_intro $r
  rule_lhs_g hG
  all_goals rule_no_iflets
  all_goals try opt_den_subst
  opt_cases_val
  all_goals (simp only [Val.ty, Val.bits] at *; subst_vars)
  all_goals rule_rhs_c []
  all_goals opt_some_subst
  all_goals try opt_den_subst
  all_goals (apply GraphOk.make_val hG (by opt_P); opt_node_x)
  all_goals (apply val_congr; exact selects_extend_distrib _ _ _ _)))

set_option maxHeartbeats 4000000 in
/-- `selects.isle:81`: lift two zero extensions through `select`. -/
theorem ok_rule_selects_81 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_81 := by
  selects_extend_noinfo
    rule_selects_extend rule_selects_81

set_option maxHeartbeats 4000000 in
/-- `selects.isle:85`: lift two sign extensions through `select`. -/
theorem ok_rule_selects_85 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_85 := by
  selects_extend_noinfo
    rule_selects_extend rule_selects_85

/-! Inhabited width guards and concrete values on both sides, for both condition outcomes. -/

-- Zero extension keeps the high source bit, rather than interpreting it as a sign bit.
example : Ty.i8.width < Ty.i16.width ∧
    Sem.select (1#32) (Sem.uextend 16 (0x80#8)) (Sem.uextend 16 (0xff#8)) = 0x80#16 ∧
    Sem.uextend 16 (Sem.select (1#32) (0x80#8) (0xff#8)) = 0x80#16 := by decide

example : Ty.i16.width < Ty.i64.width ∧
    Sem.select (0#8) (Sem.uextend 64 (0x8000#16)) (Sem.uextend 64 (0xffff#16)) = 0xffff#64 ∧
    Sem.uextend 64 (Sem.select (0#8) (0x8000#16) (0xffff#16)) = 0xffff#64 := by decide

-- A condition's high bit is truthy; extending a selected negative value fills the high bits.
example : Ty.i8.width < Ty.i32.width ∧
    Sem.select (0x80#8) (Sem.sextend 32 (0x80#8)) (Sem.sextend 32 (0x7f#8)) = 0xffffff80#32 ∧
    Sem.sextend 32 (Sem.select (0x80#8) (0x80#8) (0x7f#8)) = 0xffffff80#32 := by decide

example : Ty.i64.width < Ty.i128.width ∧
    Sem.select (0#16) (Sem.sextend 128 (0#64))
      (Sem.sextend 128 (0x8000000000000000#64)) = 0xffffffffffffffff8000000000000000#128 ∧
    Sem.sextend 128 (Sem.select (0#16) (0#64) (0x8000000000000000#64)) =
      0xffffffffffffffff8000000000000000#128 := by decide

-- Equal widths are permitted by the pure distribution lemma, not by an extension node.
example : Sem.select (0#8) (Sem.uextend 8 (0x80#8)) (Sem.uextend 8 (0xff#8)) = 0xff#8 ∧
    Sem.uextend 8 (Sem.select (0#8) (0x80#8) (0xff#8)) = 0xff#8 := by decide

example : Sem.select (1#8) (Sem.sextend 8 (0x80#8)) (Sem.sextend 8 (0x7f#8)) = 0x80#8 ∧
    Sem.sextend 8 (Sem.select (1#8) (0x80#8) (0x7f#8)) = 0x80#8 := by decide

end Opt.Proof
