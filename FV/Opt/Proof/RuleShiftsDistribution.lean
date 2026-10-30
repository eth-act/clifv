import FV.Opt.Proof.RuleInfraIcmp
import FV.Opt.Proof.RuleRestEmbedSshr
import FV.Opt.Proof.RuleRestEmbedRotl
import FV.Opt.Proof.RuleRestEmbedRotr

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option Elab.async false
set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt Clif
attribute [local implicit_reducible] Ty.width

/-- A left shift is modular multiplication, even when subtraction wraps. -/
private theorem shift_sub_distrib {w u : Nat} (x y : BitVec w) (z : BitVec u) :
    Sem.isub (Sem.ishl x z) (Sem.ishl y z) = Sem.ishl (Sem.isub x y) z := by
  simp only [Sem.isub, Sem.ishl]
  calc
    (x <<< Sem.shiftAmt w z) - (y <<< Sem.shiftAmt w z) =
        BitVec.twoPow w (Sem.shiftAmt w z) * x -
          BitVec.twoPow w (Sem.shiftAmt w z) * y := by
      simp only [BitVec.shiftLeft_eq_mul_twoPow, BitVec.mul_comm]
    _ = BitVec.twoPow w (Sem.shiftAmt w z) * (x - y) := BitVec.mul_sub.symm
    _ = (x - y) <<< Sem.shiftAmt w z := BitVec.twoPow_mul_eq_shiftLeft _ _

/-- `shifts.isle:315`: distribute a shared shift over modular subtraction. -/
theorem ok_rule_shifts_315 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_315 := by
  rule_intro rule_shifts_315
  rule_lhs_g hG
  all_goals rule_no_iflets
  all_goals try opt_den_subst
  all_goals simp only [Sem.shift, Option.some.injEq] at *
  opt_destruct
  all_goals subst_vars
  all_goals rule_rhs_c [Interp.matchAll.eq_1, Interp.matchAll.eq_2]
  all_goals opt_some_subst
  all_goals try opt_den_subst
  all_goals (apply GraphOk.make_val hG (by opt_P); opt_node_x)
  all_goals try decide
  all_goals apply val_congr
  all_goals simp only [Sem.binary, Sem.shift, Option.some.injEq]
  all_goals exact shift_sub_distrib _ _ _

-- The helper is inhabited with different data/amount widths and a wrapped shift count.
example : Sem.isub (Sem.ishl (127#8) (9#16)) (Sem.ishl (1#8) (9#16)) = 252#8 := by
  decide

-- The original root also applies to i128 data and a dynamic i128 shift amount.
example :
    Sem.isub (Sem.ishl (0#128) (127#128)) (Sem.ishl (1#128) (127#128)) =
      0x80000000000000000000000000000000#128 ∧
    Sem.ishl (Sem.isub (0#128) (1#128)) (127#128) =
      0x80000000000000000000000000000000#128 := by decide

end Opt.Proof
