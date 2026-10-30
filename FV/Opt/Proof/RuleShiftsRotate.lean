import FV.Opt.Proof.RuleInfraIcmp
import FV.Opt.Proof.RuleRestEmbedSshr
import FV.Opt.Proof.RuleRestEmbedRotl
import FV.Opt.Proof.RuleRestEmbedRotr
import FV.Opt.Proof.RuleShiftsRotateSem

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option Elab.async false

namespace Opt.Proof

open Isle Isle.Opt Clif
attribute [local implicit_reducible] Ty.width

local macro "rotate_finish " composition:ident : tactic => `(tactic| (
  simp only [Sem.binary, Sem.iadd, Sem.isub, Sem.uextend,
    Sem.rotl, Sem.rotr, Sem.shiftAmt]
  apply $composition
  simp (disch := first | assumption | omega) only
    [Nat.mod_mod, rotate_add_amount, rotate_sub_amount, rotate_extend_amount]))

set_option hygiene false in
local macro "rule_rotate " r:ident composition:ident : tactic => `(tactic| (
  rule_intro $r
  rule_lhs_g hG
  all_goals try opt_den_subst
  all_goals simp only [Sem.shift, Option.some.injEq] at *
  all_goals subst_vars
  all_goals rule_no_iflets
  all_goals rule_rhs_w [Interp.matchAll.eq_1, Interp.matchAll.eq_2]
  all_goals opt_some_subst
  all_goals try opt_den_subst
  all_goals try opt_val_ty_subst
  all_goals try simp only [Val.ty, Nat.lt_irrefl] at *
  all_goals (apply GraphOk.make_val hG (by opt_P); opt_node_x)
  all_goals simp only [Sem.shift, Option.some.injEq] at *
  all_goals subst_vars
  all_goals first | apply some_val_congr | apply val_congr | skip
  all_goals rotate_finish $composition))

theorem ok_rule_shifts_239 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_shifts_239 := by
  rule_rotate rule_shifts_239 rotate_ll

theorem ok_rule_shifts_240 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_shifts_240 := by
  rule_rotate rule_shifts_240 rotate_ll

theorem ok_rule_shifts_241 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_shifts_241 := by
  rule_rotate rule_shifts_241 rotate_rr

theorem ok_rule_shifts_242 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_shifts_242 := by
  rule_rotate rule_shifts_242 rotate_rr

theorem ok_rule_shifts_244 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_shifts_244 := by
  rule_rotate rule_shifts_244 rotate_lr

theorem ok_rule_shifts_245 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_shifts_245 := by
  rule_rotate rule_shifts_245 rotate_lr

theorem ok_rule_shifts_246 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_shifts_246 := by
  rule_rotate rule_shifts_246 rotate_rl

theorem ok_rule_shifts_247 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_shifts_247 := by
  rule_rotate rule_shifts_247 rotate_rl

theorem ok_rule_shifts_259 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_shifts_259 := by
  rule_rotate rule_shifts_259 rotate_rr

theorem ok_rule_shifts_261 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_shifts_261 := by
  rule_rotate rule_shifts_261 rotate_ll

theorem ok_rule_shifts_264 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_shifts_264 := by
  rule_rotate rule_shifts_264 rotate_lr

theorem ok_rule_shifts_266 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_shifts_266 := by
  rule_rotate rule_shifts_266 rotate_rl

-- The first eight original roots all admit these presented constants in either
-- amount position. These are not iconst.i128: the dynamic amount and data may
-- independently be i128. The final four admit the equal-type pair below.
example : ofInst (.iconst .i8 (255#8)) ≠ none ∧
    ofInst (.iconst .i16 (257#16)) ≠ none ∧
    Sem.rotl (Sem.rotl (1#128) (255#8)) (257#16) = 1#128 ∧
    Sem.rotl (Sem.rotl (1#128) (257#16)) (255#8) = 1#128 ∧
    Sem.rotr (Sem.rotr (1#128) (255#8)) (257#16) = 1#128 ∧
    Sem.rotr (Sem.rotr (1#128) (257#16)) (255#8) = 1#128 ∧
    Sem.rotr (Sem.rotl (1#128) (255#8)) (257#16) = (1#128).rotateLeft 126 ∧
    Sem.rotr (Sem.rotl (1#128) (257#16)) (255#8) = (1#128).rotateLeft 2 ∧
    Sem.rotl (Sem.rotr (1#128) (255#8)) (257#16) = (1#128).rotateRight 126 ∧
    Sem.rotl (Sem.rotr (1#128) (257#16)) (255#8) = (1#128).rotateRight 2 := by decide

example : (Val.mk .i128 (1#128)).ty = (Val.mk .i128 (3#128)).ty ∧
    Sem.rotr (Sem.rotr (1#128) (1#128)) (3#128) = (1#128).rotateRight 4 ∧
    Sem.rotl (Sem.rotl (1#128) (1#128)) (3#128) = (1#128).rotateLeft 4 ∧
    Sem.rotr (Sem.rotl (1#128) (1#128)) (3#128) = (1#128).rotateLeft 126 ∧
    Sem.rotl (Sem.rotr (1#128) (1#128)) (3#128) = (1#128).rotateRight 126 := by decide

end Opt.Proof
