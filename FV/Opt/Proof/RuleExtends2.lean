import FV.Opt.Proof.RuleRestEmbedSshr
import FV.Opt.Proof.RuleRestEmbedRotl
import FV.Opt.Proof.RuleRestEmbedRotr
import FV.Opt.Proof.RuleIntSplit

/-!
# Comparisons of sign extensions against zero

The constructor's masked zero and signed re-extension evaluate before graph construction.
Preserve the non-i128 facts used by `fitsIn64_ofClif`, then specialize widths before the
right-hand side grows. Specialize the condition code before evaluating its if-let, so the
state-preserving helper reduces and the valuation chain remains connected.
At a float operand type the right-hand `iconst_s` has no rule (`tyInt_ofClif_f32`/`_f64`) and
the evaluation throws; a float extension result type (bit-level, like the integer type of its
width) adds arms, hence the heartbeat budgets.
The original `RuleOk` statements and premises are unchanged.
-/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000
set_option Elab.async false

namespace Opt.Proof

open Isle Isle.Opt Clif

-- `Sem.icmp` returns `BitVec 8`; implicit argument checks must also see `.i8.width = 8`.
attribute [local implicit_reducible] Ty.width

theorem extends_zero_mask (x : Int) : Rust.band64 (Rust.asU64 0) x = 0 := by
  simp [Rust.band64, Rust.asU64]

theorem extends_zero_sext (w : Nat) : Rust.sext w 0 = 0 := by
  simp [Rust.sext]

attribute [local opt_imm] extends_zero_mask extends_zero_sext

open Lean Elab Tactic in
elab "extends_noinfo " t:tacticSeq : tactic => withEnableInfoTree false (evalTactic t)

set_option hygiene false in
macro "rule_extends_zero " r:ident : tactic => `(tactic| (
  rule_intro $r
  rule_lhs hG
  all_goals try opt_val_ty_subst
  opt_cases_val
  all_goals opt_split_i128
  opt_cases_ty
  opt_widths
  all_goals simp only [Ty.width, Nat.reduceLT] at *
  all_goals try contradiction
  all_goals (first | rule_no_iflets | rule_iflets_c [Rust.signedCondCode])
  all_goals rule_rhs_y [reduceCtorEq, Int.reduceBEq, tyInt_ofClif_f32, tyInt_ofClif_f64]
  all_goals opt_some_subst
  all_goals try contradiction
  all_goals rule_finish_x))

set_option maxHeartbeats 12000000 in
/-- `extends.isle:40`: equality to zero after sign extension. -/
theorem ok_rule_extends_40 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_40 := by
  extends_noinfo rule_extends_zero rule_extends_40

set_option maxHeartbeats 12000000 in
/-- `extends.isle:42`: inequality to zero after sign extension. -/
theorem ok_rule_extends_42 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_42 := by
  extends_noinfo rule_extends_zero rule_extends_42

set_option maxHeartbeats 48000000 in
/-- `extends.isle:44`: signed comparisons to zero after sign extension. -/
theorem ok_rule_extends_44 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_44 := by
  extends_noinfo rule_extends_zero rule_extends_44

/-! Concrete constructor and matching-guard witnesses, with zero and signed extrema. -/

example : Rust.band64 (Rust.asU64 0) (-1) = 0 := by decide
example : Rust.i64SextendU64 (CTy.ofClif .i8) 0 = .ok 0 ∧
    Rust.i64SextendU64 (CTy.ofClif .i64) 0 = .ok 0 := ⟨rfl, rfl⟩
example : Rust.sext 0 0 = 0 ∧ Rust.sext 128 0 = 0 := by decide

example : Ty.i16 ≠ .i128 ∧ Ty.i8.width < Ty.i16.width ∧ (0#16).toInt = 0 ∧
    Sem.icmp .eq (Sem.sextend 16 (0#8)) (0#16) = 1#8 ∧
    Sem.icmp .eq (0#8) (0#8) = 1#8 := by decide

example : Ty.i64 ≠ .i128 ∧ Ty.i32.width < Ty.i64.width ∧ (0#64).toInt = 0 ∧
    Sem.icmp .ne (Sem.sextend 64 (0x80000000#32)) (0#64) = 1#8 ∧
    Sem.icmp .ne (0x80000000#32) (0#32) = 1#8 := by decide

example : Ty.i32 ≠ .i128 ∧ Ty.i8.width < Ty.i32.width ∧ (0#32).toInt = 0 ∧
    Rust.signedCondCode .slt = some .slt ∧
    Sem.icmp .slt (Sem.sextend 32 (0x80#8)) (0#32) = 1#8 ∧
    Sem.icmp .slt (0x80#8) (0#8) = 1#8 := by decide

example :
    [(IntCC.sge, 0#16), (.sgt, 0x7fff#16), (.sle, 0x8000#16)].map
      (fun (cc, x) => (Rust.signedCondCode cc,
        Sem.icmp cc (Sem.sextend 64 x) (0#64), Sem.icmp cc x (0#16))) =
    [(some .sge, 1#8, 1#8), (some .sgt, 1#8, 1#8), (some .sle, 1#8, 1#8)] := by decide

end Opt.Proof
