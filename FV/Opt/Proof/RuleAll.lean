import FV.Opt.Proof.RuleArith
import FV.Opt.Proof.RuleCprop
import FV.Opt.Proof.RuleBitops1
import FV.Opt.Proof.RuleBitops2
import FV.Opt.Proof.RuleBitops3
import FV.Opt.Proof.RuleBitops4
import FV.Opt.Proof.RuleBitops5
import FV.Opt.Proof.RuleBitops6
import FV.Opt.Proof.RuleBitops7
import FV.Opt.Proof.RuleIcmp1
import FV.Opt.Proof.RuleIcmp2
import FV.Opt.Proof.RuleIcmp3
import FV.Opt.Proof.RuleIcmp4
import FV.Opt.Proof.RuleIcmp5
import FV.Opt.Proof.RuleIcmp6
import FV.Opt.Proof.RuleIcmp7
import FV.Opt.Proof.RuleIcmp8
import FV.Opt.Proof.RuleSelects1
import FV.Opt.Proof.RuleSelects2
import FV.Opt.Proof.RuleSelects3
import FV.Opt.Proof.RuleSelects4
import FV.Opt.Proof.RuleSelects5
import FV.Opt.Proof.RuleSelects6
import FV.Opt.Proof.RuleExtends
import FV.Opt.Proof.RuleShifts1
import FV.Opt.Proof.RuleShifts2
import FV.Opt.Proof.RuleSpaceship
import FV.Opt.Proof.RuleIcmp9
import FV.Opt.Proof.RuleShifts3
import FV.Opt.Proof.RuleShifts4
import FV.Opt.Proof.RuleShifts5
import FV.Opt.Proof.RuleArith2
import FV.Opt.Proof.RuleArith3
import FV.Opt.Proof.RuleArith4
import FV.Opt.Proof.RuleArith5
import FV.Opt.Proof.RuleCprop2
import FV.Opt.Proof.RuleRemat
import FV.Opt.Proof.RuleArith6
import FV.Opt.Proof.RuleArith7
import FV.Opt.Proof.RuleSelects7
import FV.Opt.Proof.RuleBitops8
import FV.Opt.Proof.RuleCprop3
import FV.Opt.Proof.RuleCprop4
import FV.Opt.Proof.RuleSelects8
import FV.Opt.Proof.RuleIcmp10
import FV.Opt.Proof.RuleIcmp12
import FV.Opt.Proof.RuleIcmp13
import FV.Opt.Proof.RuleArith8
import FV.Opt.Proof.RuleSkeleton
import FV.Opt.Proof.RuleSkeleton2
import FV.Opt.Proof.RuleSkeleton4
import FV.Opt.Optimize

/-!
# The proven allow-list is sound

`simplifyRulesCorrect_proven`: every `simplify` rule of `Isle.Opt.program` whose id is in
`Opt.provenSimplifyRules` is `RuleOk`. `simplifySound_proven`: the Cranelift rule set with the
`proven` allow-list is a sound rule set (`Opt.SimplifySound`), the obligation the `simplify`
pass proof takes (`Opt.Config.simplifyFn` with `ruleAllow := .proven`). The same for
`simplify_skeleton` (`Opt.provenSkeletonRules`, `SkelRuleOk`): `skeletonSound_proven`.

The proof walks the generated rule list `R.«simplify»` (a list literal of the rule constants
`rule_X`) with `allowed_ok%`: an allow-listed `rule_X` takes the per-rule theorem
`ok_rule_X data_program` (over an abstract program with `Data p`), any other rule takes
`allow rule_X.id = false` by `rfl`. The proof term is built directly and checked by the kernel
only (one allow-list lookup on `Nat` literals per skipped rule); no elaborator `rfl`/`decide`
runs over the generated rule data. A new family: import its module and append its ids to
`Opt.provenSimplifyRules` (or `Opt.provenSkeletonRules`); nothing in this file lists rules.
-/

namespace Opt.Proof

open Lean Meta Elab Term
open Isle Isle.Opt

/-- `ok r` for every rule `r` of `rs` whose id `allow` accepts. -/
def AllowedOk (ok : Rule → Prop) (allow : RuleId → Bool) (rs : List Rule) : Prop :=
  ∀ r ∈ rs, allow r.id = true → ok r

theorem AllowedOk.nil {ok : Rule → Prop} {allow : RuleId → Bool} : AllowedOk ok allow [] :=
  fun _ h => nomatch h

theorem AllowedOk.take {ok : Rule → Prop} {allow : RuleId → Bool} {r : Rule} {rs : List Rule}
    (h : ok r) (t : AllowedOk ok allow rs) : AllowedOk ok allow (r :: rs) := by
  intro q hq ha
  cases hq with
  | head => exact h
  | tail _ hq => exact t q hq ha

theorem AllowedOk.skip {ok : Rule → Prop} {allow : RuleId → Bool} {r : Rule} {rs : List Rule}
    (h : allow r.id = false) (t : AllowedOk ok allow rs) : AllowedOk ok allow (r :: rs) := by
  intro q hq ha
  cases hq with
  | head => exact absurd (h.symm.trans ha) Bool.false_ne_true
  | tail _ hq => exact t q hq ha

/-- `allow` as a function, run by the compiler (decides which rules `allowed_ok%` takes; the
kernel re-checks every skip). -/
private unsafe def evalAllowUnsafe (allow : Lean.Expr) : TermElabM (RuleId → Bool) := do
  evalExpr (RuleId → Bool) (← mkArrow (Lean.mkConst ``RuleId) (Lean.mkConst ``Bool)) allow

@[implemented_by evalAllowUnsafe]
private opaque evalAllow (allow : Lean.Expr) : TermElabM (RuleId → Bool)

/-- `allowed_ok% ok allow rs`: a proof of `AllowedOk ok allow rs`, for a rule list `rs` that
the kernel reduces to a list literal of rule constants (`program.rulesOf t` reduces to the
generated `R.«t»`). Each rule `rule_X` that `allow` accepts (`allow` evaluated by compiled
code) needs the theorem `Opt.Proof.ok_rule_X`, applied to `data_program`; the others are
skipped with `allow rule_X.id = false` by `rfl`. The term is not checked by the elaborator:
the kernel checks it (the skips by `Nat` literal reduction) when the declaration is added. -/
syntax (name := allowedOkStx) "allowed_ok% " term:max term:max term:max : term

@[term_elab allowedOkStx] def elabAllowedOk : TermElab := fun stx _ => do
  let `(allowed_ok% $okStx $allowStx $rsStx) := stx | throwUnsupportedSyntax
  let ok ← elabTerm okStx (some (← mkArrow (Lean.mkConst ``Rule) (mkSort .zero)))
  let allow ← elabTerm allowStx (some (← mkArrow (Lean.mkConst ``RuleId) (Lean.mkConst ``Bool)))
  let rs ← elabTerm rsStx (some (mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``Rule)))
  synthesizeSyntheticMVarsNoPostponing
  let ok ← instantiateMVars ok
  let allow ← instantiateMVars allow
  let rs ← instantiateMVars rs
  if ok.hasMVar || allow.hasMVar || rs.hasMVar then
    throwError "allowed_ok%: the arguments must be fully elaborated"
  let env ← getEnv
  let whnfK (e : Lean.Expr) : TermElabM Lean.Expr :=
    ofExceptKernelException (Kernel.whnf env {} e)
  -- The cells `rule :: tail` of the list, outermost first.
  let mut cells : Array (Lean.Expr × Lean.Expr) := #[]
  let mut e ← whnfK rs
  while e.isAppOfArity ``List.cons 3 do
    let tl := e.appArg!
    cells := cells.push (e.appFn!.appArg!, tl)
    e ← if tl.isAppOfArity ``List.cons 3 || tl.isAppOfArity ``List.nil 1 then pure tl
      else whnfK tl
  unless e.isAppOfArity ``List.nil 1 do
    throwError "allowed_ok%: {rs} does not reduce to a list literal"
  let allowFn ← evalAllow allow
  let data := Lean.mkConst ``data_program
  let mut prf := mkApp2 (Lean.mkConst ``AllowedOk.nil) ok allow
  for (r, tl) in cells.reverse do
    let .const rn [] := r
      | throwError "allowed_ok%: {r} in {rs} is not a rule constant"
    let id ← whnfK (mkApp (Lean.mkConst ``Rule.id) r)
    let some id := id.rawNatLit?
      | throwError "allowed_ok%: the id of {rn} does not reduce to a literal: {id}"
    if allowFn id then
      let thm := `Opt.Proof ++ Name.mkSimple ("ok_" ++ rn.getString!)
      unless env.contains thm do
        throwError "allowed_ok%: {rn} is allow-listed but there is no theorem {thm}"
      prf := mkAppN (Lean.mkConst ``AllowedOk.take) #[ok, allow, r, tl, ← mkAppM thm #[data], prf]
    else
      let h := mkApp2 (Lean.mkConst ``Eq.refl [.one]) (Lean.mkConst ``Bool)
        (Lean.mkConst ``Bool.false)
      prf := mkAppN (Lean.mkConst ``AllowedOk.skip) #[ok, allow, r, tl, h, prf]
  mkExpectedTypeHint prf (mkApp3 (Lean.mkConst ``AllowedOk) ok allow rs)

/-- Every allow-listed `simplify` rule is `RuleOk`. -/
theorem simplify_allowed_ok :
    AllowedOk (RuleOk program) RuleAllow.proven.pred (program.rulesOf T.«simplify».id) :=
  allowed_ok% (RuleOk program) RuleAllow.proven.pred (program.rulesOf T.«simplify».id)

theorem simplifyRulesCorrect_proven : SimplifyRulesCorrect program RuleAllow.proven.pred :=
  simplify_allowed_ok

theorem simplify_rules_length : (program.rulesOf T.«simplify».id).length = 1281 := by
  decide +kernel

/-- **The proven rule set is sound.** -/
theorem simplifySound_proven : SimplifySound (RuleSetId.fnWith .proven .cranelift) :=
  simplifySound _ simplifyRulesCorrect_proven (by rw [simplify_rules_length]; decide)

/-- Every allow-listed `simplify_skeleton` rule is `SkelRuleOk` (`Opt.provenSkeletonRules`,
theorems in `FV/Opt/Proof/RuleSkeleton.lean`, `RuleSkeleton2.lean`, `RuleSkeleton4.lean`). -/
theorem skeleton_allowed_ok : AllowedOk (SkelRuleOk program) RuleAllow.proven.pred
    (program.rulesOf T.«simplify_skeleton».id) :=
  allowed_ok% (SkelRuleOk program) RuleAllow.proven.pred (program.rulesOf T.«simplify_skeleton».id)

theorem skeletonRulesCorrect_proven : SkeletonRulesCorrect program RuleAllow.proven.pred :=
  skeleton_allowed_ok

theorem skeleton_rules_length : (program.rulesOf T.«simplify_skeleton».id).length = 39 := by
  decide +kernel

/-- **The proven skeleton rule set is sound** (the obligation `simplify`'s pass proof takes for
`Opt.Config.skeletonFn` with `ruleAllow := .proven`). -/
theorem skeletonSound_proven : SkeletonSound (RuleSetId.skeletonFnWith .proven .cranelift) :=
  skeletonSound _ skeletonRulesCorrect_proven (by rw [skeleton_rules_length]; decide)

end Opt.Proof
