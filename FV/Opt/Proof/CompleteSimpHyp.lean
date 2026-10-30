import FV.Opt.HandRules
import FV.Opt.Proof.RulesProv

/-!
# The rule-set obligations of the completeness of simplify (M1, #24)

`Opt.SimplifySound`/`Opt.SkeletonSound` (`FV/Opt/Proof/Sem.lean`) are what the *soundness* of the
simplify stage needs of a rule set. Its *completeness* (`Opt.simplify_complete`,
`FV/Opt/Proof/CompleteSimp.lean`: the validator `Opt.simpOk` accepts the pass's output) needs only
that the rules pass values on: `Opt.SimpRulesProv`/`Opt.SkelRulesProv`
(`FV/Opt/Proof/RulesProv.lean`). The pass's guards (`Opt.optimizeAt`, `Opt.skelMake`,
`Opt.runSkel`) do the rest: `make` hash-conses and simplifies only well-typed nodes over
placeable values, candidates must be known values of the root's type, and a skeleton candidate
must be `Opt.skelCandOk` — which, for values the rules were given, is `Opt.SkelCandOk` below.

Discharged here: both obligations for the hand rules' skeleton part (`HandRules.simplifySkeleton`
has no rules) and for the empty rule set (`Opt.noRules`, non-vacuity). `SimpRulesProv` for
`HandRules.simplify`: `Opt.simpRulesProv_hand` (`FV/Opt/Proof/CompleteSimpHand.lean`); for the
exported Cranelift rules: `Opt.simpRulesProv_isle`, `Opt.skelRulesProv_isle`
(`FV/Opt/Proof/IsleProv.lean`).
-/

namespace Opt

open Clif

/-- `n` is a well-typed pure node over `R`-values whose result type is `t`. -/
def NodeIn (ty : ValueId → Option Ty) (fn : Function) (R : ValueId → Prop) (t : Option Ty)
    (n : Inst) : Prop :=
  isPure n = true ∧ pureTyped ty fn n = true ∧ SState.nodeTy n = t ∧ ∀ y ∈ operands n, R y

/-- The values a skeleton instruction or terminator reads (all its operands). -/
def skelOps : Isle.Opt.SkelInst → List ValueId
  | .inst i => operands i
  | .term t => termOperands t

/-- A replacement instruction: over `R`, not pure, not reading a link-time symbol. -/
def SkelInstOk (R : ValueId → Prop) (j : Inst) : Prop :=
  isPure j = false ∧ notSym j = true ∧ ∀ y ∈ operands j, R y

/-- A replacement terminator of `t`: a branch over `R` whose block calls go where `t`'s go, with
arguments of the same types, and whose `br_table` index is an `i32`. -/
def SkelTermOk (ty : ValueId → Option Ty) (R : ValueId → Prop) (t t' : Terminator) : Prop :=
  isBranch t' = true ∧ (∀ y ∈ termOperands t', R y) ∧
    (∀ bc' ∈ termCalls t', ∃ bc ∈ termCalls t, bc'.block = bc.block ∧ bc'.args.map ty = bc.args.map ty) ∧
    ∀ x d tb, t' = .brTable x d tb → ty x = some .i32

/-- A skeleton candidate the driver may apply mentions only `R` values (module doc). -/
def SkelCandOk (ty : ValueId → Option Ty) (R : ValueId → Prop) :
    Isle.Opt.SkelInst → Isle.Opt.SkelSimp → Prop
  | .inst _, .removeWithVal v => R v
  | .inst _, .replace (.inst j) => SkelInstOk R j
  | .inst _, .replaceBranchCond c => R c
  | .inst _, .replaceWithTwo (.inst a) (.inst b) => SkelInstOk R a ∧ SkelInstOk R b
  | .term t, .replace (.term t') => SkelTermOk ty R t t'
  | .term _, .replaceBranchCond c => R c
  | .term t, .replaceWithTwo (.inst a) (.term t') => SkelInstOk R a ∧ SkelTermOk ty R t t'
  | _, _ => True

/-- The empty rule set (no candidates). -/
def noRules : SimplifyFn := fun _ _ _ st _ => .ok ([], [], st)

theorem simpRulesProv_noRules : SimpRulesProv noRules := by
  intro σ enodes typeOf make P Q _ _ s v cands names s' hP _ h
  simp only [noRules, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -, rfl⟩ := h
  exact ⟨hP, fun _ h => h, fun c hc => by cases hc⟩

/-- The hand rules have no skeleton rules. -/
theorem skelRulesProv_hand : SkelRulesProv HandRules.simplifySkeleton := by
  intro σ enodes typeOf make trapBlock P Q QB _ _ s i cands names s' hP _ h
  simp only [HandRules.simplifySkeleton, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -, rfl⟩ := h
  exact ⟨hP, fun _ h => h, fun c hc => by cases hc⟩

end Opt
