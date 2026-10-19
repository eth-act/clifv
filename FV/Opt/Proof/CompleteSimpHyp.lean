import FV.Opt.Proof.SimpLoop
import FV.Opt.Proof.CompleteLicm
import FV.Opt.HandRules

/-!
# The syntactic obligations of a rule set for the completeness of simplify (M1, #24)

`Opt.SimplifySound`/`Opt.SkeletonSound` (`FV/Opt/Proof/Sem.lean`) are what the *soundness* of the
simplify stage needs of a rule set. Its *completeness* (`Opt.simplify_complete`,
`FV/Opt/Proof/CompleteSimp.lean`: the validator `Opt.simpOk` accepts the pass's output) needs
syntactic facts instead, stated here in the same parametric style (the graph state `σ` is
abstract, so a rule set can only change it through `make`):

* `Opt.SimpRulesOk rules`: given a set `R` of values closed under the operands of their nodes
  (`enodes`, every node a well-typed pure node), and a `make` that, for a well-typed pure node over
  `R`, returns a value of the node's type in `R`, the rules call `make` only on well-typed pure
  nodes over `R`, and every candidate is the root itself or a value of `R` of the root's type.
  The driver instantiates `R` with the values it can place where the root is defined (never a
  later leaf of the block, a removed value, or the root itself). The root is not in the
  hash-consing table while its rules run (`Opt.pureBest`), so `make` never returns it.
* `Opt.SkelRulesOk skel`: the same closure for `simplify_skeleton`, and each candidate the
  driver applies (`Opt.SkelCandOk`) mentions only `R` values; replacement instructions are not
  pure and read no link-time symbol; a new terminator is a branch whose block calls go to blocks
  the original terminator branches to, with arguments of the same types (and an `i32`
  `br_table` index).

Discharged here: `SkelRulesOk` for the hand rules (`HandRules.simplifySkeleton` has no rules),
`SimpRulesOk` for the empty rule set (`Opt.noRules`, non-vacuity). `SimpRulesOk` for
`HandRules.simplify`: `Opt.simpRulesOk_hand` (`FV/Opt/Proof/CompleteSimpHand.lean`).
-/

namespace Opt

open Clif

/-- `n` is a well-typed pure node over `R`-values whose result type is `t`. -/
def NodeIn (ty : ValueId → Option Ty) (fn : Function) (R : ValueId → Prop) (t : Option Ty)
    (n : Inst) : Prop :=
  isPure n = true ∧ pureTyped ty fn n = true ∧ SState.nodeTy n = t ∧ ∀ y ∈ operands n, R y

/-- The state moves on: `R` and the types only grow. -/
def RGrows {σ : Type} (typeOf : σ → ValueId → Option Ty) (R : σ → ValueId → Prop) (st st' : σ) :
    Prop :=
  (∀ x, R st x → R st' x) ∧ ∀ x t, typeOf st x = some t → typeOf st' x = some t

/-- The graph premise: every node of an `R`-value is a well-typed pure node over `R` of the
value's type. -/
def GraphIn {σ : Type} (enodes : σ → ValueId → List Inst) (typeOf : σ → ValueId → Option Ty)
    (fn : Function) (P : σ → Prop) (R : σ → ValueId → Prop) : Prop :=
  ∀ st x, P st → R st x → ∀ n ∈ enodes st x, NodeIn (typeOf st) fn (R st) (typeOf st x) n

/-- The `make` premise: on a well-typed pure node over `R` it keeps `P`, grows, and returns a
value of the node's type in `R` or in `X`. -/
def MakeIn {σ : Type} (make : σ → Inst → ValueId × σ) (typeOf : σ → ValueId → Option Ty)
    (fn : Function) (P : σ → Prop) (R : σ → ValueId → Prop) (X : ValueId → Prop) : Prop :=
  ∀ st n, P st → NodeIn (typeOf st) fn (R st) (SState.nodeTy n) n →
    P (make st n).2 ∧ RGrows typeOf R st (make st n).2 ∧
      (R (make st n).2 (make st n).1 ∨ X (make st n).1) ∧
      typeOf (make st n).2 (make st n).1 = SState.nodeTy n

/-- **The completeness obligation of a `simplify` rule set** (module doc). -/
def SimpRulesOk (rules : SimplifyFn) : Prop :=
  ∀ {σ : Type} (enodes : σ → ValueId → List Inst) (typeOf : σ → ValueId → Option Ty)
    (make : σ → Inst → ValueId × σ) (fn : Function) (P : σ → Prop) (R : σ → ValueId → Prop),
    GraphIn enodes typeOf fn P R → MakeIn make typeOf fn P R (fun _ => False) →
    ∀ st v cands names st', P st →
      (∀ n ∈ enodes st v, NodeIn (typeOf st) fn (R st) (typeOf st v) n) →
      rules enodes typeOf make st v = .ok (cands, names, st') →
      P st' ∧ RGrows typeOf R st st' ∧
        ∀ c ∈ cands, c.1 = v ∨ (R st' c.1 ∧ typeOf st' c.1 = typeOf st v)

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

/-- **The completeness obligation of a `simplify_skeleton` rule set** (module doc). -/
def SkelRulesOk (skel : SkeletonFn) : Prop :=
  ∀ {σ : Type} (enodes : σ → ValueId → List Inst) (typeOf : σ → ValueId → Option Ty)
    (make : σ → Inst → ValueId × σ) (trapBlock : σ → BlockId → Option TrapCode) (fn : Function)
    (P : σ → Prop) (R : σ → ValueId → Prop),
    GraphIn enodes typeOf fn P R → MakeIn make typeOf fn P R (fun _ => False) →
    ∀ st i cands names st', P st → (∀ y ∈ skelOps i, R st y) →
      skel enodes typeOf make trapBlock st i = .ok (cands, names, st') →
      P st' ∧ RGrows typeOf R st st' ∧ ∀ c ∈ cands, SkelCandOk (typeOf st') (R st') i c

/-- The empty rule set (no candidates). -/
def noRules : SimplifyFn := fun _ _ _ st _ => .ok ([], [], st)

theorem simpRulesOk_noRules : SimpRulesOk noRules := by
  intro σ enodes typeOf make fn P R _ _ st v cands names st' hP _ h
  simp only [noRules, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -, rfl⟩ := h
  exact ⟨hP, ⟨fun _ h => h, fun _ _ h => h⟩, fun c hc => by cases hc⟩

/-- The hand rules have no skeleton rules. -/
theorem skelRulesOk_hand : SkelRulesOk HandRules.simplifySkeleton := by
  intro σ enodes typeOf make trapBlock fn P R _ _ st i cands names st' hP _ h
  simp only [HandRules.simplifySkeleton, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -, rfl⟩ := h
  exact ⟨hP, ⟨fun _ h => h, fun _ _ h => h⟩, fun c hc => by cases hc⟩

end Opt
