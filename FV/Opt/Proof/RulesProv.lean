import FV.Opt.Rules
import FV.Opt.Simplify

/-!
# Provenance obligations of a rule set (M1, #24)

What the completeness of the simplify stage needs of a rule set, with the pass's own guards
(`Opt.optimizeAt` and `Opt.skelMake` make only well-typed pure nodes over solid values, never
over the value being rewritten, and the pass drops candidates that are unknown or of another
type): the rules only *pass values on*. Every value a rule set returns, and every operand of a
node it asks `make` for, is a value it was given — the root, an operand of a node of a value it
was given (`enodes`), or a value `make` returned.

Stated parametrically (the state `σ` is abstract): for any set `Q` of values closed under node
operands (`EnodesIn`) and any `make` that, on a node over `Q`, keeps the invariant `P` and returns
a value of `Q` (`MakeQ`), the rules keep `P`, `Q` only grows, and every candidate is in `Q`
(`SimpRulesProv`). For `simplify_skeleton` also the block calls are passed on: every block call
of a candidate is one of the original terminator's (`QB`; `SkelRulesProv`).
-/

namespace Opt

open Clif

/-- The values and block calls a skeleton instruction or terminator mentions are in `Qv`/`QB`. -/
def SkelInstQ (Qv : ValueId → Prop) (QB : BlockCall → Prop) : Isle.Opt.SkelInst → Prop
  | .inst i => ∀ y ∈ operands i, Qv y
  | .term t => (∀ y ∈ termOperands t, Qv y) ∧ ∀ bc ∈ termCalls t, QB bc

/-- The values and block calls a skeleton simplification mentions are in `Qv`/`QB`. -/
def SkelSimpQ (Qv : ValueId → Prop) (QB : BlockCall → Prop) : Isle.Opt.SkelSimp → Prop
  | .remove => True
  | .removeWithVal v => Qv v
  | .replace i => SkelInstQ Qv QB i
  | .replaceWithVal i v => SkelInstQ Qv QB i ∧ Qv v
  | .replaceBranchCond c => Qv c
  | .replaceWithTwo a b => SkelInstQ Qv QB a ∧ SkelInstQ Qv QB b

/-- `Q` only grows from `s` to `s'`. -/
def QGrows {σ : Type} (Q : σ → ValueId → Prop) (s s' : σ) : Prop := ∀ x, Q s x → Q s' x

/-- `Q` is closed under the operands of the nodes of its values. -/
def EnodesIn {σ : Type} (enodes : σ → ValueId → List Inst) (P : σ → Prop)
    (Q : σ → ValueId → Prop) : Prop :=
  ∀ s x, P s → Q s x → ∀ n ∈ enodes s x, ∀ y ∈ operands n, Q s y

/-- `make` on a node over `Q` keeps `P`, lets `Q` grow, and returns a value of `Q`. -/
def MakeQ {σ : Type} (make : σ → Inst → ValueId × σ) (P : σ → Prop)
    (Q : σ → ValueId → Prop) : Prop :=
  ∀ s n, P s → (∀ y ∈ operands n, Q s y) →
    P (make s n).2 ∧ QGrows Q s (make s n).2 ∧ Q (make s n).2 (make s n).1

/-- **The provenance obligation of a `simplify` rule set** (module doc). -/
def SimpRulesProv (rules : SimplifyFn) : Prop :=
  ∀ {σ : Type} (enodes : σ → ValueId → List Inst) (typeOf : σ → ValueId → Option Ty)
    (make : σ → Inst → ValueId × σ) (P : σ → Prop) (Q : σ → ValueId → Prop),
    EnodesIn enodes P Q → MakeQ make P Q →
    ∀ s v cands names s', P s → Q s v →
      rules enodes typeOf make s v = .ok (cands, names, s') →
      P s' ∧ QGrows Q s s' ∧ ∀ c ∈ cands, Q s' c.1

/-- **The provenance obligation of a `simplify_skeleton` rule set** (module doc). -/
def SkelRulesProv (skel : SkeletonFn) : Prop :=
  ∀ {σ : Type} (enodes : σ → ValueId → List Inst) (typeOf : σ → ValueId → Option Ty)
    (make : σ → Inst → ValueId × σ) (trapBlock : σ → BlockId → Option TrapCode) (P : σ → Prop)
    (Q : σ → ValueId → Prop) (QB : BlockCall → Prop),
    EnodesIn enodes P Q → MakeQ make P Q →
    ∀ s i cands names s', P s → SkelInstQ (Q s) QB i →
      skel enodes typeOf make trapBlock s i = .ok (cands, names, s') →
      P s' ∧ QGrows Q s s' ∧ ∀ c ∈ cands, SkelSimpQ (Q s') QB c

end Opt
