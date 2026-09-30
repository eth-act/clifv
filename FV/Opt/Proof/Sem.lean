import FV.Opt.Rules
import FV.Clif.Run

/-!
# Semantics of pure nodes, and the rule-set obligations

The interface between the rule proofs and the pass proofs of the mid-end
(`docs/contracts/midend.md`, "Planned proof architecture" steps 1–3):

* `Opt.evalNode fr mem n`: the single result of `Clif.evalInst` (step 1).
* `Opt.SimplifySound rules`: the obligation of a `simplify` rule set (`Opt.SimplifyFn`): under a
  valuation `den st` of the driver's e-graph that is a *model* of it (every node of a defined
  class evaluates to the class's value, types agree) and a `make` that extends the model, every
  candidate of a defined class `v` has `v`'s value.
* `Opt.SkeletonSound skel`: the same for `simplify_skeleton` (`Opt.SkeletonFn`); each chosen
  simplification refines the original instruction or terminator (`Opt.SkelRefines`).

Only the forward direction is required: an undefined class (`den st x = none`) constrains
nothing. The graph state type `σ` is abstract, so a rule set can only change the state through
`make`. The pass proofs (`FV/Opt/Proof/Simplify*.lean`) instantiate `P`/`den` with the
driver's invariant; the rule proofs discharge the obligations for the allow-listed rules.
-/

namespace Opt

open Clif

/-- A valuation of values (e-class ids). -/
abbrev Valuation := ValueId → Option Val

/-- `ρ'` extends `ρ`. -/
def Valuation.Le (ρ ρ' : Valuation) : Prop := ∀ x a, ρ x = some a → ρ' x = some a

/-- The single result of a (pure) node, evaluated in `fr` (registers, stack-slot bases and
the function's globals) and `mem` (link-time symbols). `none` unless `evalInst` returns
exactly one value. -/
def evalNode (fr : Frame) (mem : Mem) (n : Inst) : Option Val :=
  match evalInst fr mem n with
  | .ok ([r], _) => some r
  | _ => none

/-- `den` is a model of the graph `enodes`/`typeOf` in every state satisfying `P`. -/
structure GraphModel {σ : Type} (enodes : σ → ValueId → List Inst)
    (typeOf : σ → ValueId → Option Ty) (P : σ → Prop) (den : σ → Valuation) (fr : Frame)
    (mem : Mem) : Prop where
  nodes : ∀ st x a, P st → den st x = some a → ∀ n ∈ enodes st x,
    evalNode { fr with regs := den st } mem n = some a
  types : ∀ st x t a, P st → typeOf st x = some t → den st x = some a → a.ty = t

/-- `make` keeps the model and gives the made node's value to its class. -/
def MakeSound {σ : Type} (make : σ → Inst → ValueId × σ) (P : σ → Prop)
    (den : σ → Valuation) (fr : Frame) (mem : Mem) : Prop :=
  ∀ st n, P st → P (make st n).2 ∧ Valuation.Le (den st) (den (make st n).2) ∧
    ∀ b, evalNode { fr with regs := den st } mem n = some b → den (make st n).2 (make st n).1 = some b

/-- **Obligation of a `simplify` rule set.** -/
def SimplifySound (rules : SimplifyFn) : Prop :=
  ∀ {σ : Type} (enodes : σ → ValueId → List Inst) (typeOf : σ → ValueId → Option Ty)
    (make : σ → Inst → ValueId × σ) (P : σ → Prop) (den : σ → Valuation) (fr : Frame)
    (mem : Mem),
    GraphModel enodes typeOf P den fr mem → MakeSound make P den fr mem →
    ∀ st v cands names st', P st →
      rules enodes typeOf make st v = .ok (cands, names, st') →
      P st' ∧ Valuation.Le (den st) (den st') ∧
        ∀ a, den st v = some a → ∀ c ∈ cands, den st' c.1 = some a

/-! ## Skeleton simplifications -/

/-- Where a branch goes: target block, argument values, memory (`ret`/`return_call`: stuck). -/
def termEval (fr : Frame) (mem : Mem) : Terminator → Res (BlockId × List Val × Mem)
  | .jump d => do
    let vs ← fr.getMany d.args
    pure (d.block, vs, mem)
  | .brif c t e => do
    let cv ← fr.get c
    let d := if Sem.truthy cv.bits then t else e
    let vs ← fr.getMany d.args
    pure (d.block, vs, mem)
  | .brTable x dflt table => do
    let xv ← fr.get x
    let d := table[xv.toNat]?.getD dflt
    let vs ← fr.getMany d.args
    pure (d.block, vs, mem)
  | .trap code => .trap code
  | .ret _ | .returnCall .. | .tryCall .. | .tryCallIndirect .. => .stuck "not a branch"

/-- A result-free instruction, then a terminator. -/
def seqEval (fr : Frame) (mem : Mem) (a : Inst) (t : Terminator) :
    Res (BlockId × List Val × Mem) :=
  match evalInst fr mem a with
  | .ok ([], m) => termEval fr m t
  | .ok _ => .stuck "result"
  | .trap c => .trap c
  | .stuck m => .stuck m

/-- Two result-free instructions. -/
def seqEval2 (fr : Frame) (mem : Mem) (a b : Inst) : Res (List Val × Mem) :=
  match evalInst fr mem a with
  | .ok ([], m) => evalInst fr m b
  | .ok _ => .stuck "result"
  | .trap c => .trap c
  | .stuck m => .stuck m

/-- `tgt` refines `src`: same result or trap (a stuck `src` allows anything). -/
def ResRefines {α : Type} (src tgt : Res α) : Prop :=
  (∀ a, src = .ok a → tgt = .ok a) ∧ (∀ c, src = .trap c → tgt = .trap c)

/-- Branch refinement modulo trap blocks: going to a block `b` with `tb b = some c` (a block
that traps with `c` after pure statements) may become trapping with `c` at once. -/
def BrRefines (tb : BlockId → Option TrapCode) (src tgt : Res (BlockId × List Val × Mem)) :
    Prop :=
  (∀ b vs m, src = .ok (b, vs, m) → tgt = .ok (b, vs, m) ∨ ∃ c, tb b = some c ∧ tgt = .trap c) ∧
    (∀ c, src = .trap c → tgt = .trap c)

/-- A chosen skeleton simplification `c` refines the original `orig`, evaluated in `fr`/`mem`
(the cases `Opt.skelStmt`/`Opt.skelTerm` apply; the others are ignored by the driver). -/
def SkelRefines (tb : BlockId → Option TrapCode) (fr : Frame) (mem : Mem) :
    Isle.Opt.SkelInst → Isle.Opt.SkelSimp → Prop
  | .inst i, .remove =>
    (∀ vs m, evalInst fr mem i = .ok (vs, m) → m = mem) ∧ ∀ c, evalInst fr mem i ≠ .trap c
  | .inst i, .removeWithVal v =>
    (∀ vs m, evalInst fr mem i = .ok (vs, m) → m = mem ∧ ∃ a, vs = [a] ∧ fr.regs v = some a) ∧
      ∀ c, evalInst fr mem i ≠ .trap c
  | .inst i, .replace (.inst i') => ResRefines (evalInst fr mem i) (evalInst fr mem i')
  | .inst i, .replaceBranchCond c =>
    match i with
    | .trapz _ code => ResRefines (evalInst fr mem i) (evalInst fr mem (.trapz c code))
    | .trapnz _ code => ResRefines (evalInst fr mem i) (evalInst fr mem (.trapnz c code))
    | _ => True
  | .inst i, .replaceWithTwo (.inst a) (.inst b) =>
    ResRefines (evalInst fr mem i) (seqEval2 fr mem a b)
  | .term t, .replace (.term t') => BrRefines tb (termEval fr mem t) (termEval fr mem t')
  | .term t, .replaceBranchCond c =>
    match t with
    | .brif _ th el => BrRefines tb (termEval fr mem t) (termEval fr mem (.brif c th el))
    | _ => True
  | .term t, .replaceWithTwo (.inst a) (.term t') =>
    BrRefines tb (termEval fr mem t) (seqEval fr mem a t')
  | _, _ => True

/-- **Obligation of a `simplify_skeleton` rule set**: under the same model assumptions as
`SimplifySound` (and a `trapBlock` that is `tb` in every state), every candidate refines the
original in the final valuation. -/
def SkeletonSound (skel : SkeletonFn) : Prop :=
  ∀ {σ : Type} (enodes : σ → ValueId → List Inst) (typeOf : σ → ValueId → Option Ty)
    (make : σ → Inst → ValueId × σ) (trapBlock : σ → BlockId → Option TrapCode)
    (P : σ → Prop) (den : σ → Valuation) (fr : Frame) (mem : Mem)
    (tb : BlockId → Option TrapCode),
    GraphModel enodes typeOf P den fr mem → MakeSound make P den fr mem →
    (∀ st, P st → trapBlock st = tb) →
    ∀ st i cands names st', P st →
      skel enodes typeOf make trapBlock st i = .ok (cands, names, st') →
      P st' ∧ Valuation.Le (den st) (den st') ∧
        ∀ c ∈ cands, SkelRefines tb { fr with regs := den st' } mem i c

end Opt
