import Lean
import FV.Backend.Proof.IselPrgCheck

/-!
# Progress of the ISLE lowering (V7): the model obligations and the statement

`Model aext actor aidata`: the transfer functions of the extern helpers are sound for the
driver's embedding `sem ctx` (`FV/Backend/Isel.lean`):

* `ext`: an extractor the model accepts on `a` never returns `unmodeled`, and on a value `a`
  describes either succeeds with fields one of the model's outputs describes, or fails (and the
  model did not promise success);
* `ctor`: the same for constructors (`externCtor`);
* `idata`: the `InstructionData` of an E instruction of the function is variant `k` of
  `InstructionData` with fields `aidata k` describes.

`HandOk`: the hand-checked rules' right-hand sides return.

`Progress`: the statement of `IselPrgSound`'s theorem: a run of a table term from arguments its
inputs describe, at a fuel of at least the entry's, returns (never throws), with a value its
output describes, surely a value if `osome`.
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Interp Isle.Aarch64

variable (f : Clif.Function) (ctx : Ctx)

/-- **The extern helpers' transfer functions are sound** for `sem ctx`. -/
structure Model (aext : TermId → PA → Option (List (List PA) × Bool))
    (actor : TermId → List PA → Option (PA × Bool)) (aidata : Nat → Option (List PA)) : Prop where
  ext : ∀ (term : Term) (a : PA) (outs : List (List PA)) (must : Bool) (v : V) (st : LState),
    aext term.id a = some (outs, must) → γ f ctx a v →
      (∃ fs, externExtract ctx term v st = .ok fs ∧ ∃ out ∈ outs, γL f ctx out fs) ∨
      (externExtract ctx term v st = .fail ∧ must = false)
  ctor : ∀ (term : Term) (as : List PA) (a : PA) (must : Bool) (vs : List V) (st : LState),
    actor term.id as = some (a, must) → γL f ctx as vs →
      (∃ w st', externCtor ctx term vs st = .ok (w, st') ∧ γ f ctx a w) ∨
      (externCtor ctx term vs st = .fail ∧ must = false)
  idata : ∀ (v : V), γ f ctx .idata v → ∃ k fs afs, v = .data tyInstData k fs ∧
    aidata k = some afs ∧ γL f ctx afs fs

/-- **The hand-checked rules** (`hand r.id = some (c, a)`): from fuel `c`, the right-hand side of
rule `r` of an entry's term, from the environment of a successful match on arguments the entry's
inputs describe, returns a value `a` describes. -/
def HandOk (p : Program) (cfg : Config) (tab : PTab) (hand : RuleId → Option (Nat × PA)) : Prop :=
  ∀ e ∈ tab, ∀ r ∈ p.rulesOf e.t, ∀ c a, hand r.id = some (c, a) →
    ∀ (args : List V), γL f ctx e.ins args →
    ∀ (m : Nat) (s : LState × Array RuleId) (env : Isle.Interp.Env V) (s' : LState × Array RuleId),
      (matchRule p (sem ctx) cfg m r args).run s = .ok (some env, s') →
    ∀ n, c ≤ n → ∃ (v : V) (s'' : LState × Array RuleId),
      (evalExpr p (sem ctx) cfg n r.rhs env).run s' = .ok (some v, s'') ∧ γ f ctx a v

/-- **Progress at fuel `n`**: every entry of `tab` whose fuel is at most `n` runs, from
arguments its inputs describe, to a value its output describes (surely a value if `osome`). -/
def Progress (p : Program) (cfg : Config) (tab : PTab) (n : Nat) : Prop :=
  ∀ e ∈ tab, e.fu ≤ n → ∀ (ty : TypeId) (args : List V) (st : LState) (tr : Array RuleId),
    γL f ctx e.ins args →
    ∃ (v : Option V) (st' : LState) (tr' : Array RuleId),
      (applyTerm p (sem ctx) cfg n ty e.t args).run (st, tr) = .ok (v, (st', tr')) ∧
      (e.osome = true → v.isSome) ∧ ∀ w, v = some w → γ f ctx e.out w

end Backend.Proof.Prg
