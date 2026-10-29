module

public import FV.Backend.Proof.SpillCtlShapeT
public import FV.Backend.Proof.IselCovTSound
public import FV.Backend.Proof.IselShpBase

@[expose] public section

/-!
# Control shapes of the typed ISLE lowering: the state invariant, hand-checked rules

`IselShpBase` with the typed shapes (`CtlShapeT`) and the typed domain (`AT`):

* `ShpIsT N s0 s`: every control form emitted since `s0` has its typed shape, and the vreg
  counter is at least `N`;
* `HandOkT ctx N vs rl`: root rule `rl` keeps `ShpIsT N s0` (the root rules the abstract
  interpreter does not check: calls, `try_call`s, `br_table`);
* `SubOkT`: a sub-run the typed interpreter vouches for.

`ShpIsT.of_shpIs`: a run that keeps the integer invariant from its own start state keeps the
typed one from any earlier state (`CtlShape` is a `CtlShapeT`), so the integer proofs of
context-independent runs (the control-form oracles) carry over.
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64
open Backend.Proof.Cov (ShpIs)

/-- **The state invariant** of the typed control-shape analysis. -/
def ShpIsT (N : Nat) (s0 s : LState) : Prop := CtlSinceT N s0 s ∧ N ≤ s.nextVreg

/-- **A hand-checked root rule** keeps the typed invariant. -/
def HandOkT (ctx : Ctx) (N : Nat) (vs : List V) (rl : Rule) : Prop :=
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (s0 s : LState) (tr : Array RuleId) (env : Isle.Interp.Env V)
    (s1 : LState × Array RuleId) (r : Option V) (s2 : LState) (tr2 : Array RuleId),
    1000 ≤ m → 1000 ≤ n → ShpIsT N s0 s →
    (matchRule program (sem ctx) cfg m rl vs).run (s, tr) = .ok (some env, s1) →
    (evalExpr program (sem ctx) cfg n rl.rhs env).run s1 = .ok (r, (s2, tr2)) →
    ShpIsT N s0 s2

/-- **A sub-run the typed interpreter vouches for.** -/
def SubOkT (f : Clif.Function) (ctx : Ctx) (N : Nat) (t : TermId) (as : List AT) (out : AT) :
    Prop :=
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (n : Nat) (ty : TypeId) (vs : List V) (s0 s : LState) (tr : Array RuleId) (r : Option V)
    (s' : LState) (tr' : Array RuleId),
    Holds2 f ctx as vs → ShpIsT N s0 s →
    (applyTerm program (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    ShpIsT N s0 s' ∧ ∀ v, r = some v → γ f ctx out v

section
variable {N : Nat} {s0 s s' : LState}

theorem ShpIsT.refl (h : N ≤ s.nextVreg) : ShpIsT N s s := ⟨⟨[], by simp, by simp⟩, h⟩

/-- The integer invariant from the run's own start state gives the typed one. -/
theorem ShpIsT.of_shpIs (h0 : ShpIsT N s0 s) (h : ShpIs N s s') : ShpIsT N s0 s' := by
  obtain ⟨⟨ms0, e0, h0⟩, -⟩ := h0
  obtain ⟨⟨ms, e, h1⟩, hn⟩ := h
  refine ⟨⟨ms0 ++ ms, by rw [e, e0]; simp, fun m hm hc => ?_⟩, hn⟩
  rcases List.mem_append.mp hm with hm | hm
  · exact h0 m hm hc
  · exact (h1 m hm hc).toT

/-- The integer invariant at the run's start state. -/
theorem ShpIsT.shpIs_self (h : ShpIsT N s0 s) : ShpIs N s s := ⟨⟨[], by simp, by simp⟩, h.2⟩

theorem ShpIsT.fresh (h : ShpIsT N s0 s) (c : RegClass) : ShpIsT N s0 (s.fresh c).2 :=
  ⟨h.1, by simp only [LState.fresh]; have := h.2; omega⟩

theorem ShpIsT.emit (h : ShpIsT N s0 s) {m : MInst} (hm : m.isCtl = true → CtlShapeT N m) :
    ShpIsT N s0 (s.emit m) := by
  obtain ⟨⟨ms, he, hms⟩, hn⟩ := h
  refine ⟨⟨ms ++ [m], by simp [LState.emit, he], fun x hx => ?_⟩, hn⟩
  rcases List.mem_append.1 hx with hx | hx
  · exact hms x hx
  · rw [List.mem_singleton.1 hx]; exact hm

theorem ShpIsT.emit_nctl (h : ShpIsT N s0 s) {m : MInst} (hm : m.isCtl = false) :
    ShpIsT N s0 (s.emit m) :=
  h.emit fun h' => absurd (hm ▸ h') (by decide)

theorem ShpIsT.emit_eq (h : ShpIsT N s0 s) {m : MInst} {s' : LState} (he : s' = s.emit m)
    (hm : m.isCtl = true → CtlShapeT N m) : ShpIsT N s0 s' :=
  he ▸ h.emit hm

end

end Backend.Proof.CovT
