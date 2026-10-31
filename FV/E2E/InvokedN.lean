import FV.E2E.IselSimI
import FV.E2E.CallPostExists
import FV.E2E.LinkClif

/-!
# The invocation of call number `n` (SEM1 item (b), `docs/plans/uninit.md` §5.9)

`XI.at n` cannot depend on the CLIF state, so the guard of the oracle call semantics uses the
invocation of *the* call state with count `n`:

* `InvokedN env p cs n`: the extern invocation of a state reached from `cs` after `n` calls that
  makes a call (`callNum s = 1`);
* `reachN_uncons`, `reachN_cmp`: `Clif.step` is a function, so the states reached from `cs` lie on
  one path (`reachN_cmp`: of two reached states one is reached from the other);
* `invokedN_unique`: two calling states with the same count are equal, so `InvokedN n` is
  single-valued;
* `NoRetCall env p cs`: no reached state ends in `return_call` (scope condition: a `return_call`
  to an extern counts no call — `callNum` is `0` — and its step can continue in the caller, so a
  later call could have the same count; cg_clif emits no `return_call`); `noRetCall_of_linv`: it
  follows from the frame invariant `Clif.LInv` for functions without `return_call`;
* `invoked_sub_invokedN`: under `NoRetCall`, a reached state's invocation is `InvokedN` of its
  count;
* `callPost_invokedN_exists`: the accepted results of `CallPost` for `env.only (InvokedN n)` exist
  when the returning invocation keeps allocations and symbols and its declarations agree on the
  ABI return count.
-/

namespace E2E

open Backend Backend.Proof

/-- One step at the head of a reached path. -/
theorem reachN_uncons {env : Clif.Env} {p : Clif.Program} {s s' a : Clif.State} {k : Nat}
    (h : ReachN env p s a k) (hs : Clif.step env p s = .next s') :
    (a = s ∧ k = 0) ∨ (ReachN env p s' a (k - callNum s) ∧ callNum s ≤ k) := by
  induction h with
  | refl => exact .inl ⟨rfl, rfl⟩
  | @snoc t a m ht hst ih =>
    rcases ih with ⟨rfl, rfl⟩ | ⟨ih, hle⟩
    · rw [hs] at hst
      cases hst
      refine .inr ⟨?_, by omega⟩
      have : callNum t - callNum t = 0 := by omega
      rw [Nat.zero_add, this]
      exact .refl
    · refine .inr ⟨?_, by omega⟩
      have := ReachN.snoc ih hst
      rwa [show m - callNum s + callNum t = m + callNum t - callNum s by omega] at this

/-- **The reached states lie on one path**: of two states reached from `cs`, one is reached
from the other, with the difference of the counts. -/
theorem reachN_cmp {env : Clif.Env} {p : Clif.Program} {cs a b : Clif.State} {i j : Nat}
    (ha : ReachN env p cs a i) (hb : ReachN env p cs b j) :
    (∃ k, ReachN env p a b k ∧ j = i + k) ∨ (∃ k, ReachN env p b a k ∧ i = j + k) := by
  induction hb with
  | refl => exact .inr ⟨i, ha, by omega⟩
  | @snoc s s' m _ hst ih =>
    rcases ih with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · exact .inl ⟨k + callNum s, ReachN.snoc hk hst, by omega⟩
    · rcases reachN_uncons hk hst with ⟨rfl, rfl⟩ | ⟨hk', hle⟩
      · have h1 := ReachN.snoc ReachN.refl hst
        rw [Nat.zero_add] at h1
        exact .inl ⟨callNum a, h1, by omega⟩
      · exact .inr ⟨k - callNum s, hk', by omega⟩

/-- A path from a calling state to another state counts that call. -/
theorem reachN_ge {env : Clif.Env} {p : Clif.Program} {a b : Clif.State} {k : Nat}
    (h : ReachN env p a b k) (hne : a ≠ b) : callNum a ≤ k := by
  induction h with
  | refl => exact (hne rfl).elim
  | @snoc t _ m ht _ ih =>
    by_cases hat : a = t
    · subst hat
      cases ht with
      | refl => omega
      | snoc _ _ => omega
    · have := ih hat
      omega

/-- **The extern invocation of call number `n`**: the invocation of a calling state reached from
`cs` after `n` calls. -/
def InvokedN (env : Clif.Env) (p : Clif.Program) (cs : Clif.State) (n : Nat) (name : String)
    (vals : List Clif.Val) (m : Clif.Mem) : Prop :=
  ∃ s, ReachN env p cs s n ∧ callNum s = 1 ∧ Clif.Invoked env p s name vals m

/-- **Two calling states with the same count are equal.** -/
theorem reachN_call_unique {env : Clif.Env} {p : Clif.Program} {cs s₁ s₂ : Clif.State} {n : Nat}
    (h₁ : ReachN env p cs s₁ n) (c₁ : callNum s₁ = 1) (h₂ : ReachN env p cs s₂ n)
    (c₂ : callNum s₂ = 1) : s₁ = s₂ := by
  refine Classical.byContradiction fun hne => ?_
  rcases reachN_cmp h₁ h₂ with ⟨k, hk, hc⟩ | ⟨k, hk, hc⟩
  · have := reachN_ge hk hne
    omega
  · have := reachN_ge hk (Ne.symm hne)
    omega

/-- **`InvokedN n` is single-valued.** -/
theorem invokedN_unique {env : Clif.Env} {p : Clif.Program} {cs : Clif.State} {n : Nat}
    {nm nm' : String} {vals vals' : List Clif.Val} {m m' : Clif.Mem}
    (h : InvokedN env p cs n nm vals m) (h' : InvokedN env p cs n nm' vals' m') :
    nm = nm' ∧ vals = vals' ∧ m = m' := by
  obtain ⟨s, hs, hc, hi⟩ := h
  obtain ⟨s', hs', hc', hi'⟩ := h'
  obtain rfl := reachN_call_unique hs hc hs' hc'
  exact invoked_unique hi hi'

/-- **Scope condition: no reached state ends in `return_call`.** -/
def NoRetCall (env : Clif.Env) (p : Clif.Program) (cs : Clif.State) : Prop :=
  ∀ s n, ReachN env p cs s n → s.frame.body = [] → ∀ fn args, s.frame.term ≠ .returnCall fn args

/-- **`NoRetCall` from the frame invariant**: every frame of the entry state is a frame of a
function of `P` without `return_call` (`Clif.LInv`), and the program's functions are `P`'s. -/
theorem noRetCall_of_linv {env : Clif.Env} {p P : Clif.Program} {cs : Clif.State}
    (hP : ∀ g ∈ P.funcs, Clif.LinkFree g) (hp : ∀ g ∈ p.funcs, g ∈ P.funcs)
    (hI : Clif.LInv P cs) : NoRetCall env p cs := by
  intro s n hs hb fn args ht
  have hIs : ∀ t k, ReachN env p cs t k → Clif.LInv P t := by
    intro t k h
    induction h with
    | refl => exact hI
    | snoc _ hst ih => exact (Clif.step_next_linv hP ih hst hp).1
  rcases (hIs s n hs).1 with ⟨hf, ⟨b, hbm, -, hbt⟩ | ⟨-, bc, hbt⟩⟩
  · exact hP _ hf b hbm fn args (hbt.symm.trans ht)
  · rw [hbt] at ht; cases ht

/-- An invoking state that does not end in `return_call` makes a call. -/
theorem callNum_of_invoked {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {nm : String}
    {vals : List Clif.Val} {m : Clif.Mem} (h : Clif.Invoked env p s nm vals m)
    (hnr : s.frame.body = [] → ∀ fn args, s.frame.term ≠ .returnCall fn args) :
    callNum s = 1 := by
  obtain ⟨-, h⟩ := h
  unfold callNum
  revert h
  cases hb : s.frame.body with
  | cons st _ =>
    intro h
    simp only at h ⊢
    cases hi : st.inst <;> simp_all [Clif.Inst.isCallLike]
  | nil =>
    intro h
    simp only at h ⊢
    have hnr := hnr hb
    cases ht : s.frame.term <;> simp_all [Clif.Terminator.isTry]

/-- **A reached state's invocation is the invocation of its count** (under `NoRetCall`). -/
theorem invoked_sub_invokedN {env : Clif.Env} {p : Clif.Program} {cs s : Clif.State} {n : Nat}
    (hnrc : NoRetCall env p cs) (hs : ReachN env p cs s n) :
    ∀ nm vals m, Clif.Invoked env p s nm vals m → InvokedN env p cs n nm vals m :=
  fun _ _ _ h => ⟨s, hs, callNum_of_invoked h (hnrc s n hs), h⟩

/-- **An accepted result exists for every call** to the environment restricted to the invocation
of call number `n`, when that invocation, if it returns, keeps the live allocations and symbols
and its possible declarations (those with as many parameters as it has values, #733) agree on an
ABI return count. -/
theorem callPost_invokedN_exists {env : Clif.Env} {p : Clif.Program} {cs : Clif.State} {n : Nat}
    {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {Γ : Rel} {f : Clif.Function}
    {c : BitVec 64} {sym : String → Int → BitVec 64}
    (hR : ∀ nm vals m g rvals cm', InvokedN env p cs n nm vals m → env.extern nm = some g →
      g vals m = .returned rvals cm' →
      (∀ a k, cm'.valid a k = true → m.valid a k = true) ∧ cm'.symbols = m.symbols ∧
      ∃ ℓ, rvals.length ≤ ℓ ∧
        (∀ ext ∈ exts, ext.name = nm → vals.length = ext.sig.params.length →
          rvals.length = ext.sig.returns.length → (sigRets ext.sig).length = ℓ) ∧
        (∀ sig ∈ sigs, (∀ s', env.sigOf nm = some s' → sig.abiMatch s' = true) →
          vals.length = sig.params.length → rvals.length = sig.returns.length →
          (sigRets sig).length = ℓ)) :
    ∀ d uses w, ∃ r,
      CallPost (env.only (InvokedN env p cs n)) exts sigs (RelW Γ f c) sym d uses w r := by
  intro d uses w
  by_cases hinv : ∃ nm vals m, InvokedN env p cs n nm vals m
  · obtain ⟨n0, vals0, m0, h0⟩ := hinv
    -- the return count of the invocation's outcome (any, if it does not return)
    by_cases hret : ∃ g rvals cm', env.extern n0 = some g ∧ g vals0 m0 = .returned rvals cm'
    · obtain ⟨g0, rv0, cm1, hg0, hr0⟩ := hret
      obtain ⟨hv, hsym, ℓ, hℓ, hext, hsig⟩ := hR n0 vals0 m0 g0 rv0 cm1 h0 hg0 hr0
      refine callPost_only_exists (n0 := n0) (vals0 := vals0) (cm0 := m0)
        (fun _ _ _ h => invokedN_unique h h0) ℓ (fun g rvals cm' hg hr => ?_) d uses w
      rw [hg0] at hg; cases hg
      rw [hr0] at hr; cases hr
      exact ⟨hv, hsym, hℓ, hext, hsig⟩
    · exact callPost_only_exists (n0 := n0) (vals0 := vals0) (cm0 := m0)
        (fun _ _ _ h => invokedN_unique h h0) 0
        (fun g rvals cm' hg hr => (hret ⟨g, rvals, cm', hg, hr⟩).elim) d uses w
  · have none_ret : ∀ (nm : String) g' vals rvals cm cm',
        (env.only (InvokedN env p cs n)).extern nm = some g' →
        g' vals cm = .returned rvals cm' → False := by
      intro nm g' vals rvals cm cm' hg' hret
      obtain ⟨g, -, rfl⟩ := Clif.Env.only_extern_eq hg'
      exact hinv ⟨nm, vals, cm, (onlyFn_returned hret).1⟩
    exact ⟨([], w), fun _ _ _ _ _ _ _ _ _ hg _ _ _ hret _ => (none_ret _ _ _ _ _ _ hg hret).elim,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ hg _ _ _ _ hret _ _ =>
        (none_ret _ _ _ _ _ _ hg hret).elim⟩

end E2E
