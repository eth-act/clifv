import FV.E2E.ExtSemGuard
import FV.E2E.RelWPatch
import FV.E2E.ClifEnvOnlyContracts

/-!
# Accepted call results exist at a single invocation (SEM1 item (b), `docs/plans/uninit.md` §5.9)

The guarded call semantics meets the callee contracts once every call `(d, uses, w)` has a
result `CallPost` accepts (`xCallsOk_guard`). For the environment restricted to one CLIF
invocation `(n0, vals0, cm0)` (`Clif.Env.only`, e.g. the invocation of the CLIF state reached
after `n` calls) there is one: the CLIF results as values (`valCV`, padded to the ABI return
count `ℓ`) and `w` with the memory after the call written (`patchW`), when the callee keeps the
live allocations and symbols and every declaration the call can stand for has `ℓ` ABI returns
(`callPost_only_exists`).
-/

namespace E2E

open Backend Backend.Proof

/-- A CLIF value as a VCode value (zero-extended). -/
def valCV (v : Clif.Val) : CV := v.bits.setWidth 128

theorem vHolds_valCV (v : Clif.Val) : VHolds v (valCV v) := by
  obtain ⟨t, b⟩ := v
  have hw : t.width ≤ 128 := by cases t <;> decide
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  have hp : 2 ^ t.width ≤ 2 ^ 128 := Nat.pow_le_pow_right (by decide) hw
  simp only [valCV, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 128), Nat.mod_eq_of_lt hb]

/-- The CLIF results as `ℓ` VCode values. -/
def outsOf (rvals : List Clif.Val) (ℓ : Nat) : List CV :=
  rvals.map valCV ++ List.replicate (ℓ - rvals.length) 0

theorem outsOf_length {rvals : List Clif.Val} {ℓ : Nat} (h : rvals.length ≤ ℓ) :
    (outsOf rvals ℓ).length = ℓ := by
  simp only [outsOf, List.length_append, List.length_map, List.length_replicate]
  omega

theorem prefixHold_outsOf {rvals : List Clif.Val} {ℓ : Nat} (h : rvals.length ≤ ℓ) :
    PrefixHold rvals (outsOf rvals ℓ) := by
  refine ⟨by rw [outsOf_length h]; exact h, fun j v x hv hx => ?_⟩
  have hj : j < rvals.length := (List.getElem?_eq_some_iff.mp hv).1
  rw [outsOf, List.getElem?_append_left (by simpa using hj), List.getElem?_map, hv] at hx
  cases hx
  exact vHolds_valCV v

/-- **An accepted result exists for every call** to the environment restricted to the single
invocation `(n0, vals0, cm0)`. The declarations compared are those with as many parameters as the
invocation has values (a call through one passes that many, #733). -/
theorem callPost_only_exists {env : Clif.Env} {A : String → List Clif.Val → Clif.Mem → Prop}
    {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {Γ : Rel} {f : Clif.Function}
    {c : BitVec 64} {sym : String → Int → BitVec 64}
    {n0 : String} {vals0 : List Clif.Val} {cm0 : Clif.Mem}
    (hA : ∀ n vals cm, A n vals cm → n = n0 ∧ vals = vals0 ∧ cm = cm0)
    (ℓ : Nat)
    (hR : ∀ g rvals cm', env.extern n0 = some g → g vals0 cm0 = .returned rvals cm' →
      (∀ a k, cm'.valid a k = true → cm0.valid a k = true) ∧ cm'.symbols = cm0.symbols ∧
      rvals.length ≤ ℓ ∧
      (∀ ext ∈ exts, ext.name = n0 → vals0.length = ext.sig.params.length →
        rvals.length = ext.sig.returns.length → ext.sig.returns.length = ℓ) ∧
      (∀ sig ∈ sigs, (∀ s, env.sigOf n0 = some s → sig.abiMatch s = true) →
        vals0.length = sig.params.length → rvals.length = sig.returns.length →
        sig.returns.length = ℓ)) :
    ∀ d uses w, ∃ r, CallPost (env.only A) exts sigs (RelW Γ f c) sym d uses w r := by
  intro d uses w
  -- the invocation's outcome (if it returns)
  by_cases hex : ∃ g rvals cm', env.extern n0 = some g ∧ g vals0 cm0 = .returned rvals cm'
  · obtain ⟨g0, rv0, cm1, hg0, hr0⟩ := hex
    obtain ⟨hv, hsym, hℓ, hext, hsig⟩ := hR g0 rv0 cm1 hg0 hr0
    -- every admitted returning call is this one
    have key : ∀ (n : String) g' vals rvals cm cm', (env.only A).extern n = some g' →
        g' vals cm = .returned rvals cm' →
          n = n0 ∧ vals = vals0 ∧ rvals = rv0 ∧ cm = cm0 ∧ cm' = cm1 := by
      intro n g' vals rvals cm cm' hg' hret
      obtain ⟨g, hg1, rfl⟩ := Clif.Env.only_extern_eq hg'
      obtain ⟨hAi, hret'⟩ := onlyFn_returned hret
      obtain ⟨rfl, rfl, rfl⟩ := hA n vals cm hAi
      rw [hg0] at hg1
      cases hg1
      rw [hr0] at hret'
      cases hret'
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨(outsOf rv0 ℓ, patchW cm1 w), fun ext hext' g sl cm args vals rvals cm' hg _ ha hmr hret
        hlen => ?_, fun sig hsig' n g sl cm u args vals rvals cm' _ _ hg hs _ _ _ hmr hret hlen hty =>
        ?_⟩
    · obtain ⟨hn, rfl, rfl, rfl, rfl⟩ := key _ _ _ _ _ _ hg hret
      exact ⟨by rw [outsOf_length hℓ]; exact (hext ext hext' hn ha.1 hlen).symm,
        prefixHold_outsOf hℓ, relW_patchW hmr hv hsym⟩
    · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := key _ _ _ _ _ _ hg hret
      have hpl : vals.length = sig.params.length := by
        simpa [Clif.AbiParam.tys] using congrArg List.length hty
      exact ⟨by rw [outsOf_length hℓ]; exact (hsig sig hsig' (by simpa using hs) hpl hlen).symm,
        prefixHold_outsOf hℓ, relW_patchW hmr hv hsym⟩
  · -- no admitted call returns: every result is accepted
    have none_ret : ∀ (n : String) g' vals rvals cm cm', (env.only A).extern n = some g' →
        g' vals cm = .returned rvals cm' → False := by
      intro n g' vals rvals cm cm' hg' hret
      obtain ⟨g, hg1, rfl⟩ := Clif.Env.only_extern_eq hg'
      obtain ⟨hAi, hret'⟩ := onlyFn_returned hret
      obtain ⟨rfl, rfl, rfl⟩ := hA n vals cm hAi
      exact hex ⟨g, rvals, cm', hg1, hret'⟩
    exact ⟨([], w), fun _ _ _ _ _ _ _ _ _ hg _ _ _ hret _ => (none_ret _ _ _ _ _ _ hg hret).elim,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ hg _ _ _ _ _ hret _ _ =>
        (none_ret _ _ _ _ _ _ hg hret).elim⟩

/-- **A state invokes at most one extern call** (name, argument values, memory). -/
theorem invoked_unique {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {n n' : String}
    {vals vals' : List Clif.Val} {m m' : Clif.Mem} (h : Clif.Invoked env p s n vals m)
    (h' : Clif.Invoked env p s n' vals' m') : n = n' ∧ vals = vals' ∧ m = m' := by
  obtain ⟨rfl, h⟩ := h
  obtain ⟨rfl, h'⟩ := h'
  have hc : ∀ fn args, Clif.CallInv s fn args n vals → Clif.CallInv s fn args n' vals' →
      n = n' ∧ vals = vals' ∧ s.mem = s.mem := by
    rintro fn args ⟨e, he, rfl, hv⟩ ⟨e', he', rfl, hv'⟩
    rw [he] at he'; cases he'
    rw [hv] at hv'; cases hv'
    exact ⟨rfl, rfl, rfl⟩
  have hi : ∀ callee args, Clif.IndInv env p s callee args n vals →
      Clif.IndInv env p s callee args n' vals' → n = n' ∧ vals = vals' ∧ s.mem = s.mem := by
    rintro callee args ⟨cv, hcv, hv, hn⟩ ⟨cv', hcv', hv', hn'⟩
    rw [hcv] at hcv'; cases hcv'
    rw [hv] at hv'; cases hv'
    rw [hn] at hn'; cases hn'
    exact ⟨rfl, rfl, rfl⟩
  revert h h'
  generalize s.frame.body = b
  cases b with
  | cons st _ =>
    dsimp only
    generalize st.inst = i
    cases i <;> first
      | exact fun h h' => hc _ _ h h'
      | exact fun h h' => hi _ _ h h'
      | exact fun h => False.elim h
  | nil =>
    dsimp only
    generalize s.frame.term = t
    cases t <;> first
      | exact fun h h' => hc _ _ h h'
      | exact fun h h' => hi _ _ h h'
      | exact fun h => False.elim h

/-- **An accepted result exists for every call** to the environment restricted to the
invocation of a CLIF state (`Clif.Invoked`, the per-state premises of the counted pipelines),
when that invocation, if it returns, keeps the live allocations and symbols and fixes the ABI
return count `ℓ`. -/
theorem callPost_invoked_exists {env : Clif.Env} {p : Clif.Program} {s : Clif.State}
    {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {Γ : Rel} {f : Clif.Function}
    {c : BitVec 64} {sym : String → Int → BitVec 64} (ℓ : Nat)
    (hR : ∀ n vals g rvals cm', Clif.Invoked env p s n vals s.mem → env.extern n = some g →
      g vals s.mem = .returned rvals cm' →
      (∀ a k, cm'.valid a k = true → s.mem.valid a k = true) ∧ cm'.symbols = s.mem.symbols ∧
      rvals.length ≤ ℓ ∧
      (∀ ext ∈ exts, ext.name = n → rvals.length = ext.sig.returns.length →
        ext.sig.returns.length = ℓ) ∧
      (∀ sig ∈ sigs, (∀ s', env.sigOf n = some s' → sig.abiMatch s' = true) →
        rvals.length = sig.returns.length → sig.returns.length = ℓ)) :
    ∀ d uses w, ∃ r,
      CallPost (env.only (Clif.Invoked env p s)) exts sigs (RelW Γ f c) sym d uses w r := by
  by_cases hinv : ∃ n vals m, Clif.Invoked env p s n vals m
  · obtain ⟨n0, vals0, m0, h0⟩ := hinv
    have hm0 : m0 = s.mem := h0.1
    subst hm0
    exact callPost_only_exists (n0 := n0) (vals0 := vals0) (cm0 := s.mem)
      (fun n vals cm h => invoked_unique h h0) ℓ
      (fun g rvals cm' hg hret => by
        obtain ⟨hv, hsy, hl, he, hs⟩ := hR n0 vals0 g rvals cm' h0 hg hret
        exact ⟨hv, hsy, hl, fun ext hx hn _ => he ext hx hn, fun sig hx hm _ => hs sig hx hm⟩)
  · intro d uses w
    have none_ret : ∀ (n : String) g' vals rvals cm cm',
        (env.only (Clif.Invoked env p s)).extern n = some g' →
        g' vals cm = .returned rvals cm' → False := by
      intro n g' vals rvals cm cm' hg' hret
      obtain ⟨g, -, rfl⟩ := Clif.Env.only_extern_eq hg'
      exact hinv ⟨n, vals, cm, (onlyFn_returned hret).1⟩
    exact ⟨([], w), fun _ _ _ _ _ _ _ _ _ hg _ _ _ hret _ => (none_ret _ _ _ _ _ _ hg hret).elim,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ hg _ _ _ _ _ hret _ _ =>
        (none_ret _ _ _ _ _ _ hg hret).elim⟩

/-- A call of a smaller restriction that returns is a call of the larger one. -/
theorem only_returned_mono {env : Clif.Env} {A A' : String → List Clif.Val → Clif.Mem → Prop}
    (hAA : ∀ n vals m, A n vals m → A' n vals m) {n : String}
    {g : List Clif.Val → Clif.Mem → Clif.Outcome} {vals : List Clif.Val} {cm : Clif.Mem}
    {rvals : List Clif.Val} {cm' : Clif.Mem} (hg : (env.only A).extern n = some g)
    (hret : g vals cm = .returned rvals cm') :
    ∃ g', (env.only A').extern n = some g' ∧ g' vals cm = .returned rvals cm' := by
  obtain ⟨g0, hg0, rfl⟩ := Clif.Env.only_extern_eq hg
  obtain ⟨hA, hret'⟩ := onlyFn_returned hret
  refine ⟨Clif.onlyFn A' n g0, by rw [Clif.Env.only_extern, hg0]; rfl, ?_⟩
  rw [Clif.onlyFn_of (hAA n vals cm hA)]
  exact hret'

/-- **`CallPost` is antitone in the restriction**: a result accepted for the environment
restricted to `A'` is accepted for the one restricted to any `A ⊆ A'`. -/
theorem callPost_only_mono {env : Clif.Env} {A A' : String → List Clif.Val → Clif.Mem → Prop}
    (hAA : ∀ n vals m, A n vals m → A' n vals m) {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {MR : MemRelT} {sym : String → Int → BitVec 64}
    {d : Option String} {uses : List CV} {w : Arm.ArmState} {r : List CV × Arm.ArmState}
    (h : CallPost (env.only A') exts sigs MR sym d uses w r) :
    CallPost (env.only A) exts sigs MR sym d uses w r := by
  refine ⟨fun ext hext g sl cm args vals rvals cm' hg hd ha hmr hret hlen => ?_,
    fun sig hsig n g sl cm u args vals rvals cm' hd hu hg hs hlo h8 hall hmr hret hlen hty => ?_⟩
  · obtain ⟨g', hg', hret'⟩ := only_returned_mono hAA hg hret
    exact h.1 ext hext g' sl cm args vals rvals cm' hg' hd ha hmr hret' hlen
  · obtain ⟨g', hg', hret'⟩ := only_returned_mono hAA hg hret
    exact h.2 sig hsig n g' sl cm u args vals rvals cm' hd hu hg' (by simpa using hs) hlo h8 hall
      hmr hret' hlen hty

/-- **The guarded semantics meets both contracts** of the environment restricted to `A`, for a
guard accepting results for a larger restriction `A'`. -/
theorem xCallsOk_guard_only {env : Clif.Env} {A A' : String → List Clif.Val → Clif.Mem → Prop}
    (hAA : ∀ n vals m, A n vals m → A' n vals m) {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {MR : MemRelT} (X : ExtSem)
    (hex : ∀ d uses w, ∃ r, CallPost (env.only A') exts sigs MR X.sym d uses w r) :
    XCallsOk (env.only A) exts MR (X.guard (CallPost (env.only A') exts sigs MR X.sym)) ∧
      XCallsIndOk (env.only A) sigs MR (X.guard (CallPost (env.only A') exts sigs MR X.sym)) := by
  refine ⟨fun ext hext g sl cm w d uses args vals rvals cm' hg hd ha hmr hret hlen => ?_,
    fun sig hsig n g sl cm w u args vals rvals cm' hg hs hlo h8 hall hmr hret hlen hty => ?_⟩
  · obtain ⟨⟨outs, w'⟩, hc, hq⟩ := ExtSem.guard_spec (X := X) (hex d uses w)
    obtain ⟨h1, h2, h3⟩ := (callPost_only_mono hAA hq).1 ext hext g sl cm args vals rvals cm' hg
      hd ha hmr hret hlen
    exact ⟨outs, w', hc, h1, h2, h3⟩
  · obtain ⟨⟨outs, w'⟩, hc, hq⟩ := ExtSem.guard_spec (X := X) (hex none (u :: args) w)
    obtain ⟨h1, h2, h3⟩ := (callPost_only_mono hAA hq).2 sig hsig n g sl cm u args vals rvals cm'
      rfl rfl hg hs hlo h8 hall hmr hret hlen hty
    exact ⟨outs, w', hc, h1, h2, h3⟩

end E2E
