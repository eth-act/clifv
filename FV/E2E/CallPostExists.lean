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
invocation `(n0, vals0, cm0)`. -/
theorem callPost_only_exists {env : Clif.Env} {A : String → List Clif.Val → Clif.Mem → Prop}
    {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {Γ : Rel} {f : Clif.Function}
    {c : BitVec 64} {sym : String → Int → BitVec 64}
    {n0 : String} {vals0 : List Clif.Val} {cm0 : Clif.Mem}
    (hA : ∀ n vals cm, A n vals cm → n = n0 ∧ vals = vals0 ∧ cm = cm0)
    (ℓ : Nat)
    (hR : ∀ g rvals cm', env.extern n0 = some g → g vals0 cm0 = .returned rvals cm' →
      (∀ a k, cm'.valid a k = true → cm0.valid a k = true) ∧ cm'.symbols = cm0.symbols ∧
      rvals.length ≤ ℓ ∧
      (∀ ext ∈ exts, ext.name = n0 → rvals.length = ext.sig.returns.length →
        (sigRets ext.sig).length = ℓ) ∧
      (∀ sig ∈ sigs, (∀ s, env.sigOf n0 = some s → sig.abiMatch s = true) →
        rvals.length = sig.returns.length → (sigRets sig).length = ℓ)) :
    ∀ d uses w, ∃ r, CallPost (env.only A) exts sigs (RelW Γ f c) sym d uses w r := by
  intro d uses w
  -- the invocation's outcome (if it returns)
  by_cases hex : ∃ g rvals cm', env.extern n0 = some g ∧ g vals0 cm0 = .returned rvals cm'
  · obtain ⟨g0, rv0, cm1, hg0, hr0⟩ := hex
    obtain ⟨hv, hsym, hℓ, hext, hsig⟩ := hR g0 rv0 cm1 hg0 hr0
    -- every admitted returning call is this one
    have key : ∀ (n : String) g' vals rvals cm cm', (env.only A).extern n = some g' →
        g' vals cm = .returned rvals cm' → n = n0 ∧ rvals = rv0 ∧ cm = cm0 ∧ cm' = cm1 := by
      intro n g' vals rvals cm cm' hg' hret
      obtain ⟨g, hg1, rfl⟩ := Clif.Env.only_extern_eq hg'
      obtain ⟨hAi, hret'⟩ := onlyFn_returned hret
      obtain ⟨rfl, rfl, rfl⟩ := hA n vals cm hAi
      rw [hg0] at hg1
      cases hg1
      rw [hr0] at hret'
      cases hret'
      exact ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨(outsOf rv0 ℓ, patchW cm1 w), fun ext hext' g sl cm args vals rvals cm' hg _ _ hmr hret
        hlen => ?_, fun sig hsig' n g sl cm u args vals rvals cm' _ _ hg hs _ _ _ hmr hret hlen _ => ?_⟩
    · obtain ⟨hn, rfl, rfl, rfl⟩ := key _ _ _ _ _ _ hg hret
      exact ⟨by rw [outsOf_length hℓ]; exact (hext ext hext' hn hlen).symm, prefixHold_outsOf hℓ,
        relW_patchW hmr hv hsym⟩
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := key _ _ _ _ _ _ hg hret
      exact ⟨by rw [outsOf_length hℓ]; exact (hsig sig hsig' (by simpa using hs) hlen).symm,
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

end E2E
