import FV.E2E.ExtSemGuardRX

/-!
# `guardR` keeping the program only at related calls (SEM1 #537, #680 (3), stage 2)

Finding: `CallPostNX := CallPostN ∧ ExtOkR` (#690) is never vacuous at a world without error
(`ExtOkR` rejects results with an error), also where `CallPostN` is vacuous (no CLIF invocation of
count `n` is related to the call). There `guardR` replaces a missing answer of `X` by an ε-chosen
result, which no machine call realises, so `CalleeOkGP.os` of `XI.guardRI (CallPostNX …)` cannot
be proved from `X`'s contracts at the activation's call states (e.g. the calls of a later
activation at the same `sp` after the return, which `OnCallPR` also admits). Asking `ExtOkR` only
where `CallPost` is not vacuous keeps `CallPostN`'s vacuity, so the guarded semantics answers
`X`'s results at unrelated calls:

* `CallPostXR`, `CallPostNXR`; `callPostXR_exists_of`, `callPostNXR_exists`;
* `xCallsOk_guardRXR_only` (stage 1); **`guardR_extV`** (`ext` when the guard's results keep the
  program where it is not vacuous); **`hX_guardRXRI`**, `guardRXRI_ext`;
* **`guardRXR_sub`**: where `CallPost` is not vacuous only if `X` answers a `CallPost`-result
  (stage 2), every answer of the guarded semantics is `X`'s, given `X`'s `ext`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **`CallPost` with results that keep the program where `CallPost` is not vacuous.** -/
def CallPostXR (env : Clif.Env) (exts : List Clif.ExtFunc) (sigs : List Clif.Signature)
    (MR : MemRelT) (sym : String → Int → BitVec 64) (d : Option String) (uses : List CV)
    (w : Arm.ArmState) (r : List CV × Arm.ArmState) : Prop :=
  CallPost env exts sigs MR sym d uses w r ∧
    ((¬ ∀ r', CallPost env exts sigs MR sym d uses w r') → ExtOkR w r)

/-- `CallPostN` with results that keep the program where it is not vacuous. -/
def CallPostNXR (env : Clif.Env) (p : Clif.Program) (cs : Clif.State) (exts : List Clif.ExtFunc)
    (sigs : List Clif.Signature) (MR : MemRelT) (sym : String → Int → BitVec 64) (n : Nat) :
    Option String → List CV → Arm.ArmState → List CV × Arm.ArmState → Prop :=
  CallPostXR (env.only (InvokedN env p cs n)) exts sigs MR sym

/-- `CallPostXR` is vacuous where `CallPost` is. -/
theorem callPostXR_vacuous {env : Clif.Env} {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {MR : MemRelT} {sym : String → Int → BitVec 64}
    {d : Option String} {uses : List CV} {w : Arm.ArmState}
    (h : ¬ ∀ r, CallPostXR env exts sigs MR sym d uses w r) :
    ¬ ∀ r, CallPost env exts sigs MR sym d uses w r :=
  fun hall => h fun r => ⟨hall r, fun hn => absurd hall hn⟩

/-- **Accepted results exist** where `CallPost`-results exist. -/
theorem callPostXR_exists_of {env : Clif.Env} {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {Γ : Rel} {f : Clif.Function} {c : BitVec 64}
    {sym : String → Int → BitVec 64}
    (hex : ∀ d uses w, ∃ r, CallPost env exts sigs (RelW Γ f c) sym d uses w r) :
    ∀ d uses w, ∃ r, CallPostXR env exts sigs (RelW Γ f c) sym d uses w r := fun d uses w =>
  let ⟨_, hr⟩ := hex d uses w
  ⟨_, (callPost_fixW hr).1, fun _ => (callPost_fixW hr).2⟩

/-- **For the invocation of call `n`** (`callPost_invokedN_exists`). -/
theorem callPostNXR_exists {env : Clif.Env} {p : Clif.Program} {cs : Clif.State}
    {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {Γ : Rel} {f : Clif.Function}
    {c : BitVec 64} {sym : String → Int → BitVec 64} (hR : InvokedRetOk env p cs exts sigs)
    (n : Nat) : ∀ d uses w, ∃ r, CallPostNXR env p cs exts sigs (RelW Γ f c) sym n d uses w r :=
  callPostXR_exists_of (callPost_invokedN_exists (hR n))

/-- **Stage 1 for `guardR` on `CallPostXR`** (`xCallsOk_guardRX_only`). -/
theorem xCallsOk_guardRXR_only {env : Clif.Env} {A A' : String → List Clif.Val → Clif.Mem → Prop}
    (hAA : ∀ n vals m, A n vals m → A' n vals m) {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {MR : MemRelT} (X : ExtSem)
    (hex : ∀ d uses w, ∃ r, CallPostXR (env.only A') exts sigs MR X.sym d uses w r) :
    XCallsOk (env.only A) exts MR (X.guardR (CallPostXR (env.only A') exts sigs MR X.sym)) ∧
      XCallsIndOk (env.only A) sigs MR (X.guardR (CallPostXR (env.only A') exts sigs MR X.sym)) := by
  refine ⟨fun ext hext g sl cm w d uses args vals rvals cm' hg hd ha hmr hret hlen => ?_,
    fun sig hsig n g sl cm w u args vals rvals cm' hg hs hlo hargs hmr hret hlen hty => ?_⟩
  · have hn : ¬ ∀ r, CallPostXR (env.only A') exts sigs MR X.sym d uses w r := fun h =>
      callPost_not_vacuous (sl := sl) hext hg hd ha hmr hret hlen fun r =>
        callPost_only_mono hAA (h r).1
    obtain ⟨⟨outs, w'⟩, hc, hq⟩ := ExtSem.guardR_spec (X := X) (hex d uses w) hn
    obtain ⟨h1, h2, h3⟩ := (callPost_only_mono hAA hq.1).1 ext hext g sl cm args vals rvals cm' hg
      hd ha hmr hret hlen
    exact ⟨outs, w', hc, h1, h2, h3⟩
  · have hn : ¬ ∀ r, CallPostXR (env.only A') exts sigs MR X.sym none (u :: args) w r := fun h =>
      callPost_not_vacuous_ind (sl := sl) hsig hg hs hlo hargs hmr hret hlen hty
        fun r => callPost_only_mono hAA (h r).1
    obtain ⟨⟨outs, w'⟩, hc, hq⟩ := ExtSem.guardR_spec (X := X) (hex none (u :: args) w) hn
    obtain ⟨h1, h2, h3⟩ := (callPost_only_mono hAA hq.1).2 sig hsig n g sl cm u args vals rvals cm'
      rfl rfl hg hs hlo hargs hmr hret hlen hty
    exact ⟨outs, w', hc, h1, h2, h3⟩

/-- **The guarded semantics keeps `X`'s `ext`** when the guard's results keep the program where
the guard is not vacuous. -/
theorem guardR_extV {X : ExtSem}
    {Q : Option String → List CV → Arm.ArmState → List CV × Arm.ArmState → Prop}
    (hQ : ∀ d uses w r, (¬ ∀ r', Q d uses w r') → Q d uses w r → ExtOkR w r)
    (hX : ∀ d uses w outs w', X.call d uses w = some (outs, w') → Arm.r .ERR w = .None →
      Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    ∀ d uses w outs w', (X.guardR Q).call d uses w = some (outs, w') → Arm.r .ERR w = .None →
      Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  intro d uses w outs w' h herr
  simp only [ExtSem.guardR] at h
  cases hx : X.call d uses w with
  | some r =>
    rw [hx] at h
    dsimp only at h
    by_cases hq : Q d uses w r
    · simp only [hq, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact hX d uses w outs w' hx herr
    · simp only [hq, ↓reduceIte] at h
      split at h
      · rename_i hex
        simp only [Option.some.injEq] at h
        have := hQ d uses w _ (fun hall => hq (hall r)) (Classical.choose_spec hex) herr
        rw [h] at this
        exact this
      · simp only [Option.some.injEq] at h
        subst h
        exact hX d uses w outs w' hx herr
  | none =>
    rw [hx] at h
    dsimp only at h
    split at h
    · rename_i hex
      simp only [Option.some.injEq] at h
      have := hQ d uses w _ hex.2 (Classical.choose_spec hex.1) herr
      rw [h] at this
      exact this
    · cases h

/-- **The per-state callee contracts of the `CallPostNXR`-guarded semantics** (`hX_guardRXI`). -/
theorem hX_guardRXRI {env : Clif.Env} {p : Clif.Program} {cs : Clif.State}
    {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {Γ : Rel} {f : Clif.Function}
    {c : BitVec 64} (XI : ExtSemI) (hnrc : NoRetCall env p cs)
    (hR : InvokedRetOk env p cs exts sigs) :
    ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) exts (RelW Γ f c)
        ((XI.guardRI (CallPostNXR env p cs exts sigs (RelW Γ f c) XI.sym)).at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) sigs (RelW Γ f c)
        ((XI.guardRI (CallPostNXR env p cs exts sigs (RelW Γ f c) XI.sym)).at n) :=
  fun _ n hs => xCallsOk_guardRXR_only (invoked_sub_invokedN hnrc hs) (XI.at n)
    (callPostNXR_exists hR n)

/-- **`ext` of the `CallPostNXR`-guarded call `n`** from `ext` of `XI`'s call `n`. -/
theorem guardRXRI_ext {env : Clif.Env} {p : Clif.Program} {cs : Clif.State}
    {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {MR : MemRelT} (XI : ExtSemI) (n : Nat)
    (hX : ∀ d uses w outs w', (XI.at n).call d uses w = some (outs, w') → Arm.r .ERR w = .None →
      Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    ∀ d uses w outs w',
      ((XI.guardRI (CallPostNXR env p cs exts sigs MR XI.sym)).at n).call d uses w = some (outs, w') →
      Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program :=
  guardR_extV (fun _ _ _ _ hn h => h.2 (callPostXR_vacuous hn)) hX

/-- **Stage 2 interface for `CallPostXR`**: where `CallPost` is not vacuous only if `X` answers a
`CallPost`-result, every answer of the guarded semantics is `X`'s (`X` keeping the program). -/
theorem guardRXR_sub {env : Clif.Env} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature}
    {MR : MemRelT} {sym : String → Int → BitVec 64} {X : ExtSem} {d : Option String}
    {uses : List CV} {w : Arm.ArmState}
    (hX : ∀ outs w', X.call d uses w = some (outs, w') → Arm.r .ERR w = .None →
      Arm.r .ERR w' = .None ∧ w'.program = w.program)
    (h2 : (¬ ∀ r, CallPost env exts sigs MR sym d uses w r) →
      ∃ x, X.call d uses w = some x ∧ CallPost env exts sigs MR sym d uses w x)
    {r : List CV × Arm.ArmState}
    (hr : (X.guardR (CallPostXR env exts sigs MR sym)).call d uses w = some r) :
    X.call d uses w = some r :=
  ExtSem.guardR_eq_of (fun hn => by
    obtain ⟨⟨outs, w'⟩, hx, hq⟩ := h2 (callPostXR_vacuous hn)
    exact ⟨_, hx, hq, fun _ => hX outs w' hx⟩) hr

end E2E
