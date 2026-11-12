import FV.E2E.ExtSemGuardR
import FV.E2E.LinkArmXPB

/-!
# `guardR` with results that keep the program (SEM1 #537, #680 (2), #690)

Finding (#690): `ActEntryPR` for `XI.guardRI (CallPostN …)` asks (`CalleeOkGP.ext`) every answer
of the guarded semantics from a world without error to have no error and the same program, but
`ExtSem.guardR`'s ε answers are only `CallPost`-accepted, and `CallPost` never constrains the
program. Guarding with `CallPostX := CallPost ∧ ExtOkR` fixes it:

* `ExtOkR w r`, `CallPostX`, `CallPostNX`; `fixW` (the result world with no error and `w`'s
  program: `RelW` does not read either but the error, which it pins to none),
  `callPost_fixW`, `callPostX_exists_of` (accepted results that keep the program exist where
  accepted results exist), `callPostNX_exists` (for the invocation of call `n`);
* `xCallsOk_guardRX_only` (stage 1, as `xCallsOk_guardR_only`: non-vacuity is inherited);
* **`guardR_ext`**: the guarded semantics keeps `ext` of `X`;
* `ExtSemI` level: **`hX_guardRXI`** (stage 1 for any `XI`), `guardRXI_ext`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- A result that keeps the error and the program of the call world. -/
def ExtOkR (w : Arm.ArmState) (r : List CV × Arm.ArmState) : Prop :=
  Arm.r .ERR w = .None → Arm.r .ERR r.2 = .None ∧ r.2.program = w.program

/-- **`CallPost` with results that keep the program.** -/
def CallPostX (env : Clif.Env) (exts : List Clif.ExtFunc) (sigs : List Clif.Signature)
    (MR : MemRelT) (sym : String → Int → BitVec 64) (d : Option String) (uses : List CV)
    (w : Arm.ArmState) (r : List CV × Arm.ArmState) : Prop :=
  CallPost env exts sigs MR sym d uses w r ∧ ExtOkR w r

/-- `CallPostN` with results that keep the program. -/
def CallPostNX (env : Clif.Env) (p : Clif.Program) (cs : Clif.State) (exts : List Clif.ExtFunc)
    (sigs : List Clif.Signature) (MR : MemRelT) (sym : String → Int → BitVec 64) (n : Nat) :
    Option String → List CV → Arm.ArmState → List CV × Arm.ArmState → Prop :=
  CallPostX (env.only (InvokedN env p cs n)) exts sigs MR sym

/-- The result world `w'` with `w`'s program (if it has no error; else `w` itself). -/
def fixW (w w' : Arm.ArmState) : Arm.ArmState :=
  if Arm.r .ERR w' = .None then Arm.set_program w' w.program else w

theorem relW_set_program {Γ : Rel} {f : Clif.Function} {c : BitVec 64}
    {sl : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {w' : Arm.ArmState} (p : Arm.Program)
    (h : RelW Γ f c sl cm w') : RelW Γ f c sl cm (Arm.set_program w' p) := by
  obtain ⟨⟨hm, hs, ho⟩, hsp, herr⟩ := h
  have e : spv (Arm.set_program w' p) = spv w' := by simp only [spv, r_set_program]
  refine ⟨⟨⟨fun a b hv hb => ?_, hm.valid, hm.symbols⟩, ?_, ?_⟩, e.trans hsp, ?_⟩
  · rw [← hm.bytes a b hv hb]; rfl
  · simpa only [Rel.slotReg, e] using hs
  · simpa only [OutRel, e] using ho
  · rw [r_set_program]; exact herr

theorem callPost_fixW {env : Clif.Env} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature}
    {Γ : Rel} {f : Clif.Function} {c : BitVec 64} {sym : String → Int → BitVec 64}
    {d : Option String} {uses : List CV} {w : Arm.ArmState} {r : List CV × Arm.ArmState}
    (h : CallPost env exts sigs (RelW Γ f c) sym d uses w r) :
    CallPostX env exts sigs (RelW Γ f c) sym d uses w (r.1, fixW w r.2) := by
  by_cases he : Arm.r .ERR r.2 = .None
  · have e : fixW w r.2 = Arm.set_program r.2 w.program := by simp only [fixW, he, ↓reduceIte]
    rw [e]
    refine ⟨⟨fun ext hext g sl cm args vals rvals cm' hg hd ha hmr hret hlen => ?_,
      fun sig hsig n g sl cm u args vals rvals cm' hd hu hg hs hlo hargs hmr hret hlen hty => ?_⟩,
      fun _ => ⟨by rw [r_set_program]; exact he, rfl⟩⟩
    · obtain ⟨h1, h2, h3⟩ := h.1 ext hext g sl cm args vals rvals cm' hg hd ha hmr hret hlen
      exact ⟨h1, h2, relW_set_program _ h3⟩
    · obtain ⟨h1, h2, h3⟩ :=
        h.2 sig hsig n g sl cm u args vals rvals cm' hd hu hg hs hlo hargs hmr hret hlen hty
      exact ⟨h1, h2, relW_set_program _ h3⟩
  · -- no contract applies (it would pin the error to none): any result is accepted
    refine ⟨⟨fun ext hext g sl cm args vals rvals cm' hg hd ha hmr hret hlen => ?_,
      fun sig hsig n g sl cm u args vals rvals cm' hd hu hg hs hlo hargs hmr hret hlen hty => ?_⟩,
      fun herr => ?_⟩
    · exact absurd (h.1 ext hext g sl cm args vals rvals cm' hg hd ha hmr hret hlen).2.2.2.2 he
    · exact absurd
        (h.2 sig hsig n g sl cm u args vals rvals cm' hd hu hg hs hlo hargs hmr hret hlen hty).2.2.2.2
        he
    · simp only [fixW, he, ↓reduceIte]; exact ⟨herr, trivial⟩

/-- **Accepted results that keep the program exist** where accepted results exist. -/
theorem callPostX_exists_of {env : Clif.Env} {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {Γ : Rel} {f : Clif.Function} {c : BitVec 64}
    {sym : String → Int → BitVec 64}
    (hex : ∀ d uses w, ∃ r, CallPost env exts sigs (RelW Γ f c) sym d uses w r) :
    ∀ d uses w, ∃ r, CallPostX env exts sigs (RelW Γ f c) sym d uses w r := fun d uses w =>
  let ⟨r, hr⟩ := hex d uses w
  ⟨_, callPost_fixW hr⟩

/-- **For the invocation of call `n`** (`callPost_invokedN_exists`). -/
theorem callPostNX_exists {env : Clif.Env} {p : Clif.Program} {cs : Clif.State}
    {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {Γ : Rel} {f : Clif.Function}
    {c : BitVec 64} {sym : String → Int → BitVec 64} (hR : InvokedRetOk env p cs exts sigs)
    (n : Nat) : ∀ d uses w, ∃ r, CallPostNX env p cs exts sigs (RelW Γ f c) sym n d uses w r :=
  callPostX_exists_of (callPost_invokedN_exists (hR n))

/-- **Stage 1 for `guardR` on `CallPostX`** (`xCallsOk_guardR_only`). -/
theorem xCallsOk_guardRX_only {env : Clif.Env} {A A' : String → List Clif.Val → Clif.Mem → Prop}
    (hAA : ∀ n vals m, A n vals m → A' n vals m) {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {MR : MemRelT} (X : ExtSem)
    (hex : ∀ d uses w, ∃ r, CallPostX (env.only A') exts sigs MR X.sym d uses w r) :
    XCallsOk (env.only A) exts MR (X.guardR (CallPostX (env.only A') exts sigs MR X.sym)) ∧
      XCallsIndOk (env.only A) sigs MR (X.guardR (CallPostX (env.only A') exts sigs MR X.sym)) := by
  refine ⟨fun ext hext g sl cm w d uses args vals rvals cm' hg hd ha hmr hret hlen => ?_,
    fun sig hsig n g sl cm w u args vals rvals cm' hg hs hlo hargs hmr hret hlen hty => ?_⟩
  · have hn : ¬ ∀ r, CallPostX (env.only A') exts sigs MR X.sym d uses w r := fun h =>
      callPost_not_vacuous (sl := sl) hext hg hd ha hmr hret hlen fun r =>
        callPost_only_mono hAA (h r).1
    obtain ⟨⟨outs, w'⟩, hc, hq⟩ := ExtSem.guardR_spec (X := X) (hex d uses w) hn
    obtain ⟨h1, h2, h3⟩ := (callPost_only_mono hAA hq.1).1 ext hext g sl cm args vals rvals cm' hg
      hd ha hmr hret hlen
    exact ⟨outs, w', hc, h1, h2, h3⟩
  · have hn : ¬ ∀ r, CallPostX (env.only A') exts sigs MR X.sym none (u :: args) w r := fun h =>
      callPost_not_vacuous_ind (sl := sl) hsig hg hs hlo hargs hmr hret hlen hty
        fun r => callPost_only_mono hAA (h r).1
    obtain ⟨⟨outs, w'⟩, hc, hq⟩ := ExtSem.guardR_spec (X := X) (hex none (u :: args) w) hn
    obtain ⟨h1, h2, h3⟩ := (callPost_only_mono hAA hq.1).2 sig hsig n g sl cm u args vals rvals cm'
      rfl rfl hg hs hlo hargs hmr hret hlen hty
    exact ⟨outs, w', hc, h1, h2, h3⟩

/-- **The guarded semantics keeps `X`'s `ext`** when the guard's results keep the program. -/
theorem guardR_ext {X : ExtSem}
    {Q : Option String → List CV → Arm.ArmState → List CV × Arm.ArmState → Prop}
    (hQ : ∀ d uses w r, Q d uses w r → ExtOkR w r)
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
      exact hQ d uses w _ hq herr
    · simp only [hq, ↓reduceIte] at h
      split at h
      · rename_i hex
        simp only [Option.some.injEq] at h
        have := hQ d uses w _ (Classical.choose_spec hex) herr
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
      have := hQ d uses w _ (Classical.choose_spec hex.1) herr
      rw [h] at this
      exact this
    · cases h

/-- **The per-state callee contracts of the `CallPostNX`-guarded semantics** (`hX_guardRI`). -/
theorem hX_guardRXI {env : Clif.Env} {p : Clif.Program} {cs : Clif.State}
    {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {Γ : Rel} {f : Clif.Function}
    {c : BitVec 64} (XI : ExtSemI) (hnrc : NoRetCall env p cs)
    (hR : InvokedRetOk env p cs exts sigs) :
    ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) exts (RelW Γ f c)
        ((XI.guardRI (CallPostNX env p cs exts sigs (RelW Γ f c) XI.sym)).at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) sigs (RelW Γ f c)
        ((XI.guardRI (CallPostNX env p cs exts sigs (RelW Γ f c) XI.sym)).at n) :=
  fun _ n hs => xCallsOk_guardRX_only (invoked_sub_invokedN hnrc hs) (XI.at n)
    (callPostNX_exists hR n)

/-- **`ext` of the `CallPostNX`-guarded call `n`** from `ext` of `XI`'s call `n`. -/
theorem guardRXI_ext {env : Clif.Env} {p : Clif.Program} {cs : Clif.State}
    {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {MR : MemRelT} (XI : ExtSemI) (n : Nat)
    (hX : ∀ d uses w outs w', (XI.at n).call d uses w = some (outs, w') → Arm.r .ERR w = .None →
      Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    ∀ d uses w outs w',
      ((XI.guardRI (CallPostNX env p cs exts sigs MR XI.sym)).at n).call d uses w = some (outs, w') →
      Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program :=
  guardR_ext (fun _ _ _ _ h => h.2) hX

end E2E
