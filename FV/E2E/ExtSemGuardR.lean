import FV.E2E.CallPostExists

/-!
# A guard that keeps undefined calls undefined outside the related invocations
(SEM1 #537, item (d), docs/plans/uninit.md §5.9, Finding (UninitZ13), #680)

`ExtSem.guard X Q` answers an ε-chosen `Q`-result wherever `X`'s is not one, also where `X` is
undefined and every result satisfies `Q` (no CLIF invocation is related to the call): there the
machine contract, vacuous for `X`, would have to match the ε answer. `ExtSem.guardR X Q` answers
`X`'s result where it satisfies `Q`; otherwise an ε-chosen `Q`-result only where `Q` is not
vacuous; otherwise `X`'s (possibly undefined) result:

* `guardR_of` (`X`'s accepted result is kept), `guardR_spec` (where `Q` is satisfiable and not
  vacuous, an accepted result), **`guardR_eq_of`** (stage 2: where every non-vacuous `Q` accepts
  `X`'s result, every answer is `X`'s);
* `callPost_not_vacuous` (at a query of the extern contracts some result is rejected), and
  **`xCallsOk_guardR_only`** (stage 1, as `xCallsOk_guard_only`).
-/

namespace E2E

open Backend Backend.Proof

open Classical in
/-- **`X` guarded by `Q`, undefined outside `Q`'s scope**: `X`'s result where it satisfies `Q`;
otherwise an ε-chosen `Q`-result where `Q` is satisfiable and not vacuous; otherwise `X`'s. -/
noncomputable def _root_.Backend.Proof.ExtSem.guardR (X : ExtSem)
    (Q : Option String → List CV → Arm.ArmState → List CV × Arm.ArmState → Prop) : ExtSem where
  call d uses w :=
    match X.call d uses w with
    | some r => if Q d uses w r then some r
      else if h : ∃ r', Q d uses w r' then some (Classical.choose h) else some r
    | none => if h : (∃ r', Q d uses w r') ∧ ¬ ∀ r', Q d uses w r' then some (Classical.choose h.1)
      else none
  sym := X.sym
  tp := X.tp
  tlsFlags := X.tlsFlags

theorem _root_.Backend.Proof.ExtSem.guardR_of {X : ExtSem}
    {Q : Option String → List CV → Arm.ArmState → List CV × Arm.ArmState → Prop}
    {d : Option String} {uses : List CV} {w : Arm.ArmState} {r : List CV × Arm.ArmState}
    (hx : X.call d uses w = some r) (hq : Q d uses w r) : (X.guardR Q).call d uses w = some r := by
  simp only [ExtSem.guardR, hx, hq, ↓reduceIte]

/-- **Where `Q` is satisfiable and not vacuous, the guarded semantics answers a `Q`-result.** -/
theorem _root_.Backend.Proof.ExtSem.guardR_spec {X : ExtSem}
    {Q : Option String → List CV → Arm.ArmState → List CV × Arm.ArmState → Prop}
    {d : Option String} {uses : List CV} {w : Arm.ArmState} (h : ∃ r, Q d uses w r)
    (hn : ¬ ∀ r, Q d uses w r) :
    ∃ r, (X.guardR Q).call d uses w = some r ∧ Q d uses w r := by
  simp only [ExtSem.guardR]
  cases hx : X.call d uses w with
  | some r =>
    by_cases hq : Q d uses w r
    · exact ⟨r, by simp [hq], hq⟩
    · exact ⟨Classical.choose h, by simp [hq, h], Classical.choose_spec h⟩
  | none =>
    refine ⟨Classical.choose h, ?_, Classical.choose_spec h⟩
    dsimp only
    split
    · rfl
    · rename_i hc; exact absurd ⟨h, hn⟩ hc

/-- **Stage 2**: where `Q` is not vacuous only if `X` answers a `Q`-result, every answer of the
guarded semantics is `X`'s. -/
theorem _root_.Backend.Proof.ExtSem.guardR_eq_of {X : ExtSem}
    {Q : Option String → List CV → Arm.ArmState → List CV × Arm.ArmState → Prop}
    {d : Option String} {uses : List CV} {w : Arm.ArmState}
    (h : (¬ ∀ r, Q d uses w r) → ∃ x, X.call d uses w = some x ∧ Q d uses w x)
    {r : List CV × Arm.ArmState} (hr : (X.guardR Q).call d uses w = some r) :
    X.call d uses w = some r := by
  simp only [ExtSem.guardR] at hr
  cases hx : X.call d uses w with
  | some x =>
    rw [hx] at hr
    by_cases hq : Q d uses w x
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hr; rw [hr]
    · obtain ⟨x', hx', hq'⟩ := h fun hall => hq (hall x)
      rw [hx] at hx'; cases hx'
      exact absurd hq' hq
  | none =>
    rw [hx] at hr
    dsimp only at hr
    by_cases hc : (∃ r', Q d uses w r') ∧ ¬ ∀ r', Q d uses w r'
    · obtain ⟨x', hx', -⟩ := h hc.2
      rw [hx] at hx'; cases hx'
    · split at hr
      · rename_i hc'; exact absurd hc' hc
      · cases hr

/-- **At a query of the extern contracts, `CallPost` rejects some result** (one with a wrong
number of values). -/
theorem callPost_not_vacuous {env : Clif.Env} {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {MR : MemRelT} {sym : String → Int → BitVec 64}
    {d : Option String} {uses : List CV} {w : Arm.ArmState}
    {ext : Clif.ExtFunc} (hext : ext ∈ exts) {g : List Clif.Val → Clif.Mem → Clif.Outcome}
    {sl : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {args : List CV} {vals rvals : List Clif.Val}
    {cm' : Clif.Mem} (hg : env.extern ext.name = some g)
    (hd : d = some ext.name ∧ uses = args ∨
      d = none ∧ ext.colocated = false ∧ uses = ofX (sym ext.name 0) :: args)
    (ha : ArgsAt ext.sig vals args w) (hmr : MR sl cm w) (hret : g vals cm = .returned rvals cm')
    (hlen : rvals.length = ext.sig.returns.length) :
    ¬ ∀ r, CallPost env exts sigs MR sym d uses w r := fun hall => by
  have := ((hall (List.replicate (ext.sig.returns.length + 1) (ofX 0), w)).1 ext hext g sl cm
    args vals rvals cm' hg hd ha hmr hret hlen).1
  simp at this

theorem callPost_not_vacuous_ind {env : Clif.Env} {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {MR : MemRelT} {sym : String → Int → BitVec 64}
    {w : Arm.ArmState} {sig : Clif.Signature} (hsig : sig ∈ sigs) {n : String}
    {g : List Clif.Val → Clif.Mem → Clif.Outcome} {sl : List (Clif.SlotId × Nat)} {cm : Clif.Mem}
    {u : CV} {args : List CV} {vals rvals : List Clif.Val} {cm' : Clif.Mem}
    (hg : env.extern n = some g) (hs : ∀ s, env.sigOf n = some s → sig.abiMatch s = true)
    (hu : lo64 u = sym n 0) (h8 : vals.length ≤ 8) (hall : AllHold vals args) (hmr : MR sl cm w)
    (hret : g vals cm = .returned rvals cm') (hlen : rvals.length = sig.returns.length)
    (hty : vals.map (·.ty) = Clif.AbiParam.tys sig.params) :
    ¬ ∀ r, CallPost env exts sigs MR sym none (u :: args) w r := fun hall' => by
  have := ((hall' (List.replicate (sig.returns.length + 1) (ofX 0), w)).2 sig hsig n g sl cm u
    args vals rvals cm' rfl rfl hg hs hu h8 hall hmr hret hlen hty).1
  simp at this

/-- **Stage 1 for `guardR`** (`xCallsOk_guard_only`): with an accepted result for every call, the
guarded semantics meets both extern contracts of the environment restricted to `A ⊆ A'`. -/
theorem xCallsOk_guardR_only {env : Clif.Env} {A A' : String → List Clif.Val → Clif.Mem → Prop}
    (hAA : ∀ n vals m, A n vals m → A' n vals m) {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {MR : MemRelT} (X : ExtSem)
    (hex : ∀ d uses w, ∃ r, CallPost (env.only A') exts sigs MR X.sym d uses w r) :
    XCallsOk (env.only A) exts MR (X.guardR (CallPost (env.only A') exts sigs MR X.sym)) ∧
      XCallsIndOk (env.only A) sigs MR (X.guardR (CallPost (env.only A') exts sigs MR X.sym)) := by
  refine ⟨fun ext hext g sl cm w d uses args vals rvals cm' hg hd ha hmr hret hlen => ?_,
    fun sig hsig n g sl cm w u args vals rvals cm' hg hs hlo h8 hall hmr hret hlen hty => ?_⟩
  · have hn : ¬ ∀ r, CallPost (env.only A') exts sigs MR X.sym d uses w r := fun h =>
      callPost_not_vacuous (sl := sl) hext hg hd ha hmr hret hlen fun r => callPost_only_mono hAA (h r)
    obtain ⟨⟨outs, w'⟩, hc, hq⟩ := ExtSem.guardR_spec (X := X) (hex d uses w) hn
    obtain ⟨h1, h2, h3⟩ := (callPost_only_mono hAA hq).1 ext hext g sl cm args vals rvals cm' hg
      hd ha hmr hret hlen
    exact ⟨outs, w', hc, h1, h2, h3⟩
  · have hn : ¬ ∀ r, CallPost (env.only A') exts sigs MR X.sym none (u :: args) w r := fun h =>
      callPost_not_vacuous_ind (sl := sl) hsig hg hs hlo h8 hall hmr hret hlen hty
        fun r => callPost_only_mono hAA (h r)
    obtain ⟨⟨outs, w'⟩, hc, hq⟩ := ExtSem.guardR_spec (X := X) (hex none (u :: args) w) hn
    obtain ⟨h1, h2, h3⟩ := (callPost_only_mono hAA hq).2 sig hsig n g sl cm u args vals rvals cm'
      rfl rfl hg hs hlo h8 hall hmr hret hlen hty
    exact ⟨outs, w', hc, h1, h2, h3⟩

end E2E
