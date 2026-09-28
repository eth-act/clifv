import FV.Isle.Interp

/-!
# The interpreter only changes the embedding state through extern constructors

`Pres I R x`: running `x` from a state satisfying `I` ends (if it succeeds) in a state
satisfying `I` that is `R`-related to the start. If every extern constructor call preserves
`I` and moves along the preorder `R`, then so does every interpreter function, single
(`evalExpr` … `selectRule`) and multi (`evalExprN` … `matchIfLetsN`), at every fuel
(`pres_single`, `pres_multi`). The mid-end instance: `I` = the driver's graph invariant,
`R` = "the valuation only grows" (`FV/Opt/Proof/RuleBase.lean`).
-/

namespace Opt.Proof

open Isle Isle.Interp

section
variable {σ : Type} (I : σ → Prop) (R : σ → σ → Prop)

/-- `x` keeps `I` and moves the state along `R`. -/
def Pres {α : Type} (x : M σ α) : Prop :=
  ∀ s tr a s' tr', I s → x.run (s, tr) = .ok (a, (s', tr')) → I s' ∧ R s s'

/-- `R` is a preorder. -/
structure PreOrd : Prop where
  refl : ∀ s, R s s
  trans : ∀ a b c, R a b → R b c → R a c

variable {I R}

theorem pres_pure (hR : PreOrd R) {α : Type} (a : α) : Pres I R (pure a : M σ α) := by
  intro s tr a' s' tr' hI h
  cases h
  exact ⟨hI, hR.refl _⟩

theorem pres_bind (hR : PreOrd R) {α β : Type} {x : M σ α} {f : α → M σ β}
    (hx : Pres I R x) (hf : ∀ a, Pres I R (f a)) : Pres I R (x >>= f) := by
  intro s tr b s' tr' hI h
  change (StateT.bind x f).run (s, tr) = _ at h
  simp only [StateT.bind, StateT.run] at h
  cases hxr : x (s, tr) with
  | error e => rw [hxr] at h; cases h
  | ok r =>
    rw [hxr] at h
    obtain ⟨a, s1, tr1⟩ := r
    obtain ⟨h1, h2⟩ := hx s tr a s1 tr1 hI hxr
    obtain ⟨h3, h4⟩ := hf a s1 tr1 b s' tr' h1 h
    exact ⟨h3, hR.trans _ _ _ h2 h4⟩

theorem pres_throw {α : Type} (e : Err) : Pres I R (throw e : M σ α) := by
  intro s tr a s' tr' _ h
  cases h

theorem pres_get (hR : PreOrd R) : Pres I R (get : M σ (σ × Array RuleId)) := by
  intro s tr a s' tr' hI h
  cases h
  exact ⟨hI, hR.refl _⟩

theorem pres_fire (hR : PreOrd R) (r : RuleId) : Pres I R (fire r : M σ Unit) := by
  intro s tr a s' tr' hI h
  cases h
  exact ⟨hI, hR.refl _⟩

theorem pres_lift (hR : PreOrd R) {α : Type} (e : Except Err α) :
    Pres I R (liftM e : M σ α) := by
  intro s tr a s' tr' hI h
  cases e with
  | error => cases h
  | ok => cases h; exact ⟨hI, hR.refl _⟩

theorem pres_monadLift (hR : PreOrd R) {α : Type} (e : Except Err α) :
    Pres I R (monadLift e : M σ α) := by
  intro s tr a s' tr' hI h
  cases e with
  | error => cases h
  | ok => cases h; exact ⟨hI, hR.refl _⟩

theorem pres_bindAll (hR : PreOrd R) {α β : Type} {f : α → M σ (List β)}
    (hf : ∀ a, Pres I R (f a)) : ∀ l, Pres I R (bindAll f l)
  | [] => pres_pure hR _
  | a :: as => by
    simp only [bindAll]
    exact pres_bind hR (hf a) fun _ => pres_bind hR (pres_bindAll hR hf as) fun _ => pres_pure hR _

/-- Every result of `bindAll f l` comes from one call `f a` (`a ∈ l`), run from a state
`R`-after the start and ending `R`-before the end. -/
theorem bindAll_run_mem (hR : PreOrd R) {α β : Type} {f : α → M σ (List β)}
    (hf : ∀ a, Pres I R (f a)) : ∀ (l : List α) (s : σ) (tr : Array RuleId) (res : List β)
      (s' : σ) (tr' : Array RuleId), I s →
      (bindAll f l).run (s, tr) = .ok (res, (s', tr')) → ∀ b ∈ res,
      ∃ a ∈ l, ∃ (s1 : σ) (tr1 : Array RuleId) (bs : List β) (s2 : σ) (tr2 : Array RuleId),
        I s1 ∧ R s s1 ∧ (f a).run (s1, tr1) = .ok (bs, (s2, tr2)) ∧
        b ∈ bs ∧ R s2 s'
  | [], s, tr, res, s', tr', _, h, b, hb => by
    simp only [bindAll] at h
    cases h
    simp at hb
  | a :: as, s, tr, res, s', tr', hI, h, b, hb => by
    simp only [bindAll, bind, StateT.bind, StateT.run, pure, StateT.pure, Except.bind] at h
    cases hfa : f a (s, tr) with
    | error e => rw [hfa] at h; cases h
    | ok r1 =>
      obtain ⟨bs, s1, tr1⟩ := r1
      rw [hfa] at h
      simp only at h
      cases hr : bindAll f as (s1, tr1) with
      | error e => rw [hr] at h; cases h
      | ok r2 =>
        obtain ⟨cs, s2, tr2⟩ := r2
        rw [hr] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨hI1, hR1⟩ := hf a s tr bs s1 tr1 hI hfa
        rcases List.mem_append.1 hb with hb | hb
        · exact ⟨a, List.mem_cons_self .., s, tr, bs, s1, tr1, hI, hR.refl _, hfa, hb,
            (pres_bindAll hR hf as s1 tr1 cs s' tr' hI1 hr).2⟩
        · obtain ⟨a', ha', s3, tr3, bs', s4, tr4, h1, h2, h3, h4, h5⟩ :=
            bindAll_run_mem hR hf as s1 tr1 cs s' tr' hI1 hr b hb
          exact ⟨a', List.mem_cons_of_mem _ ha', s3, tr3, bs', s4, tr4, h1,
            hR.trans _ _ _ hR1 h2, h3, h4, h5⟩

end

/-! ## All interpreter functions -/

section
variable {V σ : Type} (p : Program) (cfg : Config) (I : σ → Prop) (R : σ → σ → Prop)

/-- Every extern constructor call keeps `I` and moves along `R`. -/
def CtorPres (sem : Sem V σ) : Prop :=
  ∀ t vs s v s', I s → sem.ctor t vs s = .ok (v, s') → I s' ∧ R s s'

/-- The single-term interpreter at fuel `n`. -/
def SinglePres (sem : Sem V σ) (n : Nat) : Prop :=
  (∀ e env, Pres I R (evalExpr p sem cfg n e env)) ∧
  (∀ es env, Pres I R (evalArgs p sem cfg n es env)) ∧
  (∀ bs env, Pres I R (evalBinds p sem cfg n bs env)) ∧
  (∀ ty t vs, Pres I R (applyTerm p sem cfg n ty t vs)) ∧
  (∀ r vs, Pres I R (matchRule p sem cfg n r vs)) ∧
  (∀ ils env, Pres I R (matchIfLets p sem cfg n ils env)) ∧
  (∀ r vs, Pres I R (tryRule p sem cfg n r vs)) ∧
  (∀ rs vs, Pres I R (alsoMatching p sem cfg n rs vs)) ∧
  (∀ term rs vs, Pres I R (selectRule p sem cfg n term rs vs))

/-- The multi-term interpreter at fuel `n`. -/
def MultiPres (msem : MultiSem V σ) (n : Nat) : Prop :=
  (∀ e env, Pres I R (evalExprN p msem cfg n e env)) ∧
  (∀ es env, Pres I R (evalArgsN p msem cfg n es env)) ∧
  (∀ bs env, Pres I R (evalBindsN p msem cfg n bs env)) ∧
  (∀ ty t vs, Pres I R (applyTermN p msem cfg n ty t vs)) ∧
  (∀ term rs vs, Pres I R (applyMulti p msem cfg n term rs vs)) ∧
  (∀ ils env, Pres I R (matchIfLetsN p msem cfg n ils env))

/-- Every extern multi-constructor call keeps `I` and moves along `R`. -/
def CtorMultiPres (msem : MultiSem V σ) : Prop :=
  ∀ t vs s ws s', I s → msem.ctorMulti t vs s = .ok (ws, s') → I s' ∧ R s s'

variable {p cfg I R}

theorem pres_single (hR : PreOrd R) {sem : Sem V σ} (hc : CtorPres I R sem) :
    ∀ n, SinglePres p cfg I R sem n := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      first
      | (simp only [evalExpr]; exact pres_throw _)
      | (simp only [evalArgs]; exact pres_throw _)
      | (simp only [evalBinds]; exact pres_throw _)
      | (simp only [applyTerm]; exact pres_throw _)
      | (simp only [matchRule]; exact pres_throw _)
      | (simp only [matchIfLets]; exact pres_throw _)
      | (simp only [tryRule]; exact pres_throw _)
      | (simp only [alsoMatching]; exact pres_throw _)
      | (simp only [selectRule]; exact pres_throw _)
  | succ n ih =>
    obtain ⟨hE, hA, hB, hT, hM, hI, hTr, hAl, hS⟩ := ih
    have pb := @pres_bind σ I R hR
    have pp := @pres_pure σ I R hR
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e env
      cases e with
      | var _ x => simp only [evalExpr]; split <;> first | exact pp _ | exact pres_throw _
      | constBool => simp only [evalExpr]; exact pp _
      | constInt => simp only [evalExpr]; exact pp _
      | constPrim => simp only [evalExpr]; split <;> first | exact pp _ | exact pres_throw _
      | «let» _ bs body =>
        simp only [evalExpr]
        exact pb (hB _ _) fun r => by split <;> first | exact hE _ _ | exact pp _
      | term ty t args =>
        simp only [evalExpr]
        exact pb (hA _ _) fun r => by split <;> first | exact hT _ _ _ | exact pp _
    · intro es env
      cases es with
      | nil => simp only [evalArgs]; exact pp _
      | cons e es =>
        simp only [evalArgs]
        exact pb (hE _ _) fun r => by
          split
          · exact pp _
          · exact pb (hA _ _) fun r => by split <;> exact pp _
    · intro bs env
      cases bs with
      | nil => simp only [evalBinds]; exact pp _
      | cons b bs =>
        obtain ⟨x, ty, e⟩ := b
        simp only [evalBinds]
        exact pb (hE _ _) fun r => by
          split
          · exact pp _
          · split
            · exact hB _ _
            · exact pres_throw _
    · intro ty t vs
      simp only [applyTerm]
      refine pb (pres_monadLift hR _) fun term => ?_
      split
      · exact pp _
      · exact pp _
      · split
        · exact pres_throw _
        · intro s tr a s' tr' hIs h
          simp only [bind, StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure, Except.bind]
            at h
          cases hct : sem.ctor term vs s with
          | ok r =>
            obtain ⟨v, st'⟩ := r
            simp only [hct, set, StateT.set, Except.bind, StateT.pure] at h
            cases h
            exact hc _ _ _ _ _ hIs hct
          | fail =>
            simp only [hct] at h
            split at h
            · cases h; exact ⟨hIs, hR.refl _⟩
            · cases h
          | unmodeled w => simp only [hct] at h; cases h
      · split
        · exact pres_throw _
        · exact pb (hS _ _ _) fun r => by
            split
            · split
              · exact pp _
              · exact pres_throw _
            · exact pb (hE _ _) fun r => by
                split
                · exact pb (pres_fire hR _) fun _ => pp _
                · exact pp _
      · exact pres_throw _
    · intro r vs
      simp only [matchRule]
      refine pb (pres_get hR) fun st => ?_
      refine pb (pres_monadLift hR _) fun r => ?_
      split
      · exact pp _
      · exact hI _ _
    · intro ils env
      cases ils with
      | nil => simp only [matchIfLets]; exact pp _
      | cons il ils =>
        simp only [matchIfLets]
        exact pb (hE _ _) fun r => by
          split
          · exact pp _
          · exact pb (pres_get hR) fun st => pb (pres_monadLift hR _) fun r => by
              split
              · exact pp _
              · exact hI _ _
    · intro r vs
      simp only [tryRule]
      intro s tr a s' tr' hIs h
      simp only [bind, StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure, Except.bind] at h
      cases hm : matchRule p sem cfg n r vs (s, tr) with
      | error e => rw [hm] at h; cases h
      | ok res =>
        rw [hm] at h
        obtain ⟨o, s1, tr1⟩ := res
        simp only at h
        cases o with
        | some env =>
          cases h
          exact hM _ _ s tr _ _ _ hIs hm
        | none =>
          simp only [set, StateT.set, pure, StateT.pure] at h
          cases h
          exact ⟨hIs, hR.refl _⟩
    · intro rs vs
      cases rs with
      | nil => simp only [alsoMatching]; exact pp _
      | cons r rs =>
        simp only [alsoMatching]
        intro s tr a s' tr' hIs h
        simp only [bind, StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure, Except.bind]
          at h
        cases hm : matchRule p sem cfg n r vs (s, tr) with
        | error e => rw [hm] at h; cases h
        | ok res =>
          rw [hm] at h
          simp only [set, StateT.set, pure, Except.pure] at h
          cases hal : alsoMatching p sem cfg n rs vs (s, tr) with
          | error e => simp only [hal] at h; cases h
          | ok res' =>
            obtain ⟨l, s2, tr2⟩ := res'
            simp only [hal] at h
            cases h
            exact hAl rs vs s tr _ _ _ hIs hal
    · intro term rs vs
      cases rs with
      | nil => simp only [selectRule]; exact pp _
      | cons r rs =>
        simp only [selectRule]
        exact pb (hTr _ _) fun o => by
          split
          · exact hS _ _ _
          · split
            · exact pb (hAl _ _) fun _ => by
                split
                · exact pp _
                · exact pres_throw _
            · exact pp _

theorem pres_multi (hR : PreOrd R) {msem : MultiSem V σ} (hc : CtorPres I R msem.toSem)
    (hcm : CtorMultiPres I R msem) : ∀ n, MultiPres p cfg I R msem n := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      first
      | (simp only [evalExprN]; exact pres_throw _)
      | (simp only [evalArgsN]; exact pres_throw _)
      | (simp only [evalBindsN]; exact pres_throw _)
      | (simp only [applyTermN]; exact pres_throw _)
      | (simp only [applyMulti]; exact pres_throw _)
      | (simp only [matchIfLetsN]; exact pres_throw _)
  | succ n ih =>
    obtain ⟨hE, hA, hB, hT, hM, hI⟩ := ih
    have hsing := pres_single (p := p) (cfg := cfg) hR hc n
    have pb := @pres_bind σ I R hR
    have pp := @pres_pure σ I R hR
    have pa := @pres_bindAll σ I R hR
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e env
      cases e with
      | var _ x => simp only [evalExprN]; split <;> first | exact pp _ | exact pres_throw _
      | constBool => simp only [evalExprN]; exact pp _
      | constInt => simp only [evalExprN]; exact pp _
      | constPrim => simp only [evalExprN]; split <;> first | exact pp _ | exact pres_throw _
      | «let» _ bs body =>
        simp only [evalExprN]
        exact pb (hB _ _) fun envs => pa (fun e => hE _ _) _
      | term ty t args =>
        simp only [evalExprN]
        exact pb (hA _ _) fun argss => pa (fun vs => hT _ _ _) _
    · intro es env
      cases es with
      | nil => simp only [evalArgsN]; exact pp _
      | cons e es =>
        simp only [evalArgsN]
        exact pb (hE _ _) fun vs => pa (fun v => pb (hA _ _) fun _ => pp _) _
    · intro bs env
      cases bs with
      | nil => simp only [evalBindsN]; exact pp _
      | cons b bs =>
        obtain ⟨x, ty, e⟩ := b
        simp only [evalBindsN]
        exact pb (hE _ _) fun vs => pa (fun v => by
          split
          · exact hB _ _
          · exact pres_throw _) _
    · intro ty t vs
      simp only [applyTermN]
      refine pb (pres_monadLift hR _) fun term => ?_
      split
      · split
        · exact pb (hM _ _ _) fun _ => pp _
        · exact pb (hsing.2.2.2.1 _ _ _) fun _ => pp _
      · split
        · intro s tr a s' tr' hIs h
          simp only [bind, StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure, Except.bind]
            at h
          cases hct : msem.ctorMulti term vs s with
          | ok r =>
            obtain ⟨ws, st'⟩ := r
            simp only [hct, set, StateT.set, Except.bind] at h
            cases h
            exact hcm _ _ _ _ _ hIs hct
          | fail => simp only [hct] at h; cases h; exact ⟨hIs, hR.refl _⟩
          | unmodeled w => simp only [hct] at h; cases h
        · exact pb (hsing.2.2.2.1 _ _ _) fun _ => pp _
      · exact pb (hsing.2.2.2.1 _ _ _) fun _ => pp _
    · intro term rs vs
      cases rs with
      | nil => simp only [applyMulti]; exact pp _
      | cons r rs =>
        simp only [applyMulti]
        exact pb (pres_get hR) fun st => pb (pres_monadLift hR _) fun envs =>
          pb (pa (fun env => hI _ _) _) fun envs =>
            pb (pa (fun env => pb (hE _ _) fun ws =>
              pa (fun w => pb (pres_fire hR _) fun _ => pp _) _) _) fun here =>
              pb (hM _ _ _) fun _ => pp _
    · intro ils env
      cases ils with
      | nil => simp only [matchIfLetsN]; exact pp _
      | cons il ils =>
        simp only [matchIfLetsN]
        exact pb (hE _ _) fun vs => pa (fun v =>
          pb (pres_get hR) fun st => pb (pres_monadLift hR _) fun envs =>
            pa (fun e => hI _ _) _) _

end

end Opt.Proof
