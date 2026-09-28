import FV.Opt.Proof.Sem
import FV.Opt.Proof.InterpMatch
import FV.Opt.Proof.InterpState
import FV.Isle.Opt.Simplify

/-!
# Rule obligations for `simplify`, and their lifting to `Isle.Opt.simplify`

`RuleOk p r`: whenever the `simplify` rule `r` of the program `p` fires on an e-class `v` with
value `a` (in a model `den` of the e-graph, `Opt.GraphModel`, with a sound `make`,
`Opt.MakeSound`), every e-class its right-hand side returns has value `a`. Concretely: for
every environment `env1` its argument patterns relate to `[.value v]` (`ArgsRel`, the
relational reading of the matcher), every environment `env2` its if-lets produce from it, and
every value its right-hand side evaluates to — from any later state of the run (the valuation
only grows).

`simplify_sound`: if every rule of `p.rulesOf simplify` accepted by `allow` is `RuleOk`, the
`simplify` multi-term, run by the interpreter, returns only candidates with `v`'s value, keeps
the model and only extends the valuation. `simplifySound`: the same for `Isle.Opt.simplify`
with the allow-list, i.e. `Opt.SimplifySound` (`FV/Opt/Proof/Sem.lean`).
-/

namespace Opt.Proof

open Isle Isle.Opt Isle.Interp Clif

/-- The model assumptions of `Opt.SimplifySound` for an `EGraph`. -/
structure GraphOk {σ : Type} (G : EGraph σ) (P : σ → Prop) (den : σ → Valuation) (fr : Frame)
    (mem : Mem) : Prop where
  model : GraphModel G.enodes G.typeOf P den fr mem
  make : MakeSound G.make P den fr mem

/-- The interpreter-state invariant: the caller's invariant holds. -/
abbrev SI {σ : Type} (P : σ → Prop) : St σ → Prop := fun s => P s.inner

/-- The interpreter-state relation: the valuation only grows. -/
abbrev SR {σ : Type} (den : σ → Valuation) : St σ → St σ → Prop :=
  fun s s' => Valuation.Le (den s.inner) (den s'.inner)

theorem Valuation.le_refl (ρ : Valuation) : Valuation.Le ρ ρ := fun _ _ h => h

theorem Valuation.le_trans {ρ₁ ρ₂ ρ₃ : Valuation} (h₁ : Valuation.Le ρ₁ ρ₂)
    (h₂ : Valuation.Le ρ₂ ρ₃) : Valuation.Le ρ₁ ρ₃ := fun x a h => h₂ x a (h₁ x a h)

theorem preOrd_SR {σ : Type} (den : σ → Valuation) : PreOrd (SR den) :=
  ⟨fun _ => Valuation.le_refl _, fun _ _ _ h₁ h₂ => Valuation.le_trans h₁ h₂⟩

section
variable {σ : Type} {G : EGraph σ} {P : σ → Prop} {den : σ → Valuation} {fr : Frame} {mem : Mem}

/-- The state after an extern constructor: unchanged, or a `make_inst`. -/
theorem ctorFn_state (fn : String) (args : List V) (st : St σ) (v : V) (st' : St σ)
    (h : ctorFn G fn args st = .ok (some (v, st'))) :
    st'.inner = st.inner ∨ ∃ ty d, st' = (makeInst G st ty d).2 := by
  unfold ctorFn at h
  split at h
  · rename_i t d
    cases ht : t.ty? with
    | error e => simp [ht, bind, Except.bind] at h
    | ok ty =>
      simp only [ht, bind, Except.bind, pure, Except.pure] at h
      cases h
      exact .inr ⟨ty, d, rfl⟩
  · split at h <;> (cases h; exact .inl rfl)
  · split at h <;> (cases h; exact .inl rfl)
  · cases hp : ctorPure G fn args st with
    | error e => simp [hp, bind, Except.bind] at h
    | ok o =>
      simp only [hp, bind, Except.bind, pure, Except.pure] at h
      cases o <;> simp at h
      obtain ⟨-, rfl⟩ := h
      exact .inl rfl

theorem makeInst_pres (hG : GraphOk G P den fr mem) (st : St σ) (ty : CTy) (d : V)
    (hP : P st.inner) : P (makeInst G st ty d).2.inner ∧
      Valuation.Le (den st.inner) (den (makeInst G st ty d).2.inner) := by
  unfold makeInst
  split
  · rename_i i _
    obtain ⟨h1, h2, -⟩ := hG.make st.inner i hP
    exact ⟨h1, h2⟩
  · exact ⟨hP, Valuation.le_refl _⟩

theorem ctorPres_sem (hG : GraphOk G P den fr mem) : CtorPres (SI P) (SR den) (sem G).toSem := by
  intro t vs s v s' hP h
  simp only [sem] at h
  split at h
  · rename_i fn _
    cases hc : ctorFn G fn vs s with
    | error e => simp [hc, toExt] at h
    | ok o =>
      cases o with
      | none => simp [hc, toExt] at h
      | some x =>
        simp only [hc, toExt] at h
        cases h
        rcases ctorFn_state fn vs s _ _ hc with h | ⟨ty, d, h⟩
        · simp only [SI, SR, h]; exact ⟨hP, Valuation.le_refl _⟩
        · rw [h]; exact makeInst_pres hG s ty d hP
  · cases h

theorem ctorMultiPres_sem : CtorMultiPres (SI P) (SR den) (sem G) := by
  intro t vs s ws s' _ h
  cases h

end

/-- Rules are proven for runs whose fuel is at least this (the interpreter's fuel is 10⁶;
`simplify` spends one unit per rule before the last one). -/
def fuelMin : Nat := 1000

/-- **Obligation of one `simplify` rule** (see the module doc). -/
def RuleOk (p : Isle.Program) (r : Rule) : Prop :=
  ∀ (σ : Type) (G : EGraph σ) (P : σ → Prop) (den : σ → Valuation) (fr : Frame) (mem : Mem),
  GraphOk G P den fr mem →
  ∀ (s0 : St σ) (v : Nat) (a : Val), P s0.inner → den s0.inner v = some a →
  ∀ env1, ArgsRel p (sem G) s0 r.args [.value v] (Array.replicate r.vars.length none) env1 →
  ∀ n, fuelMin ≤ n →
  ∀ s1 tr1 envs2 s2 tr2, P s1.inner → Valuation.Le (den s0.inner) (den s1.inner) →
    (matchIfLetsN p (sem G) cfg n r.iflets env1).run (s1, tr1) = .ok (envs2, (s2, tr2)) →
  ∀ env2 ∈ envs2,
  ∀ s3 tr3 ws s4 tr4, P s3.inner → Valuation.Le (den s2.inner) (den s3.inner) →
    (evalExprN p (sem G) cfg n r.rhs env2).run (s3, tr3) = .ok (ws, (s4, tr4)) →
  ∀ m, V.value m ∈ ws → den s4.inner m = some a

/-- The `simplify` rules accepted by `allow` are all `RuleOk`. -/
def SimplifyRulesCorrect (p : Isle.Program) (allow : RuleId → Bool) : Prop :=
  ∀ r ∈ p.rulesOf T.«simplify».id, allow r.id = true → RuleOk p r

/-- **The generic obligation of one rule of a multi-term** run on the argument `arg`: from a
start state satisfying `I`, every environment the argument patterns relate to `[arg]`, every
environment of the if-lets and every result `w` of the right-hand side (from later states):
`Q r.id w` holds in the end state. `RuleOk` (`simplify`) and `SkelRuleOk`
(`simplify_skeleton`) are instances. -/
def RuleSpec {σ : Type} (p : Isle.Program) (G : EGraph σ) (P : σ → Prop) (den : σ → Valuation)
    (arg : V) (I : St σ → Prop) (Q : RuleId → V → St σ → Prop) (r : Rule) : Prop :=
  ∀ (s0 : St σ), P s0.inner → I s0 →
  ∀ env1, ArgsRel p (sem G) s0 r.args [arg] (Array.replicate r.vars.length none) env1 →
  ∀ n, fuelMin ≤ n →
  ∀ s1 tr1 envs2 s2 tr2, P s1.inner → Valuation.Le (den s0.inner) (den s1.inner) →
    (matchIfLetsN p (sem G) cfg n r.iflets env1).run (s1, tr1) = .ok (envs2, (s2, tr2)) →
  ∀ env2 ∈ envs2,
  ∀ s3 tr3 ws s4 tr4, P s3.inner → Valuation.Le (den s2.inner) (den s3.inner) →
    (evalExprN p (sem G) cfg n r.rhs env2).run (s3, tr3) = .ok (ws, (s4, tr4)) →
  ∀ w ∈ ws, Q r.id w s4

section
variable {σ : Type} {G : EGraph σ} {P : σ → Prop} {den : σ → Valuation} {fr : Frame} {mem : Mem}

theorem run_liftM' {α : Type} (x : Except Err α) (s : St σ × Array RuleId) :
    (liftM x : M (St σ) α) s = (match x with | .ok a => .ok (a, s) | .error e => .error e) := by
  cases x <;> rfl

/-- **Interpreter soundness of a multi-term's rule list** (generic): if every rule accepted by
`allow` meets `RuleSpec` for an invariant `I` and a result property `Q`, both kept when the
valuation grows, then `applyMulti` keeps the model, only extends the valuation, and every
result of an accepted rule satisfies `Q` in the end state. -/
theorem applyMulti_gen (p : Isle.Program) (hG : GraphOk G P den fr mem) (allow : RuleId → Bool)
    (arg : V) (I : St σ → Prop) (Q : RuleId → V → St σ → Prop)
    (hI : ∀ s s', I s → Valuation.Le (den s.inner) (den s'.inner) → I s')
    (hQ : ∀ rid w s s', Q rid w s → Valuation.Le (den s.inner) (den s'.inner) → Q rid w s')
    (term : Term) :
    ∀ (rs : List Rule), (∀ r ∈ rs, allow r.id = true → RuleSpec p G P den arg I Q r) →
    ∀ n, fuelMin + rs.length ≤ n →
    ∀ (s : St σ) tr res (s' : St σ) tr', P s.inner → I s →
      (applyMulti p (sem G) cfg n term rs [arg]).run (s, tr) = .ok (res, (s', tr')) →
      P s'.inner ∧ Valuation.Le (den s.inner) (den s'.inner) ∧
      ∀ rid w, (rid, w) ∈ res → allow rid = true → Q rid w s' := by
  have hR := preOrd_SR den
  have hmulti := pres_multi (p := p) (cfg := cfg) hR (ctorPres_sem hG) ctorMultiPres_sem
  intro rs
  induction rs with
  | nil =>
    intro _ n _ s tr res s' tr' hP _ h
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [fuelMin] at *; omega⟩
    simp only [applyMulti] at h
    cases h
    exact ⟨hP, Valuation.le_refl _, fun _ _ h => by simp at h⟩
  | cons r rs ih =>
    intro hrs n hn s tr res s' tr' hP hv h
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp at hn; omega⟩
    have hn' : fuelMin + rs.length ≤ n := by simp at hn; omega
    have hfuel : fuelMin ≤ n := by omega
    obtain ⟨hE, -, -, -, hM, hI'⟩ := hmulti n
    simp only [applyMulti, bind, StateT.bind, StateT.run, get, getThe, MonadStateOf.get,
      StateT.get, pure, Except.pure, StateT.pure, Except.bind] at h
    -- the argument match (pure)
    cases hm : matchArgsN p (sem G) s r.args [arg] (Array.replicate r.vars.length none) with
    | error e => simp only [hm, run_liftM'] at h; cases h
    | ok envs1 =>
    simp only [hm, run_liftM'] at h
    -- the if-lets
    cases hil : bindAll (fun env => matchIfLetsN p (sem G) cfg n r.iflets env) envs1 (s, tr) with
    | error e => rw [hil] at h; cases h
    | ok x1 =>
    obtain ⟨envs2, s2, tr2⟩ := x1
    rw [hil] at h
    simp only at h
    -- the right-hand sides
    let body := fun env => (do
      let ws ← evalExprN p (sem G) cfg n r.rhs env
      bindAll (fun w => do fire r.id; pure [(r.id, w)]) ws : M (St σ) (List (RuleId × V)))
    have hbody : ∀ env, Pres (SI P) (SR den) (body env) := fun env =>
      pres_bind hR (hE _ _) fun ws => pres_bindAll hR (fun w => pres_bind hR (pres_fire hR _)
        fun _ => pres_pure hR _) _
    cases hh : bindAll body envs2 (s2, tr2) with
    | error e =>
      have : bindAll (fun env => (do
          let ws ← evalExprN p (sem G) cfg n r.rhs env
          bindAll (fun w => do fire r.id; pure [(r.id, w)]) ws : M (St σ) (List (RuleId × V))))
          envs2 (s2, tr2) = .error e := hh
      simp only [bind, StateT.bind, pure, StateT.pure] at this
      rw [this] at h; cases h
    | ok x2 =>
    obtain ⟨here, s3, tr3⟩ := x2
    have hh' : bindAll (fun env => (do
          let ws ← evalExprN p (sem G) cfg n r.rhs env
          bindAll (fun w => do fire r.id; pure [(r.id, w)]) ws : M (St σ) (List (RuleId × V))))
          envs2 (s2, tr2) = .ok (here, s3, tr3) := hh
    simp only [bind, StateT.bind, pure, StateT.pure] at hh'
    rw [hh'] at h
    simp only at h
    cases hrest : applyMulti p (sem G) cfg n term rs [arg] (s3, tr3) with
    | error e => rw [hrest] at h; cases h
    | ok x3 =>
    obtain ⟨rest, s4, tr4⟩ := x3
    rw [hrest] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    -- invariants along the run
    have hilP : Pres (SI P) (SR den) (bindAll (fun env =>
        matchIfLetsN p (sem G) cfg n r.iflets env) envs1) := pres_bindAll hR (fun _ => hI' _ _) _
    obtain ⟨hP2, hR2⟩ := hilP s tr envs2 s2 tr2 hP hil
    obtain ⟨hP3, hR3⟩ := pres_bindAll hR hbody envs2 s2 tr2 here s3 tr3 hP2 hh
    have hv3 : I s3 := hI _ _ hv (Valuation.le_trans hR2 hR3)
    obtain ⟨hP4, hR4, hrestok⟩ := ih (fun r hr => hrs r (List.mem_cons_of_mem _ hr)) n hn'
      s3 tr3 rest s4 tr4 hP3 hv3 hrest
    refine ⟨hP4, Valuation.le_trans hR2 (Valuation.le_trans hR3 hR4), ?_⟩
    intro rid m hmem hallow
    rcases List.mem_append.1 hmem with hmem | hmem
    · -- a result of `r`
      obtain ⟨env2, henv2, s5, tr5, bs, s6, tr6, hP5, hR5, hrun, hbs, hR6⟩ :=
        bindAll_run_mem hR hbody envs2 s2 tr2 here s3 tr3 hP2 hh _ hmem
      simp only [body, bind, StateT.bind, StateT.run] at hrun
      cases hev : evalExprN p (sem G) cfg n r.rhs env2 (s5, tr5) with
      | error e => rw [hev] at hrun; cases hrun
      | ok x4 =>
      obtain ⟨ws, s7, tr7⟩ := x4
      rw [hev] at hrun
      obtain ⟨hP7, hR7⟩ := hE _ _ s5 tr5 ws s7 tr7 hP5 hev
      -- the result list: `(r.id, w)` for `w ∈ ws`
      have hfire : Pres (SI P) (SR den) (bindAll (fun w => (do fire r.id; pure [(r.id, w)] :
          M (St σ) (List (RuleId × V)))) ws) :=
        pres_bindAll hR (fun w => pres_bind hR (pres_fire hR _) fun _ => pres_pure hR _) _
      obtain ⟨w, hw, s8, tr8, bs', s9, tr9, -, hR8, hrun', hbs', hR9⟩ :=
        bindAll_run_mem hR (fun w => pres_bind hR (pres_fire hR _) fun _ => pres_pure hR _)
          ws s7 tr7 bs s6 tr6 hP7 hrun _ hbs
      simp only [fire, bind, StateT.bind, StateT.run, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, pure, StateT.pure, Except.pure, Except.bind] at hrun'
      cases hrun'
      simp only [List.mem_singleton, Prod.mk.injEq] at hbs'
      obtain ⟨rfl, rfl⟩ := hbs'
      have hrin : r ∈ r :: rs := List.mem_cons_self ..
      -- the match
      obtain ⟨env1, henv1, s10, tr10, envs2', s11, tr11, hP10, hR10, hilrun, henv2', hR11⟩ :=
        bindAll_run_mem hR (fun _ => hI' _ _) envs1 s tr envs2 s2 tr2 hP hil _ henv2
      have hrel := matchArgsN_sound p (sem G) s _ _ _ _ _ hm henv1
      have := hrs r hrin hallow s hP hv env1 hrel n hfuel s10 tr10 envs2' s11 tr11 hP10 hR10
        hilrun env2 henv2' s5 tr5 ws s7 tr7 hP5 (Valuation.le_trans hR11 hR5) hev _ hw
      exact hQ _ _ _ _ this (Valuation.le_trans hR8 (Valuation.le_trans hR9
        (Valuation.le_trans hR6 hR4)))
    · exact hrestok rid m hmem hallow

/-- A `RuleOk` rule meets the generic obligation for `simplify` on `.value v` (invariant: `v`
has value `a`; result property: a value result has value `a`). -/
theorem RuleOk.spec {p : Isle.Program} {r : Rule} (h : RuleOk p r) (hG : GraphOk G P den fr mem)
    (v : Nat) (a : Val) :
    RuleSpec p G P den (.value v) (fun s => den s.inner v = some a)
      (fun _ w s => ∀ m, w = .value m → den s.inner m = some a) r := by
  intro s0 hP hv env1 hrel n hn s1 tr1 envs2 s2 tr2 hP1 hle1 hil env2 henv2 s3 tr3 ws s4 tr4
    hP3 hle3 hev w hw m hm
  subst hm
  exact h _ G P den fr mem hG s0 v a hP hv env1 hrel n hn s1 tr1 envs2 s2 tr2 hP1 hle1 hil env2
    henv2 s3 tr3 ws s4 tr4 hP3 hle3 hev m hw

theorem applyMulti_sound (p : Isle.Program) (hG : GraphOk G P den fr mem) (allow : RuleId → Bool)
    (v : Nat) (a : Val) (term : Term) :
    ∀ (rs : List Rule), (∀ r ∈ rs, allow r.id = true → RuleOk p r) →
    ∀ n, fuelMin + rs.length ≤ n →
    ∀ (s : St σ) tr res (s' : St σ) tr', P s.inner → den s.inner v = some a →
      (applyMulti p (sem G) cfg n term rs [.value v]).run (s, tr) = .ok (res, (s', tr')) →
      P s'.inner ∧ Valuation.Le (den s.inner) (den s'.inner) ∧
      ∀ rid m, (rid, V.value m) ∈ res → allow rid = true → den s'.inner m = some a := by
  intro rs hrs n hn s tr res s' tr' hP hv h
  obtain ⟨h1, h2, h3⟩ := applyMulti_gen p hG allow (.value v) (fun s => den s.inner v = some a)
    (fun _ w s => ∀ m, w = .value m → den s.inner m = some a)
    (fun _ _ h hle => hle _ _ h) (fun _ _ _ _ h hle m hm => hle _ _ (h m hm)) term rs
    (fun r hr ha => (hrs r hr ha).spec hG v a) n hn s tr res s' tr' hP hv h
  exact ⟨h1, h2, fun rid m hm ha => h3 rid _ hm ha m rfl⟩

theorem simplify_kind : T.«simplify».kind = .decl ⟨false, true, false, false⟩ (some .internal) none :=
  rfl

/-- **Lifting**: the `simplify` rules accepted by `allow` being `RuleOk`, `Isle.Opt.simplify`
with the allow-list is a sound rule set. -/
theorem simplifySound (allow : RuleId → Bool) (hc : SimplifyRulesCorrect program allow)
    (hlen : fuelMin + (program.rulesOf T.«simplify».id).length ≤ cfg.fuel) :
    SimplifySound (fun enodes typeOf make st v => Isle.Opt.simplify enodes typeOf make st v allow) := by
  intro σ enodes typeOf make P den fr mem hM hMk st v cands names st' hP h
  let G : EGraph σ := { enodes, typeOf, make }
  have hG : GraphOk G P den fr mem := ⟨hM, hMk⟩
  unfold Isle.Opt.simplify at h
  dsimp only at h
  split at h
  · cases h
  · rename_i r hr
    simp only [Interp.runMultiTerm, simplify_kind] at hr
    simp only [TermFlags.isMulti, Bool.not_true, Bool.false_eq_true, ite_false, bind,
      Except.bind] at hr
    split at hr
    · cases hr
    · rename_i x hx
      obtain ⟨vals, s1, tr1⟩ := x
      simp only [pure, Except.pure, Except.ok.injEq] at hr
      subst hr
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      obtain ⟨h1, h2, -⟩ := applyMulti_gen program hG allow (.value v) (fun _ => True)
        (fun _ _ _ => True) (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial) T.«simplify» _
        (fun _ _ _ => by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; trivial) cfg.fuel hlen
        { inner := st } #[] vals s1 tr1 hP trivial hx
      refine ⟨h1, h2, ?_⟩
      intro a hv c hcm
      obtain ⟨-, -, h3⟩ := applyMulti_sound program hG allow v a T.«simplify» _ hc cfg.fuel hlen
        { inner := st } #[] vals s1 tr1 hP hv hx
      simp only [List.mem_map, List.mem_filterMap] at hcm
      obtain ⟨⟨c', nm⟩, ⟨⟨rid, w⟩, hmem, hw⟩, rfl⟩ := hcm
      cases w with
      | value n =>
        simp only at hw
        split at hw
        · rename_i hal
          simp only [Option.some.injEq, Prod.mk.injEq] at hw
          obtain ⟨rfl, -⟩ := hw
          exact h3 rid n hmem hal
        · cases hw
      | _ => simp at hw

end

end Opt.Proof
