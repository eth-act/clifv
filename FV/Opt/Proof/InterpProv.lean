import FV.Opt.Proof.InterpState
import FV.Opt.Proof.InterpMatch

/-!
# The interpreter only passes values on

`HT I R P x Q`: running `x` from a state satisfying `I` and the precondition `P` ends (if it
succeeds) in a state satisfying `I`, `R`-related to the start, whose result satisfies `Q`.

A value predicate `G s v` ("`v` is good in state `s`"), monotone along the preorder `R`, is a
*provenance* invariant of an embedding (`ProvSem`, `ProvMultiSem`) if literals and constants are
good, data is good iff its fields are, extractors on good values give good values, and extern
constructors on good arguments keep `I`, move along `R` and return good values. Then every
interpreter function, single (`evalExpr` … `selectRule`, `prov_single`) and multi
(`matchPatN`, `evalExprN` … `matchIfLetsN`, `prov_multi`), on good arguments and environments
returns good values, for every program and fuel; in particular `runMultiTerm`
(`runMultiTerm_prov`). This is the value analogue of the state invariant of
`FV/Opt/Proof/InterpState.lean`; the mid-end instance (`FV/Opt/Proof/IsleProv.lean`) reads "good"
as "mentions only values the rules were given".
-/

namespace Opt.Proof

open Isle Isle.Interp

/-! ## Hoare triples over the interpreter monad -/

section
variable {σ : Type} (I : σ → Prop) (R : σ → σ → Prop)

/-- From `I` and `P`, `x` keeps `I`, moves along `R` and ends with `Q`. -/
def HT {α : Type} (P : σ → Prop) (x : M σ α) (Q : σ → α → Prop) : Prop :=
  ∀ s tr a s' tr', I s → P s → x.run (s, tr) = .ok (a, (s', tr')) → I s' ∧ R s s' ∧ Q s' a

/-- `P` is kept along `R`. -/
def Mono (P : σ → Prop) : Prop := ∀ s s', P s → R s s' → P s'

variable {I R}

theorem ht_conseq {α : Type} {P P' : σ → Prop} {Q Q' : σ → α → Prop} {x : M σ α}
    (h : HT I R P x Q) (hP : ∀ s, P' s → P s) (hQ : ∀ s a, Q s a → Q' s a) : HT I R P' x Q' := by
  intro s tr a s' tr' hI hP' hx
  obtain ⟨h1, h2, h3⟩ := h s tr a s' tr' hI (hP s hP') hx
  exact ⟨h1, h2, hQ _ _ h3⟩

theorem ht_frame {α : Type} {F P : σ → Prop} {Q : σ → α → Prop} {x : M σ α} (hF : Mono R F)
    (h : HT I R P x Q) : HT I R (fun s => F s ∧ P s) x (fun s a => F s ∧ Q s a) := by
  intro s tr a s' tr' hI hP hx
  obtain ⟨h1, h2, h3⟩ := h s tr a s' tr' hI hP.2 hx
  exact ⟨h1, h2, hF _ _ hP.1 h2, h3⟩

theorem ht_pure (hR : PreOrd R) {α : Type} {P : σ → Prop} {Q : σ → α → Prop} (a : α)
    (h : ∀ s, P s → Q s a) : HT I R P (pure a : M σ α) Q := by
  intro s tr a' s' tr' hI hP hx
  cases hx
  exact ⟨hI, hR.refl _, h _ hP⟩

theorem ht_bind (hR : PreOrd R) {α β : Type} {P : σ → Prop} {Q : σ → α → Prop}
    {Q' : σ → β → Prop} {x : M σ α} {f : α → M σ β} (hx : HT I R P x Q)
    (hf : ∀ a, HT I R (fun s => Q s a) (f a) Q') : HT I R P (x >>= f) Q' := by
  intro s tr b s' tr' hI hP h
  change (StateT.bind x f).run (s, tr) = _ at h
  simp only [StateT.bind, StateT.run] at h
  cases hxr : x (s, tr) with
  | error e => rw [hxr] at h; cases h
  | ok r =>
    rw [hxr] at h
    obtain ⟨a, s1, tr1⟩ := r
    obtain ⟨h1, h2, h3⟩ := hx s tr a s1 tr1 hI hP hxr
    obtain ⟨h4, h5, h6⟩ := hf a s1 tr1 b s' tr' h1 h3 h
    exact ⟨h4, hR.trans _ _ _ h2 h5, h6⟩

/-- `ht_bind` with a frame `F` carried over `x`. -/
theorem ht_bindF (hR : PreOrd R) {α β : Type} {F P P' : σ → Prop} {Q : σ → α → Prop}
    {Q' : σ → β → Prop} {x : M σ α} {f : α → M σ β} (hF : Mono R F) (hx : HT I R P x Q)
    (hP : ∀ s, P' s → F s ∧ P s) (hf : ∀ a, HT I R (fun s => F s ∧ Q s a) (f a) Q') :
    HT I R P' (x >>= f) Q' :=
  ht_bind hR (ht_conseq (ht_frame hF hx) hP fun _ _ h => h) hf

theorem ht_throw {α : Type} {P : σ → Prop} {Q : σ → α → Prop} (e : Err) :
    HT I R P (throw e : M σ α) Q := by
  intro s tr a s' tr' _ _ h
  cases h

theorem ht_get (hR : PreOrd R) {P : σ → Prop} :
    HT I R P (get : M σ (σ × Array RuleId)) (fun s a => P s ∧ a.1 = s ∧ I s) := by
  intro s tr a s' tr' hI hP h
  cases h
  exact ⟨hI, hR.refl _, hP, rfl, hI⟩

theorem ht_fire (hR : PreOrd R) {P : σ → Prop} (r : RuleId) :
    HT I R P (fire r : M σ Unit) (fun s _ => P s) := by
  intro s tr a s' tr' hI hP h
  cases h
  exact ⟨hI, hR.refl _, hP⟩

theorem ht_monadLift (hR : PreOrd R) {α : Type} {P : σ → Prop} (e : Except Err α) :
    HT I R P (monadLift e : M σ α) (fun s a => P s ∧ e = .ok a) := by
  intro s tr a s' tr' hI hP h
  cases e with
  | error => cases h
  | ok => cases h; exact ⟨hI, hR.refl _, hP, rfl⟩

theorem ht_liftM (hR : PreOrd R) {α : Type} {P : σ → Prop} (e : Except Err α) :
    HT I R P (liftM e : M σ α) (fun s a => P s ∧ e = .ok a) := by
  intro s tr a s' tr' hI hP h
  cases e with
  | error => cases h
  | ok => cases h; exact ⟨hI, hR.refl _, hP, rfl⟩

/-- `bindAll f l` from a kept precondition `F`: every result of every call is good. -/
theorem ht_bindAll (hR : PreOrd R) {α β : Type} {F : σ → Prop} {Gb : σ → β → Prop}
    {f : α → M σ (List β)} (hF : Mono R F) (hGb : ∀ b, Mono R (fun s => Gb s b)) :
    ∀ l : List α, (∀ a ∈ l, HT I R F (f a) (fun s bs => ∀ b ∈ bs, Gb s b)) →
      HT I R F (bindAll f l) (fun s bs => ∀ b ∈ bs, Gb s b)
  | [], _ => by
    simp only [bindAll]
    exact ht_pure hR _ fun _ _ b hb => by simp at hb
  | a :: as, hf => by
    simp only [bindAll]
    refine ht_bindF hR hF (hf a (List.mem_cons_self ..)) (fun s h => ⟨h, h⟩) fun bs => ?_
    refine ht_bindF (F := fun s => ∀ b ∈ bs, Gb s b) hR
      (fun s s' h hr b hb => hGb b s s' (h b hb) hr)
      (ht_bindAll hR hF hGb as fun a ha => hf a (List.mem_cons_of_mem _ ha))
      (fun s h => ⟨h.2, h.1⟩) fun cs => ht_pure hR _ fun s h b hb => ?_
    rcases List.mem_append.1 hb with hb | hb
    · exact h.1 b hb
    · exact h.2 b hb

end

/-! ## Good values and environments -/

section
variable {V σ : Type} (I : σ → Prop) (R : σ → σ → Prop) (G : σ → V → Prop)

/-- Every bound entry of `env` is good in `s`. -/
def EnvG (s : σ) (env : Env V) : Prop := ∀ (x : Nat) (v : V), env[x]? = some (some v) → G s v

/-- `G` is a provenance invariant of the single-term embedding `sem` (module doc). -/
structure ProvSem (sem : Sem V σ) : Prop where
  mono : ∀ s s' v, G s v → R s s' → G s' v
  int : ∀ s ty i, G s (sem.int ty i)
  bool : ∀ s b, G s (sem.bool b)
  prim : ∀ s ty n c, sem.prim ty n = some c → G s c
  mkData : ∀ s ty k fs, (∀ v ∈ fs, G s v) → G s (sem.mkData ty k fs)
  unData : ∀ s ty v k fs, G s v → sem.unData ty v = some (k, fs) → ∀ w ∈ fs, G s w
  extract : ∀ t v s fs, I s → G s v → sem.extract t v s = .ok fs → ∀ w ∈ fs, G s w
  ctor : ∀ t args s v s', I s → (∀ a ∈ args, G s a) → sem.ctor t args s = .ok (v, s') →
    I s' ∧ R s s' ∧ G s' v

/-- `G` is a provenance invariant of the multi-term embedding `msem` (module doc). -/
structure ProvMultiSem (msem : MultiSem V σ) : Prop extends ProvSem I R G msem.toSem where
  extractMulti : ∀ t v s fss, I s → G s v → msem.extractMulti t v s = .ok fss →
    ∀ fs ∈ fss, ∀ w ∈ fs, G s w
  ctorMulti : ∀ t args s ws s', I s → (∀ a ∈ args, G s a) →
    msem.ctorMulti t args s = .ok (ws, s') → I s' ∧ R s s' ∧ ∀ w ∈ ws, G s' w

variable {I R G}

theorem envG_set {s : σ} {env : Env V} {v : V} (x : Nat) (h : EnvG G s env) (hv : G s v) :
    EnvG G s (env.set! x (some v)) := by
  intro y w hy
  simp only [Array.set!, Array.getElem?_setIfInBounds] at hy
  split at hy
  · split at hy
    · cases hy; exact hv
    · cases hy
  · exact h y w hy

theorem envG_replicate (s : σ) (n : Nat) : EnvG G s (Array.replicate n (none : Option V)) := by
  intro y w hy
  simp only [Array.getElem?_replicate] at hy
  split at hy <;> cases hy

theorem mono_envG (hm : ∀ s s' v, G s v → R s s' → G s' v) (env : Env V) :
    Mono R (fun s => EnvG G s env) :=
  fun s s' h hr x v hx => hm s s' v (h x v hx) hr

theorem mono_all (hm : ∀ s s' v, G s v → R s s' → G s' v) (vs : List V) :
    Mono R (fun s => ∀ v ∈ vs, G s v) :=
  fun s s' h hr v hv => hm s s' v (h v hv) hr

theorem mono_and {F₁ F₂ : σ → Prop} (h₁ : Mono R F₁) (h₂ : Mono R F₂) :
    Mono R (fun s => F₁ s ∧ F₂ s) :=
  fun s s' h hr => ⟨h₁ s s' h.1 hr, h₂ s s' h.2 hr⟩

theorem eq_of_mem_ite_single {α : Type} {c : Prop} [Decidable c] {a b : α}
    (h : a ∈ (if c then [b] else [])) : a = b := by
  split at h <;> simp_all

/-! ## Matching -/

section single
variable {p : Program} {sem : Sem V σ}

mutual
theorem matchPat_good (h : ProvSem I R G sem) (st : σ) (hI : I st) :
    ∀ (pat : Pattern) (v : V) (env env' : Env V), G st v → EnvG G st env →
      matchPat p sem st pat v env = .ok (some env') → EnvG G st env'
  | .bind _ x sub, v, env, env', hv, he, hm => by
    simp only [matchPat] at hm
    split at hm
    · exact matchPat_good h st hI sub _ _ _ hv (envG_set x he hv) hm
    · cases hm
  | .var _ x, v, env, env', hv, he, hm => by
    simp only [matchPat] at hm
    split at hm
    · simp only [except_pure_eq_ok] at hm
      split at hm
      · cases hm; exact he
      · cases hm
    · cases hm
  | .constBool _ b, v, env, env', hv, he, hm => by
    simp only [matchPat, except_pure_eq_ok] at hm
    split at hm
    · cases hm; exact he
    · cases hm
  | .constInt ty i, v, env, env', hv, he, hm => by
    simp only [matchPat, except_pure_eq_ok] at hm
    split at hm
    · cases hm; exact he
    · cases hm
  | .constPrim ty n, v, env, env', hv, he, hm => by
    simp only [matchPat] at hm
    split at hm
    · simp only [except_pure_eq_ok] at hm
      split at hm
      · cases hm; exact he
      · cases hm
    · cases hm
  | .wildcard _, v, env, env', hv, he, hm => by
    simp only [matchPat, except_pure_eq_ok] at hm
    cases hm; exact he
  | .and _ ps, v, env, env', hv, he, hm => by
    simp only [matchPat] at hm
    exact matchAll_good h st hI ps v env env' hv he hm
  | .term ty t args, v, env, env', hv, he, hm => by
    simp only [matchPat] at hm
    cases ht : termOf p t with
    | error e => rw [ht] at hm; cases hm
    | ok term =>
      rw [ht] at hm
      simp only [bind, Except.bind] at hm
      split at hm
      · split at hm
        · rename_i k' fs hu
          split at hm
          · exact matchArgs_good h st hI args fs env env' (h.unData st ty v _ fs hv hu) he hm
          · cases hm
        · cases hm
      · split at hm
        · rename_i k' fs hu
          exact matchArgs_good h st hI args fs env env' (h.unData st ty v _ fs hv hu) he hm
        · cases hm
      · split at hm
        · cases hm
        · split at hm
          · rename_i fs hx
            exact matchArgs_good h st hI args fs env env' (h.extract term v st fs hI hv hx) he hm
          · split at hm
            · cases hm
            · cases hm
          · cases hm
      · cases hm
theorem matchAll_good (h : ProvSem I R G sem) (st : σ) (hI : I st) :
    ∀ (ps : List Pattern) (v : V) (env env' : Env V), G st v → EnvG G st env →
      matchAll p sem st ps v env = .ok (some env') → EnvG G st env'
  | [], v, env, env', hv, he, hm => by
    simp only [matchAll, except_pure_eq_ok] at hm
    cases hm; exact he
  | q :: qs, v, env, env', hv, he, hm => by
    simp only [matchAll, bind, Except.bind] at hm
    split at hm
    · cases hm
    · rename_i o hq
      cases o with
      | none => cases hm
      | some e =>
        exact matchAll_good h st hI qs v e env' hv (matchPat_good h st hI q v env e hv he hq) hm
theorem matchArgs_good (h : ProvSem I R G sem) (st : σ) (hI : I st) :
    ∀ (ps : List Pattern) (vs : List V) (env env' : Env V), (∀ w ∈ vs, G st w) → EnvG G st env →
      matchArgs p sem st ps vs env = .ok (some env') → EnvG G st env'
  | [], [], env, env', hv, he, hm => by
    simp only [matchArgs, except_pure_eq_ok] at hm
    cases hm; exact he
  | q :: qs, w :: ws, env, env', hv, he, hm => by
    simp only [matchArgs, bind, Except.bind] at hm
    split at hm
    · cases hm
    · rename_i o hq
      cases o with
      | none => cases hm
      | some e =>
        exact matchArgs_good h st hI qs ws e env' (fun w hw => hv w (List.mem_cons_of_mem _ hw))
          (matchPat_good h st hI q w env e (hv w (List.mem_cons_self ..)) he hq) hm
  | [], _ :: _, env, env', hv, he, hm => by simp [matchArgs] at hm
  | _ :: _, [], env, env', hv, he, hm => by simp [matchArgs] at hm
end

end single

section multi
variable {p : Program} {msem : MultiSem V σ}

mutual
theorem matchPatN_good (h : ProvMultiSem I R G msem) (st : σ) (hI : I st) :
    ∀ (pat : Pattern) (v : V) (env : Env V) (envs : List (Env V)), G st v → EnvG G st env →
      matchPatN p msem st pat v env = .ok envs → ∀ e ∈ envs, EnvG G st e
  | .bind _ x sub, v, env, envs, hv, he, hm => by
    simp only [matchPatN] at hm
    split at hm
    · exact matchPatN_good h st hI sub _ _ _ hv (envG_set x he hv) hm
    · cases hm
  | .var _ x, v, env, envs, hv, he, hm => by
    simp only [matchPatN] at hm
    split at hm
    · simp only [except_pure_eq_ok] at hm
      subst hm
      intro e hem
      rw [eq_of_mem_ite_single hem]; exact he
    · cases hm
  | .constBool _ b, v, env, envs, hv, he, hm => by
    simp only [matchPatN, except_pure_eq_ok] at hm
    subst hm
    intro e hem
    rw [eq_of_mem_ite_single hem]; exact he
  | .constInt ty i, v, env, envs, hv, he, hm => by
    simp only [matchPatN, except_pure_eq_ok] at hm
    subst hm
    intro e hem
    rw [eq_of_mem_ite_single hem]; exact he
  | .constPrim ty n, v, env, envs, hv, he, hm => by
    simp only [matchPatN] at hm
    split at hm
    · simp only [except_pure_eq_ok] at hm
      subst hm
      intro e hem
      rw [eq_of_mem_ite_single hem]; exact he
    · cases hm
  | .wildcard _, v, env, envs, hv, he, hm => by
    simp only [matchPatN, except_pure_eq_ok] at hm
    subst hm
    intro e hem
    rw [List.mem_singleton.1 hem]; exact he
  | .and _ ps, v, env, envs, hv, he, hm => by
    simp only [matchPatN] at hm
    exact matchAllN_good h st hI ps v env envs hv he hm
  | .term ty t args, v, env, envs, hv, he, hm => by
    simp only [matchPatN] at hm
    cases ht : termOf p t with
    | error e => rw [ht] at hm; cases hm
    | ok term =>
      rw [ht] at hm
      simp only [bind, Except.bind] at hm
      split at hm
      · split at hm
        · rename_i k' fs hu
          split at hm
          · exact matchArgsN_good h st hI args fs env envs (h.unData st ty v _ fs hv hu) he hm
          · simp only [except_pure_eq_ok] at hm; subst hm; simp
        · cases hm
      · split at hm
        · rename_i k' fs hu
          exact matchArgsN_good h st hI args fs env envs (h.unData st ty v _ fs hv hu) he hm
        · cases hm
      · split at hm
        · split at hm
          · rename_i fss hx
            intro e hem
            obtain ⟨fs, hfs, r', h1, h2⟩ := bindAll_ok_mem hm hem
            exact matchArgsN_good h st hI args fs env r'
              (h.extractMulti term v st fss hI hv hx fs hfs) he h1 e h2
          · simp only [except_pure_eq_ok] at hm; subst hm; simp
          · cases hm
        · split at hm
          · rename_i fs hx
            exact matchArgsN_good h st hI args fs env envs (h.extract term v st fs hI hv hx) he hm
          · split at hm
            · cases hm
            · simp only [except_pure_eq_ok] at hm; subst hm; simp
          · cases hm
      · cases hm
theorem matchAllN_good (h : ProvMultiSem I R G msem) (st : σ) (hI : I st) :
    ∀ (ps : List Pattern) (v : V) (env : Env V) (envs : List (Env V)), G st v → EnvG G st env →
      matchAllN p msem st ps v env = .ok envs → ∀ e ∈ envs, EnvG G st e
  | [], v, env, envs, hv, he, hm => by
    simp only [matchAllN, except_pure_eq_ok] at hm
    subst hm
    intro e hem
    rw [List.mem_singleton.1 hem]; exact he
  | q :: qs, v, env, envs, hv, he, hm => by
    simp only [matchAllN, bind, Except.bind] at hm
    split at hm
    · cases hm
    · rename_i es hq
      intro e hem
      obtain ⟨e1, he1, r', h1, h2⟩ := bindAll_ok_mem hm hem
      exact matchAllN_good h st hI qs v e1 r' hv
        (matchPatN_good h st hI q v env es hv he hq e1 he1) h1 e h2
theorem matchArgsN_good (h : ProvMultiSem I R G msem) (st : σ) (hI : I st) :
    ∀ (ps : List Pattern) (vs : List V) (env : Env V) (envs : List (Env V)),
      (∀ w ∈ vs, G st w) → EnvG G st env →
      matchArgsN p msem st ps vs env = .ok envs → ∀ e ∈ envs, EnvG G st e
  | [], [], env, envs, hv, he, hm => by
    simp only [matchArgsN, except_pure_eq_ok] at hm
    subst hm
    intro e hem
    rw [List.mem_singleton.1 hem]; exact he
  | q :: qs, w :: ws, env, envs, hv, he, hm => by
    simp only [matchArgsN, bind, Except.bind] at hm
    split at hm
    · cases hm
    · rename_i es hq
      intro e hem
      obtain ⟨e1, he1, r', h1, h2⟩ := bindAll_ok_mem hm hem
      exact matchArgsN_good h st hI qs ws e1 r' (fun w hw => hv w (List.mem_cons_of_mem _ hw))
        (matchPatN_good h st hI q w env es (hv w (List.mem_cons_self ..)) he hq e1 he1) h1 e h2
  | [], _ :: _, env, envs, hv, he, hm => by simp [matchArgsN] at hm
  | _ :: _, [], env, envs, hv, he, hm => by simp [matchArgsN] at hm
end

end multi

end

/-! ## All interpreter functions -/

section
variable {V σ : Type} (p : Program) (cfg : Config) (I : σ → Prop) (R : σ → σ → Prop)
  (G : σ → V → Prop)

/-- Every `some` result satisfies `P`. -/
abbrev OptG {α : Type} (P : α → Prop) (o : Option α) : Prop := ∀ a, o = some a → P a

/-- The single-term interpreter at fuel `n` returns good values from good arguments. -/
def SingleProv (sem : Sem V σ) (n : Nat) : Prop :=
  (∀ e env, HT I R (fun s => EnvG G s env) (evalExpr p sem cfg n e env)
    (fun s o => OptG (G s) o)) ∧
  (∀ es env, HT I R (fun s => EnvG G s env) (evalArgs p sem cfg n es env)
    (fun s o => OptG (fun vs => ∀ v ∈ vs, G s v) o)) ∧
  (∀ bs env, HT I R (fun s => EnvG G s env) (evalBinds p sem cfg n bs env)
    (fun s o => OptG (EnvG G s) o)) ∧
  (∀ ty t vs, HT I R (fun s => ∀ v ∈ vs, G s v) (applyTerm p sem cfg n ty t vs)
    (fun s o => OptG (G s) o)) ∧
  (∀ r vs, HT I R (fun s => ∀ v ∈ vs, G s v) (matchRule p sem cfg n r vs)
    (fun s o => OptG (EnvG G s) o)) ∧
  (∀ ils env, HT I R (fun s => EnvG G s env) (matchIfLets p sem cfg n ils env)
    (fun s o => OptG (EnvG G s) o)) ∧
  (∀ r vs, HT I R (fun s => ∀ v ∈ vs, G s v) (tryRule p sem cfg n r vs)
    (fun s o => OptG (EnvG G s) o)) ∧
  (∀ rs vs, HT I R (fun s => ∀ v ∈ vs, G s v) (alsoMatching p sem cfg n rs vs)
    (fun _ _ => True)) ∧
  (∀ term rs vs, HT I R (fun s => ∀ v ∈ vs, G s v) (selectRule p sem cfg n term rs vs)
    (fun s o => OptG (fun re => EnvG G s re.2) o))

/-- The multi-term interpreter at fuel `n` returns good values from good arguments. -/
def MultiProv (msem : MultiSem V σ) (n : Nat) : Prop :=
  (∀ e env, HT I R (fun s => EnvG G s env) (evalExprN p msem cfg n e env)
    (fun s vs => ∀ v ∈ vs, G s v)) ∧
  (∀ es env, HT I R (fun s => EnvG G s env) (evalArgsN p msem cfg n es env)
    (fun s vss => ∀ vs ∈ vss, ∀ v ∈ vs, G s v)) ∧
  (∀ bs env, HT I R (fun s => EnvG G s env) (evalBindsN p msem cfg n bs env)
    (fun s envs => ∀ e ∈ envs, EnvG G s e)) ∧
  (∀ ty t vs, HT I R (fun s => ∀ v ∈ vs, G s v) (applyTermN p msem cfg n ty t vs)
    (fun s ws => ∀ w ∈ ws, G s w)) ∧
  (∀ term rs vs, HT I R (fun s => ∀ v ∈ vs, G s v) (applyMulti p msem cfg n term rs vs)
    (fun s ws => ∀ w ∈ ws, G s w.2)) ∧
  (∀ ils env, HT I R (fun s => EnvG G s env) (matchIfLetsN p msem cfg n ils env)
    (fun s envs => ∀ e ∈ envs, EnvG G s e))

variable {p cfg I R G}

theorem prov_single (hR : PreOrd R) {sem : Sem V σ} (h : ProvSem I R G sem) :
    ∀ n, SingleProv p cfg I R G sem n := by
  have hm := h.mono
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      first
      | (simp only [evalExpr]; exact ht_throw _)
      | (simp only [evalArgs]; exact ht_throw _)
      | (simp only [evalBinds]; exact ht_throw _)
      | (simp only [applyTerm]; exact ht_throw _)
      | (simp only [matchRule]; exact ht_throw _)
      | (simp only [matchIfLets]; exact ht_throw _)
      | (simp only [tryRule]; exact ht_throw _)
      | (simp only [alsoMatching]; exact ht_throw _)
      | (simp only [selectRule]; exact ht_throw _)
  | succ n ih =>
    obtain ⟨hE, hA, hB, hT, hM, hIl, hTr, hAl, hS⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e env
      cases e with
      | var _ x =>
        simp only [evalExpr]
        split
        · rename_i v hx
          exact ht_pure hR _ fun s hs w hw => by cases hw; exact hs x v hx
        · exact ht_throw _
      | constBool =>
        simp only [evalExpr]
        exact ht_pure hR _ fun s _ w hw => by cases hw; exact h.bool _ _
      | constInt =>
        simp only [evalExpr]
        exact ht_pure hR _ fun s _ w hw => by cases hw; exact h.int _ _ _
      | constPrim =>
        simp only [evalExpr]
        split
        · rename_i c hc
          exact ht_pure hR _ fun s _ w hw => by cases hw; exact h.prim _ _ _ _ hc
        · exact ht_throw _
      | «let» _ bs body =>
        simp only [evalExpr]
        refine ht_bind hR (hB _ _) fun r => ?_
        cases r with
        | some env' => exact ht_conseq (hE _ _) (fun s hs => hs _ rfl) fun _ _ h => h
        | none => exact ht_pure hR _ fun _ _ _ hw => by cases hw
      | term ty t args =>
        simp only [evalExpr]
        refine ht_bind hR (hA _ _) fun r => ?_
        cases r with
        | some vs => exact ht_conseq (hT _ _ _) (fun s hs => hs _ rfl) fun _ _ h => h
        | none => exact ht_pure hR _ fun _ _ _ hw => by cases hw
    · intro es env
      cases es with
      | nil =>
        simp only [evalArgs]
        exact ht_pure hR _ fun _ _ _ hw => by cases hw; simp
      | cons e es =>
        simp only [evalArgs]
        refine ht_bindF hR (mono_envG hm env) (hE _ _) (fun s h => ⟨h, h⟩) fun r => ?_
        cases r with
        | none => exact ht_pure hR _ fun _ _ _ hw => by cases hw
        | some v =>
          refine ht_bindF (F := fun s => G s v) hR (fun s s' h hr => hm s s' v h hr) (hA _ _)
            (fun s h => ⟨h.2 _ rfl, h.1⟩) fun r => ?_
          cases r with
          | none => exact ht_pure hR _ fun _ _ _ hw => by cases hw
          | some vs =>
            refine ht_pure hR _ fun s h l hl => ?_
            cases hl
            intro w hw
            rcases List.mem_cons.1 hw with rfl | hw
            · exact h.1
            · exact h.2 _ rfl w hw
    · intro bs env
      cases bs with
      | nil =>
        simp only [evalBinds]
        exact ht_pure hR _ fun s hs e he => by cases he; exact hs
      | cons b bs =>
        obtain ⟨x, ty, e⟩ := b
        simp only [evalBinds]
        refine ht_bindF hR (mono_envG hm env) (hE _ _) (fun s h => ⟨h, h⟩) fun r => ?_
        cases r with
        | none => exact ht_pure hR _ fun _ _ _ hw => by cases hw
        | some v =>
          dsimp only
          split
          · exact ht_conseq (hB _ _) (fun s h => envG_set x h.1 (h.2 _ rfl)) fun _ _ h => h
          · exact ht_throw _
    · intro ty t vs
      simp only [applyTerm]
      refine ht_bind hR (ht_monadLift hR _) fun term => ?_
      split
      · exact ht_pure hR _ fun s hs w hw => by cases hw; exact h.mkData _ _ _ _ hs.1
      · exact ht_pure hR _ fun s hs w hw => by cases hw; exact h.mkData _ _ _ _ hs.1
      · split
        · exact ht_throw _
        · intro s tr a s' tr' hIs hP hrun
          simp only [bind, StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
            pure, Except.pure, Except.bind] at hrun
          cases hct : sem.ctor term vs s with
          | ok r =>
            obtain ⟨v, st'⟩ := r
            simp only [hct, set] at hrun
            cases hrun
            obtain ⟨h1, h2, h3⟩ := h.ctor _ _ _ _ _ hIs hP.1 hct
            exact ⟨h1, h2, fun w hw => by cases hw; exact h3⟩
          | fail =>
            simp only [hct] at hrun
            split at hrun
            · cases hrun; exact ⟨hIs, hR.refl _, fun w hw => by cases hw⟩
            · cases hrun
          | unmodeled w => simp only [hct] at hrun; cases hrun
      · split
        · exact ht_throw _
        · refine ht_bindF hR (mono_all hm vs) (hS _ _ _) (fun s h => ⟨h.1, h.1⟩) fun o => ?_
          cases o with
          | none =>
            dsimp only
            split
            · exact ht_pure hR _ fun _ _ _ hw => by cases hw
            · exact ht_throw _
          | some re =>
            obtain ⟨r, env⟩ := re
            refine ht_bind hR (ht_conseq (hE _ _) (fun s h => h.2 _ rfl) fun _ _ h => h)
              fun o => ?_
            cases o with
            | some v =>
              exact ht_bind hR (ht_fire hR _) fun _ =>
                ht_pure hR _ fun s h w hw => by cases hw; exact h _ rfl
            | none => exact ht_pure hR _ fun _ _ _ hw => by cases hw
      · exact ht_throw _
    · intro r vs
      simp only [matchRule]
      refine ht_bind hR (ht_get hR) fun x => ?_
      obtain ⟨st, tr0⟩ := x
      refine ht_bind hR (ht_monadLift hR _) fun o => ?_
      cases o with
      | none => exact ht_pure hR _ fun _ _ _ hw => by cases hw
      | some env =>
        refine ht_conseq (hIl _ _) (fun s hs => ?_) fun _ _ h => h
        obtain ⟨⟨hvs, hst, hIs⟩, hmr⟩ := hs
        simp only at hst
        subst hst
        exact matchArgs_good h _ hIs _ _ _ _ hvs (envG_replicate _ _) hmr
    · intro ils env
      cases ils with
      | nil =>
        simp only [matchIfLets]
        exact ht_pure hR _ fun s hs e he => by cases he; exact hs
      | cons il ils =>
        simp only [matchIfLets]
        refine ht_bindF hR (mono_envG hm env) (hE _ _) (fun s h => ⟨h, h⟩) fun o => ?_
        cases o with
        | none => exact ht_pure hR _ fun _ _ _ hw => by cases hw
        | some v =>
          refine ht_bind hR (ht_get hR) fun x => ?_
          obtain ⟨st, tr0⟩ := x
          refine ht_bind hR (ht_monadLift hR _) fun o => ?_
          cases o with
          | none => exact ht_pure hR _ fun _ _ _ hw => by cases hw
          | some env' =>
            refine ht_conseq (hIl _ _) (fun s hs => ?_) fun _ _ h => h
            obtain ⟨⟨⟨henv, hv⟩, hst, hIs⟩, hmr⟩ := hs
            simp only at hst
            subst hst
            exact matchPat_good h _ hIs _ _ _ _ (hv _ rfl) henv hmr
    · intro r vs
      simp only [tryRule]
      intro s tr a s' tr' hIs hP hrun
      simp only [bind, StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, pure,
        Except.pure, Except.bind] at hrun
      cases hmr : matchRule p sem cfg n r vs (s, tr) with
      | error e => rw [hmr] at hrun; cases hrun
      | ok res =>
        rw [hmr] at hrun
        obtain ⟨o, s1, tr1⟩ := res
        simp only at hrun
        cases o with
        | some env =>
          cases hrun
          exact hM _ _ s tr _ _ _ hIs hP hmr
        | none =>
          simp only [set] at hrun
          cases hrun
          exact ⟨hIs, hR.refl _, fun e he => by cases he⟩
    · intro rs vs
      cases rs with
      | nil => simp only [alsoMatching]; exact ht_pure hR _ fun _ _ => trivial
      | cons r rs =>
        simp only [alsoMatching]
        intro s tr a s' tr' hIs hP hrun
        simp only [bind, StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, pure,
          Except.pure, Except.bind] at hrun
        cases hmr : matchRule p sem cfg n r vs (s, tr) with
        | error e => rw [hmr] at hrun; cases hrun
        | ok res =>
          rw [hmr] at hrun
          simp only [set, StateT.set, pure, Except.pure] at hrun
          cases hal : alsoMatching p sem cfg n rs vs (s, tr) with
          | error e => simp only [hal] at hrun; cases hrun
          | ok res' =>
            obtain ⟨l, s2, tr2⟩ := res'
            simp only [hal] at hrun
            cases hrun
            obtain ⟨h1, h2, -⟩ := hAl rs vs s tr _ _ _ hIs hP hal
            exact ⟨h1, h2, trivial⟩
    · intro term rs vs
      cases rs with
      | nil => simp only [selectRule]; exact ht_pure hR _ fun _ _ _ hw => by cases hw
      | cons r rs =>
        simp only [selectRule]
        refine ht_bindF hR (mono_all hm vs) (hTr _ _) (fun s h => ⟨h, h⟩) fun o => ?_
        cases o with
        | none => exact ht_conseq (hS _ _ _) (fun s h => h.1) fun _ _ h => h
        | some env =>
          dsimp only
          split
          · refine ht_bindF (F := fun s => EnvG G s env) hR (mono_envG hm env) (hAl _ _)
              (fun s h => ⟨h.2 _ rfl, h.1⟩) fun others => ?_
            split
            · exact ht_pure hR _ fun s h re hre => by cases hre; exact h.1
            · exact ht_throw _
          · exact ht_pure hR _ fun s h re hre => by cases hre; exact h.2 _ rfl

theorem prov_multi (hR : PreOrd R) {msem : MultiSem V σ} (h : ProvMultiSem I R G msem) :
    ∀ n, MultiProv p cfg I R G msem n := by
  have hm := h.mono
  have hEnvs : ∀ envs : List (Env V), Mono R (fun s => ∀ e ∈ envs, EnvG G s e) :=
    fun envs s s' h hr e he => mono_envG hm e s s' (h e he) hr
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      first
      | (simp only [evalExprN]; exact ht_throw _)
      | (simp only [evalArgsN]; exact ht_throw _)
      | (simp only [evalBindsN]; exact ht_throw _)
      | (simp only [applyTermN]; exact ht_throw _)
      | (simp only [applyMulti]; exact ht_throw _)
      | (simp only [matchIfLetsN]; exact ht_throw _)
  | succ n ih =>
    obtain ⟨hE, hA, hB, hT, hM, hIl⟩ := ih
    have hsing := prov_single (p := p) (cfg := cfg) hR h.toProvSem n
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e env
      cases e with
      | var _ x =>
        simp only [evalExprN]
        split
        · rename_i v hx
          exact ht_pure hR _ fun s hs w hw => by rw [List.mem_singleton.1 hw]; exact hs x v hx
        · exact ht_throw _
      | constBool =>
        simp only [evalExprN]
        exact ht_pure hR _ fun s _ w hw => by rw [List.mem_singleton.1 hw]; exact h.bool _ _
      | constInt =>
        simp only [evalExprN]
        exact ht_pure hR _ fun s _ w hw => by rw [List.mem_singleton.1 hw]; exact h.int _ _ _
      | constPrim =>
        simp only [evalExprN]
        split
        · rename_i c hc
          exact ht_pure hR _ fun s _ w hw => by
            rw [List.mem_singleton.1 hw]; exact h.prim _ _ _ _ hc
        · exact ht_throw _
      | «let» _ bs body =>
        simp only [evalExprN]
        exact ht_bind hR (hB _ _) fun envs =>
          ht_bindAll hR (hEnvs envs) (fun w s s' h hr => hm s s' w h hr) envs fun e he =>
            ht_conseq (hE _ _) (fun s hs => hs e he) fun _ _ h => h
      | term ty t args =>
        simp only [evalExprN]
        exact ht_bind hR (hA _ _) fun argss =>
          ht_bindAll (F := fun s => ∀ vs ∈ argss, ∀ v ∈ vs, G s v) (Gb := fun s w => G s w) hR
            (fun s s' h hr vs hvs => mono_all hm vs s s' (h vs hvs) hr)
            (fun w s s' h hr => hm s s' w h hr) argss fun vs hvs =>
            ht_conseq (hT _ _ _) (fun s hs => hs vs hvs) fun _ _ h => h
    · intro es env
      cases es with
      | nil =>
        simp only [evalArgsN]
        exact ht_pure hR _ fun _ _ l hl => by rw [List.mem_singleton.1 hl]; simp
      | cons e es =>
        simp only [evalArgsN]
        refine ht_bindF hR (mono_envG hm env) (hE _ _) (fun s h => ⟨h, h⟩) fun vs => ?_
        refine ht_bindAll (Gb := fun s (l : List V) => ∀ v ∈ l, G s v) hR
          (mono_and (mono_envG hm env) (mono_all hm vs))
          (fun l s s' h hr v hv => hm s s' v (h v hv) hr) vs fun v hv => ?_
        refine ht_bindF (F := fun s => G s v) hR (fun s s' h hr => hm s s' v h hr) (hA _ _)
          (fun s h => ⟨h.2 v hv, h.1⟩) fun rests => ht_pure hR _ fun s h l hl => ?_
        obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
        intro w hw
        rcases List.mem_cons.1 hw with rfl | hw
        · exact h.1
        · exact h.2 l' hl' w hw
    · intro bs env
      cases bs with
      | nil =>
        simp only [evalBindsN]
        exact ht_pure hR _ fun s hs e he => by rw [List.mem_singleton.1 he]; exact hs
      | cons b bs =>
        obtain ⟨x, ty, e⟩ := b
        simp only [evalBindsN]
        refine ht_bindF hR (mono_envG hm env) (hE _ _) (fun s h => ⟨h, h⟩) fun vs => ?_
        refine ht_bindAll hR (mono_and (mono_envG hm env) (mono_all hm vs))
          (fun e => mono_envG hm e) vs fun v hv => ?_
        split
        · exact ht_conseq (hB _ _) (fun s h => envG_set x h.1 (h.2 v hv)) fun _ _ h => h
        · exact ht_throw _
    · intro ty t vs
      have hsT : ∀ P : σ → Prop, (∀ s, P s → ∀ v ∈ vs, G s v) → HT I R P
          (do let v ← applyTerm p msem.toSem cfg n ty t vs; pure v.toList : M σ (List V))
          (fun s ws => ∀ w ∈ ws, G s w) := fun P hP =>
        ht_bind hR (ht_conseq (hsing.2.2.2.1 _ _ _) hP fun _ _ h => h) fun o =>
          ht_pure hR _ fun s h w hw => h w (by cases o <;> simp_all)
      simp only [applyTermN]
      refine ht_bind hR (ht_monadLift hR _) fun term => ?_
      split
      · split
        · refine ht_bind hR (ht_conseq (hM _ _ _) (fun s h => h.1) fun _ _ h => h) fun rs =>
            ht_pure hR _ fun s h w hw => ?_
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
          exact h x hx
        · exact hsT _ fun s h => h.1
      · split
        · intro s tr a s' tr' hIs hP hrun
          simp only [bind, StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
            pure, Except.pure, Except.bind] at hrun
          cases hct : msem.ctorMulti term vs s with
          | ok r =>
            obtain ⟨ws, st'⟩ := r
            simp only [hct, set] at hrun
            cases hrun
            exact h.ctorMulti _ _ _ _ _ hIs hP.1 hct
          | fail =>
            simp only [hct] at hrun
            cases hrun
            exact ⟨hIs, hR.refl _, fun w hw => by simp at hw⟩
          | unmodeled w => simp only [hct] at hrun; cases hrun
        · exact hsT _ fun s h => h.1
      · exact hsT _ fun s h => h.1
    · intro term rs vs
      cases rs with
      | nil => simp only [applyMulti]; exact ht_pure hR _ fun _ _ _ hw => by simp at hw
      | cons r rs =>
        simp only [applyMulti]
        refine ht_bind hR (ht_get hR) fun x => ?_
        obtain ⟨st, tr0⟩ := x
        refine ht_bind hR (ht_monadLift hR _) fun envs1 => ?_
        refine ht_bindF (F := fun s => ∀ v ∈ vs, G s v) (P := fun s => ∀ e ∈ envs1, EnvG G s e)
          hR (mono_all hm vs)
          (ht_bindAll hR (hEnvs envs1) (fun e => mono_envG hm e) envs1 fun e he =>
            ht_conseq (hIl _ _) (fun s hs => hs e he) fun _ _ h => h)
          (fun s hs => ⟨hs.1.1, ?_⟩) fun envs2 => ?_
        · obtain ⟨⟨hvs, hst, hIs⟩, hma⟩ := hs
          simp only at hst
          subst hst
          exact matchArgsN_good h _ hIs _ _ _ _ hvs (envG_replicate _ _) hma
        refine ht_bindF (F := fun s => ∀ v ∈ vs, G s v) (P := fun s => ∀ e ∈ envs2, EnvG G s e)
          (Q := fun s ws => ∀ w ∈ ws, G s (w : RuleId × V).2)
          hR (mono_all hm vs) ?_ (fun s hs => hs) fun here => ?_
        · refine ht_bindAll (Gb := fun s (w : RuleId × V) => G s w.2) hR (hEnvs envs2)
            (fun w s s' h hr => hm s s' w.2 h hr) envs2 fun e he => ?_
          refine ht_bind hR (ht_conseq (hE _ _) (fun s hs => hs e he) fun _ _ h => h)
            fun ws => ?_
          refine ht_bindAll (Gb := fun s (w : RuleId × V) => G s w.2) hR (mono_all hm ws)
            (fun w s s' h hr => hm s s' w.2 h hr) ws fun w hw => ?_
          exact ht_bind hR (ht_fire hR _) fun _ =>
            ht_pure hR _ fun s h x hx => by rw [List.mem_singleton.1 hx]; exact h w hw
        refine ht_bindF (F := fun s => ∀ x ∈ here, G s x.2) hR
          (fun s s' h hr x hx => hm s s' x.2 (h x hx) hr) (hM _ _ _) (fun s hs => ⟨hs.2, hs.1⟩)
          fun rest => ht_pure hR _ fun s h x hx => ?_
        rcases List.mem_append.1 hx with hx | hx
        · exact h.1 x hx
        · exact h.2 x hx
    · intro ils env
      cases ils with
      | nil =>
        simp only [matchIfLetsN]
        exact ht_pure hR _ fun s hs e he => by rw [List.mem_singleton.1 he]; exact hs
      | cons il ils =>
        simp only [matchIfLetsN]
        refine ht_bindF hR (mono_envG hm env) (hE _ _) (fun s h => ⟨h, h⟩) fun vs => ?_
        refine ht_bindAll hR (mono_and (mono_envG hm env) (mono_all hm vs))
          (fun e => mono_envG hm e) vs fun v hv => ?_
        refine ht_bind hR (ht_get hR) fun x => ?_
        obtain ⟨st, tr0⟩ := x
        refine ht_bind hR (ht_monadLift hR _) fun envs => ?_
        refine ht_conseq (P := fun s => ∀ e ∈ envs, EnvG G s e)
          (ht_bindAll hR (hEnvs envs) (fun e => mono_envG hm e) envs fun e he =>
            ht_conseq (hIl _ _) (fun s hs => hs e he) fun _ _ h => h)
          (fun s hs => ?_) fun _ _ h => h
        obtain ⟨⟨⟨henv, hvs⟩, hst, hIs⟩, hma⟩ := hs
        simp only at hst
        subst hst
        exact matchPatN_good h _ hIs _ _ _ _ (hvs v hv) henv hma

/-- **The interpreter only passes values on**: a multi term run on good arguments from a state
satisfying `I` ends in a state satisfying `I`, `R`-after the start, and every result is good
there. -/
theorem runMultiTerm_prov (hR : PreOrd R) {msem : MultiSem V σ} (h : ProvMultiSem I R G msem)
    (t : Term) (args : List V) (st : σ) (r : MultiResult V σ) (hI : I st)
    (hargs : ∀ a ∈ args, G st a) (hrun : Interp.runMultiTerm p msem cfg t args st = .ok r) :
    I r.state ∧ R st r.state ∧ ∀ x ∈ r.values, G r.state x.2 := by
  unfold Interp.runMultiTerm at hrun
  split at hrun
  · split at hrun
    · cases hrun
    · simp only [bind, Except.bind] at hrun
      cases hx : (applyMulti p msem cfg cfg.fuel t (p.rulesOf t.id) args).run (st, #[]) with
      | error e => rw [hx] at hrun; cases hrun
      | ok res =>
        obtain ⟨vs, st', tr⟩ := res
        rw [hx] at hrun
        cases hrun
        exact (prov_multi (p := p) (cfg := cfg) hR h cfg.fuel).2.2.2.2.1 t _ args st #[] vs st' tr
          hI hargs hx
  · cases hrun

end

end Opt.Proof
