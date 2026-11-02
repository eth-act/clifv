import FV.Backend.Proof.KillBase
import FV.Backend.Proof.IselFlowCheck

/-!
# A uniform invariant of ISLE runs (V4, `SpillKillFree`)

For any program and embedding, with overlap checking off: a value predicate `P` (depending on
the embedding state), a state invariant `Is` and a run relation `Rs`, closed under the
interpreter's primitive steps on a set `T` of terms (with black-box oracle terms `O`), hold
along every run (`uSound`), and along a root term's run whose rules are in scope, hand-checked
or never match (`uRoot`).

`ruleTys` lists the typed call sites `(ty, t)` of a rule's expressions: `applyTerm` builds an
enum variant with the *call site's* type, so the data-construction hook is asked only at
call sites the model allows (`UModel.C`).
-/

namespace Isle

mutual
/-- The typed call sites `(ty, t)` of an expression. -/
def exprTys : Expr → List (TypeId × TermId)
  | .term ty t args => (ty, t) :: exprTysL args
  | .let _ bs body => bindTys bs ++ exprTys body
  | _ => []
/-- `exprTys` of a list. -/
def exprTysL : List Expr → List (TypeId × TermId)
  | [] => []
  | e :: es => exprTys e ++ exprTysL es
/-- `exprTys` of `let*` bindings. -/
def bindTys : List (VarId × TypeId × Expr) → List (TypeId × TermId)
  | [] => []
  | (_, _, e) :: bs => exprTys e ++ bindTys bs
end

/-- The typed call sites of a rule: in its if-let right-hand sides and its right-hand side. -/
def ruleTys (r : Rule) : List (TypeId × TermId) :=
  r.iflets.flatMap (fun il => exprTys il.rhs) ++ exprTys r.rhs

end Isle

namespace Isle.Interp

variable {V σ : Type} {p : Program} {sem : Sem V σ} {cfg : Config}

variable (p sem) in
/-- **A uniform invariant of ISLE runs**: a value predicate `P` (in a state), a state invariant
`Is`, a run relation `Rs`, the terms runs may apply (`T`), the call sites `(ty, t)` they may
build data at (`C`), and black-box oracle terms (`O`), with the facts the soundness proof needs
about the embedding's primitive steps on them. -/
structure UModel where
  P : σ → V → Prop
  Is : σ → Prop
  Rs : σ → σ → Prop
  T : TermId → Prop
  C : TypeId → TermId → Prop
  O : TermId → Prop
  rs_refl : ∀ s, Rs s s
  rs_trans : ∀ a b c, Rs a b → Rs b c → Rs a c
  mono : ∀ s s' v, Is s → Is s' → Rs s s' → P s v → P s' v
  int : ∀ s ty i, Is s → P s (sem.int ty i)
  bool : ∀ s b, Is s → P s (sem.bool b)
  prim : ∀ s ty n c, Is s → sem.prim ty n = some c → P s c
  mkd : ∀ s ty t term k vs, T t → C ty t → termOf p t = .ok term →
    (term.kind = .enumVariant k ∨ (term.kind = .struct ∧ k = 0)) → Is s → (∀ v ∈ vs, P s v) →
    P s (sem.mkData ty k vs)
  un : ∀ s ty t term v k fs, T t → termOf p t = .ok term →
    ((∃ k', term.kind = .enumVariant k') ∨ term.kind = .struct) → Is s → P s v →
    sem.unData ty v = some (k, fs) → ∀ f ∈ fs, P s f
  ext : ∀ s t term flags c fn inf v fs, T t → termOf p t = .ok term →
    term.kind = .decl flags c (some (.external fn inf)) → Is s → P s v →
    sem.extract term v s = .ok fs → ∀ f ∈ fs, P s f
  ctor : ∀ s t term flags fn ex vs v s', T t → termOf p t = .ok term →
    term.kind = .decl flags (some (.external fn)) ex → Is s → (∀ v ∈ vs, P s v) →
    sem.ctor term vs s = .ok (v, s') → P s' v ∧ Is s' ∧ Rs s s'
  oracle : ∀ t, O t → ∀ (cfg : Config), cfg.checkOverlap = false →
    ∀ n ty vs s tr r s' tr', (∀ v ∈ vs, P s v) → Is s →
    (applyTerm p sem cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    Is s' ∧ Rs s s' ∧ ∀ v, r = some v → P s' v
  closed : ∀ t, T t → ¬ O t → ∀ rl ∈ p.rulesOf t,
    (∀ u ∈ ruleTerms rl, T u) ∧ ∀ q ∈ ruleTys rl, C q.1 q.2

/-- The variables of an environment satisfy `P` in state `s`. -/
def EnvP (P : σ → V → Prop) (s : σ) (env : Env V) : Prop :=
  ∀ (x : Nat) w, env[x]? = some (some w) → P s w

section Env
variable {P : σ → V → Prop}

theorem envP_empty (s : σ) (n : Nat) : EnvP P s (Array.replicate n (none : Option V)) := by
  intro x w hx
  simp [Array.getElem?_replicate] at hx

theorem envP_set {s : σ} {env : Env V} (he : EnvP P s env) {v : V} (hv : P s v) (x : Nat) :
    EnvP P s (env.set! x (some v)) := by
  intro y w hy
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hy
  by_cases hyx : x = y
  · subst hyx
    simp only [↓reduceIte] at hy
    split at hy
    · cases hy; exact hv
    · cases hy
  · simp only [hyx, ↓reduceIte] at hy
    exact he y w hy

theorem envP_mono {Q : σ → V → Prop} {s s' : σ} {env : Env V} (he : EnvP P s env)
    (hm : ∀ v, P s v → Q s' v) : EnvP Q s' env :=
  fun x w hx => hm w (he x w hx)

end Env

/-! ## Membership in the term and call-site lists -/

section Mem
variable {T : TermId → Prop} {C : TypeId → TermId → Prop}

theorem ruleTerms_args {rl : Rule} (h : ∀ u ∈ ruleTerms rl, T u) : ∀ u ∈ patTermsL rl.args, T u :=
  fun u hu => h u (by simp [ruleTerms, hu])

theorem ruleTerms_iflets {rl : Rule} (h : ∀ u ∈ ruleTerms rl, T u) (hC : ∀ q ∈ ruleTys rl, C q.1 q.2) :
    ∀ il ∈ rl.iflets, (∀ u ∈ patTerms il.lhs, T u) ∧ (∀ u ∈ exprTerms il.rhs, T u) ∧
      ∀ q ∈ exprTys il.rhs, C q.1 q.2 := by
  intro il hil
  refine ⟨fun u hu => h u ?_, fun u hu => h u ?_, fun q hq => hC q ?_⟩
  · simp only [ruleTerms, List.mem_append, List.mem_flatMap]
    exact .inl (.inr ⟨il, hil, .inl hu⟩)
  · simp only [ruleTerms, List.mem_append, List.mem_flatMap]
    exact .inl (.inr ⟨il, hil, .inr hu⟩)
  · simp only [ruleTys, List.mem_append, List.mem_flatMap]
    exact .inl ⟨il, hil, hq⟩

theorem ruleTerms_rhs {rl : Rule} (h : ∀ u ∈ ruleTerms rl, T u) : ∀ u ∈ exprTerms rl.rhs, T u :=
  fun u hu => h u (by simp [ruleTerms, hu])

theorem ruleTys_rhs {rl : Rule} (h : ∀ q ∈ ruleTys rl, C q.1 q.2) : ∀ q ∈ exprTys rl.rhs, C q.1 q.2 :=
  fun q hq => h q (by simp [ruleTys, hq])

end Mem

/-! ## Patterns -/

section Pat
variable (U : UModel p sem)

mutual
/-- **Pattern soundness**: matching `q` against a value with `P` extends an environment with
`P` to one with `P`. -/
theorem pat_ok : ∀ (q : Pattern) (v : V) (env env' : Env V) (s : σ),
    matchPat p sem s q v env = .ok (some env') → (∀ u ∈ patTerms q, U.T u) → U.Is s →
    U.P s v → EnvP U.P s env → EnvP U.P s env'
  | .bind ty x sub, v, env, env', s, h, hT, hIs, hv, he => by
    rw [matchPat.eq_1] at h
    split at h
    · exact pat_ok sub v _ env' s h (fun u hu => hT u (by simpa [patTerms] using hu)) hIs hv
        (envP_set he hv x)
    · cases h
  | .var ty x, v, env, env', s, h, hT, hIs, hv, he => by
    rw [matchPat.eq_2] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      split at h
      · cases h; exact he
      · cases h
    · cases h
  | .constBool ty b, v, env, env', s, h, hT, hIs, hv, he => by
    rw [matchPat.eq_3] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    split at h
    · cases h; exact he
    · cases h
  | .constInt ty i, v, env, env', s, h, hT, hIs, hv, he => by
    rw [matchPat.eq_4] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    split at h
    · cases h; exact he
    · cases h
  | .constPrim ty nm, v, env, env', s, h, hT, hIs, hv, he => by
    rw [matchPat.eq_5] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      split at h
      · cases h; exact he
      · cases h
    · cases h
  | .wildcard ty, v, env, env', s, h, hT, hIs, hv, he => by
    rw [matchPat.eq_6] at h
    cases h; exact he
  | .and ty ps, v, env, env', s, h, hT, hIs, hv, he => by
    rw [matchPat.eq_7] at h
    exact patAll_ok ps v env env' s h (fun u hu => hT u (by simpa [patTerms] using hu)) hIs hv he
  | .term ty t args, v, env, env', s, h, hT, hIs, hv, he => by
    rw [matchPat.eq_8] at h
    have hTt : U.T t := hT t (by simp [patTerms])
    have hTa : ∀ u ∈ patTermsL args, U.T u := fun u hu => hT u (by simp [patTerms, hu])
    cases ht : termOf p t with
    | error e => rw [ht] at h; cases h
    | ok term =>
      rw [ht] at h
      simp only [bind, Except.bind] at h
      cases hk : term.kind with
      | enumVariant k =>
        rw [hk] at h
        simp only at h
        split at h
        · rename_i k' fs hu
          split at h
          · exact patArgs_ok args fs env env' s h hTa hIs
              (U.un _ _ _ _ _ _ _ hTt ht (.inl ⟨k, hk⟩) hIs hv hu) he
          · cases h
        · cases h
      | struct =>
        rw [hk] at h
        simp only at h
        split at h
        · rename_i k' fs hu
          exact patArgs_ok args fs env env' s h hTa hIs
            (U.un _ _ _ _ _ _ _ hTt ht (.inr hk) hIs hv hu) he
        · cases h
      | decl flags ctor ext =>
        rw [hk] at h
        cases ext with
        | none => cases h
        | some ex =>
          cases ex with
          | internal form => cases h
          | external fn inf =>
            simp only at h
            split at h
            · cases h
            · split at h
              · rename_i fs hx
                exact patArgs_ok args fs env env' s h hTa hIs
                  (U.ext _ _ _ _ _ _ _ _ _ hTt ht hk hIs hv hx) he
              · split at h
                · cases h
                · cases h
              · cases h
/-- `pat_ok` for `and`: every pattern against the same value. -/
theorem patAll_ok : ∀ (qs : List Pattern) (v : V) (env env' : Env V) (s : σ),
    matchAll p sem s qs v env = .ok (some env') → (∀ u ∈ patTermsL qs, U.T u) → U.Is s →
    U.P s v → EnvP U.P s env → EnvP U.P s env'
  | [], v, env, env', s, h, hT, hIs, hv, he => by
    rw [matchAll.eq_1] at h
    cases h
    exact he
  | q :: qs, v, env, env', s, h, hT, hIs, hv, he => by
    rw [matchAll.eq_2] at h
    cases hq : matchPat p sem s q v env with
    | error e => rw [hq] at h; cases h
    | ok o =>
      rw [hq] at h
      cases o with
      | none => cases h
      | some e1 =>
        exact patAll_ok qs v e1 env' s h (fun u hu => hT u (by simp [patTermsL, hu])) hIs hv
          (pat_ok q v env e1 s hq (fun u hu => hT u (by simp [patTermsL, hu])) hIs hv he)
/-- `pat_ok` pointwise: patterns against values with `P`. -/
theorem patArgs_ok : ∀ (qs : List Pattern) (fs : List V) (env env' : Env V) (s : σ),
    matchArgs p sem s qs fs env = .ok (some env') → (∀ u ∈ patTermsL qs, U.T u) → U.Is s →
    (∀ f ∈ fs, U.P s f) → EnvP U.P s env → EnvP U.P s env'
  | [], [], env, env', s, h, hT, hIs, hv, he => by
    rw [matchArgs.eq_1] at h
    cases h
    exact he
  | q :: qs, f :: fs, env, env', s, h, hT, hIs, hv, he => by
    rw [matchArgs.eq_2] at h
    cases hq : matchPat p sem s q f env with
    | error e => rw [hq] at h; cases h
    | ok o =>
      rw [hq] at h
      cases o with
      | none => cases h
      | some e1 =>
        exact patArgs_ok qs fs e1 env' s h (fun u hu => hT u (by simp [patTermsL, hu])) hIs
          (fun g hg => hv g (List.mem_cons_of_mem _ hg))
          (pat_ok q f env e1 s hq (fun u hu => hT u (by simp [patTermsL, hu])) hIs
            (hv f List.mem_cons_self) he)
  | [], _ :: _, env, env', s, h, hT, hIs, hv, he => by
    rw [matchArgs.eq_3] at h
    all_goals first | cases h | (intros; simp_all)
  | _ :: _, [], env, env', s, h, hT, hIs, hv, he => by
    rw [matchArgs.eq_3] at h
    all_goals first | cases h | (intros; simp_all)
end

end Pat

/-! ## Rule selection and the internal-term step -/

/-- With overlap checking off, a committed rule matched at a fuel between the selection's
fuel minus two and minus two plus the number of candidates. -/
theorem selectRule_some_fuel (hc : cfg.checkOverlap = false) :
    ∀ {n : Nat} {term : Term} {rs : List Rule} {vs : List V} {s s' : σ × Array RuleId}
      {r : Rule} {env : Env V},
      (selectRule p sem cfg n term rs vs).run s = .ok (some (r, env), s') →
      r ∈ rs ∧ ∃ m, m + 2 ≤ n ∧ n ≤ m + 2 + rs.length ∧
        (matchRule p sem cfg m r vs).run s = .ok (some env, s')
  | 0, _, _, _, _, _, _, _, h => by rw [selectRule.eq_1] at h; cases h
  | n + 1, _, [], _, _, _, _, _, h => by rw [selectRule.eq_2] at h; cases h
  | n + 1, term, r' :: rs, vs, s, s', r, env, h => by
    rw [selectRule.eq_3] at h
    simp only [M.run_bind] at h
    cases n with
    | zero => rw [tryRule.eq_1] at h; cases h
    | succ k =>
      cases ht : (tryRule p sem cfg (k + 1) r' vs).run s with
      | error e => rw [ht] at h; cases h
      | ok q =>
        obtain ⟨res, s1⟩ := q
        rw [ht] at h
        simp only [M.except_ok_bind] at h
        rcases tryRule_run ht with ⟨env', hres, hm⟩ | ⟨hres, hs1⟩
        · subst hres
          simp only [hc, Bool.false_eq_true, ↓reduceIte, M.run_pure, Except.ok.injEq,
            Prod.mk.injEq, Option.some.injEq] at h
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
          exact ⟨List.mem_cons_self .., k, by omega, by simp, hm⟩
        · subst hres hs1
          obtain ⟨hr, m, hmn, hnm, hm⟩ := selectRule_some_fuel hc h
          exact ⟨List.mem_cons_of_mem _ hr, m, by omega, by simp; omega, hm⟩

/-- **One step of an internal constructor**: no rule matched (no value, state unchanged), or
a rule of the term matched from the start state and its right-hand side ran to the result. -/
theorem internal_cases (hc : cfg.checkOverlap = false) {n : Nat} {ty : TypeId} {t : TermId}
    {vs : List V} {term : Term} {flags : TermFlags} {ex : Option Extractor}
    (ht : termOf p t = .ok term) (hk : term.kind = .decl flags (some .internal) ex)
    (hm : flags.isMulti = false) {s s' : σ} {tr tr' : Array RuleId} {r : Option V}
    (h : (applyTerm p sem cfg (n + 1) ty t vs).run (s, tr) = .ok (r, (s', tr'))) :
    (r = none ∧ s' = s) ∨
    ∃ rl ∈ p.rulesOf t, ∃ m env s1 tr1 tr2, m + 2 ≤ n ∧ n ≤ m + 2 + (p.rulesOf t).length ∧
      (matchRule p sem cfg m rl vs).run (s, tr) = .ok (some env, (s1, tr1)) ∧
      (evalExpr p sem cfg n rl.rhs env).run (s1, tr1) = .ok (r, (s', tr2)) := by
  rw [applyTerm_internal_run ht hk hm] at h
  obtain ⟨⟨sel, ⟨s1, tr1⟩⟩, h1, h2⟩ := except_bind_eq_ok h
  cases sel with
  | none =>
    have := selectRule_none h1
    cases this
    simp only at h2
    split at h2
    · cases pure_ok h2; exact .inl ⟨rfl, rfl⟩
    · exact (throw_ok h2).elim
  | some re =>
    obtain ⟨rl, env⟩ := re
    obtain ⟨hrl, m, hmn, hnm, hmatch⟩ := selectRule_some_fuel hc h1
    simp only at h2
    obtain ⟨ev, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
    refine .inr ⟨rl, hrl, m, env, s1, tr1, tr2, hmn, hnm, hmatch, ?_⟩
    cases ev with
    | some v =>
      obtain ⟨u, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
      have hf := fire_ok h5
      cases pure_ok h6
      simp only at hf
      subst hf
      exact h3
    | none => cases pure_ok h4; exact h3

/-! ## Soundness -/

section Sound
variable (U : UModel p sem)

variable (cfg) in
/-- The soundness statements at fuel `n`. -/
structure USoundAt (n : Nat) : Prop where
  expr : ∀ e env s tr r s' tr', (∀ u ∈ exprTerms e, U.T u) → (∀ q ∈ exprTys e, U.C q.1 q.2) →
    EnvP U.P s env → U.Is s →
    (evalExpr p sem cfg n e env).run (s, tr) = .ok (r, (s', tr')) →
    U.Is s' ∧ U.Rs s s' ∧ ∀ v, r = some v → U.P s' v
  args : ∀ es env s tr r s' tr', (∀ u ∈ exprTermsL es, U.T u) →
    (∀ q ∈ exprTysL es, U.C q.1 q.2) → EnvP U.P s env → U.Is s →
    (evalArgs p sem cfg n es env).run (s, tr) = .ok (r, (s', tr')) →
    U.Is s' ∧ U.Rs s s' ∧ ∀ vs, r = some vs → ∀ v ∈ vs, U.P s' v
  binds : ∀ bs env s tr r s' tr', (∀ u ∈ bindTerms bs, U.T u) →
    (∀ q ∈ bindTys bs, U.C q.1 q.2) → EnvP U.P s env → U.Is s →
    (evalBinds p sem cfg n bs env).run (s, tr) = .ok (r, (s', tr')) →
    U.Is s' ∧ U.Rs s s' ∧ ∀ env', r = some env' → EnvP U.P s' env'
  apply : ∀ ty t vs s tr r s' tr', U.T t → U.C ty t → (∀ v ∈ vs, U.P s v) → U.Is s →
    (applyTerm p sem cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    U.Is s' ∧ U.Rs s s' ∧ ∀ v, r = some v → U.P s' v
  mrule : ∀ rl vs s tr env s' tr', (∀ u ∈ ruleTerms rl, U.T u) →
    (∀ q ∈ ruleTys rl, U.C q.1 q.2) → (∀ v ∈ vs, U.P s v) → U.Is s →
    (matchRule p sem cfg n rl vs).run (s, tr) = .ok (some env, (s', tr')) →
    U.Is s' ∧ U.Rs s s' ∧ EnvP U.P s' env
  iflets : ∀ ils env s tr env' s' tr', (∀ il ∈ ils, (∀ u ∈ patTerms il.lhs, U.T u) ∧
      (∀ u ∈ exprTerms il.rhs, U.T u) ∧ ∀ q ∈ exprTys il.rhs, U.C q.1 q.2) →
    EnvP U.P s env → U.Is s →
    (matchIfLets p sem cfg n ils env).run (s, tr) = .ok (some env', (s', tr')) →
    U.Is s' ∧ U.Rs s s' ∧ EnvP U.P s' env'

/-- **Soundness of the uniform invariant**, at every fuel. -/
theorem uSoundAt (hc : cfg.checkOverlap = false) : ∀ n, USoundAt cfg U n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  cases n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rename_i h <;>
      first
      | (rw [evalExpr.eq_1] at h; exact (throw_ok h).elim)
      | (rw [evalArgs.eq_1] at h; exact (throw_ok h).elim)
      | (rw [evalBinds.eq_1] at h; exact (throw_ok h).elim)
      | (rw [applyTerm.eq_1] at h; exact (throw_ok h).elim)
      | (rw [matchRule.eq_1] at h; exact (throw_ok h).elim)
      | (rw [matchIfLets.eq_1] at h; exact (throw_ok h).elim)
  | succ n =>
  have ihn := ih n (Nat.lt_succ_self n)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- evalExpr
    intro e env s tr r s' tr' hT hC he hIs h
    cases e with
    | var ty x =>
      rw [evalExpr.eq_2] at h
      split at h
      · rename_i w hw
        cases pure_ok h
        exact ⟨hIs, U.rs_refl _, fun v hv => by cases hv; exact he x _ hw⟩
      · exact (throw_ok h).elim
    | constBool ty b =>
      rw [evalExpr.eq_3] at h
      cases pure_ok h; exact ⟨hIs, U.rs_refl _, fun v hv => by cases hv; exact U.bool _ _ hIs⟩
    | constInt ty i =>
      rw [evalExpr.eq_4] at h
      cases pure_ok h; exact ⟨hIs, U.rs_refl _, fun v hv => by cases hv; exact U.int _ _ _ hIs⟩
    | constPrim ty nm =>
      rw [evalExpr.eq_5] at h
      split at h
      · rename_i c hcp
        cases pure_ok h
        exact ⟨hIs, U.rs_refl _, fun v hv => by cases hv; exact U.prim _ _ _ _ hIs hcp⟩
      · exact (throw_ok h).elim
    | «let» ty bs body =>
      rw [evalExpr.eq_6] at h
      obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
      obtain ⟨hIs1, r1, he1⟩ := ihn.binds _ _ _ _ _ _ _
        (fun u hu => hT u (by simp [exprTerms, hu])) (fun q hq => hC q (by simp [exprTys, hq]))
        he hIs h1
      cases o with
      | none => cases pure_ok h2; exact ⟨hIs1, r1, fun v hv => by cases hv⟩
      | some env' =>
        obtain ⟨hIs2, r2, hv2⟩ := ihn.expr _ _ _ _ _ _ _
          (fun u hu => hT u (by simp [exprTerms, hu])) (fun q hq => hC q (by simp [exprTys, hq]))
          (he1 env' rfl) hIs1 h2
        exact ⟨hIs2, U.rs_trans _ _ _ r1 r2, hv2⟩
    | term ty t args =>
      rw [evalExpr.eq_7] at h
      obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
      obtain ⟨hIs1, r1, hv1⟩ := ihn.args _ _ _ _ _ _ _
        (fun u hu => hT u (by simp [exprTerms, hu])) (fun q hq => hC q (by simp [exprTys, hq]))
        he hIs h1
      cases o with
      | none => cases pure_ok h2; exact ⟨hIs1, r1, fun v hv => by cases hv⟩
      | some vs =>
        obtain ⟨hIs2, r2, hv2⟩ := ihn.apply _ _ _ _ _ _ _ _ (hT t (by simp [exprTerms]))
          (hC (ty, t) (by simp [exprTys])) (hv1 vs rfl) hIs1 h2
        exact ⟨hIs2, U.rs_trans _ _ _ r1 r2, hv2⟩
  · -- evalArgs
    intro es env s tr r s' tr' hT hC he hIs h
    cases es with
    | nil =>
      rw [evalArgs.eq_2] at h
      cases pure_ok h; exact ⟨hIs, U.rs_refl _, fun vs hv => by cases hv; simp⟩
    | cons e es =>
      rw [evalArgs.eq_3] at h
      obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
      obtain ⟨hIs1, r1, hv1⟩ := ihn.expr _ _ _ _ _ _ _
        (fun u hu => hT u (by simp [exprTermsL, hu])) (fun q hq => hC q (by simp [exprTysL, hq]))
        he hIs h1
      cases o with
      | none => cases pure_ok h2; exact ⟨hIs1, r1, fun vs hv => by cases hv⟩
      | some v =>
        obtain ⟨o2, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
        obtain ⟨hIs2, r2, hv2⟩ := ihn.args _ _ _ _ _ _ _
          (fun u hu => hT u (by simp [exprTermsL, hu])) (fun q hq => hC q (by simp [exprTysL, hq]))
          (envP_mono he fun w hw => U.mono _ _ _ hIs hIs1 r1 hw) hIs1 h3
        have r12 := U.rs_trans _ _ _ r1 r2
        cases o2 with
        | none => cases pure_ok h4; exact ⟨hIs2, r12, fun vs hv => by cases hv⟩
        | some vs =>
          cases pure_ok h4
          refine ⟨hIs2, r12, fun ws hw => ?_⟩
          cases hw
          intro w hw
          rcases List.mem_cons.mp hw with rfl | hw
          · exact U.mono _ _ _ hIs1 hIs2 r2 (hv1 w rfl)
          · exact hv2 vs rfl w hw
  · -- evalBinds
    intro bs env s tr r s' tr' hT hC he hIs h
    cases bs with
    | nil =>
      rw [evalBinds.eq_2] at h
      cases pure_ok h; exact ⟨hIs, U.rs_refl _, fun e he' => by cases he'; exact he⟩
    | cons b bs =>
      obtain ⟨x, ty, e⟩ := b
      rw [evalBinds.eq_3] at h
      obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
      obtain ⟨hIs1, r1, hv1⟩ := ihn.expr _ _ _ _ _ _ _
        (fun u hu => hT u (by simp [bindTerms, hu])) (fun q hq => hC q (by simp [bindTys, hq]))
        he hIs h1
      cases o with
      | none => cases pure_ok h2; exact ⟨hIs1, r1, fun e he' => by cases he'⟩
      | some v =>
        simp only at h2
        split at h2
        · obtain ⟨hIs2, r2, he2⟩ := ihn.binds _ _ _ _ _ _ _
            (fun u hu => hT u (by simp [bindTerms, hu])) (fun q hq => hC q (by simp [bindTys, hq]))
            (envP_set (envP_mono he fun w hw => U.mono _ _ _ hIs hIs1 r1 hw) (hv1 v rfl) x)
            hIs1 h2
          exact ⟨hIs2, U.rs_trans _ _ _ r1 r2, he2⟩
        · exact (throw_ok h2).elim
  · -- applyTerm
    intro ty t vs s tr r s' tr' hT hC hvs hIs h
    by_cases hO : U.O t
    · exact U.oracle t hO cfg hc _ _ _ _ _ _ _ _ hvs hIs h
    cases ht : termOf p t with
    | error e =>
      rw [applyTerm.eq_2] at h
      obtain ⟨term', s1, h1, h2⟩ := bind_ok h
      obtain ⟨_, ht', -⟩ := liftM_ok h1
      rw [ht] at ht'; cases ht'
    | ok term =>
      cases hk : term.kind with
      | enumVariant k =>
        rw [applyTerm.eq_2] at h
        obtain ⟨term', s1, h1, h2⟩ := bind_ok h
        obtain ⟨_, ht', he⟩ := liftM_ok h1
        rw [ht] at ht'; cases ht'; cases he
        rw [hk] at h2
        cases pure_ok h2
        exact ⟨hIs, U.rs_refl _, fun v hv => by
          cases hv; exact U.mkd _ _ _ _ _ _ hT hC ht (.inl hk) hIs hvs⟩
      | struct =>
        rw [applyTerm.eq_2] at h
        obtain ⟨term', s1, h1, h2⟩ := bind_ok h
        obtain ⟨_, ht', he⟩ := liftM_ok h1
        rw [ht] at ht'; cases ht'; cases he
        rw [hk] at h2
        cases pure_ok h2
        exact ⟨hIs, U.rs_refl _, fun v hv => by
          cases hv; exact U.mkd _ _ _ _ _ _ hT hC ht (.inr ⟨hk, rfl⟩) hIs hvs⟩
      | decl flags ctor ex =>
        cases ctor with
        | none =>
          rw [applyTerm.eq_2] at h
          obtain ⟨term', s1, h1, h2⟩ := bind_ok h
          obtain ⟨_, ht', he⟩ := liftM_ok h1
          rw [ht] at ht'; cases ht'; cases he
          rw [hk] at h2
          exact (throw_ok h2).elim
        | some c =>
          cases c with
          | external fn =>
            rw [applyTerm.eq_2] at h
            obtain ⟨term', s1, h1, h2⟩ := bind_ok h
            obtain ⟨_, ht', he⟩ := liftM_ok h1
            rw [ht] at ht'; cases ht'; cases he
            rw [hk] at h2
            simp only at h2
            split at h2
            · exact (throw_ok h2).elim
            · obtain ⟨g, s2, h3, h4⟩ := bind_ok h2
              cases get_ok h3
              simp only at h4
              split at h4
              · rename_i v st' hct
                obtain ⟨u, s3, h5, h6⟩ := bind_ok h4
                cases set_ok h5
                cases pure_ok h6
                obtain ⟨hv, hIs', hR⟩ := U.ctor _ _ _ _ _ _ _ _ _ hT ht hk hIs hvs hct
                exact ⟨hIs', hR, fun w hw => by cases hw; exact hv⟩
              · split at h4
                · cases pure_ok h4; exact ⟨hIs, U.rs_refl _, fun w hw => by cases hw⟩
                · exact (throw_ok h4).elim
              · exact (throw_ok h4).elim
          | internal =>
            cases hm : flags.isMulti with
            | true =>
              rw [applyTerm.eq_2] at h
              obtain ⟨term', s1, h1, h2⟩ := bind_ok h
              obtain ⟨_, ht', he⟩ := liftM_ok h1
              rw [ht] at ht'; cases ht'; cases he
              rw [hk] at h2
              simp only [hm, ↓reduceIte] at h2
              exact (throw_ok h2).elim
            | false =>
              rcases internal_cases hc ht hk hm h with ⟨rfl, rfl⟩ |
                ⟨rl, hrl, m, env, s1, tr1, tr2, hmn, -, hmatch, hrhs⟩
              · exact ⟨hIs, U.rs_refl _, fun v hv => by cases hv⟩
              · obtain ⟨hTr, hCr⟩ := U.closed t hT hO rl hrl
                obtain ⟨hIs1, r1, he1⟩ :=
                  (ih m (by omega)).mrule _ _ _ _ _ _ _ hTr hCr hvs hIs hmatch
                obtain ⟨hIs2, r2, hv2⟩ := ihn.expr _ _ _ _ _ _ _ (ruleTerms_rhs hTr)
                  (ruleTys_rhs hCr) he1 hIs1 hrhs
                exact ⟨hIs2, U.rs_trans _ _ _ r1 r2, hv2⟩
  · -- matchRule
    intro rl vs s tr env s' tr' hT hC hvs hIs h
    rw [matchRule.eq_2] at h
    obtain ⟨g, s1, h1, h2⟩ := bind_ok h
    cases get_ok h1
    simp only at h2
    obtain ⟨o, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
    obtain ⟨_, hma, he⟩ := liftM_ok h3
    cases he
    cases o with
    | none => cases pure_ok h4
    | some env0 =>
      exact ihn.iflets _ _ _ _ _ _ _ (ruleTerms_iflets hT hC) 
        (patArgs_ok U _ _ _ _ _ hma (ruleTerms_args hT) hIs hvs (envP_empty _ _)) hIs h4
  · -- matchIfLets
    intro ils env s tr env' s' tr' hT he hIs h
    cases ils with
    | nil =>
      rw [matchIfLets.eq_2] at h
      cases pure_ok h; exact ⟨hIs, U.rs_refl _, he⟩
    | cons il ils =>
      rw [matchIfLets.eq_3] at h
      obtain ⟨hTl, hTr, hCr⟩ := hT il List.mem_cons_self
      obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
      obtain ⟨hIs1, r1, hv1⟩ := ihn.expr _ _ _ _ _ _ _ hTr hCr he hIs h1
      cases o with
      | none => cases pure_ok h2
      | some v =>
        obtain ⟨g, s2, h3, h4⟩ := bind_ok h2
        cases get_ok h3
        simp only at h4
        obtain ⟨o2, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
        obtain ⟨_, hmp, he2⟩ := liftM_ok h5
        cases he2
        cases o2 with
        | none => cases pure_ok h6
        | some env1 =>
          obtain ⟨hIs2, r2, he3⟩ := ihn.iflets _ _ _ _ _ _ _
            (fun il' hil' => hT il' (List.mem_cons_of_mem _ hil'))
            (pat_ok U _ _ _ _ _ hmp hTl hIs1 (hv1 v rfl)
              (envP_mono he fun w hw => U.mono _ _ _ hIs hIs1 r1 hw)) hIs1 h6
          exact ⟨hIs2, U.rs_trans _ _ _ r1 r2, he3⟩

/-- **The uniform invariant along every run** of a term of `T` at an allowed call site. -/
theorem uSound (hc : cfg.checkOverlap = false) :
    ∀ n ty t vs s tr r s' tr', U.T t → U.C ty t → (∀ v ∈ vs, U.P s v) → U.Is s →
      (applyTerm p sem cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
      U.Is s' ∧ U.Rs s s' ∧ ∀ v, r = some v → U.P s' v :=
  fun n => (uSoundAt U hc n).apply

/-- **A root term**: an internal, non-multi term (not necessarily in `T`) whose rules are each
in scope (their terms in `T`, their call sites in `C`), hand-checked (`Hand`, with the
allowed-result predicate `Q`; the hand obligation gets the fuel of the root run `n = k + 1`,
of the right-hand side `k` and of the committed match `m`), or never match the arguments. Every
run from arguments with `P` keeps the invariant and returns a value with `P` or `Q`. -/
theorem uRoot (hc : cfg.checkOverlap = false) (Q : σ → V → Prop) (Hand : Rule → Prop)
    {n : Nat} {ty : TypeId} {t : TermId} {term : Term} {flags : TermFlags}
    {ex : Option Extractor} {vs : List V}
    (ht : termOf p t = .ok term) (hk : term.kind = .decl flags (some .internal) ex)
    (hm : flags.isMulti = false)
    (hrules : ∀ rl ∈ p.rulesOf t,
      ((∀ u ∈ ruleTerms rl, U.T u) ∧ ∀ q ∈ ruleTys rl, U.C q.1 q.2) ∨ Hand rl ∨
        ∀ m s0 env s1, (matchRule p sem cfg m rl vs).run s0 ≠ .ok (some env, s1))
    (hhand : ∀ rl ∈ p.rulesOf t, Hand rl →
      ∀ k m s tr env s1 tr1 r s2 tr2, n = k + 1 → m + 2 ≤ k →
        k ≤ m + 2 + (p.rulesOf t).length → (∀ v ∈ vs, U.P s v) → U.Is s →
        (matchRule p sem cfg m rl vs).run (s, tr) = .ok (some env, (s1, tr1)) →
        (evalExpr p sem cfg k rl.rhs env).run (s1, tr1) = .ok (r, (s2, tr2)) →
        U.Is s2 ∧ U.Rs s s2 ∧ ∀ v, r = some v → Q s2 v)
    {s s' : σ} {tr tr' : Array RuleId} {r : Option V}
    (hvs : ∀ v ∈ vs, U.P s v) (hIs : U.Is s)
    (h : (applyTerm p sem cfg n ty t vs).run (s, tr) = .ok (r, (s', tr'))) :
    U.Is s' ∧ U.Rs s s' ∧ ∀ v, r = some v → U.P s' v ∨ Q s' v := by
  cases n with
  | zero => rw [applyTerm.eq_1] at h; exact (throw_ok h).elim
  | succ k =>
  rcases internal_cases hc ht hk hm h with ⟨rfl, rfl⟩ |
    ⟨rl, hrl, m, env, s1, tr1, tr2, hmk, hkm, hmatch, hrhs⟩
  · exact ⟨hIs, U.rs_refl _, fun v hv => by cases hv⟩
  · rcases hrules rl hrl with ⟨hTr, hCr⟩ | hH | hno
    · obtain ⟨hIs1, r1, he1⟩ := (uSoundAt U hc m).mrule _ _ _ _ _ _ _ hTr hCr hvs hIs hmatch
      obtain ⟨hIs2, r2, hv2⟩ := (uSoundAt U hc k).expr _ _ _ _ _ _ _ (ruleTerms_rhs hTr)
        (ruleTys_rhs hCr) he1 hIs1 hrhs
      exact ⟨hIs2, U.rs_trans _ _ _ r1 r2, fun v hv => .inl (hv2 v hv)⟩
    · obtain ⟨hIs2, r2, hv2⟩ := hhand rl hrl hH k m s tr env s1 tr1 r s' tr2 rfl hmk hkm hvs hIs
        hmatch hrhs
      exact ⟨hIs2, r2, fun v hv => .inr (hv2 v hv)⟩
    · exact absurd hmatch (hno m _ _ _)

end Sound

end Isle.Interp
