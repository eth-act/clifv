import Lean
import FV.Backend.Proof.RelocProvCheck

/-!
# Name provenance of the ISLE lowering: soundness of the abstract interpretation (L1e, #216)

The soundness half of `RelocProvCheck`, a port of V1's flow soundness (`IselFlowCheck`,
section `Sound`) to the name-provenance domain `NA`:

* inversion lemmas for the abstract evaluation (`aExpr_let`, `aRule_inv`, `chkTab_get`, ...);
* pattern soundness (`aPat_sound`, `aPatArgs_sound`): matching a value an abstract value
  describes yields an environment the abstract environment describes;
* `soundAt` (by strong induction on the interpreter's fuel): given a `Model`, if `chkTab` holds
  then every interpreter run whose abstract evaluation succeeds produces values the abstract
  results describe and preserves the model's state invariant. The field `root` covers a term
  outside the table whose rules each pass `aRule` or never match.

The only difference from V1 is the abstraction of integer constants (`NA.cInt`, model field
`int`). The selection lemma `Flow.selectRule_some_lt` and the preorder lemma `presAt` are
domain-independent and reused.
-/

namespace Backend.Proof.RelocProv

open Backend Isle Isle.Interp Isle.Aarch64

section Inv
variable {p : Program} {tab : Tab} {strict : Bool}

/-! ### Inversion of the abstract evaluation -/

theorem aExpr_let {ty : TypeId} {bs : List (VarId × TypeId × Isle.Expr)} {body : Isle.Expr}
    {aenv : List NA} {a : NA} (h : aExpr p tab strict (.let ty bs body) aenv = some a) :
    ∃ aenv', aBinds p tab strict bs aenv = some aenv' ∧ aExpr p tab strict body aenv' = some a := by
  rw [aExpr.eq_5] at h
  split at h
  · exact ⟨_, ‹_›, h⟩
  · cases h

theorem aExpr_term {ty : TypeId} {t : TermId} {args : List Isle.Expr} {aenv : List NA} {a : NA}
    (h : aExpr p tab strict (.term ty t args) aenv = some a) :
    ∃ as, aArgs p tab strict args aenv = some as ∧ aApply p tab strict ty t as = some a := by
  rw [aExpr.eq_6] at h
  split at h
  · exact ⟨_, ‹_›, h⟩
  · cases h

theorem aArgs_cons {e : Isle.Expr} {es : List Isle.Expr} {aenv : List NA} {as : List NA}
    (h : aArgs p tab strict (e :: es) aenv = some as) :
    ∃ a as', as = a :: as' ∧ aExpr p tab strict e aenv = some a ∧
      aArgs p tab strict es aenv = some as' := by
  rw [aArgs.eq_2] at h
  split at h
  · cases h; exact ⟨_, _, rfl, ‹_›, ‹_›⟩
  · cases h

theorem aBinds_cons {x : VarId} {ty : TypeId} {e : Isle.Expr} {bs : List (VarId × TypeId × Isle.Expr)}
    {aenv aenv' : List NA} (h : aBinds p tab strict ((x, ty, e) :: bs) aenv = some aenv') :
    ∃ a, aExpr p tab strict e aenv = some a ∧ aBinds p tab strict bs (aenv.set x a) = some aenv' := by
  rw [aBinds.eq_2] at h
  split at h
  · exact ⟨_, ‹_›, h⟩
  · cases h

theorem aIfLets_cons {il : IfLet} {ils : List IfLet} {aenv aenv' : List NA}
    (h : aIfLets p tab strict (il :: ils) aenv = some aenv') :
    ∃ a, aExpr p tab strict il.rhs aenv = some a ∧
      aIfLets p tab strict ils (aPat p a il.lhs aenv) = some aenv' := by
  rw [aIfLets.eq_2] at h
  split at h
  · exact ⟨_, ‹_›, h⟩
  · cases h

theorem aRule_inv {ins : List NA} {out : NA} {r : Rule} (h : aRule p tab strict ins out r = true) :
    ∃ aenv a, aRuleEnv p tab strict ins r = some aenv ∧ aExpr p tab strict r.rhs aenv = some a ∧
      a.le out = true := by
  unfold aRule at h
  split at h
  · split at h
    · exact ⟨_, _, ‹_›, ‹_›, h⟩
    · cases h
  · cases h

theorem chkTab_get (h : chkTab p tab strict = true) {t : TermId} {ins : List NA} {out : NA}
    (hg : tabGet tab t = some (ins, out)) : ∀ r ∈ p.rulesOf t, aRule p tab strict ins out r = true := by
  unfold tabGet at hg
  cases hf : tab.find? (·.1 == t) with
  | none => rw [hf] at hg; cases hg
  | some e =>
    rw [hf] at hg
    simp only [Option.map_some, Option.some.injEq] at hg
    have hm := List.mem_of_find?_eq_some hf
    have he := List.find?_some hf
    simp only [beq_iff_eq] at he
    have := List.all_eq_true.mp h e hm
    rw [he, hg] at this
    exact List.all_eq_true.mp this

end Inv

/-! ## Soundness -/

section Sound
variable {V σ : Type} {p : Program} {sem : Sem V σ} {cfg : Config}

variable {strict : Bool} (md : Model sem strict)

theorem holds2_mono {s s' : σ} (h : md.Rs s s') : ∀ {as : List NA} {vs : List V},
    Holds2 md.γ s as vs → Holds2 md.γ s' as vs
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨md.mono _ _ _ _ h h1, holds2_mono h h2⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem envOK_mono {s s' : σ} (h : md.Rs s s') {aenv : List NA} {env : Isle.Interp.Env V}
    (he : EnvOK md.γ s aenv env) : EnvOK md.γ s' aenv env :=
  fun x w hx => md.mono _ _ _ _ h (he x w hx)

theorem envOK_empty (s : σ) (aenv : List NA) (n : Nat) :
    EnvOK md.γ s aenv (Array.replicate n none) := by
  intro x w hx
  simp [Array.getElem?_replicate] at hx

theorem envOK_set {s : σ} {aenv : List NA} {env : Isle.Interp.Env V} (he : EnvOK md.γ s aenv env) {a : NA}
    {v : V} (hv : md.γ a s v) (x : Nat) :
    EnvOK md.γ s (aenv.set x a) (env.set! x (some v)) := by
  intro y w hy
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hy
  by_cases hyx : x = y
  · subst hyx
    simp only [↓reduceIte] at hy
    split at hy
    · cases hy
      rw [List.getD_eq_getElem?_getD, List.getElem?_set]
      simp only [↓reduceIte]
      split
      · exact hv
      · exact md.top _ _
    · cases hy
  · simp only [hyx, ↓reduceIte] at hy
    have := he y w hy
    rwa [List.getD_eq_getElem?_getD, List.getElem?_set_ne hyx, ← List.getD_eq_getElem?_getD]

theorem envOK_aPat_wild {s : σ} {aenv : List NA} {env : Isle.Interp.Env V} (he : EnvOK md.γ s aenv env) :
    EnvOK md.γ s aenv env := he

mutual
/-- **Pattern soundness**: matching `q` against a value `a` describes extends a described
environment to one `aPat` describes. -/
theorem aPat_sound : ∀ (q : Pattern) (a : NA) (aenv : List NA) (v : V) (env env' : Isle.Interp.Env V) (s : σ),
    matchPat p sem s q v env = .ok (some env') → md.γ a s v → EnvOK md.γ s aenv env →
    EnvOK md.γ s (aPat p a q aenv) env'
  | .bind ty x sub, a, aenv, v, env, env', s, h, hv, he => by
    rw [matchPat.eq_1] at h
    rw [aPat.eq_1]
    split at h
    · exact aPat_sound sub a _ v _ env' s h hv (envOK_set md he hv x)
    · cases h
  | .var ty x, a, aenv, v, env, env', s, h, hv, he => by
    rw [matchPat.eq_2] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      split at h
      · cases h; exact he
      · cases h
    · cases h
  | .constBool ty b, a, aenv, v, env, env', s, h, hv, he => by
    rw [matchPat.eq_3] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    split at h
    · cases h; exact he
    · cases h
  | .constInt ty i, a, aenv, v, env, env', s, h, hv, he => by
    rw [matchPat.eq_4] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    split at h
    · cases h; exact he
    · cases h
  | .constPrim ty nm, a, aenv, v, env, env', s, h, hv, he => by
    rw [matchPat.eq_5] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      split at h
      · cases h; exact he
      · cases h
    · cases h
  | .wildcard ty, a, aenv, v, env, env', s, h, hv, he => by
    rw [matchPat.eq_6] at h
    cases h; exact he
  | .and ty ps, a, aenv, v, env, env', s, h, hv, he => by
    rw [matchPat.eq_7] at h
    rw [aPat.eq_2]
    exact aPatAll_sound_all ps a aenv v env env' s h hv he
  | .term ty t args, a, aenv, v, env, env', s, h, hv, he => by
    rw [matchPat.eq_8] at h
    rw [aPat.eq_3]
    cases ht : termOf p t with
    | error e => rw [ht] at h; cases h
    | ok term =>
      rw [ht] at h
      simp only [bind, Except.bind] at h ⊢
      cases hk : term.kind with
      | enumVariant k =>
        rw [hk] at h
        simp only at h ⊢
        split at h
        · rename_i k' fs hu
          split at h
          · exact aPatAll_sound_args args a aenv fs env env' s h (md.un _ _ _ _ _ _ hv hu) he
          · cases h
        · cases h
      | struct =>
        rw [hk] at h
        simp only at h ⊢
        split at h
        · rename_i k' fs hu
          exact aPatAll_sound_args args a aenv fs env env' s h (md.un _ _ _ _ _ _ hv hu) he
        · cases h
      | decl flags ctor ext =>
        rw [hk] at h
        cases ext with
        | none => cases h
        | some ex =>
          cases ex with
          | internal form => cases h
          | external fn inf =>
            simp only at h ⊢
            split at h
            · cases h
            · split at h
              · rename_i fs hx
                exact aPatAll_sound_args args _ aenv fs env env' s h (md.ext _ _ _ _ _ hv hx) he
              · split at h
                · cases h
                · cases h
              · cases h
/-- `aPatAll` for `and`: every pattern against the same value. -/
theorem aPatAll_sound_all : ∀ (qs : List Pattern) (a : NA) (aenv : List NA) (v : V)
    (env env' : Isle.Interp.Env V) (s : σ),
    matchAll p sem s qs v env = .ok (some env') → md.γ a s v → EnvOK md.γ s aenv env →
    EnvOK md.γ s (aPatAll p a qs aenv) env'
  | [], a, aenv, v, env, env', s, h, hv, he => by
    rw [matchAll.eq_1] at h
    cases h
    rw [aPatAll.eq_1]
    exact he
  | q :: qs, a, aenv, v, env, env', s, h, hv, he => by
    rw [matchAll.eq_2] at h
    rw [aPatAll.eq_2]
    cases hq : matchPat p sem s q v env with
    | error e => rw [hq] at h; cases h
    | ok o =>
      rw [hq] at h
      cases o with
      | none => cases h
      | some e1 =>
        exact aPatAll_sound_all qs a _ v e1 env' s h hv (aPat_sound q a aenv v env e1 s hq hv he)
/-- `aPatAll` for fields: the patterns against values the same `a` describes. -/
theorem aPatAll_sound_args : ∀ (qs : List Pattern) (a : NA) (aenv : List NA) (fs : List V)
    (env env' : Isle.Interp.Env V) (s : σ),
    matchArgs p sem s qs fs env = .ok (some env') → (∀ f ∈ fs, md.γ a s f) →
    EnvOK md.γ s aenv env → EnvOK md.γ s (aPatAll p a qs aenv) env'
  | [], a, aenv, [], env, env', s, h, hv, he => by
    rw [matchArgs.eq_1] at h
    cases h
    rw [aPatAll.eq_1]
    exact he
  | q :: qs, a, aenv, f :: fs, env, env', s, h, hv, he => by
    rw [matchArgs.eq_2] at h
    rw [aPatAll.eq_2]
    cases hq : matchPat p sem s q f env with
    | error e => rw [hq] at h; cases h
    | ok o =>
      rw [hq] at h
      cases o with
      | none => cases h
      | some e1 =>
        exact aPatAll_sound_args qs a _ fs e1 env' s h (fun g hg => hv g (List.mem_cons_of_mem _ hg))
          (aPat_sound q a aenv f env e1 s hq (hv f List.mem_cons_self) he)
  | [], a, aenv, _ :: _, env, env', s, h, hv, he => by
    rw [matchArgs.eq_3] at h
    all_goals first | cases h | (intros; simp_all)
  | _ :: _, a, aenv, [], env, env', s, h, hv, he => by
    rw [matchArgs.eq_3] at h
    all_goals first | cases h | (intros; simp_all)
end

/-- Pointwise pattern soundness (`aPatArgs`, `top` past the end of the abstract values). -/
theorem aPatArgs_sound : ∀ (qs : List Pattern) (as : List NA) (aenv : List NA) (vs : List V)
    (env env' : Isle.Interp.Env V) (s : σ),
    matchArgs p sem s qs vs env = .ok (some env') → Holds2 md.γ s as vs →
    EnvOK md.γ s aenv env → EnvOK md.γ s (aPatArgs p as qs aenv) env'
  | [], as, aenv, [], env, env', s, h, hv, he => by
    rw [matchArgs.eq_1] at h
    cases h
    cases as <;> exact he
  | q :: qs, a :: as, aenv, v :: vs, env, env', s, h, hv, he => by
    rw [matchArgs.eq_2] at h
    rw [aPatArgs.eq_1]
    cases hq : matchPat p sem s q v env with
    | error e => rw [hq] at h; cases h
    | ok o =>
      rw [hq] at h
      cases o with
      | none => cases h
      | some e1 =>
        exact aPatArgs_sound qs as _ vs e1 env' s h hv.2 (aPat_sound md q a aenv v env e1 s hq hv.1 he)
  | q :: qs, [], aenv, v :: vs, env, env', s, h, hv, he => hv.elim
  | [], _, aenv, _ :: _, env, env', s, h, hv, he => by
    rw [matchArgs.eq_3] at h
    all_goals first | cases h | (intros; simp_all)
  | _ :: _, _, aenv, [], env, env', s, h, hv, he => by
    rw [matchArgs.eq_3] at h
    all_goals first | cases h | (intros; simp_all)

variable (p cfg) (tab : Tab)

/-- The soundness statements at fuel `n`. -/
structure SoundAt (n : Nat) : Prop where
  expr : ∀ e aenv a env s tr r s' tr', aExpr p tab strict e aenv = some a →
    EnvOK md.γ s aenv env → md.Is s →
    (evalExpr p sem cfg n e env).run (s, tr) = .ok (r, (s', tr')) →
    md.Is s' ∧ ∀ v, r = some v → md.γ a s' v
  args : ∀ es aenv as env s tr r s' tr', aArgs p tab strict es aenv = some as →
    EnvOK md.γ s aenv env → md.Is s →
    (evalArgs p sem cfg n es env).run (s, tr) = .ok (r, (s', tr')) →
    md.Is s' ∧ ∀ vs, r = some vs → Holds2 md.γ s' as vs
  binds : ∀ bs aenv aenv' env s tr r s' tr', aBinds p tab strict bs aenv = some aenv' →
    EnvOK md.γ s aenv env → md.Is s →
    (evalBinds p sem cfg n bs env).run (s, tr) = .ok (r, (s', tr')) →
    md.Is s' ∧ ∀ env', r = some env' → EnvOK md.γ s' aenv' env'
  apply : ∀ ty t as a vs s tr r s' tr', aApply p tab strict ty t as = some a →
    Holds2 md.γ s as vs → md.Is s →
    (applyTerm p sem cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    md.Is s' ∧ ∀ v, r = some v → md.γ a s' v
  root : ∀ ty t term flags ex ins out vs s tr r s' tr', termOf p t = .ok term →
    term.kind = .decl flags (some .internal) ex →
    (∀ rl ∈ p.rulesOf t, aRule p tab strict ins out rl = true ∨
      ∀ m s0 env s1, (matchRule p sem cfg m rl vs).run s0 ≠ .ok (some env, s1)) →
    Holds2 md.γ s ins vs → md.Is s →
    (applyTerm p sem cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    md.Is s' ∧ ∀ v, r = some v → md.γ out s' v
  mrule : ∀ rl ins aenv vs s tr env s' tr', aRuleEnv p tab strict ins rl = some aenv →
    Holds2 md.γ s ins vs → md.Is s →
    (matchRule p sem cfg n rl vs).run (s, tr) = .ok (some env, (s', tr')) →
    md.Is s' ∧ EnvOK md.γ s' aenv env
  iflets : ∀ ils aenv aenv' env s tr env' s' tr', aIfLets p tab strict ils aenv = some aenv' →
    EnvOK md.γ s aenv env → md.Is s →
    (matchIfLets p sem cfg n ils env).run (s, tr) = .ok (some env', (s', tr')) →
    md.Is s' ∧ EnvOK md.γ s' aenv' env'

variable {p cfg tab}

theorem holds2_le : ∀ {as bs : List NA} {vs : List V} {s : σ}, leAll as bs = true →
    Holds2 md.γ s as vs → Holds2 md.γ s bs vs
  | [], [], [], _, _, _ => trivial
  | a :: as, b :: bs, v :: vs, s, h, ⟨h1, h2⟩ => by
    simp only [leAll, Bool.and_eq_true] at h
    exact ⟨md.le _ _ _ _ h.1 h1, holds2_le h.2 h2⟩
  | [], _ :: _, _, _, h, _ => by simp [leAll] at h
  | _ :: _, [], _, _, h, _ => by simp [leAll] at h
  | [], [], _ :: _, _, _, h => h.elim
  | _ :: _, _ :: _, [], _, _, h => h.elim

/-- **Soundness of the abstract interpretation**, at every fuel. -/
theorem soundAt (hc : cfg.checkOverlap = false) (htab : chkTab p tab strict = true) :
    ∀ n, SoundAt p cfg md tab n := by
  have pres := presAt (p := p) (cfg := cfg) md.rs_refl md.rs_trans md.rs_ctor
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  cases n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rename_i h <;>
      first
      | (rw [evalExpr.eq_1] at h; exact (throw_ok h).elim)
      | (rw [evalArgs.eq_1] at h; exact (throw_ok h).elim)
      | (rw [evalBinds.eq_1] at h; exact (throw_ok h).elim)
      | (rw [applyTerm.eq_1] at h; exact (throw_ok h).elim)
      | (rw [matchRule.eq_1] at h; exact (throw_ok h).elim)
      | (rw [matchIfLets.eq_1] at h; exact (throw_ok h).elim)
  | succ n =>
  have ihn := ih n (Nat.lt_succ_self n)
  -- `root` first: `apply` of an internal term uses it at the same fuel
  have hroot : ∀ ty t term flags ex ins out vs s tr r s' tr', termOf p t = .ok term →
      term.kind = .decl flags (some .internal) ex →
      (∀ rl ∈ p.rulesOf t, aRule p tab strict ins out rl = true ∨
        ∀ m s0 env s1, (matchRule p sem cfg m rl vs).run s0 ≠ .ok (some env, s1)) →
      Holds2 md.γ s ins vs → md.Is s →
      (applyTerm p sem cfg (n + 1) ty t vs).run (s, tr) = .ok (r, (s', tr')) →
      md.Is s' ∧ ∀ v, r = some v → md.γ out s' v := by
    intro ty t term flags ex ins out vs s tr r s' tr' ht hk hrules hins hIs h
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
    rw [applyTerm_internal_run ht hk hm] at h
    obtain ⟨⟨sel, ⟨s1, tr1⟩⟩, h1, h2⟩ := except_bind_eq_ok h
    cases sel with
    | none =>
      have := selectRule_none h1
      cases this
      simp only at h2
      split at h2
      · cases pure_ok h2; exact ⟨hIs, fun v hv => by cases hv⟩
      · exact (throw_ok h2).elim
    | some re =>
      obtain ⟨rl, env⟩ := re
      obtain ⟨hrl, m, hmn, hmatch⟩ := Flow.selectRule_some_lt hc h1
      have hok : aRule p tab strict ins out rl = true := by
        rcases hrules rl hrl with h | h
        · exact h
        · exact absurd hmatch (h m _ _ _)
      obtain ⟨aenv, a, hae, ha, hle⟩ := aRule_inv hok
      obtain ⟨hIs1, he1⟩ := (ih m (by omega)).mrule _ _ _ _ _ _ _ _ _ hae hins hIs hmatch
      simp only at h2
      obtain ⟨ev, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
      obtain ⟨hIs2, hv2⟩ := ihn.expr _ _ _ _ _ _ _ _ _ ha he1 hIs1 h3
      cases ev with
      | some v =>
        obtain ⟨u, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
        have hf := fire_ok h5
        cases pure_ok h6
        simp only at hf
        subst hf
        exact ⟨hIs2, fun w hw => by cases hw; exact md.le _ _ _ _ hle (hv2 v rfl)⟩
      | none => cases pure_ok h4; exact ⟨hIs2, fun w hw => by cases hw⟩
  refine ⟨?_, ?_, ?_, ?_, hroot, ?_, ?_⟩
  · -- evalExpr
    intro e aenv a env s tr r s' tr' ha he hIs h
    cases e with
    | var ty x =>
      rw [evalExpr.eq_2] at h
      rw [aExpr.eq_1] at ha
      cases ha
      split at h
      · rename_i w hw
        cases pure_ok h
        exact ⟨hIs, fun v hv => by cases hv; exact he x _ hw⟩
      · exact (throw_ok h).elim
    | constBool ty b =>
      rw [evalExpr.eq_3] at h; rw [aExpr.eq_2] at ha; cases ha
      cases pure_ok h; exact ⟨hIs, fun v hv => by cases hv; exact md.bool _ _⟩
    | constInt ty i =>
      rw [evalExpr.eq_4] at h; rw [aExpr.eq_4] at ha; cases ha
      cases pure_ok h; exact ⟨hIs, fun v hv => by cases hv; exact md.int _ _ _⟩
    | constPrim ty nm =>
      rw [evalExpr.eq_5] at h; rw [aExpr.eq_3] at ha; cases ha
      split at h
      · rename_i c hcp
        cases pure_ok h; exact ⟨hIs, fun v hv => by cases hv; exact md.prim _ _ _ _ hcp⟩
      · exact (throw_ok h).elim
    | «let» ty bs body =>
      rw [evalExpr.eq_6] at h
      obtain ⟨aenv', hb, hbody⟩ := aExpr_let ha
      obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
      obtain ⟨hIs1, he1⟩ := ihn.binds _ _ _ _ _ _ _ _ _ hb he hIs h1
      cases o with
      | none => cases pure_ok h2; exact ⟨hIs1, fun v hv => by cases hv⟩
      | some env' => exact ihn.expr _ _ _ _ _ _ _ _ _ hbody (he1 env' rfl) hIs1 h2
    | term ty t args =>
      rw [evalExpr.eq_7] at h
      obtain ⟨as, hargs, happ⟩ := aExpr_term ha
      obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
      obtain ⟨hIs1, hv1⟩ := ihn.args _ _ _ _ _ _ _ _ _ hargs he hIs h1
      cases o with
      | none => cases pure_ok h2; exact ⟨hIs1, fun v hv => by cases hv⟩
      | some vs => exact ihn.apply _ _ _ _ _ _ _ _ _ _ happ (hv1 vs rfl) hIs1 h2
  · -- evalArgs
    intro es aenv as env s tr r s' tr' ha he hIs h
    cases es with
    | nil =>
      rw [evalArgs.eq_2] at h; rw [aArgs.eq_1] at ha; cases ha
      cases pure_ok h; exact ⟨hIs, fun vs hv => by cases hv; trivial⟩
    | cons e es =>
      rw [evalArgs.eq_3] at h
      obtain ⟨a, as', rfl, hae, haes⟩ := aArgs_cons ha
      obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
      obtain ⟨hIs1, hv1⟩ := ihn.expr _ _ _ _ _ _ _ _ _ hae he hIs h1
      have r1 := (pres _).expr _ _ _ _ _ _ _ h1
      cases o with
      | none => cases pure_ok h2; exact ⟨hIs1, fun vs hv => by cases hv⟩
      | some v =>
        obtain ⟨o2, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
        obtain ⟨hIs2, hv2⟩ := ihn.args _ _ _ _ _ _ _ _ _ haes (envOK_mono md r1 he) hIs1 h3
        have r2 := (pres _).args _ _ _ _ _ _ _ h3
        cases o2 with
        | none => cases pure_ok h4; exact ⟨hIs2, fun vs hv => by cases hv⟩
        | some vs =>
          cases pure_ok h4
          exact ⟨hIs2, fun ws hw => by
            cases hw; exact ⟨md.mono _ _ _ _ r2 (hv1 v rfl), hv2 vs rfl⟩⟩
  · -- evalBinds
    intro bs aenv aenv' env s tr r s' tr' ha he hIs h
    cases bs with
    | nil =>
      rw [evalBinds.eq_2] at h; rw [aBinds.eq_1] at ha; cases ha
      cases pure_ok h; exact ⟨hIs, fun e he' => by cases he'; exact he⟩
    | cons b bs =>
      obtain ⟨x, ty, e⟩ := b
      rw [evalBinds.eq_3] at h
      obtain ⟨a, hae, hbs⟩ := aBinds_cons ha
      obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
      obtain ⟨hIs1, hv1⟩ := ihn.expr _ _ _ _ _ _ _ _ _ hae he hIs h1
      have r1 := (pres _).expr _ _ _ _ _ _ _ h1
      cases o with
      | none => cases pure_ok h2; exact ⟨hIs1, fun e he' => by cases he'⟩
      | some v =>
        simp only at h2
        split at h2
        · exact ihn.binds _ _ _ _ _ _ _ _ _ hbs
            (envOK_set md (envOK_mono md r1 he) (hv1 v rfl) x) hIs1 h2
        · exact (throw_ok h2).elim
  · -- applyTerm
    intro ty t as a vs s tr r s' tr' ha hvs hIs h
    unfold aApply at ha
    cases ht : termOf p t with
    | error e =>
      rw [applyTerm.eq_2] at h
      obtain ⟨term', s1, h1, h2⟩ := bind_ok h
      obtain ⟨_, ht', -⟩ := liftM_ok h1
      rw [ht] at ht'; cases ht'
    | ok term =>
      rw [ht] at ha
      simp only at ha
      cases hk : term.kind with
      | enumVariant k =>
        rw [hk] at ha; cases ha
        rw [applyTerm.eq_2] at h
        obtain ⟨term', s1, h1, h2⟩ := bind_ok h
        obtain ⟨_, ht', he⟩ := liftM_ok h1
        rw [ht] at ht'; cases ht'; cases he
        rw [hk] at h2
        cases pure_ok h2
        exact ⟨hIs, fun v hv => by cases hv; exact md.mkd _ _ _ _ _ hvs⟩
      | struct =>
        rw [hk] at ha; cases ha
        rw [applyTerm.eq_2] at h
        obtain ⟨term', s1, h1, h2⟩ := bind_ok h
        obtain ⟨_, ht', he⟩ := liftM_ok h1
        rw [ht] at ht'; cases ht'; cases he
        rw [hk] at h2
        cases pure_ok h2
        exact ⟨hIs, fun v hv => by cases hv; exact md.mkd _ _ _ _ _ hvs⟩
      | decl flags ctor ex =>
        rw [hk] at ha
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
          | internal =>
            simp only at ha
            cases hg : tabGet tab t with
            | none => rw [hg] at ha; cases ha
            | some e =>
              obtain ⟨ins, out⟩ := e
              rw [hg] at ha
              simp only at ha
              split at ha
              · rename_i hle
                cases ha
                exact hroot ty t term flags ex ins _ vs s tr r s' tr' ht hk
                  (fun rl hrl => .inl (chkTab_get htab hg rl hrl)) (holds2_le md hle hvs) hIs h
              · cases ha
          | external fn =>
            simp only at ha
            split at ha
            · rename_i hpre
              cases ha
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
                · rename_i v st' hc
                  obtain ⟨u, s3, h5, h6⟩ := bind_ok h4
                  cases set_ok h5
                  cases pure_ok h6
                  obtain ⟨hv, hIs'⟩ := md.ctor _ _ _ _ _ _ hvs hIs hpre hc
                  exact ⟨hIs', fun w hw => by cases hw; exact hv⟩
                · split at h4
                  · cases pure_ok h4; exact ⟨hIs, fun w hw => by cases hw⟩
                  · exact (throw_ok h4).elim
                · exact (throw_ok h4).elim
            · cases ha
  · -- matchRule
    intro rl ins aenv vs s tr env s' tr' hae hins hIs h
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
      exact ihn.iflets _ _ _ _ _ _ _ _ _ hae
        (aPatArgs_sound md _ _ _ _ _ _ _ hma hins (envOK_empty md _ _ _)) hIs h4
  · -- matchIfLets
    intro ils aenv aenv' env s tr env' s' tr' ha he hIs h
    cases ils with
    | nil =>
      rw [matchIfLets.eq_2] at h; rw [aIfLets.eq_1] at ha; cases ha
      cases pure_ok h; exact ⟨hIs, he⟩
    | cons il ils =>
      rw [matchIfLets.eq_3] at h
      obtain ⟨a, hae, hails⟩ := aIfLets_cons ha
      obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
      obtain ⟨hIs1, hv1⟩ := ihn.expr _ _ _ _ _ _ _ _ _ hae he hIs h1
      have r1 := (pres _).expr _ _ _ _ _ _ _ h1
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
          exact ihn.iflets _ _ _ _ _ _ _ _ _ hails
            (aPat_sound md _ _ _ _ _ _ _ hmp (hv1 v rfl) (envOK_mono md r1 he)) hIs1 h6


end Sound

end Backend.Proof.RelocProv
