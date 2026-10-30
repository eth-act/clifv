import FV.Backend.Proof.StockSourceView
import FV.Backend.Proof.IselCmpInv
import FV.Backend.Proof.StockNoOpportunityPre
import FV.Backend.Proof.IselCovSound
import FV.Backend.Proof.StockPatternSource

/-! State-aware composition of the existing checked coverage analysis for Stock.
The source-pattern facts are transported through its proof-only identity view.
The induction below reuses IselCovSound's fuel proof; legacy interfaces are unchanged.
Helper/oracle contracts are internal obligations, not new accepted-program checks. -/
namespace Backend.Stock.Proof.Coverage
open Backend.Proof Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
attribute [local irreducible] Isle.Aarch64.program
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

variable {f : Clif.Function} {ctx : Ctx}

/-- Helper contracts and an actual Stock state invariant for checked evaluation.
The source model is used only for pure pattern soundness. -/
structure Model (p : Program) (f : Clif.Function) (ctx : Ctx) where
  Is : State → Prop
  source : CovModel aext actor apre aOracle p f (sourceIdentityCtx ctx)
  ctor : ∀ (t : TermId) (term : Term), termOf p t = .ok term →
    ∀ (as : List AW) (vs : List V) (v : V) (st st' : State),
      Holds2 f (sourceIdentityCtx ctx) as vs → Is st → noOpportunityPre term.id as = true →
      (Stock.sem ctx).ctor term vs st = .ok (v, st') →
        γ f (sourceIdentityCtx ctx) (actor term.id as) v ∧ Is st'
  oracle : ∀ (cfg : Config), cfg.checkOverlap = false → ∀ (n : Nat) (ty : TypeId) (t : TermId)
    (as : List AW) (vs : List V) (a : AW) (s : State) (tr : Array RuleId)
    (r : Option V) (s' : State) (tr' : Array RuleId),
    aOracle t as = some a → Holds2 f (sourceIdentityCtx ctx) as vs → Is s →
      (applyTerm p (Stock.sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
        Is s' ∧ ∀ v, r = some v → γ f (sourceIdentityCtx ctx) a v

private theorem pat_sound {p : Program} (mapped : MappedCtxInv f ctx) (md : Model p f ctx)
    (q : Pattern) (a : AW) (aenv : List AW) (v : V) (env env' : Isle.Interp.Env V)
    (st : State) (matched : matchPat p (Stock.sem ctx) st q v env = .ok (some env'))
    (held : γ f (sourceIdentityCtx ctx) a v) (henv : EnvOK f (sourceIdentityCtx ctx) aenv env) :
    ∃ aenv' ∈ aPat p aext a q aenv, EnvOK f (sourceIdentityCtx ctx) aenv' env' := by
  have view : DFGViewEq ctx (sourceIdentityCtx ctx) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  rw [stock_matchPat_source view] at matched
  exact Cov.aPat_sound mapped.identityView md.source q a aenv v env env' st.base matched held henv

private theorem patArgs_sound {p : Program} (mapped : MappedCtxInv f ctx) (md : Model p f ctx)
    (qs : List Pattern) (as : List AW) (aenv : List AW) (vs : List V)
    (env env' : Isle.Interp.Env V) (st : State)
    (matched : matchArgs p (Stock.sem ctx) st qs vs env = .ok (some env'))
    (held : HoldsP f (sourceIdentityCtx ctx) as vs) (henv : EnvOK f (sourceIdentityCtx ctx) aenv env) :
    ∃ aenv' ∈ aPatArgs p aext as qs aenv, EnvOK f (sourceIdentityCtx ctx) aenv' env' := by
  have view : DFGViewEq ctx (sourceIdentityCtx ctx) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  rw [stock_matchArgs_source view] at matched
  exact Cov.aPatArgs_sound mapped.identityView md.source qs as aenv vs env env' st.base
    matched held henv

section Sound
variable {p : Program} (mapped : MappedCtxInv f ctx) (md : Model p f ctx) (cfg : Config)
  (tab : Tab)

/-- The soundness statements at fuel `n`. -/
structure SoundAt (n : Nat) : Prop where
  expr : ∀ e aenv a env s tr r s' tr', aExpr p tab actor noOpportunityPre aOracle e aenv = some a →
    EnvOK f (sourceIdentityCtx ctx) aenv env → md.Is s →
    (evalExpr p (Stock.sem ctx) cfg n e env).run (s, tr) = .ok (r, (s', tr')) →
    md.Is s' ∧ ∀ v, r = some v → γ f (sourceIdentityCtx ctx) a v
  args : ∀ es aenv as env s tr r s' tr', aArgs p tab actor noOpportunityPre aOracle es aenv = some as →
    EnvOK f (sourceIdentityCtx ctx) aenv env → md.Is s →
    (evalArgs p (Stock.sem ctx) cfg n es env).run (s, tr) = .ok (r, (s', tr')) →
    md.Is s' ∧ ∀ vs, r = some vs → Holds2 f (sourceIdentityCtx ctx) as vs
  binds : ∀ bs aenv aenv' env s tr r s' tr', aBinds p tab actor noOpportunityPre aOracle bs aenv = some aenv' →
    EnvOK f (sourceIdentityCtx ctx) aenv env → md.Is s →
    (evalBinds p (Stock.sem ctx) cfg n bs env).run (s, tr) = .ok (r, (s', tr')) →
    md.Is s' ∧ ∀ env', r = some env' → EnvOK f (sourceIdentityCtx ctx) aenv' env'
  apply : ∀ ty t as a vs s tr r s' tr', aApply p tab actor noOpportunityPre aOracle ty t as = some a →
    Holds2 f (sourceIdentityCtx ctx) as vs → md.Is s →
    (applyTerm p (Stock.sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    md.Is s' ∧ ∀ v, r = some v → γ f (sourceIdentityCtx ctx) a v
  root : ∀ ty t term flags ex ins out vs s tr r s' tr', termOf p t = .ok term →
    term.kind = .decl flags (some .internal) ex →
    (∀ rl ∈ p.rulesOf t, aRule p tab aext actor noOpportunityPre aOracle ins out rl = true ∨
      ∀ m s0 env s1, (matchRule p (Stock.sem ctx) cfg m rl vs).run s0 ≠ .ok (some env, s1)) →
    Holds2 f (sourceIdentityCtx ctx) ins vs → md.Is s →
    (applyTerm p (Stock.sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    md.Is s' ∧ ∀ v, r = some v → γ f (sourceIdentityCtx ctx) out v
  mrule : ∀ rl ins envs vs s tr env s' tr', aRuleEnvs p tab aext actor noOpportunityPre aOracle ins rl = some envs →
    Holds2 f (sourceIdentityCtx ctx) ins vs → md.Is s →
    (matchRule p (Stock.sem ctx) cfg n rl vs).run (s, tr) = .ok (some env, (s', tr')) →
    md.Is s' ∧ ∃ aenv ∈ envs, EnvOK f (sourceIdentityCtx ctx) aenv env
  iflets : ∀ ils aenv envs env s tr env' s' tr', aIfLets p tab aext actor noOpportunityPre aOracle ils aenv = some envs →
    EnvOK f (sourceIdentityCtx ctx) aenv env → md.Is s →
    (matchIfLets p (Stock.sem ctx) cfg n ils env).run (s, tr) = .ok (some env', (s', tr')) →
    md.Is s' ∧ ∃ aenv' ∈ envs, EnvOK f (sourceIdentityCtx ctx) aenv' env'


include mapped in
theorem soundAt (hc : cfg.checkOverlap = false) (htab : chkTab p tab aext actor noOpportunityPre aOracle = true) :
    ∀ n, SoundAt md cfg tab n := by
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
  have hroot : ∀ ty t term flags ex ins out vs s tr r s' tr', termOf p t = .ok term →
      term.kind = .decl flags (some .internal) ex →
      (∀ rl ∈ p.rulesOf t, aRule p tab aext actor noOpportunityPre aOracle ins out rl = true ∨
        ∀ m s0 env s1, (matchRule p (Stock.sem ctx) cfg m rl vs).run s0 ≠ .ok (some env, s1)) →
      Holds2 f (sourceIdentityCtx ctx) ins vs → md.Is s →
      (applyTerm p (Stock.sem ctx) cfg (n + 1) ty t vs).run (s, tr) = .ok (r, (s', tr')) →
      md.Is s' ∧ ∀ v, r = some v → γ f (sourceIdentityCtx ctx) out v := by
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
      obtain ⟨hrl, m, hmn, hmatch⟩ := Backend.Proof.Flow.selectRule_some_lt hc h1
      have hok : aRule p tab aext actor noOpportunityPre aOracle ins out rl = true := by
        rcases hrules rl hrl with h | h
        · exact h
        · exact absurd hmatch (h m _ _ _)
      obtain ⟨envs, hae, hall⟩ := aRule_inv hok
      obtain ⟨hIs1, aenv, haenv, he1⟩ := (ih m (by omega)).mrule _ _ _ _ _ _ _ _ _ hae hins hIs hmatch
      obtain ⟨a, ha, hle⟩ := hall aenv haenv
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
        exact ⟨hIs2, fun w hw => by cases hw; exact le_sound a out hle v (hv2 v rfl)⟩
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
      cases pure_ok h; exact ⟨hIs, fun v hv => by cases hv; rfl⟩
    | constInt ty i =>
      rw [evalExpr.eq_4] at h; rw [aExpr.eq_3] at ha; cases ha
      cases pure_ok h
      exact ⟨hIs, fun v hv => by cases hv; exact aint_sound ty i⟩
    | constPrim ty nm =>
      rw [evalExpr.eq_5] at h; rw [aExpr.eq_4] at ha; cases ha
      split at h
      · rename_i c hcp
        cases pure_ok h
        refine ⟨hIs, fun v hv => ?_⟩
        cases hv
        change (Backend.sem (sourceIdentityCtx ctx)).prim ty nm = some c at hcp
        rw [prim_sem_ex] at hcp
        unfold aprim
        rw [hcp]
        unfold primTy at hcp
        split at hcp
        · simp only [Option.map_eq_some_iff] at hcp
          obtain ⟨t, -, rfl⟩ := hcp
          exact ⟨t, List.mem_singleton_self _, rfl⟩
        · cases hcp
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
      cases o with
      | none => cases pure_ok h2; exact ⟨hIs1, fun vs hv => by cases hv⟩
      | some v =>
        obtain ⟨o2, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
        obtain ⟨hIs2, hv2⟩ := ihn.args _ _ _ _ _ _ _ _ _ haes he hIs1 h3
        cases o2 with
        | none => cases pure_ok h4; exact ⟨hIs2, fun vs hv => by cases hv⟩
        | some vs =>
          cases pure_ok h4
          exact ⟨hIs2, fun ws hw => by cases hw; exact ⟨hv1 v rfl, hv2 vs rfl⟩⟩
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
      cases o with
      | none => cases pure_ok h2; exact ⟨hIs1, fun e he' => by cases he'⟩
      | some v =>
        simp only at h2
        split at h2
        · exact ihn.binds _ _ _ _ _ _ _ _ _ hbs (envOK_set he (hv1 v rfl) x) hIs1 h2
        · exact (throw_ok h2).elim
  · -- applyTerm
    intro ty t as a vs s tr r s' tr' ha hvs hIs h
    unfold aApply at ha
    split at ha
    · rename_i hb
      exact (holds2_bot hb hvs).elim
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
        exact ⟨hIs, fun v hv => by cases hv; exact γ_mkData hvs⟩
      | struct =>
        rw [hk] at ha; cases ha
        rw [applyTerm.eq_2] at h
        obtain ⟨term', s1, h1, h2⟩ := bind_ok h
        obtain ⟨_, ht', he⟩ := liftM_ok h1
        rw [ht] at ht'; cases ht'; cases he
        rw [hk] at h2
        cases pure_ok h2
        exact ⟨hIs, fun v hv => by cases hv; exact γ_mkData hvs⟩
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
            split at ha
            · rename_i a' hor
              cases ha
              exact md.oracle cfg hc (n + 1) ty t as vs _ s tr r s' tr' hor hvs hIs h
            · obtain ⟨ins, hm, hle⟩ := tabGet_le ha
              exact hroot ty t term flags ex ins a vs s tr r s' tr' ht hk
                (fun rl hrl => .inl (chkTab_mem htab hm rl hrl)) (holds2_le hle hvs) hIs h
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
                · rename_i v st' hcv
                  obtain ⟨u, s3, h5, h6⟩ := bind_ok h4
                  cases set_ok h5
                  cases pure_ok h6
                  obtain ⟨hv, hIs'⟩ := md.ctor t _ ht _ _ _ _ _ hvs hIs hpre hcv
                  exact ⟨hIs', fun w hw => by cases hw; exact hv⟩
                · split at h4
                  · cases pure_ok h4; exact ⟨hIs, fun w hw => by cases hw⟩
                  · exact (throw_ok h4).elim
                · exact (throw_ok h4).elim
            · cases ha
  · -- matchRule
    intro rl ins envs vs s tr env s' tr' hae hins hIs h
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
      obtain ⟨aenv0, hm0, he0⟩ := patArgs_sound mapped md _ _ _ _ _ _ _ hma (holdsP_of_holds2 hins)
        (envOK_empty (List.replicate rl.vars.length .top) _)
      unfold aRuleEnvs at hae
      cases hif : aIfLets p tab aext actor noOpportunityPre aOracle rl.iflets aenv0 with
      | none =>
        cases hm : (aPatArgs p aext ins rl.args (List.replicate rl.vars.length .top)).mapM
            (fun e => aIfLets p tab aext actor noOpportunityPre aOracle rl.iflets e) with
        | none => rw [hm] at hae; cases hae
        | some yss =>
          obtain ⟨y, -, hy⟩ := mapM_some_mem hm aenv0 hm0
          rw [hif] at hy; cases hy
      | some envs0 =>
        obtain ⟨hIs2, aenv1, hm1, he1⟩ := ihn.iflets _ _ _ _ _ _ _ _ _ hif he0 hIs h4
        exact ⟨hIs2, aenv1, flat_mapM_mem hae hm0 hif hm1, he1⟩
  · -- matchIfLets
    intro ils aenv envs env s tr env' s' tr' ha he hIs h
    cases ils with
    | nil =>
      rw [matchIfLets.eq_2] at h; rw [aIfLets.eq_1] at ha; cases ha
      cases pure_ok h; exact ⟨hIs, aenv, List.mem_singleton_self _, he⟩
    | cons il ils =>
      rw [matchIfLets.eq_3] at h
      obtain ⟨a, hae, hails⟩ := aIfLets_cons ha
      obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
      obtain ⟨hIs1, hv1⟩ := ihn.expr _ _ _ _ _ _ _ _ _ hae he hIs h1
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
          obtain ⟨aenv1, hm1, he1⟩ := pat_sound mapped md _ _ _ _ _ _ _ hmp (hv1 v rfl) he
          cases hif : aIfLets p tab aext actor noOpportunityPre aOracle ils aenv1 with
          | none =>
            cases hm : (aPat p aext a il.lhs aenv).mapM
                (fun e => aIfLets p tab aext actor noOpportunityPre aOracle ils e) with
            | none => rw [hm] at hails; cases hails
            | some yss =>
              obtain ⟨y, -, hy⟩ := mapM_some_mem hm aenv1 hm1
              rw [hif] at hy; cases hy
          | some envs1 =>
            obtain ⟨hIs2, aenv2, hm2, he2⟩ := ihn.iflets _ _ _ _ _ _ _ _ _ hif he1 hIs1 h6
            exact ⟨hIs2, aenv2, flat_mapM_mem hails hm1 hif hm2, he2⟩

end Sound
end Backend.Stock.Proof.Coverage
