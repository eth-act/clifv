import FV.Backend.Proof.IselCovSound
import FV.Backend.Proof.IselCovCheckT
import FV.Backend.Proof.IselCovLeT

/-!
# Form coverage over float-capable contexts: soundness of the abstract interpreter

The typed counterpart of `IselCovSound`: for a context with `CtxInvT` whose instructions the
scope `S` describes with the opcode split `iOps`/`fOps` (`InstSplit`; the exclusion checker's
pruning is `failsTG_sound`), `soundAtT` states that the abstract evaluation of patterns,
expressions, rules and table terms describes every run. The facts about the extern helpers and
the oracle are the fields of `CovModelT` (built in `IselCovExtT`).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64



/-!
# Form coverage of the ISLE lowering (V3): soundness of the abstract interpreter

For the driver's semantics `sem ctx` and a context with `CtxInv` (the exclusion checker's
pruning is `fails_sound`): `soundAtT` (by induction on the fuel) states that the abstract
evaluation of patterns, expressions, rules and table terms describes every run. The facts
about the extern helpers and the oracle are the fields of `CovModelT` (`IselCovExt`).
-/

variable {S : Clif.Inst → Bool} {iOps fOps : List Nat} {f : Clif.Function} {ctx : Ctx}

/-! ## Positional descriptions -/

theorem deepOk_fieldsT {d : Nat × Bool} {t k : Nat} {vs : List V} (h : DeepOk d (.data t k vs)) :
    ∀ w ∈ vs, γT S iOps fOps f ctx (.flat d.1 d.2) w := by
  intro w hw
  refine ⟨fun r hr => h.1 r ?_, fun hc => ?_⟩
  · rw [regsIn_data]; exact regsIn_sub_of_mem hw r hr
  · have := h.2 hc
    rw [covV_data] at this
    simp only [Bool.and_eq_true] at this
    exact covV_of_mem this.2 hw

theorem filter_data_memT {as bs : List AW} {k : Nat}
    (h : as.filter (fun b => match b with | .data _ k' _ => k == k' | _ => false) = bs) {x : AW}
    (hx : x ∈ as) {t : Nat} {fs : List AW} (hxd : x = .data t k fs) : x ∈ bs := by
  subst h hxd; simp [List.mem_filter, hx]

theorem deepAny_memT {as : List AW} {x : AW} (hx : x ∈ as) {v : V} (h : γT S iOps fOps f ctx x v) :
    DeepOk (AW.deepL as) v :=
  deepAny_soundT as v (γAnyT_iff.mpr ⟨x, hx, h⟩)

/-- **Fields of an enum value** (`aun`). -/
theorem aun_soundT {a : AW} {t k : Nat} {vs : List V} (h : γT S iOps fOps f ctx a (.data t k vs)) (n : Nat) :
    ∃ as, aun a k n = some as ∧ HoldsPT S iOps fOps f ctx as vs := by
  cases a with
  | data t' k' fs =>
    obtain ⟨vs', he, hl⟩ := h
    cases he
    exact ⟨fs, by simp [aun], holdsPT_of_holds2T hl⟩
  | alts as =>
    simp only [aun]
    split
    · rename_i hall
      obtain ⟨x, hx, hxv⟩ := γAnyT_iff.mp h
      have hxd := List.all_eq_true.mp hall x hx
      cases x with
      | data t' k' fs =>
        obtain ⟨vs', he, hl⟩ := hxv
        cases he
        generalize hbs : as.filter (fun b => match b with | .data _ k' _ => k == k' | _ => false) = bs
        have hmem := filter_data_memT hbs hx rfl
        match bs, hmem with
        | [.data _ _ gs], hm =>
          simp only [List.mem_singleton, AW.data.injEq] at hm
          obtain ⟨-, -, rfl⟩ := hm
          exact ⟨fs, rfl, holdsPT_of_holds2T hl⟩
        | [], hm => cases hm
        | b :: c :: bs', hm =>
          refine ⟨List.replicate n (.flat (AW.deepL (b :: c :: bs')).1 (AW.deepL (b :: c :: bs')).2),
            by cases b <;> rfl, holdsPT_replicate (fun w hw => ?_) n⟩
          exact deepOk_fieldsT (deepAny_memT hm ⟨vs, rfl, hl⟩) w hw
        | [.bot], hm => simp at hm
        | [.flat _ _], hm => simp at hm
        | [.reg _], hm => simp at hm
        | [.ty _], hm => simp at hm
        | [.bool _], hm => simp at hm
        | [.logic _], hm => simp at hm
        | [.scale _], hm => simp at hm
        | [.simm9], hm => simp at hm
        | [.xv _], hm => simp at hm
        | [.num _ _], hm => simp at hm
        | [.alts _], hm => simp at hm
      | _ => simp at hxd
    · exact ⟨_, rfl, holdsPT_replicate (fun w hw => deepOk_fieldsT (deepAny_soundT as _ h) w hw) n⟩
  | flat m c => exact ⟨_, rfl, holdsPT_replicate (fun w hw => deepOk_fieldsT (d := (m, c)) h w hw) n⟩
  | xv e =>
    cases e with
    | data =>
      refine ⟨_, rfl, holdsPT_replicate (fun w hw => ?_) n⟩
      exact deepOk_fieldsT (d := (0, true)) ⟨fun r hr => (by rw [h.2.1] at hr; cases hr),
        fun _ => h.2.2⟩ w hw
    | inst => obtain ⟨⟨_, _, _, he, _⟩, -⟩ := h; cases he
    | value => obtain ⟨⟨_, he⟩, -⟩ := h; cases he
  | bot => exact h.elim
  | reg m => obtain ⟨_, he, _⟩ := h; cases he
  | ty ts => obtain ⟨_, _, he⟩ := h; cases he
  | bool b => cases h
  | logic sz => obtain ⟨_, he, _⟩ := h; cases he
  | scale b => obtain ⟨_, he, _⟩ := h; cases he
  | simm9 => obtain ⟨_, he, _⟩ := h; cases he
  | num k b => rcases numOk_shape h with ⟨_, he⟩ | ⟨_, he⟩ <;> cases he

/-- **Fields of a struct value** (`aunS`). -/
theorem aunS_soundT {a : AW} {t k : Nat} {vs : List V} (h : γT S iOps fOps f ctx a (.data t k vs)) (n : Nat) :
    ∃ as, aunS a n = some as ∧ HoldsPT S iOps fOps f ctx as vs := by
  cases a with
  | data t' k' fs =>
    obtain ⟨vs', he, hl⟩ := h
    cases he
    exact ⟨fs, rfl, holdsPT_of_holds2T hl⟩
  | alts as =>
    exact ⟨_, rfl, holdsPT_replicate (fun w hw => deepOk_fieldsT (deepAny_soundT as _ h) w hw) n⟩
  | flat m c => exact ⟨_, rfl, holdsPT_replicate (fun w hw => deepOk_fieldsT (d := (m, c)) h w hw) n⟩
  | xv e =>
    cases e with
    | data =>
      refine ⟨_, rfl, holdsPT_replicate (fun w hw => ?_) n⟩
      exact deepOk_fieldsT (d := (0, true)) ⟨fun r hr => (by rw [h.2.1] at hr; cases hr),
        fun _ => h.2.2⟩ w hw
    | inst => obtain ⟨⟨_, _, _, he, _⟩, -⟩ := h; cases he
    | value => obtain ⟨⟨_, he⟩, -⟩ := h; cases he
  | bot => exact h.elim
  | reg m => obtain ⟨_, he, _⟩ := h; cases he
  | ty ts => obtain ⟨_, _, he⟩ := h; cases he
  | bool b => cases h
  | logic sz => obtain ⟨_, he, _⟩ := h; cases he
  | scale b => obtain ⟨_, he, _⟩ := h; cases he
  | simm9 => obtain ⟨_, he, _⟩ := h; cases he
  | num k b => rcases numOk_shape h with ⟨_, he⟩ | ⟨_, he⟩ <;> cases he

/-! ## Integer constants -/

/-- A constant's value is described by `aint`. -/
theorem aint_soundT (ty : TypeId) (i : Int) : γT S iOps fOps f ctx (aint i) ((sem ctx).int ty i) := by
  unfold aint
  split
  · rename_i h
    show NumOk .int _ (.int (normInt ty i))
    rw [normInt_small ty h.1 h.2]
    exact ⟨i, rfl, h.1, by omega⟩
  · exact ⟨fun r hr => by simp [sem, V.regsIn] at hr, fun _ => rfl⟩

/-! ## The model

The transfer functions of the extern helpers and the oracles (`aext`, `actor`, `apre`,
`aOracle`) are parameters: V3's (`IselCovFns`), V4's control-shape analysis (`IselShpFns`), V6c's
emission analysis (`IselEmitFns`). -/

section Params
variable (aext : TermId → AW → List AW) (actor : TermId → List AW → AW)
  (apre : TermId → List AW → Bool) (aOracle : TermId → List AW → Option AW)

/-- The facts about the extern helpers the soundness proof needs, and a state invariant. -/
structure CovModelT (S : Clif.Inst → Bool) (iOps fOps : List Nat) (p : Program)
    (f : Clif.Function) (ctx : Ctx) where
  Is : LState → Prop
  ext : ∀ (a : AW) (term : Term) (v : V) (st : LState) (fs : List V), γT S iOps fOps f ctx a v →
    (sem ctx).extract term v st = .ok fs → HoldsPT S iOps fOps f ctx (aext term.id a) fs
  ctor : ∀ (as : List AW) (vs : List V) (term : Term) (v : V) (st st' : LState),
    Holds2T S iOps fOps f ctx as vs → Is st → apre term.id as = true →
    (sem ctx).ctor term vs st = .ok (v, st') → γT S iOps fOps f ctx (actor term.id as) v ∧ Is st'
  oracle : ∀ (cfg : Config), cfg.checkOverlap = false → ∀ (n : Nat) (ty : TypeId) (t : TermId)
    (as : List AW) (vs : List V) (a : AW) (s : LState) (tr : Array RuleId) (r : Option V) (s' : LState)
    (tr' : Array RuleId), aOracle t as = some a → Holds2T S iOps fOps f ctx as vs → Is s →
    (applyTerm p (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    Is s' ∧ ∀ v, r = some v → γT S iOps fOps f ctx a v

variable {aext actor apre aOracle}

/-! ## Patterns -/

section Pat
variable {p : Program} (hctx : CtxInvT f ctx) (hsp : InstSplit S f ctx iOps fOps)
  (md : CovModelT aext actor apre aOracle S iOps fOps p f ctx)

theorem primOk_soundT {a : AW} {ty : TypeId} {n : String} {c : V} (hpo : primOk a ty n = false)
    (hc : primTy ty n = some c) (hv : γT S iOps fOps f ctx a c) : False := by
  unfold primOk at hpo
  rw [hc] at hpo
  cases c with
  | ty t =>
    cases a with
    | ty ts =>
      obtain ⟨t', ht', he⟩ := hv
      cases he
      simp only [List.any_eq_false, decide_eq_true_eq] at hpo
      exact hpo _ ht' rfl
    | _ => simp at hpo
  | _ => simp at hpo

set_option linter.unusedSectionVars false in
include hctx hsp md in
mutual
/-- **Pattern soundness**: matching `q` against a value `a` describes gives an environment one
of `aPatT`'s environments describes. -/
theorem aPat_soundT : ∀ (q : Pattern) (a : AW) (aenv : List AW) (v : V) (env env' : Isle.Interp.Env V)
    (st : LState), matchPat p (sem ctx) st q v env = .ok (some env') → γT S iOps fOps f ctx a v →
    EnvOKT S iOps fOps f ctx aenv env → ∃ aenv' ∈ aPatT p aext iOps fOps a q aenv, EnvOKT S iOps fOps f ctx aenv' env'
  | q, a, aenv, v, env, env', st, h, hv, he => by
    unfold aPatT
    split
    · rename_i hpr
      simp only [aPruneT, Bool.or_eq_true] at hpr
      rcases hpr with hb | hpr
      · exact (isBot_soundT hb hv).elim
      · split at hpr
        · rename_i e
          exact (failsTG_sound hctx hsp q (e.toAVT iOps fOps) v st env env' hpr hv.1 h).elim
        · cases hpr
    · cases q with
      | bind ty x sub =>
        rw [matchPat.eq_1] at h
        split at h
        · obtain ⟨b, hb, hbv⟩ := split_soundT hv
          obtain ⟨aenv', hm, he'⟩ := aPat_soundT sub b _ v _ env' st h hbv (envOKT_set he hbv x)
          exact ⟨aenv', List.mem_flatMap.mpr ⟨b, hb, hm⟩, he'⟩
        · cases h
      | var ty x =>
        rw [matchPat.eq_2] at h
        split at h
        · simp only [pure, Except.pure, Except.ok.injEq] at h
          split at h
          · cases h; exact ⟨aenv, List.mem_singleton_self _, he⟩
          · cases h
        · cases h
      | constBool ty b =>
        rw [matchPat.eq_3] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        split at h
        · rename_i heq
          cases h
          have hvb : v = .bool b := eq_sem_iff.mp heq
          subst hvb
          refine ⟨aenv, ?_, he⟩
          simp only
          split
          · exact List.mem_singleton_self _
          · rename_i hbo
            cases a with
            | bool b' =>
              have : V.bool b = .bool b' := hv
              cases this
              simp [boolOk] at hbo
            | _ => simp [boolOk] at hbo
        · cases h
      | constInt ty i =>
        rw [matchPat.eq_4] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        split at h
        · cases h; exact ⟨aenv, List.mem_singleton_self _, he⟩
        · cases h
      | constPrim ty n =>
        rw [matchPat.eq_5] at h
        split at h
        · rename_i c hc
          simp only [pure, Except.pure, Except.ok.injEq] at h
          split at h
          · rename_i heq
            cases h
            have hvc : v = c := eq_sem_iff.mp heq
            subst hvc
            refine ⟨aenv, ?_, he⟩
            simp only
            split
            · exact List.mem_singleton_self _
            · rename_i hpo
              rw [prim_sem_ex] at hc
              exact (primOk_soundT (Bool.eq_false_iff.mpr hpo) hc hv).elim
          · cases h
        · cases h
      | wildcard ty =>
        rw [matchPat.eq_6] at h
        cases h; exact ⟨aenv, List.mem_singleton_self _, he⟩
      | and ty ps =>
        rw [matchPat.eq_7] at h
        exact aPatAll_soundT ps a aenv v env env' st h hv he
      | term ty t args =>
        rw [matchPat.eq_8] at h
        cases ht : termOf p t with
        | error e => rw [ht] at h; cases h
        | ok term =>
          rw [ht] at h
          simp only [bind, Except.bind] at h ⊢
          simp only [ht]
          cases hk : term.kind with
          | enumVariant k =>
            rw [hk] at h
            simp only at h ⊢
            split at h
            · rename_i k' fs hu
              split at h
              · rename_i hkk
                have hvd := unData_eq hu
                subst hvd
                simp only [beq_iff_eq] at hkk
                subst hkk
                obtain ⟨as, has, hl⟩ := aun_soundT hv args.length
                rw [has]
                exact aPatArgs_soundT args as aenv fs env env' st h hl he
              · cases h
            · cases h
          | struct =>
            rw [hk] at h
            simp only at h ⊢
            split at h
            · rename_i k' fs hu
              have hvd := unData_eq hu
              subst hvd
              obtain ⟨as, has, hl⟩ := aunS_soundT hv args.length
              rw [has]
              exact aPatArgs_soundT args as aenv fs env env' st h hl he
            · cases h
          | decl flags ctor ex =>
            rw [hk] at h
            cases ex with
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
                    exact aPatArgs_soundT args _ aenv fs env env' st h (md.ext _ _ _ _ _ hv hx) he
                  · split at h
                    · cases h
                    · cases h
                  · cases h
/-- `aPatAllT`: every pattern against the same value. -/
theorem aPatAll_soundT : ∀ (qs : List Pattern) (a : AW) (aenv : List AW) (v : V)
    (env env' : Isle.Interp.Env V) (st : LState),
    matchAll p (sem ctx) st qs v env = .ok (some env') → γT S iOps fOps f ctx a v → EnvOKT S iOps fOps f ctx aenv env →
    ∃ aenv' ∈ aPatAllT p aext iOps fOps a qs aenv, EnvOKT S iOps fOps f ctx aenv' env'
  | [], a, aenv, v, env, env', st, h, hv, he => by
    rw [matchAll.eq_1] at h
    cases h
    exact ⟨aenv, by simp [aPatAllT], he⟩
  | q :: qs, a, aenv, v, env, env', st, h, hv, he => by
    rw [matchAll.eq_2] at h
    cases hq : matchPat p (sem ctx) st q v env with
    | error e => rw [hq] at h; cases h
    | ok o =>
      rw [hq] at h
      cases o with
      | none => cases h
      | some e1 =>
        obtain ⟨a1, h1, he1⟩ := aPat_soundT q a aenv v env e1 st hq hv he
        obtain ⟨a2, h2, he2⟩ := aPatAll_soundT qs a a1 v e1 env' st h hv he1
        exact ⟨a2, by rw [aPatAllT]; exact List.mem_flatMap.mpr ⟨a1, h1, h2⟩, he2⟩
/-- `aPatArgsT`: patterns against values position by position. -/
theorem aPatArgs_soundT : ∀ (qs : List Pattern) (as : List AW) (aenv : List AW) (vs : List V)
    (env env' : Isle.Interp.Env V) (st : LState),
    matchArgs p (sem ctx) st qs vs env = .ok (some env') → HoldsPT S iOps fOps f ctx as vs →
    EnvOKT S iOps fOps f ctx aenv env → ∃ aenv' ∈ aPatArgsT p aext iOps fOps as qs aenv, EnvOKT S iOps fOps f ctx aenv' env'
  | [], as, aenv, [], env, env', st, h, hv, he => by
    rw [matchArgs.eq_1] at h
    cases h
    exact ⟨aenv, by cases as <;> simp [aPatArgsT], he⟩
  | q :: qs, a :: as, aenv, v :: vs, env, env', st, h, hv, he => by
    rw [matchArgs.eq_2] at h
    cases hq : matchPat p (sem ctx) st q v env with
    | error e => rw [hq] at h; cases h
    | ok o =>
      rw [hq] at h
      cases o with
      | none => cases h
      | some e1 =>
        have hh := holdsPT_cons hv
        obtain ⟨a1, h1, he1⟩ := aPat_soundT q a aenv v env e1 st hq hh.1 he
        obtain ⟨a2, h2, he2⟩ := aPatArgs_soundT qs as a1 vs e1 env' st h hh.2 he1
        exact ⟨a2, by rw [aPatArgsT]; exact List.mem_flatMap.mpr ⟨a1, h1, h2⟩, he2⟩
  | q :: qs, [], aenv, v :: vs, env, env', st, h, hv, he => by
    rw [matchArgs.eq_2] at h
    cases hq : matchPat p (sem ctx) st q v env with
    | error e => rw [hq] at h; cases h
    | ok o =>
      rw [hq] at h
      cases o with
      | none => cases h
      | some e1 =>
        obtain ⟨a1, h1, he1⟩ := aPat_soundT q .top aenv v env e1 st hq (by simpa using hv 0 v rfl) he
        obtain ⟨a2, h2, he2⟩ := aPatArgs_soundT qs [] a1 vs e1 env' st h (holdsPT_nil_cons hv) he1
        exact ⟨a2, by rw [aPatArgsT]; exact List.mem_flatMap.mpr ⟨a1, h1, h2⟩, he2⟩
  | [], _, aenv, _ :: _, env, env', st, h, hv, he => by
    rw [matchArgs.eq_3] at h
    all_goals first | cases h | (intros; simp_all)
  | _ :: _, _, aenv, [], env, env', st, h, hv, he => by
    rw [matchArgs.eq_3] at h
    all_goals first | cases h | (intros; simp_all)
end

end Pat

/-! ## Inversion of the abstract evaluation -/

section Inv
variable {p : Program} {tab : Tab}

theorem aIfLets_consT {il : IfLet} {ils : List IfLet} {aenv : List AW} {envs : List (List AW)}
    (h : aIfLetsT p tab aext actor apre aOracle iOps fOps (il :: ils) aenv = some envs) :
    ∃ a, aExpr p tab actor apre aOracle il.rhs aenv = some a ∧
      ((aPatT p aext iOps fOps a il.lhs aenv).mapM fun e => aIfLetsT p tab aext actor apre aOracle iOps fOps ils e).map
        List.flatten = some envs := by
  rw [aIfLetsT.eq_2] at h
  split at h
  · exact ⟨_, ‹_›, h⟩
  · cases h

theorem aRule_invT {ins : List AW} {out : AW} {r : Rule}
    (h : aRuleT p tab aext actor apre aOracle iOps fOps ins out r = true) :
    ∃ envs, aRuleEnvsT p tab aext actor apre aOracle iOps fOps ins r = some envs ∧ ∀ env ∈ envs,
      ∃ a, aExpr p tab actor apre aOracle r.rhs env = some a ∧ AW.le a out = true := by
  unfold aRuleT at h
  split at h
  · rename_i envs he
    refine ⟨envs, he, fun env hm => ?_⟩
    have := List.all_eq_true.mp h env hm
    split at this
    · exact ⟨_, ‹_›, this⟩
    · cases this
  · cases h

theorem chkTab_memT (hc : chkTabT p tab aext actor apre aOracle iOps fOps = true) {t : TermId} {ins : List AW}
    {out : AW} (hm : (t, ins, out) ∈ tab) :
    ∀ r ∈ p.rulesOf t, aRuleT p tab aext actor apre aOracle iOps fOps ins out r = true := by
  have := List.all_eq_true.mp hc _ hm
  exact List.all_eq_true.mp this

end Inv

theorem holds2_leT {as bs : List AW} {vs : List V} (h : AW.leAll as bs = true)
    (hv : Holds2T S iOps fOps f ctx as vs) : Holds2T S iOps fOps f ctx bs vs :=
  leL_soundT as bs h vs hv

/-! ## Soundness of the abstract interpretation -/

section Sound
variable {p : Program} (hctx : CtxInvT f ctx) (hsp : InstSplit S f ctx iOps fOps)
  (md : CovModelT aext actor apre aOracle S iOps fOps p f ctx) (cfg : Config) (tab : Tab)

/-- The soundness statements at fuel `n`. -/
structure SoundAtT (n : Nat) : Prop where
  expr : ∀ e aenv a env s tr r s' tr', aExpr p tab actor apre aOracle e aenv = some a →
    EnvOKT S iOps fOps f ctx aenv env → md.Is s →
    (evalExpr p (sem ctx) cfg n e env).run (s, tr) = .ok (r, (s', tr')) →
    md.Is s' ∧ ∀ v, r = some v → γT S iOps fOps f ctx a v
  args : ∀ es aenv as env s tr r s' tr', aArgs p tab actor apre aOracle es aenv = some as →
    EnvOKT S iOps fOps f ctx aenv env → md.Is s →
    (evalArgs p (sem ctx) cfg n es env).run (s, tr) = .ok (r, (s', tr')) →
    md.Is s' ∧ ∀ vs, r = some vs → Holds2T S iOps fOps f ctx as vs
  binds : ∀ bs aenv aenv' env s tr r s' tr', aBinds p tab actor apre aOracle bs aenv = some aenv' →
    EnvOKT S iOps fOps f ctx aenv env → md.Is s →
    (evalBinds p (sem ctx) cfg n bs env).run (s, tr) = .ok (r, (s', tr')) →
    md.Is s' ∧ ∀ env', r = some env' → EnvOKT S iOps fOps f ctx aenv' env'
  apply : ∀ ty t as a vs s tr r s' tr', aApply p tab actor apre aOracle ty t as = some a →
    Holds2T S iOps fOps f ctx as vs → md.Is s →
    (applyTerm p (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    md.Is s' ∧ ∀ v, r = some v → γT S iOps fOps f ctx a v
  root : ∀ ty t term flags ex ins out vs s tr r s' tr', termOf p t = .ok term →
    term.kind = .decl flags (some .internal) ex →
    (∀ rl ∈ p.rulesOf t, aRuleT p tab aext actor apre aOracle iOps fOps ins out rl = true ∨
      ∀ m s0 env s1, (matchRule p (sem ctx) cfg m rl vs).run s0 ≠ .ok (some env, s1)) →
    Holds2T S iOps fOps f ctx ins vs → md.Is s →
    (applyTerm p (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    md.Is s' ∧ ∀ v, r = some v → γT S iOps fOps f ctx out v
  mrule : ∀ rl ins envs vs s tr env s' tr', aRuleEnvsT p tab aext actor apre aOracle iOps fOps ins rl = some envs →
    Holds2T S iOps fOps f ctx ins vs → md.Is s →
    (matchRule p (sem ctx) cfg n rl vs).run (s, tr) = .ok (some env, (s', tr')) →
    md.Is s' ∧ ∃ aenv ∈ envs, EnvOKT S iOps fOps f ctx aenv env
  iflets : ∀ ils aenv envs env s tr env' s' tr', aIfLetsT p tab aext actor apre aOracle iOps fOps ils aenv = some envs →
    EnvOKT S iOps fOps f ctx aenv env → md.Is s →
    (matchIfLets p (sem ctx) cfg n ils env).run (s, tr) = .ok (some env', (s', tr')) →
    md.Is s' ∧ ∃ aenv' ∈ envs, EnvOKT S iOps fOps f ctx aenv' env'

theorem γT_mkData {ty : TypeId} {k : Nat} {as : List AW} {vs : List V} (h : Holds2T S iOps fOps f ctx as vs) :
    γT S iOps fOps f ctx (.data ty k as) ((sem ctx).mkData ty k vs) := ⟨vs, rfl, h⟩

theorem holds2_botT {as : List AW} {vs : List V} (hb : as.any AW.isBot = true) (h : Holds2T S iOps fOps f ctx as vs) :
    False := by
  obtain ⟨a, ha, hab⟩ := List.any_eq_true.mp hb
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
  have hl := γLT_length h
  have : i < vs.length := by rw [← hl]; exact (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨v, hv⟩ : ∃ v, vs[i]? = some v := ⟨vs[i], List.getElem?_eq_getElem this⟩
  exact isBot_soundT hab (γLT_get h i a v hi hv)

include hctx hsp in
/-- **Soundness of the abstract interpretation**, at every fuel. -/
theorem soundAtT (hc : cfg.checkOverlap = false) (htab : chkTabT p tab aext actor apre aOracle iOps fOps = true) :
    ∀ n, SoundAtT md cfg tab n := by
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
      (∀ rl ∈ p.rulesOf t, aRuleT p tab aext actor apre aOracle iOps fOps ins out rl = true ∨
        ∀ m s0 env s1, (matchRule p (sem ctx) cfg m rl vs).run s0 ≠ .ok (some env, s1)) →
      Holds2T S iOps fOps f ctx ins vs → md.Is s →
      (applyTerm p (sem ctx) cfg (n + 1) ty t vs).run (s, tr) = .ok (r, (s', tr')) →
      md.Is s' ∧ ∀ v, r = some v → γT S iOps fOps f ctx out v := by
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
      obtain ⟨hrl, m, hmn, hmatch⟩ := selectRule_some_lt hc h1
      have hok : aRuleT p tab aext actor apre aOracle iOps fOps ins out rl = true := by
        rcases hrules rl hrl with h | h
        · exact h
        · exact absurd hmatch (h m _ _ _)
      obtain ⟨envs, hae, hall⟩ := aRule_invT hok
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
        exact ⟨hIs2, fun w hw => by cases hw; exact le_soundT a out hle v (hv2 v rfl)⟩
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
      exact ⟨hIs, fun v hv => by cases hv; exact aint_soundT ty i⟩
    | constPrim ty nm =>
      rw [evalExpr.eq_5] at h; rw [aExpr.eq_4] at ha; cases ha
      split at h
      · rename_i c hcp
        cases pure_ok h
        refine ⟨hIs, fun v hv => ?_⟩
        cases hv
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
        · exact ihn.binds _ _ _ _ _ _ _ _ _ hbs (envOKT_set he (hv1 v rfl) x) hIs1 h2
        · exact (throw_ok h2).elim
  · -- applyTerm
    intro ty t as a vs s tr r s' tr' ha hvs hIs h
    unfold aApply at ha
    split at ha
    · rename_i hb
      exact (holds2_botT hb hvs).elim
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
        exact ⟨hIs, fun v hv => by cases hv; exact γT_mkData hvs⟩
      | struct =>
        rw [hk] at ha; cases ha
        rw [applyTerm.eq_2] at h
        obtain ⟨term', s1, h1, h2⟩ := bind_ok h
        obtain ⟨_, ht', he⟩ := liftM_ok h1
        rw [ht] at ht'; cases ht'; cases he
        rw [hk] at h2
        cases pure_ok h2
        exact ⟨hIs, fun v hv => by cases hv; exact γT_mkData hvs⟩
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
                (fun rl hrl => .inl (chkTab_memT htab hm rl hrl)) (holds2_leT hle hvs) hIs h
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
                  obtain ⟨hv, hIs'⟩ := md.ctor _ _ _ _ _ _ hvs hIs hpre hcv
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
      obtain ⟨aenv0, hm0, he0⟩ := aPatArgs_soundT hctx hsp md _ _ _ _ _ _ _ hma (holdsPT_of_holds2T hins)
        (envOKT_empty (List.replicate rl.vars.length .top) _)
      unfold aRuleEnvsT at hae
      cases hif : aIfLetsT p tab aext actor apre aOracle iOps fOps rl.iflets aenv0 with
      | none =>
        cases hm : (aPatArgsT p aext iOps fOps ins rl.args (List.replicate rl.vars.length .top)).mapM
            (fun e => aIfLetsT p tab aext actor apre aOracle iOps fOps rl.iflets e) with
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
      rw [matchIfLets.eq_2] at h; rw [aIfLetsT.eq_1] at ha; cases ha
      cases pure_ok h; exact ⟨hIs, aenv, List.mem_singleton_self _, he⟩
    | cons il ils =>
      rw [matchIfLets.eq_3] at h
      obtain ⟨a, hae, hails⟩ := aIfLets_consT ha
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
          obtain ⟨aenv1, hm1, he1⟩ := aPat_soundT hctx hsp md _ _ _ _ _ _ _ hmp (hv1 v rfl) he
          cases hif : aIfLetsT p tab aext actor apre aOracle iOps fOps ils aenv1 with
          | none =>
            cases hm : (aPatT p aext iOps fOps a il.lhs aenv).mapM
                (fun e => aIfLetsT p tab aext actor apre aOracle iOps fOps ils e) with
            | none => rw [hm] at hails; cases hails
            | some yss =>
              obtain ⟨y, -, hy⟩ := mapM_some_mem hm aenv1 hm1
              rw [hif] at hy; cases hy
          | some envs1 =>
            obtain ⟨hIs2, aenv2, hm2, he2⟩ := ihn.iflets _ _ _ _ _ _ _ _ _ hif he1 hIs1 h6
            exact ⟨hIs2, aenv2, flat_mapM_mem hails hm1 hif hm2, he2⟩

end Sound

end Params

end Backend.Proof.Cov
