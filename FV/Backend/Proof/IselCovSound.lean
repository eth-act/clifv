import FV.Backend.Proof.IselCovFns

/-!
# Form coverage of the ISLE lowering (V3): soundness of the abstract interpreter

For the driver's semantics `sem ctx` and a context with `CtxInv` (the exclusion checker's
pruning is `fails_sound`): `soundAt` (by induction on the fuel) states that the abstract
evaluation of patterns, expressions, rules and table terms describes every run. The facts
about the extern helpers and the oracle are the fields of `CovModel` (`IselCovExt`).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

variable {f : Clif.Function} {ctx : Ctx}

/-! ## Positional descriptions -/

/-- Abstract values describe values pointwise (same lengths). -/
def Holds2 (f : Clif.Function) (ctx : Ctx) : List AW → List V → Prop := γL f ctx

/-- Abstract values describe values position by position, `top` past the end. -/
def HoldsP (f : Clif.Function) (ctx : Ctx) (as : List AW) (vs : List V) : Prop :=
  ∀ i v, vs[i]? = some v → γ f ctx (as.getD i .top) v

/-- The abstract environment describes the bound variables (`top` past its end). -/
def EnvOK (f : Clif.Function) (ctx : Ctx) (aenv : List AW) (env : Isle.Interp.Env V) : Prop :=
  ∀ x w, env[x]? = some (some w) → γ f ctx (aenv.getD x .top) w

theorem kind_and_15 (r : Reg) : r.kind &&& 15 ≠ 0 := by
  rcases kind_cases r with h | h | h | h <;> rw [h] <;> decide

theorem γ_top (v : V) : γ f ctx AW.top v := ⟨fun r _ => kind_and_15 r, fun h => by cases h⟩

theorem holdsP_of_holds2 : ∀ {as : List AW} {vs : List V}, Holds2 f ctx as vs → HoldsP f ctx as vs
  | [], [], _ => fun _ _ h => by simp at h
  | a :: as, v :: vs, ⟨h1, h2⟩ => by
    intro i w hw
    cases i with
    | zero => simp at hw; subst hw; exact h1
    | succ i => simpa using holdsP_of_holds2 h2 i w (by simpa using hw)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem holdsP_cons {a : AW} {as : List AW} {v : V} {vs : List V} (h : HoldsP f ctx (a :: as) (v :: vs)) :
    γ f ctx a v ∧ HoldsP f ctx as vs :=
  ⟨by simpa using h 0 v rfl, fun i w hw => by simpa using h (i + 1) w (by simpa using hw)⟩

theorem holdsP_nil_cons {v : V} {vs : List V} (h : HoldsP f ctx [] (v :: vs)) :
    HoldsP f ctx [] vs :=
  fun i w hw => by simpa using h (i + 1) w (by simpa using hw)

theorem holdsP_replicate {a : AW} {vs : List V} (h : ∀ v ∈ vs, γ f ctx a v) (n : Nat) :
    HoldsP f ctx (List.replicate n a) vs := by
  intro i v hv
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split
  · exact h v (List.mem_of_getElem? hv)
  · exact γ_top v

theorem envOK_empty (aenv : List AW) (n : Nat) : EnvOK f ctx aenv (Array.replicate n none) := by
  intro x w hx
  simp [Array.getElem?_replicate] at hx

theorem envOK_set {aenv : List AW} {env : Isle.Interp.Env V} (he : EnvOK f ctx aenv env) {a : AW}
    {v : V} (hv : γ f ctx a v) (x : Nat) :
    EnvOK f ctx (aenv.set x a) (env.set! x (some v)) := by
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
      · exact γ_top _
    · cases hy
  · simp only [hyx, ↓reduceIte] at hy
    have := he y w hy
    rwa [List.getD_eq_getElem?_getD, List.getElem?_set_ne hyx, ← List.getD_eq_getElem?_getD]

/-! ## Fields of data -/

theorem deepOk_fields {d : Nat × Bool} {t k : Nat} {vs : List V} (h : DeepOk d (.data t k vs)) :
    ∀ w ∈ vs, γ f ctx (.flat d.1 d.2) w := by
  intro w hw
  refine ⟨fun r hr => h.1 r ?_, fun hc => ?_⟩
  · rw [regsIn_data]; exact regsIn_sub_of_mem hw r hr
  · have := h.2 hc
    rw [covV_data] at this
    simp only [Bool.and_eq_true] at this
    exact covV_of_mem this.2 hw

theorem filter_data_mem {as bs : List AW} {k : Nat}
    (h : as.filter (fun b => match b with | .data _ k' _ => k == k' | _ => false) = bs) {x : AW}
    (hx : x ∈ as) {t : Nat} {fs : List AW} (hxd : x = .data t k fs) : x ∈ bs := by
  subst h hxd; simp [List.mem_filter, hx]

theorem deepAny_mem {as : List AW} {x : AW} (hx : x ∈ as) {v : V} (h : γ f ctx x v) :
    DeepOk (AW.deepL as) v :=
  deepAny_sound as v (γAny_iff.mpr ⟨x, hx, h⟩)

/-- **Fields of an enum value** (`aun`). -/
theorem aun_sound {a : AW} {t k : Nat} {vs : List V} (h : γ f ctx a (.data t k vs)) (n : Nat) :
    ∃ as, aun a k n = some as ∧ HoldsP f ctx as vs := by
  cases a with
  | data t' k' fs =>
    obtain ⟨vs', he, hl⟩ := h
    cases he
    exact ⟨fs, by simp [aun], holdsP_of_holds2 hl⟩
  | alts as =>
    simp only [aun]
    split
    · rename_i hall
      obtain ⟨x, hx, hxv⟩ := γAny_iff.mp h
      have hxd := List.all_eq_true.mp hall x hx
      cases x with
      | data t' k' fs =>
        obtain ⟨vs', he, hl⟩ := hxv
        cases he
        generalize hbs : as.filter (fun b => match b with | .data _ k' _ => k == k' | _ => false) = bs
        have hmem := filter_data_mem hbs hx rfl
        match bs, hmem with
        | [.data _ _ gs], hm =>
          simp only [List.mem_singleton, AW.data.injEq] at hm
          obtain ⟨-, -, rfl⟩ := hm
          exact ⟨fs, rfl, holdsP_of_holds2 hl⟩
        | [], hm => cases hm
        | b :: c :: bs', hm =>
          refine ⟨List.replicate n (.flat (AW.deepL (b :: c :: bs')).1 (AW.deepL (b :: c :: bs')).2),
            by cases b <;> rfl, holdsP_replicate (fun w hw => ?_) n⟩
          exact deepOk_fields (deepAny_mem hm ⟨vs, rfl, hl⟩) w hw
        | [.bot], hm => simp at hm
        | [.flat _ _], hm => simp at hm
        | [.reg _], hm => simp at hm
        | [.ty _], hm => simp at hm
        | [.bool _], hm => simp at hm
        | [.logic _], hm => simp at hm
        | [.scale _], hm => simp at hm
        | [.simm9], hm => simp at hm
        | [.xv _], hm => simp at hm
        | [.alts _], hm => simp at hm
      | _ => simp at hxd
    · exact ⟨_, rfl, holdsP_replicate (fun w hw => deepOk_fields (deepAny_sound as _ h) w hw) n⟩
  | flat m c => exact ⟨_, rfl, holdsP_replicate (fun w hw => deepOk_fields (d := (m, c)) h w hw) n⟩
  | xv e =>
    cases e with
    | data =>
      refine ⟨_, rfl, holdsP_replicate (fun w hw => ?_) n⟩
      exact deepOk_fields (d := (0, true)) ⟨fun r hr => (by rw [h.2.1] at hr; cases hr),
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

/-- **Fields of a struct value** (`aunS`). -/
theorem aunS_sound {a : AW} {t k : Nat} {vs : List V} (h : γ f ctx a (.data t k vs)) (n : Nat) :
    ∃ as, aunS a n = some as ∧ HoldsP f ctx as vs := by
  cases a with
  | data t' k' fs =>
    obtain ⟨vs', he, hl⟩ := h
    cases he
    exact ⟨fs, rfl, holdsP_of_holds2 hl⟩
  | alts as =>
    exact ⟨_, rfl, holdsP_replicate (fun w hw => deepOk_fields (deepAny_sound as _ h) w hw) n⟩
  | flat m c => exact ⟨_, rfl, holdsP_replicate (fun w hw => deepOk_fields (d := (m, c)) h w hw) n⟩
  | xv e =>
    cases e with
    | data =>
      refine ⟨_, rfl, holdsP_replicate (fun w hw => ?_) n⟩
      exact deepOk_fields (d := (0, true)) ⟨fun r hr => (by rw [h.2.1] at hr; cases hr),
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

/-! ## The model

The transfer functions of the extern constructors and the oracles (`actor`, `apre`, `aOracle`)
are parameters: V3's (`IselCovFns`) and V4's control-shape analysis (`IselShpFns`). -/

section Params
variable (actor : TermId → List AW → AW) (apre : TermId → List AW → Bool)
  (aOracle : TermId → List AW → Option AW)

/-- The facts about the extern helpers the soundness proof needs, and a state invariant. -/
structure CovModel (p : Program) (f : Clif.Function) (ctx : Ctx) where
  Is : LState → Prop
  ext : ∀ (a : AW) (term : Term) (v : V) (st : LState) (fs : List V), γ f ctx a v →
    (sem ctx).extract term v st = .ok fs → HoldsP f ctx (aext term.id a) fs
  ctor : ∀ (as : List AW) (vs : List V) (term : Term) (v : V) (st st' : LState),
    Holds2 f ctx as vs → Is st → apre term.id as = true →
    (sem ctx).ctor term vs st = .ok (v, st') → γ f ctx (actor term.id as) v ∧ Is st'
  oracle : ∀ (cfg : Config), cfg.checkOverlap = false → ∀ (n : Nat) (ty : TypeId) (t : TermId)
    (as : List AW) (vs : List V) (a : AW) (s : LState) (tr : Array RuleId) (r : Option V) (s' : LState)
    (tr' : Array RuleId), aOracle t as = some a → Holds2 f ctx as vs → Is s →
    (applyTerm p (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    Is s' ∧ ∀ v, r = some v → γ f ctx a v

variable {actor apre aOracle}

/-! ## Patterns -/

section Pat
variable {p : Program} (hctx : CtxInv f ctx) (md : CovModel actor apre aOracle p f ctx)

theorem unData_eq {ty : TypeId} {v : V} {k : Nat} {fs : List V}
    (h : (sem ctx).unData ty v = some (k, fs)) : v = .data ty k fs := by
  cases v <;> simp [sem] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

theorem primOk_sound {a : AW} {ty : TypeId} {n : String} {c : V} (hpo : primOk a ty n = false)
    (hc : primTy ty n = some c) (hv : γ f ctx a c) : False := by
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

theorem eq_sem_iff {a b : V} : (sem ctx).eq a b = true ↔ a = b := by
  show (a == b) = true ↔ a = b
  exact beq_iff_eq

set_option linter.unusedSectionVars false in
include hctx md in
mutual
/-- **Pattern soundness**: matching `q` against a value `a` describes gives an environment one
of `aPat`'s environments describes. -/
theorem aPat_sound : ∀ (q : Pattern) (a : AW) (aenv : List AW) (v : V) (env env' : Isle.Interp.Env V)
    (st : LState), matchPat p (sem ctx) st q v env = .ok (some env') → γ f ctx a v →
    EnvOK f ctx aenv env → ∃ aenv' ∈ aPat p aext a q aenv, EnvOK f ctx aenv' env'
  | q, a, aenv, v, env, env', st, h, hv, he => by
    unfold aPat
    split
    · rename_i hpr
      simp only [aPrune, Bool.or_eq_true] at hpr
      rcases hpr with hb | hpr
      · exact (isBot_sound hb hv).elim
      · split at hpr
        · rename_i e
          exact (fails_sound hctx q e.toAV v st env env' hpr hv.1 h).elim
        · cases hpr
    · cases q with
      | bind ty x sub =>
        rw [matchPat.eq_1] at h
        split at h
        · obtain ⟨b, hb, hbv⟩ := split_sound hv
          obtain ⟨aenv', hm, he'⟩ := aPat_sound sub b _ v _ env' st h hbv (envOK_set he hbv x)
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
              exact (primOk_sound (Bool.eq_false_iff.mpr hpo) hc hv).elim
          · cases h
        · cases h
      | wildcard ty =>
        rw [matchPat.eq_6] at h
        cases h; exact ⟨aenv, List.mem_singleton_self _, he⟩
      | and ty ps =>
        rw [matchPat.eq_7] at h
        exact aPatAll_sound ps a aenv v env env' st h hv he
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
                obtain ⟨as, has, hl⟩ := aun_sound hv args.length
                rw [has]
                exact aPatArgs_sound args as aenv fs env env' st h hl he
              · cases h
            · cases h
          | struct =>
            rw [hk] at h
            simp only at h ⊢
            split at h
            · rename_i k' fs hu
              have hvd := unData_eq hu
              subst hvd
              obtain ⟨as, has, hl⟩ := aunS_sound hv args.length
              rw [has]
              exact aPatArgs_sound args as aenv fs env env' st h hl he
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
                    exact aPatArgs_sound args _ aenv fs env env' st h (md.ext _ _ _ _ _ hv hx) he
                  · split at h
                    · cases h
                    · cases h
                  · cases h
/-- `aPatAll`: every pattern against the same value. -/
theorem aPatAll_sound : ∀ (qs : List Pattern) (a : AW) (aenv : List AW) (v : V)
    (env env' : Isle.Interp.Env V) (st : LState),
    matchAll p (sem ctx) st qs v env = .ok (some env') → γ f ctx a v → EnvOK f ctx aenv env →
    ∃ aenv' ∈ aPatAll p aext a qs aenv, EnvOK f ctx aenv' env'
  | [], a, aenv, v, env, env', st, h, hv, he => by
    rw [matchAll.eq_1] at h
    cases h
    exact ⟨aenv, by simp [aPatAll], he⟩
  | q :: qs, a, aenv, v, env, env', st, h, hv, he => by
    rw [matchAll.eq_2] at h
    cases hq : matchPat p (sem ctx) st q v env with
    | error e => rw [hq] at h; cases h
    | ok o =>
      rw [hq] at h
      cases o with
      | none => cases h
      | some e1 =>
        obtain ⟨a1, h1, he1⟩ := aPat_sound q a aenv v env e1 st hq hv he
        obtain ⟨a2, h2, he2⟩ := aPatAll_sound qs a a1 v e1 env' st h hv he1
        exact ⟨a2, by rw [aPatAll]; exact List.mem_flatMap.mpr ⟨a1, h1, h2⟩, he2⟩
/-- `aPatArgs`: patterns against values position by position. -/
theorem aPatArgs_sound : ∀ (qs : List Pattern) (as : List AW) (aenv : List AW) (vs : List V)
    (env env' : Isle.Interp.Env V) (st : LState),
    matchArgs p (sem ctx) st qs vs env = .ok (some env') → HoldsP f ctx as vs →
    EnvOK f ctx aenv env → ∃ aenv' ∈ aPatArgs p aext as qs aenv, EnvOK f ctx aenv' env'
  | [], as, aenv, [], env, env', st, h, hv, he => by
    rw [matchArgs.eq_1] at h
    cases h
    exact ⟨aenv, by cases as <;> simp [aPatArgs], he⟩
  | q :: qs, a :: as, aenv, v :: vs, env, env', st, h, hv, he => by
    rw [matchArgs.eq_2] at h
    cases hq : matchPat p (sem ctx) st q v env with
    | error e => rw [hq] at h; cases h
    | ok o =>
      rw [hq] at h
      cases o with
      | none => cases h
      | some e1 =>
        have hh := holdsP_cons hv
        obtain ⟨a1, h1, he1⟩ := aPat_sound q a aenv v env e1 st hq hh.1 he
        obtain ⟨a2, h2, he2⟩ := aPatArgs_sound qs as a1 vs e1 env' st h hh.2 he1
        exact ⟨a2, by rw [aPatArgs]; exact List.mem_flatMap.mpr ⟨a1, h1, h2⟩, he2⟩
  | q :: qs, [], aenv, v :: vs, env, env', st, h, hv, he => by
    rw [matchArgs.eq_2] at h
    cases hq : matchPat p (sem ctx) st q v env with
    | error e => rw [hq] at h; cases h
    | ok o =>
      rw [hq] at h
      cases o with
      | none => cases h
      | some e1 =>
        obtain ⟨a1, h1, he1⟩ := aPat_sound q .top aenv v env e1 st hq (by simpa using hv 0 v rfl) he
        obtain ⟨a2, h2, he2⟩ := aPatArgs_sound qs [] a1 vs e1 env' st h (holdsP_nil_cons hv) he1
        exact ⟨a2, by rw [aPatArgs]; exact List.mem_flatMap.mpr ⟨a1, h1, h2⟩, he2⟩
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

theorem mapM_some_mem {α β : Type} {g : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM g = some ys → ∀ x ∈ xs, ∃ y ∈ ys, g x = some y
  | [], _, _ => fun _ h => by cases h
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y0, h0, h⟩ := bind_some_ex h
    obtain ⟨ys', h1, h⟩ := bind_some_ex h
    simp only [pure, Option.some.injEq] at h
    subst h
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨y0, List.mem_cons_self, h0⟩
    · obtain ⟨y, hy, hg⟩ := mapM_some_mem h1 z hz
      exact ⟨y, List.mem_cons_of_mem _ hy, hg⟩

theorem flat_mapM_mem {α β : Type} {g : α → Option (List β)} {xs : List α} {ys : List β}
    (h : (xs.mapM g).map List.flatten = some ys) {x : α} (hx : x ∈ xs) {zs : List β}
    (hg : g x = some zs) {z : β} (hz : z ∈ zs) : z ∈ ys := by
  cases hm : xs.mapM g with
  | none => rw [hm] at h; cases h
  | some yss =>
    rw [hm] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨y, hy, hgy⟩ := mapM_some_mem hm x hx
    rw [hg] at hgy
    cases hgy
    exact List.mem_flatten.mpr ⟨zs, hy, hz⟩

theorem aExpr_let {ty : TypeId} {bs : List (VarId × TypeId × Isle.Expr)} {body : Isle.Expr}
    {aenv : List AW} {a : AW} (h : aExpr p tab actor apre aOracle (.let ty bs body) aenv = some a) :
    ∃ aenv', aBinds p tab actor apre aOracle bs aenv = some aenv' ∧
      aExpr p tab actor apre aOracle body aenv' = some a := by
  rw [aExpr.eq_5] at h
  split at h
  · exact ⟨_, ‹_›, h⟩
  · cases h

theorem aExpr_term {ty : TypeId} {t : TermId} {args : List Isle.Expr} {aenv : List AW} {a : AW}
    (h : aExpr p tab actor apre aOracle (.term ty t args) aenv = some a) :
    ∃ as, aArgs p tab actor apre aOracle args aenv = some as ∧
      aApply p tab actor apre aOracle ty t as = some a := by
  rw [aExpr.eq_6] at h
  split at h
  · exact ⟨_, ‹_›, h⟩
  · cases h

theorem aArgs_cons {e : Isle.Expr} {es : List Isle.Expr} {aenv : List AW} {as : List AW}
    (h : aArgs p tab actor apre aOracle (e :: es) aenv = some as) :
    ∃ a as', as = a :: as' ∧ aExpr p tab actor apre aOracle e aenv = some a ∧
      aArgs p tab actor apre aOracle es aenv = some as' := by
  rw [aArgs.eq_2] at h
  split at h
  · cases h; exact ⟨_, _, rfl, ‹_›, ‹_›⟩
  · cases h

theorem aBinds_cons {x : VarId} {ty : TypeId} {e : Isle.Expr} {bs : List (VarId × TypeId × Isle.Expr)}
    {aenv aenv' : List AW} (h : aBinds p tab actor apre aOracle ((x, ty, e) :: bs) aenv = some aenv') :
    ∃ a, aExpr p tab actor apre aOracle e aenv = some a ∧
      aBinds p tab actor apre aOracle bs (aenv.set x a) = some aenv' := by
  rw [aBinds.eq_2] at h
  split at h
  · exact ⟨_, ‹_›, h⟩
  · cases h

theorem aIfLets_cons {il : IfLet} {ils : List IfLet} {aenv : List AW} {envs : List (List AW)}
    (h : aIfLets p tab aext actor apre aOracle (il :: ils) aenv = some envs) :
    ∃ a, aExpr p tab actor apre aOracle il.rhs aenv = some a ∧
      ((aPat p aext a il.lhs aenv).mapM fun e => aIfLets p tab aext actor apre aOracle ils e).map
        List.flatten = some envs := by
  rw [aIfLets.eq_2] at h
  split at h
  · exact ⟨_, ‹_›, h⟩
  · cases h

theorem aRule_inv {ins : List AW} {out : AW} {r : Rule}
    (h : aRule p tab aext actor apre aOracle ins out r = true) :
    ∃ envs, aRuleEnvs p tab aext actor apre aOracle ins r = some envs ∧ ∀ env ∈ envs,
      ∃ a, aExpr p tab actor apre aOracle r.rhs env = some a ∧ AW.le a out = true := by
  unfold aRule at h
  split at h
  · rename_i envs he
    refine ⟨envs, he, fun env hm => ?_⟩
    have := List.all_eq_true.mp h env hm
    split at this
    · exact ⟨_, ‹_›, this⟩
    · cases this
  · cases h

theorem tabGet_le {t : TermId} {as : List AW} {out : AW} (h : tabGet tab t as = some out) :
    ∃ ins, (t, ins, out) ∈ tab ∧ AW.leAll as ins = true := by
  unfold tabGet at h
  split at h
  · rename_i e he
    cases h
    have hm := List.mem_of_find?_eq_some he
    have hp := List.find?_some he
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨h1, h2⟩, -⟩ := hp
    exact ⟨e.2.1, by rw [← h1]; exact hm, h2⟩
  · cases hf : tab.find? (fun e => e.1 == t && AW.leAll as e.2.1) with
    | none => rw [hf] at h; cases h
    | some e =>
      rw [hf] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      have hm := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      exact ⟨e.2.1, by rw [← hp.1]; exact hm, hp.2⟩

theorem chkTab_mem (hc : chkTab p tab aext actor apre aOracle = true) {t : TermId} {ins : List AW}
    {out : AW} (hm : (t, ins, out) ∈ tab) :
    ∀ r ∈ p.rulesOf t, aRule p tab aext actor apre aOracle ins out r = true := by
  have := List.all_eq_true.mp hc _ hm
  exact List.all_eq_true.mp this

end Inv

theorem holds2_le {as bs : List AW} {vs : List V} (h : AW.leAll as bs = true)
    (hv : Holds2 f ctx as vs) : Holds2 f ctx bs vs :=
  leL_sound as bs h vs hv

/-! ## Soundness of the abstract interpretation -/

section Sound
variable {p : Program} (hctx : CtxInv f ctx) (md : CovModel actor apre aOracle p f ctx) (cfg : Config)
  (tab : Tab)

/-- The soundness statements at fuel `n`. -/
structure SoundAt (n : Nat) : Prop where
  expr : ∀ e aenv a env s tr r s' tr', aExpr p tab actor apre aOracle e aenv = some a →
    EnvOK f ctx aenv env → md.Is s →
    (evalExpr p (sem ctx) cfg n e env).run (s, tr) = .ok (r, (s', tr')) →
    md.Is s' ∧ ∀ v, r = some v → γ f ctx a v
  args : ∀ es aenv as env s tr r s' tr', aArgs p tab actor apre aOracle es aenv = some as →
    EnvOK f ctx aenv env → md.Is s →
    (evalArgs p (sem ctx) cfg n es env).run (s, tr) = .ok (r, (s', tr')) →
    md.Is s' ∧ ∀ vs, r = some vs → Holds2 f ctx as vs
  binds : ∀ bs aenv aenv' env s tr r s' tr', aBinds p tab actor apre aOracle bs aenv = some aenv' →
    EnvOK f ctx aenv env → md.Is s →
    (evalBinds p (sem ctx) cfg n bs env).run (s, tr) = .ok (r, (s', tr')) →
    md.Is s' ∧ ∀ env', r = some env' → EnvOK f ctx aenv' env'
  apply : ∀ ty t as a vs s tr r s' tr', aApply p tab actor apre aOracle ty t as = some a →
    Holds2 f ctx as vs → md.Is s →
    (applyTerm p (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    md.Is s' ∧ ∀ v, r = some v → γ f ctx a v
  root : ∀ ty t term flags ex ins out vs s tr r s' tr', termOf p t = .ok term →
    term.kind = .decl flags (some .internal) ex →
    (∀ rl ∈ p.rulesOf t, aRule p tab aext actor apre aOracle ins out rl = true ∨
      ∀ m s0 env s1, (matchRule p (sem ctx) cfg m rl vs).run s0 ≠ .ok (some env, s1)) →
    Holds2 f ctx ins vs → md.Is s →
    (applyTerm p (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    md.Is s' ∧ ∀ v, r = some v → γ f ctx out v
  mrule : ∀ rl ins envs vs s tr env s' tr', aRuleEnvs p tab aext actor apre aOracle ins rl = some envs →
    Holds2 f ctx ins vs → md.Is s →
    (matchRule p (sem ctx) cfg n rl vs).run (s, tr) = .ok (some env, (s', tr')) →
    md.Is s' ∧ ∃ aenv ∈ envs, EnvOK f ctx aenv env
  iflets : ∀ ils aenv envs env s tr env' s' tr', aIfLets p tab aext actor apre aOracle ils aenv = some envs →
    EnvOK f ctx aenv env → md.Is s →
    (matchIfLets p (sem ctx) cfg n ils env).run (s, tr) = .ok (some env', (s', tr')) →
    md.Is s' ∧ ∃ aenv' ∈ envs, EnvOK f ctx aenv' env'

theorem γ_mkData {ty : TypeId} {k : Nat} {as : List AW} {vs : List V} (h : Holds2 f ctx as vs) :
    γ f ctx (.data ty k as) ((sem ctx).mkData ty k vs) := ⟨vs, rfl, h⟩

theorem holds2_bot {as : List AW} {vs : List V} (hb : as.any AW.isBot = true) (h : Holds2 f ctx as vs) :
    False := by
  obtain ⟨a, ha, hab⟩ := List.any_eq_true.mp hb
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
  have hl := γL_length h
  have : i < vs.length := by rw [← hl]; exact (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨v, hv⟩ : ∃ v, vs[i]? = some v := ⟨vs[i], List.getElem?_eq_getElem this⟩
  exact isBot_sound hab (γL_get h i a v hi hv)

include hctx in
/-- **Soundness of the abstract interpretation**, at every fuel. -/
theorem soundAt (hc : cfg.checkOverlap = false) (htab : chkTab p tab aext actor apre aOracle = true) :
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
      (∀ rl ∈ p.rulesOf t, aRule p tab aext actor apre aOracle ins out rl = true ∨
        ∀ m s0 env s1, (matchRule p (sem ctx) cfg m rl vs).run s0 ≠ .ok (some env, s1)) →
      Holds2 f ctx ins vs → md.Is s →
      (applyTerm p (sem ctx) cfg (n + 1) ty t vs).run (s, tr) = .ok (r, (s', tr')) →
      md.Is s' ∧ ∀ v, r = some v → γ f ctx out v := by
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
      have hok : aRule p tab aext actor apre aOracle ins out rl = true := by
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
      exact ⟨hIs, fun v hv => by
        cases hv; exact ⟨fun r hr => by simp [sem, V.regsIn] at hr, fun _ => rfl⟩⟩
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
      obtain ⟨aenv0, hm0, he0⟩ := aPatArgs_sound hctx md _ _ _ _ _ _ _ hma (holdsP_of_holds2 hins)
        (envOK_empty (List.replicate rl.vars.length .top) _)
      unfold aRuleEnvs at hae
      cases hif : aIfLets p tab aext actor apre aOracle rl.iflets aenv0 with
      | none =>
        cases hm : (aPatArgs p aext ins rl.args (List.replicate rl.vars.length .top)).mapM
            (fun e => aIfLets p tab aext actor apre aOracle rl.iflets e) with
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
          obtain ⟨aenv1, hm1, he1⟩ := aPat_sound hctx md _ _ _ _ _ _ _ hmp (hv1 v rfl) he
          cases hif : aIfLets p tab aext actor apre aOracle ils aenv1 with
          | none =>
            cases hm : (aPat p aext a il.lhs aenv).mapM
                (fun e => aIfLets p tab aext actor apre aOracle ils e) with
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
