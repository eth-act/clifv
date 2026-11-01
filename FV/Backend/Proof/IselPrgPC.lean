import FV.Backend.Proof.IselPrgPat
import FV.Backend.Proof.IselPrgMono

/-!
# Progress of the ISLE lowering (V7): partial correctness of the abstract interpretation

At **every** fuel (`pcAt`, by strong induction on the fuel): a run of an expression (arguments,
`let*` bindings, application, if-lets, match phase of a rule, table term) that the abstract
interpreter accepts and that *returns* returns a value described by the abstract result, and a
value at all when the abstract interpretation says it surely does. No fuel bound is needed here:
this is what the exhaustiveness argument uses for the rules selection tried (at whatever fuel),
including on the refined argument cases of `PA.splitL`, whose abstract costs the entry's fuel
need not cover. Progress (`IselPrgSound`) then only has to show that runs return.

The checker's facts are inverted first (`chkEntry_inv`, `ruleCost_inv`, `reach_mem`, …).
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Interp Isle.Aarch64

variable {f : Clif.Function} {ctx : Ctx}

section Inv
variable {p : Program} {tab : PTab} {aext : TermId → PA → Option (List (List PA) × Bool)}
  {actor : TermId → List PA → Option (PA × Bool)} {aidata : Nat → Option (List PA)}
  {hand : RuleId → Option (Nat × PA)}

/-! ## Inversion of the checker -/

theorem tabFind_sound {t : TermId} {as : List PA} {e : PEnt} (h : tabFind tab t as = some e) :
    e ∈ tab ∧ e.t = t ∧ PA.leL as e.ins = true := by
  unfold tabFind at h
  split at h
  · rename_i e' he
    cases h
    have hm := List.mem_of_find?_eq_some he
    have hp := List.find?_some he
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨hm, hp.1.1, hp.1.2⟩
  · have hm := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨hm, hp.1, hp.2⟩

theorem chkTab_mem (h : chkTab p tab aext actor aidata hand = true) {e : PEnt} (he : e ∈ tab) :
    chkEntry p tab aext actor aidata hand e = true :=
  List.all_eq_true.mp h e he

/-- What `chkEntry` checks. -/
theorem chkEntry_inv {e : PEnt} (h : chkEntry p tab aext actor aidata hand e = true) :
    ∃ term flags ex cs, termOf p e.t = .ok term ∧ term.kind = .decl flags (some .internal) ex ∧
      flags.isMulti = false ∧
      (reach p tab aext actor aidata e.ins (p.rulesOf e.t)).mapM
        (ruleCost p tab aext actor aidata hand e.ins e.out e.osome) = some cs ∧
      1 + max (selCost cs) (maxCost (cs.map (·.2))) ≤ e.fu ∧
      ((flags.isPartial && !e.osome) ||
        exhaustive p tab aext actor aidata (reach p tab aext actor aidata e.ins (p.rulesOf e.t))
          e.ins) = true := by
  unfold chkEntry at h
  split at h
  · cases h
  · rename_i term ht
    split at h
    · rename_i flags ex hk
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      obtain ⟨hm, h⟩ := h
      split at h
      · rename_i cs hcs
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨term, flags, ex, cs, ht, hk, hm, hcs, h.1, h.2⟩
      · cases h
    · cases h

/-- What `ruleCost` checks. -/
theorem ruleCost_inv {ins : List PA} {out : PA} {osome : Bool} {r : Rule} {ilc rc : Nat}
    (h : ruleCost p tab aext actor aidata hand ins out osome r = some (ilc, rc)) :
    ∃ envs m, aRule p tab aext actor aidata ins r = some (envs, m, ilc) ∧
      (∀ c a, hand r.id = some (c, a) → rc = c ∧ (envs = [] ∨ PA.le a out = true)) ∧
      (hand r.id = none → ∀ ae ∈ envs, ∃ a mu c, aExpr p tab actor r.rhs ae = some (a, mu, c) ∧
        PA.le a out = true ∧ (osome = true → mu = true) ∧ c ≤ rc) := by
  unfold ruleCost at h
  obtain ⟨⟨envs, m, ilc'⟩, h1, h⟩ := obind_some h
  refine ⟨envs, m, ?_, ?_, ?_⟩
  · simp only at h
    split at h
    · split at h
      · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        rw [h.1] at h1; exact h1
      · cases h
    · obtain ⟨rcs, -, h⟩ := obind_some h
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      rw [h.1] at h1; exact h1
  · intro c a hh
    simp only [hh] at h
    split at h
    · rename_i hc
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      refine ⟨h.2.symm, ?_⟩
      simp only [Bool.or_eq_true, List.isEmpty_iff] at hc
      exact hc
    · cases h
  · intro hh ae hae
    simp only [hh] at h
    obtain ⟨rcs, hrcs, h⟩ := obind_some h
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨c, hc, hgc⟩ := mapM_some_mem hrcs ae hae
    obtain ⟨⟨a, mu, c'⟩, h2, h3⟩ := obind_some hgc
    simp only at h3
    split at h3
    · rename_i hle
      simp only [pure, Option.some.injEq] at h3
      subst h3
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hle
      refine ⟨a, mu, c', h2, hle.1, fun ho => ?_, h.2 ▸ le_maxCost hc⟩
      rcases hle.2 with h | h
      · rw [ho] at h; cases h
      · exact h
    · cases h3

theorem mustRule_inv {ins : List PA} {r : Rule}
    (h : mustRule p tab aext actor aidata ins r = true) :
    ∃ envs c, aRule p tab aext actor aidata ins r = some (envs, true, c) := by
  unfold mustRule at h
  split at h
  · rename_i envs m c ha
    subst h
    exact ⟨envs, c, ha⟩
  · cases h

theorem reach_sub {ins : List PA} : ∀ {rs : List Rule} {r : Rule},
    r ∈ reach p tab aext actor aidata ins rs → r ∈ rs
  | [], _, h => by simp [reach] at h
  | r' :: rs, r, h => by
    unfold reach at h
    split at h
    · simp only [List.mem_singleton] at h
      subst h; exact List.mem_cons_self ..
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (reach_sub h)

/-- A rule after rules that are not surely matched is reached. -/
theorem reach_mem {ins : List PA} {r : Rule} {post : List Rule} : ∀ {pre : List Rule},
    (∀ r' ∈ pre, mustRule p tab aext actor aidata ins r' = false) →
    r ∈ reach p tab aext actor aidata ins (pre ++ r :: post)
  | [], _ => by
    simp only [List.nil_append, reach]
    split <;> exact List.mem_cons_self ..
  | r' :: pre, h => by
    simp only [List.cons_append, reach]
    rw [h r' (List.mem_cons_self ..)]
    exact List.mem_cons_of_mem _
      (reach_mem fun r'' hr'' => h r'' (List.mem_cons_of_mem _ hr''))

/-! ## Inversion of the abstract evaluation -/

theorem aExpr_var_inv {ty : TypeId} {x : VarId} {aenv : AEnv} {a : PA} {must : Bool} {c : Nat}
    (h : aExpr p tab actor (.var ty x) aenv = some (a, must, c)) :
    aenv[x]? = some (some a) ∧ must = true ∧ c = 1 := by
  rw [aExpr.eq_1] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨‹_›, rfl, rfl⟩
  · cases h

theorem aExpr_let_inv {ty : TypeId} {bs : List (VarId × TypeId × Isle.Expr)} {body : Isle.Expr}
    {aenv : AEnv} {a : PA} {must : Bool} {c : Nat}
    (h : aExpr p tab actor (.let ty bs body) aenv = some (a, must, c)) :
    ∃ aenv' m1 c1 m2 c2, aBinds p tab actor bs aenv = some (aenv', m1, c1) ∧
      aExpr p tab actor body aenv' = some (a, m2, c2) ∧ must = (m1 && m2) ∧ c = 1 + max c1 c2 := by
  rw [aExpr.eq_5] at h
  obtain ⟨⟨aenv', m1, c1⟩, h1, h⟩ := obind_some h
  obtain ⟨⟨a', m2, c2⟩, h2, h⟩ := obind_some h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨aenv', m1, c1, m2, c2, h1, h2, rfl, rfl⟩

theorem aExpr_term_inv {ty : TypeId} {t : TermId} {args : List Isle.Expr} {aenv : AEnv} {a : PA}
    {must : Bool} {c : Nat} (h : aExpr p tab actor (.term ty t args) aenv = some (a, must, c)) :
    ∃ as m1 c1 m2 c2, aArgs p tab actor args aenv = some (as, m1, c1) ∧
      aApply p tab actor ty t as = some (a, m2, c2) ∧ must = (m1 && m2) ∧ c = 1 + max c1 c2 := by
  rw [aExpr.eq_6] at h
  obtain ⟨⟨as, m1, c1⟩, h1, h⟩ := obind_some h
  obtain ⟨⟨a', m2, c2⟩, h2, h⟩ := obind_some h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨as, m1, c1, m2, c2, h1, h2, rfl, rfl⟩

theorem aArgs_cons_inv {e : Isle.Expr} {es : List Isle.Expr} {aenv : AEnv} {as : List PA}
    {must : Bool} {c : Nat} (h : aArgs p tab actor (e :: es) aenv = some (as, must, c)) :
    ∃ a as' m1 c1 m2 c2, aExpr p tab actor e aenv = some (a, m1, c1) ∧
      aArgs p tab actor es aenv = some (as', m2, c2) ∧ as = a :: as' ∧ must = (m1 && m2) ∧
      c = 1 + max c1 c2 := by
  rw [aArgs.eq_2] at h
  obtain ⟨⟨a, m1, c1⟩, h1, h⟩ := obind_some h
  obtain ⟨⟨as', m2, c2⟩, h2, h⟩ := obind_some h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨a, as', m1, c1, m2, c2, h1, h2, rfl, rfl, rfl⟩

theorem aBinds_cons_inv {x : VarId} {ty : TypeId} {e : Isle.Expr}
    {bs : List (VarId × TypeId × Isle.Expr)} {aenv aenv' : AEnv} {must : Bool} {c : Nat}
    (h : aBinds p tab actor ((x, ty, e) :: bs) aenv = some (aenv', must, c)) :
    ∃ a m1 c1 m2 c2, aExpr p tab actor e aenv = some (a, m1, c1) ∧ x < aenv.length ∧
      aBinds p tab actor bs (aenv.set x (some a)) = some (aenv', m2, c2) ∧ must = (m1 && m2) ∧
      c = 1 + max c1 c2 := by
  rw [aBinds.eq_2] at h
  obtain ⟨⟨a, m1, c1⟩, h1, h⟩ := obind_some h
  simp only at h
  split at h
  · rename_i hx
    obtain ⟨⟨aenv'', m2, c2⟩, h2, h⟩ := obind_some h
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨a, m1, c1, m2, c2, h1, hx, h2, rfl, rfl⟩
  · cases h

theorem aIfLets_cons_inv {il : IfLet} {ils : List IfLet} {aenv : AEnv} {envs : List AEnv}
    {must : Bool} {c : Nat}
    (h : aIfLets p tab aext actor aidata (il :: ils) aenv = some (envs, must, c)) :
    ∃ a m1 c1 envs1 m2 rs, aExpr p tab actor il.rhs aenv = some (a, m1, c1) ∧
      aPat p aext aidata a il.lhs aenv = some (envs1, m2) ∧
      envs1.mapM (fun e => aIfLets p tab aext actor aidata ils e) = some rs ∧
      envs = rs.flatMap (·.1) ∧ must = (m1 && m2 && rs.all (·.2.1)) ∧
      c = 1 + max c1 (maxCost (rs.map (·.2.2))) := by
  rw [aIfLets.eq_2] at h
  obtain ⟨⟨a, m1, c1⟩, h1, h⟩ := obind_some h
  obtain ⟨⟨envs1, m2⟩, h2, h⟩ := obind_some h
  obtain ⟨rs, h3, h⟩ := obind_some h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨a, m1, c1, envs1, m2, rs, h1, h2, h3, rfl, rfl, rfl⟩

theorem aRule_inv {ins : List PA} {r : Rule} {envs : List AEnv} {must : Bool} {c : Nat}
    (h : aRule p tab aext actor aidata ins r = some (envs, must, c)) :
    ∃ envs0 m rs, aPatArgs p aext aidata ins r.args (List.replicate r.vars.length none) =
        some (envs0, m) ∧
      envs0.mapM (fun e => aIfLets p tab aext actor aidata r.iflets e) = some rs ∧
      envs = rs.flatMap (·.1) ∧ must = (m && rs.all (·.2.1)) ∧ c = maxCost (rs.map (·.2.2)) := by
  unfold aRule at h
  obtain ⟨⟨envs0, m⟩, h1, h⟩ := obind_some h
  obtain ⟨rs, h2, h⟩ := obind_some h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨envs0, m, rs, h1, h2, rfl, rfl, rfl⟩

end Inv

/-- A match from one environment of a flattened list of if-let results. -/
theorem matchOK_flat {rs : List (List AEnv × Bool × Nat)} {y : List AEnv × Bool × Nat}
    (hy : y ∈ rs) {r : Option (Isle.Interp.Env V)} (h : MatchOK f ctx y.1 y.2.1 r) (m : Bool) :
    MatchOK f ctx (rs.flatMap (·.1)) (m && rs.all (·.2.1)) r := by
  refine ⟨fun e he => ?_, fun hm => h.2 ?_⟩
  · obtain ⟨ae, hae, hok⟩ := h.1 e he
    exact ⟨ae, List.mem_flatMap.mpr ⟨y, hy, hae⟩, hok⟩
  · simp only [Bool.and_eq_true, List.all_eq_true] at hm
    exact hm.2 y hy

theorem sem_int (ty : TypeId) (i : Int) : (sem ctx).int ty i = .int (normInt ty i) := by
  simp only [sem]

theorem γ_aint (ty : TypeId) (i : Int) : γ f ctx (aint ty i) ((sem ctx).int ty i) := by
  rw [sem_int]
  unfold aint
  generalize normInt ty i = c
  exact ⟨c, rfl, fun _ h => by cases h; exact Int.le_refl _,
    fun _ h => by cases h; exact Int.le_refl _⟩

/-! ## Partial correctness -/

section PC
variable {p : Program} {tab : PTab} {aext : TermId → PA → Option (List (List PA) × Bool)}
  {actor : TermId → List PA → Option (PA × Bool)} {aidata : Nat → Option (List PA)}
  {hand : RuleId → Option (Nat × PA)} {cfg : Config}

variable (f ctx p tab aext actor aidata cfg) in
/-- **Partial correctness at fuel `n`**: what a run that returns returns. -/
structure PCAt (n : Nat) : Prop where
  expr : ∀ e aenv a must c env s r s', aExpr p tab actor e aenv = some (a, must, c) →
    EnvOK f ctx aenv env → (evalExpr p (sem ctx) cfg n e env).run s = .ok (r, s') →
    (∀ w, r = some w → γ f ctx a w) ∧ (must = true → r.isSome)
  args : ∀ es aenv as must c env s r s', aArgs p tab actor es aenv = some (as, must, c) →
    EnvOK f ctx aenv env → (evalArgs p (sem ctx) cfg n es env).run s = .ok (r, s') →
    (∀ ws, r = some ws → γL f ctx as ws) ∧ (must = true → r.isSome)
  binds : ∀ bs aenv aenv' must c env s r s', aBinds p tab actor bs aenv = some (aenv', must, c) →
    EnvOK f ctx aenv env → (evalBinds p (sem ctx) cfg n bs env).run s = .ok (r, s') →
    (∀ env', r = some env' → EnvOK f ctx aenv' env') ∧ (must = true → r.isSome)
  apply : ∀ ty t as a must c vs s r s', aApply p tab actor ty t as = some (a, must, c) →
    γL f ctx as vs → (applyTerm p (sem ctx) cfg n ty t vs).run s = .ok (r, s') →
    (∀ w, r = some w → γ f ctx a w) ∧ (must = true → r.isSome)
  entry : ∀ e ∈ tab, ∀ ty vs s r s', γL f ctx e.ins vs →
    (applyTerm p (sem ctx) cfg n ty e.t vs).run s = .ok (r, s') →
    (∀ w, r = some w → γ f ctx e.out w) ∧ (e.osome = true → r.isSome)
  iflets : ∀ ils aenv envs must c env s r s',
    aIfLets p tab aext actor aidata ils aenv = some (envs, must, c) → EnvOK f ctx aenv env →
    (matchIfLets p (sem ctx) cfg n ils env).run s = .ok (r, s') → MatchOK f ctx envs must r
  mrule : ∀ ins rl envs must c vs s r s',
    aRule p tab aext actor aidata ins rl = some (envs, must, c) → γL f ctx ins vs →
    (matchRule p (sem ctx) cfg n rl vs).run s = .ok (r, s') → MatchOK f ctx envs must r

variable (M : Model f ctx aext actor aidata) (H : HandOk f ctx p cfg tab hand)
  (hc : cfg.checkOverlap = false) (htab : chkTab p tab aext actor aidata hand = true)

/-- A rule that surely matches on arguments its abstract arguments describe never fails to
match (at a fuel where partial correctness holds). -/
theorem mustRule_fail {n : Nat} (pc : PCAt f ctx p tab aext actor aidata cfg n) {ins : List PA}
    {rl : Rule} (hm : mustRule p tab aext actor aidata ins rl = true) {vs : List V}
    (hins : γL f ctx ins vs) {s s1 : LState × Array RuleId}
    (h : (matchRule p (sem ctx) cfg n rl vs).run s = .ok (none, s1)) : False := by
  obtain ⟨envs, c, ha⟩ := mustRule_inv hm
  have := (pc.mrule _ _ _ _ _ _ _ _ _ ha hins h).2 rfl
  cases this

include hc in
/-- **No rule selected contradicts exhaustiveness**: every rule the entry may reach was tried
and failed, but some rule surely matches the arguments or one of their cases. -/
theorem select_none_absurd {n : Nat} (pc : ∀ m < n, PCAt f ctx p tab aext actor aidata cfg m)
    {term : Term} {rules : List Rule} {ins : List PA} {vs : List V}
    {s s' : LState × Array RuleId}
    (h : (selectRule p (sem ctx) cfg n term rules vs).run s = .ok (none, s'))
    (hex : exhaustive p tab aext actor aidata (reach p tab aext actor aidata ins rules) ins = true)
    (hins : γL f ctx ins vs) : False := by
  have hall := selectRule_none_all hc h
  unfold exhaustive at hex
  simp only [Bool.or_eq_true] at hex
  rcases hex with hex | hex
  · obtain ⟨rl, hrl, hmr⟩ := List.any_eq_true.mp hex
    obtain ⟨m, hm, s2, hmatch⟩ := hall rl (reach_sub hrl)
    exact mustRule_fail (pc m hm) hmr hins hmatch
  · obtain ⟨sp, hsp, hγ⟩ := splitL_sound _ _ hins
    obtain ⟨rl, hrl, hmr⟩ := List.any_eq_true.mp (List.all_eq_true.mp hex sp hsp)
    obtain ⟨m, hm, s2, hmatch⟩ := hall rl (reach_sub hrl)
    exact mustRule_fail (pc m hm) hmr hγ hmatch

include hc in
/-- **A selected rule is reached** (the rules before it did not surely match), and its match
succeeded from the start state. -/
theorem select_some_reach {n : Nat} (pc : ∀ m < n, PCAt f ctx p tab aext actor aidata cfg m)
    {term : Term} {rules : List Rule} {ins : List PA} {vs : List V}
    {s s' : LState × Array RuleId} {rl : Rule} {env : Isle.Interp.Env V}
    (h : (selectRule p (sem ctx) cfg n term rules vs).run s = .ok (some (rl, env), s'))
    (hins : γL f ctx ins vs) :
    rl ∈ reach p tab aext actor aidata ins rules ∧
      ∃ m < n, (matchRule p (sem ctx) cfg m rl vs).run s = .ok (some env, s') := by
  obtain ⟨pre, post, hrs, hpre, m, hm, hmatch⟩ := selectRule_some_split hc h
  refine ⟨?_, m, hm, hmatch⟩
  rw [hrs]
  apply reach_mem
  intro r' hr'
  obtain ⟨m', hm', s2, h'⟩ := hpre r' hr'
  cases hmr : mustRule p tab aext actor aidata ins r'
  · rfl
  · exact (mustRule_fail (pc m' hm') hmr hins h').elim

include M H hc htab in
/-- **Partial correctness at every fuel.** -/
theorem pcAt : ∀ n, PCAt f ctx p tab aext actor aidata cfg n := by
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
  -- table terms
  have htabN : ∀ e ∈ tab, ∀ ty vs s r s', γL f ctx e.ins vs →
      (applyTerm p (sem ctx) cfg (n + 1) ty e.t vs).run s = .ok (r, s') →
      (∀ w, r = some w → γ f ctx e.out w) ∧ (e.osome = true → r.isSome) := by
    intro e he ty vs s r s' hins h
    obtain ⟨term, flags, ex, cs, ht, hk, hm, hcs, -, hex⟩ := chkEntry_inv (chkTab_mem htab he)
    rw [applyTerm_internal_run ht hk hm] at h
    obtain ⟨⟨sel, s1⟩, h1, h2⟩ := except_bind_eq_ok h
    have pc : ∀ m < n, PCAt f ctx p tab aext actor aidata cfg m := fun m hm => ih m (by omega)
    cases sel with
    | none =>
      simp only at h2
      split at h2
      · rename_i hpart
        cases pure_ok h2
        refine ⟨fun w hw => (nomatch hw), fun hos => ?_⟩
        rw [hpart, hos] at hex
        simp only [Bool.not_true, Bool.and_false, Bool.false_or] at hex
        exact (select_none_absurd hc pc h1 hex hins).elim
      · exact (throw_ok h2).elim
    | some re =>
      obtain ⟨rl, env⟩ := re
      obtain ⟨hreach, m, hm, hmatch⟩ := select_some_reach hc pc h1 hins
      obtain ⟨⟨ilc, rc⟩, -, hrc⟩ := mapM_some_mem hcs rl hreach
      obtain ⟨envs, mu, haR, hhand, hnohand⟩ := ruleCost_inv hrc
      have hok := (ih m (by omega)).mrule _ _ _ _ _ _ _ _ _ haR hins hmatch
      obtain ⟨ae, hae, heok⟩ := hok.1 env rfl
      simp only at h2
      obtain ⟨ev, s2, h3, h4⟩ := bind_ok h2
      have hev : (∀ w, ev = some w → γ f ctx e.out w) ∧ (e.osome = true → ev.isSome) := by
        cases hh : hand rl.id with
        | some ca =>
          obtain ⟨c, a⟩ := ca
          obtain ⟨-, hle⟩ := hhand c a hh
          rcases hle with hnil | hle
          · subst hnil; cases hae
          · obtain ⟨v, s'', hv, hγv⟩ := H e he rl (reach_sub hreach) c a hh vs hins m s env s1
              hmatch (max n c) (Nat.le_max_right _ _)
            have := evalExpr_mono (Nat.le_max_left n c) h3
            rw [hv] at this
            simp only [Except.ok.injEq, Prod.mk.injEq] at this
            obtain ⟨rfl, -⟩ := this
            exact ⟨fun w hw => by cases hw; exact le_sound _ _ hle _ hγv, fun _ => rfl⟩
        | none =>
          obtain ⟨a, mu', c, hae', hle, hos, -⟩ := hnohand hh ae hae
          obtain ⟨h5, h6⟩ := ihn.expr _ _ _ _ _ _ _ _ _ hae' heok h3
          exact ⟨fun w hw => le_sound _ _ hle _ (h5 w hw), fun ho => h6 (hos ho)⟩
      cases ev with
      | some v =>
        obtain ⟨u, s3, -, h6⟩ := bind_ok h4
        cases pure_ok h6
        exact ⟨fun w hw => by cases hw; exact hev.1 v rfl, fun _ => rfl⟩
      | none =>
        cases pure_ok h4
        exact ⟨fun w hw => (nomatch hw), hev.2⟩
  -- applications
  have happly : ∀ ty t as a must c vs s r s', aApply p tab actor ty t as = some (a, must, c) →
      γL f ctx as vs → (applyTerm p (sem ctx) cfg (n + 1) ty t vs).run s = .ok (r, s') →
      (∀ w, r = some w → γ f ctx a w) ∧ (must = true → r.isSome) := by
    intro ty t as a must c vs s r s' ha hvs h
    unfold aApply at ha
    rw [termOfT_eq] at ha
    split at ha
    · exact (γL_any_isBot ‹_› hvs).elim
    rw [applyTerm.eq_2] at h
    obtain ⟨term, s1, h1, h2⟩ := bind_ok h
    obtain ⟨term0, ht', he⟩ := liftM_ok h1
    obtain ⟨h_t, h_s⟩ := Prod.mk.inj he
    subst term0
    subst s1
    rw [ht'] at ha
    dsimp only at ha
    cases hk : term.kind with
    | enumVariant k =>
      rw [hk] at ha h2
      simp only [Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl, rfl⟩ := ha
      cases pure_ok h2
      exact ⟨fun w hw => by cases hw; exact ⟨vs, rfl, hvs⟩, fun _ => rfl⟩
    | struct =>
      rw [hk] at ha h2
      simp only [Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl, rfl⟩ := ha
      cases pure_ok h2
      exact ⟨fun w hw => by cases hw; exact ⟨vs, rfl, hvs⟩, fun _ => rfl⟩
    | decl flags ctor ex =>
      rw [hk] at ha h2
      cases ctor with
      | none => cases ha
      | some ctor =>
        cases ctor with
        | internal =>
          dsimp only at ha h2
          split at ha
          · cases ha
          · rename_i hm
            obtain ⟨e, hfind, he⟩ := Option.map_eq_some_iff.mp ha
            simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl, rfl⟩ := he
            obtain ⟨hmem, het, hle⟩ := tabFind_sound hfind
            rw [← het] at h
            exact htabN e hmem ty vs s r s' (leL_sound _ _ hle _ hvs) h
        | external fn =>
          dsimp only at ha h2
          split at ha
          · cases ha
          · rename_i hm
            simp only [hm, Bool.false_eq_true, ↓reduceIte] at h2
            cases hact : actor term.id as with
            | none => rw [hact] at ha; cases ha
            | some am =>
              obtain ⟨a', mustOk⟩ := am
              rw [hact] at ha
              dsimp only at ha
              split at ha
              · cases ha
              rename_i hpm
              simp only [Option.some.injEq, Prod.mk.injEq] at ha
              obtain ⟨rfl, rfl, rfl⟩ := ha
              obtain ⟨g, s2, h3, h4⟩ := bind_ok h2
              cases get_ok h3
              have hctor := M.ctor term as a' mustOk vs s.1 hact hvs
              cases hcv : externCtor ctx term vs s.1 with
              | ok q =>
                obtain ⟨w, st'⟩ := q
                have hcv' : (sem ctx).ctor term vs s.1 = .ok (w, st') := hcv
                rw [hcv'] at h4
                obtain ⟨u, s3, h5, h6⟩ := bind_ok h4
                cases set_ok h5
                cases pure_ok h6
                rcases hctor with ⟨w', st'', hw, hγ⟩ | ⟨hf, -⟩
                · rw [hw] at hcv
                  simp only [ExtResult.ok.injEq, Prod.mk.injEq] at hcv
                  obtain ⟨rfl, rfl⟩ := hcv
                  exact ⟨fun _ h => by cases h; exact hγ, fun _ => rfl⟩
                · rw [hf] at hcv; cases hcv
              | fail =>
                have hcv' : (sem ctx).ctor term vs s.1 = .fail := hcv
                rw [hcv'] at h4
                dsimp only at h4
                split at h4
                · cases pure_ok h4
                  refine ⟨fun _ h => (nomatch h), fun hmo => ?_⟩
                  rcases hctor with ⟨w', st'', hw, -⟩ | ⟨-, hmf⟩
                  · rw [hw] at hcv; cases hcv
                  · rw [hmf] at hmo; cases hmo
                · exact (throw_ok h4).elim
              | unmodeled w =>
                have hcv' : (sem ctx).ctor term vs s.1 = .unmodeled w := hcv
                rw [hcv'] at h4
                exact (throw_ok h4).elim
  refine ⟨?_, ?_, ?_, happly, htabN, ?_, ?_⟩
  · -- evalExpr
    intro e aenv a must c env s r s' ha he h
    cases e with
    | var ty x =>
      obtain ⟨hx, rfl, -⟩ := aExpr_var_inv ha
      obtain ⟨w, hw, hγ⟩ := he.2 x a hx
      rw [evalExpr.eq_2, hw] at h
      cases pure_ok h
      exact ⟨fun v hv => by cases hv; exact hγ, fun _ => rfl⟩
    | constBool ty b =>
      rw [aExpr.eq_2] at ha
      simp only [Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl, rfl⟩ := ha
      rw [evalExpr.eq_3] at h
      cases pure_ok h
      exact ⟨fun v hv => by cases hv; exact ⟨b, rfl, .inr rfl⟩, fun _ => rfl⟩
    | constInt ty i =>
      rw [aExpr.eq_3] at ha
      simp only [Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl, rfl⟩ := ha
      rw [evalExpr.eq_4] at h
      cases pure_ok h
      exact ⟨fun v hv => by cases hv; exact γ_aint ty i, fun _ => rfl⟩
    | constPrim ty nm =>
      rw [aExpr.eq_4] at ha
      split at ha
      · rename_i t hp
        simp only [Option.some.injEq, Prod.mk.injEq] at ha
        obtain ⟨rfl, rfl, rfl⟩ := ha
        have hp' : (sem ctx).prim ty nm = some (.ty t) := hp
        rw [evalExpr.eq_5, hp'] at h
        cases pure_ok h
        exact ⟨fun v hv => by cases hv; exact ⟨t, List.mem_singleton_self _, rfl⟩, fun _ => rfl⟩
      · cases ha
    | «let» ty bs body =>
      obtain ⟨aenv', m1, c1, m2, c2, hb, hbody, rfl, -⟩ := aExpr_let_inv ha
      rw [evalExpr.eq_6] at h
      obtain ⟨o, s1, h1, h2⟩ := bind_ok h
      obtain ⟨hb1, hb2⟩ := ihn.binds _ _ _ _ _ _ _ _ _ hb he h1
      cases o with
      | none =>
        cases pure_ok h2
        refine ⟨fun _ h => (nomatch h), fun hm => ?_⟩
        simp only [Bool.and_eq_true] at hm
        exact hb2 hm.1
      | some env' =>
        obtain ⟨h3, h4⟩ := ihn.expr _ _ _ _ _ _ _ _ _ hbody (hb1 env' rfl) h2
        refine ⟨h3, fun hm => h4 ?_⟩
        simp only [Bool.and_eq_true] at hm
        exact hm.2
    | term ty t args =>
      obtain ⟨as, m1, c1, m2, c2, hargs, happ, rfl, -⟩ := aExpr_term_inv ha
      rw [evalExpr.eq_7] at h
      obtain ⟨o, s1, h1, h2⟩ := bind_ok h
      obtain ⟨ha1, ha2⟩ := ihn.args _ _ _ _ _ _ _ _ _ hargs he h1
      cases o with
      | none =>
        cases pure_ok h2
        refine ⟨fun _ h => (nomatch h), fun hm => ?_⟩
        simp only [Bool.and_eq_true] at hm
        exact ha2 hm.1
      | some vs =>
        obtain ⟨h3, h4⟩ := ihn.apply _ _ _ _ _ _ _ _ _ _ happ (ha1 vs rfl) h2
        refine ⟨h3, fun hm => h4 ?_⟩
        simp only [Bool.and_eq_true] at hm
        exact hm.2
  · -- evalArgs
    intro es aenv as must c env s r s' ha he h
    cases es with
    | nil =>
      rw [aArgs.eq_1] at ha
      simp only [Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl, rfl⟩ := ha
      rw [evalArgs.eq_2] at h
      cases pure_ok h
      exact ⟨fun ws hw => by cases hw; trivial, fun _ => rfl⟩
    | cons e es =>
      obtain ⟨a, as', m1, c1, m2, c2, hae, haes, rfl, rfl, -⟩ := aArgs_cons_inv ha
      rw [evalArgs.eq_3] at h
      obtain ⟨o, s1, h1, h2⟩ := bind_ok h
      obtain ⟨he1, he2⟩ := ihn.expr _ _ _ _ _ _ _ _ _ hae he h1
      cases o with
      | none =>
        cases pure_ok h2
        refine ⟨fun _ h => (nomatch h), fun hm => ?_⟩
        simp only [Bool.and_eq_true] at hm
        exact he2 hm.1
      | some v =>
        obtain ⟨o2, s2, h3, h4⟩ := bind_ok h2
        obtain ⟨hs1, hs2⟩ := ihn.args _ _ _ _ _ _ _ _ _ haes he h3
        cases o2 with
        | none =>
          cases pure_ok h4
          refine ⟨fun _ h => (nomatch h), fun hm => ?_⟩
          simp only [Bool.and_eq_true] at hm
          exact hs2 hm.2
        | some vs =>
          cases pure_ok h4
          exact ⟨fun ws hw => by cases hw; exact ⟨he1 v rfl, hs1 vs rfl⟩, fun _ => rfl⟩
  · -- evalBinds
    intro bs aenv aenv' must c env s r s' ha he h
    cases bs with
    | nil =>
      rw [aBinds.eq_1] at ha
      simp only [Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl, rfl⟩ := ha
      rw [evalBinds.eq_2] at h
      cases pure_ok h
      exact ⟨fun e he' => by cases he'; exact he, fun _ => rfl⟩
    | cons b bs =>
      obtain ⟨x, ty, e⟩ := b
      obtain ⟨a, m1, c1, m2, c2, hae, hx, hbs, rfl, -⟩ := aBinds_cons_inv ha
      rw [evalBinds.eq_3] at h
      obtain ⟨o, s1, h1, h2⟩ := bind_ok h
      obtain ⟨he1, he2⟩ := ihn.expr _ _ _ _ _ _ _ _ _ hae he h1
      cases o with
      | none =>
        cases pure_ok h2
        refine ⟨fun _ h => (nomatch h), fun hm => ?_⟩
        simp only [Bool.and_eq_true] at hm
        exact he2 hm.1
      | some v =>
        dsimp only at h2
        rw [ite_eq_left (he.1 ▸ hx)] at h2
        obtain ⟨hb1, hb2⟩ := ihn.binds _ _ _ _ _ _ _ _ _ hbs (envOK_set he (he1 v rfl) x) h2
        refine ⟨hb1, fun hm => hb2 ?_⟩
        simp only [Bool.and_eq_true] at hm
        exact hm.2
  · -- matchIfLets
    intro ils aenv envs must c env s r s' ha he h
    cases ils with
    | nil =>
      rw [aIfLets.eq_1] at ha
      simp only [Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl, rfl⟩ := ha
      rw [matchIfLets.eq_2] at h
      cases pure_ok h
      exact matchOK_some he _
    | cons il ils =>
      obtain ⟨a, m1, c1, envs1, m2, rs, hae, hpat, hrs, rfl, rfl, -⟩ := aIfLets_cons_inv ha
      rw [matchIfLets.eq_3] at h
      obtain ⟨o, s1, h1, h2⟩ := bind_ok h
      obtain ⟨he1, he2⟩ := ihn.expr _ _ _ _ _ _ _ _ _ hae he h1
      cases o with
      | none =>
        cases pure_ok h2
        refine ⟨fun _ h => (nomatch h), fun hm => ?_⟩
        simp only [Bool.and_eq_true] at hm
        exact he2 hm.1.1
      | some v =>
        obtain ⟨g, s2, h3, h4⟩ := bind_ok h2
        cases get_ok h3
        dsimp only at h4
        obtain ⟨o2, s3, h5, h6⟩ := bind_ok h4
        obtain ⟨r1, hmp, hr1⟩ := liftM_ok h5
        obtain ⟨r1', hmp', hok1⟩ := aPat_prog M p s1.1 il.lhs a aenv v env envs1 m2 hpat (he1 v rfl) he
        rw [hmp] at hmp'
        have hE1 : r1 = r1' := Except.ok.inj hmp'
        have hE2 : o2 = r1 := (Prod.mk.inj hr1).1
        subst hE1 hE2
        cases o2 with
        | none =>
          cases pure_ok h6
          refine ⟨fun _ h => (nomatch h), fun hm => ?_⟩
          simp only [Bool.and_eq_true] at hm
          exact hok1.2 hm.1.2
        | some env1 =>
          obtain ⟨ae, hae', he2'⟩ := hok1.1 env1 rfl
          obtain ⟨⟨e2, m3, c3⟩, hy, hyq⟩ := mapM_some_mem hrs ae hae'
          have := ihn.iflets _ _ _ _ _ _ _ _ _ hyq he2' h6
          exact matchOK_flat hy this (m1 && m2)
  · -- matchRule
    intro ins rl envs must c vs s r s' ha hins h
    obtain ⟨envs0, m, rs, hpa, hrs, rfl, rfl, -⟩ := aRule_inv ha
    rw [matchRule.eq_2] at h
    obtain ⟨g, s1, h1, h2⟩ := bind_ok h
    cases get_ok h1
    dsimp only at h2
    obtain ⟨o, s2, h3, h4⟩ := bind_ok h2
    obtain ⟨r0, hma, hr0⟩ := liftM_ok h3
    obtain ⟨r0', hma', hok0⟩ := aPatArgs_prog M p s.1 rl.args ins _ vs _ envs0 m hpa hins
      (envOK_empty rl.vars.length)
    rw [hma] at hma'
    have hE1 : r0 = r0' := Except.ok.inj hma'
    have hE2 : o = r0 := (Prod.mk.inj hr0).1
    have hE3 : s2 = s := (Prod.mk.inj hr0).2
    subst hE1 hE2 hE3
    cases o with
    | none =>
      cases pure_ok h4
      refine ⟨fun _ h => (nomatch h), fun hm' => ?_⟩
      simp only [Bool.and_eq_true] at hm'
      exact hok0.2 hm'.1
    | some env0 =>
      obtain ⟨ae, hae, he0⟩ := hok0.1 env0 rfl
      obtain ⟨⟨e2, m3, c3⟩, hy, hyq⟩ := mapM_some_mem hrs ae hae
      have := ihn.iflets _ _ _ _ _ _ _ _ _ hyq he0 h4
      exact matchOK_flat hy this m

end PC

end Backend.Proof.Prg
