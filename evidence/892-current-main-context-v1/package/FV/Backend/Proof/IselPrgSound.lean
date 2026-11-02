import FV.Backend.Proof.IselPrgPC

/-!
# Progress of the ISLE lowering (V7): the progress theorem

`progress`: under the extern helpers' `Model`, the hand-checked rules' `HandOk`, overlap checking
off and a checked table (`chkTab`), every table term run at a fuel of at least its entry's fuel
returns (never throws), with a value its output describes, surely a value if `osome`
(`Progress`, `IselPrgModel`).

By strong induction on the fuel. Partial correctness (`IselPrgPC`) gives every property of a
run that returns; here we show runs return (`ProgAt`, by induction on the fuel, assuming
`Progress` below it): every cost the abstract interpreter computes covers the interpreter's fuel
use (`evalExpr (n+1)` evaluates its parts at `n`; an internal call `applyTerm n` is covered by the
callee entry's fuel `e.fu ≤ n`; `selectRule`'s fuel `selCost` covers `tryRule (2 + ilc)` →
`matchRule (1 + ilc)` → `matchIfLets ilc` for every rule it may try, `reach`), and the
interpreter's only other errors (unmodeled helpers and constants, values of the wrong shape,
unbound variables, failing infallible helpers, a total term without a matching rule) are ruled out
by the checker's acceptance (`aPat_prog`, `Model`, exhaustiveness via `select_none_absurd`).
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Interp Isle.Aarch64

variable {f : Clif.Function} {ctx : Ctx}

section Prog
variable {p : Program} {tab : PTab} {aext : TermId → PA → Option (List (List PA) × Bool)}
  {actor : TermId → List PA → Option (PA × Bool)} {aidata : Nat → Option (List PA)}
  {hand : RuleId → Option (Nat × PA)} {cfg : Config}

/-! ## Costs are positive -/

theorem aExpr_cost_pos {e : Isle.Expr} {aenv : AEnv} {a : PA} {must : Bool} {c : Nat}
    (h : aExpr p tab actor e aenv = some (a, must, c)) : 1 ≤ c := by
  cases e with
  | var => obtain ⟨-, -, rfl⟩ := aExpr_var_inv h; exact Nat.le_refl 1
  | constBool =>
    rw [aExpr.eq_2] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    omega
  | constInt =>
    rw [aExpr.eq_3] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    omega
  | constPrim =>
    rw [aExpr.eq_4] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      omega
    · cases h
  | «let» => obtain ⟨_, _, _, _, _, -, -, -, rfl⟩ := aExpr_let_inv h; omega
  | term => obtain ⟨_, _, _, _, _, -, -, -, rfl⟩ := aExpr_term_inv h; omega

theorem aArgs_cost_pos {es : List Isle.Expr} {aenv : AEnv} {as : List PA} {must : Bool} {c : Nat}
    (h : aArgs p tab actor es aenv = some (as, must, c)) : 1 ≤ c := by
  cases es with
  | nil =>
    rw [aArgs.eq_1] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    omega
  | cons => obtain ⟨_, _, _, _, _, _, -, -, -, -, rfl⟩ := aArgs_cons_inv h; omega

theorem aBinds_cost_pos {bs : List (VarId × TypeId × Isle.Expr)} {aenv aenv' : AEnv}
    {must : Bool} {c : Nat} (h : aBinds p tab actor bs aenv = some (aenv', must, c)) : 1 ≤ c := by
  cases bs with
  | nil =>
    rw [aBinds.eq_1] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    omega
  | cons b bs =>
    obtain ⟨x, ty, e⟩ := b
    obtain ⟨_, _, _, _, _, -, -, -, -, rfl⟩ := aBinds_cons_inv h
    omega

theorem aIfLets_cost_pos {ils : List IfLet} {aenv : AEnv} {envs : List AEnv} {must : Bool}
    {c : Nat} (h : aIfLets p tab aext actor aidata ils aenv = some (envs, must, c)) : 1 ≤ c := by
  cases ils with
  | nil =>
    rw [aIfLets.eq_1] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    omega
  | cons => obtain ⟨_, _, _, _, _, _, -, -, -, -, -, rfl⟩ := aIfLets_cons_inv h; omega

/-! ## Runs return -/

variable (f ctx p tab aext actor aidata cfg) in
/-- **Runs return at fuel `n`**: from the costs the abstract interpreter computes. -/
structure ProgAt (n : Nat) : Prop where
  expr : ∀ e aenv a must c env s, aExpr p tab actor e aenv = some (a, must, c) → c ≤ n →
    EnvOK f ctx aenv env →
    ∃ r s', (evalExpr p (sem ctx) cfg n e env).run s = .ok (r, s')
  args : ∀ es aenv as must c env s, aArgs p tab actor es aenv = some (as, must, c) → c ≤ n →
    EnvOK f ctx aenv env →
    ∃ r s', (evalArgs p (sem ctx) cfg n es env).run s = .ok (r, s')
  binds : ∀ bs aenv aenv' must c env s, aBinds p tab actor bs aenv = some (aenv', must, c) →
    c ≤ n → EnvOK f ctx aenv env →
    ∃ r s', (evalBinds p (sem ctx) cfg n bs env).run s = .ok (r, s')
  iflets : ∀ ils aenv envs must c env s,
    aIfLets p tab aext actor aidata ils aenv = some (envs, must, c) → c ≤ n →
    EnvOK f ctx aenv env →
    ∃ r s', (matchIfLets p (sem ctx) cfg n ils env).run s = .ok (r, s')
  mrule : ∀ ins rl envs must c vs s,
    aRule p tab aext actor aidata ins rl = some (envs, must, c) → c + 1 ≤ n → γL f ctx ins vs →
    ∃ r s', (matchRule p (sem ctx) cfg n rl vs).run s = .ok (r, s')

variable (Mo : Model f ctx aext actor aidata) (H : HandOk f ctx p cfg tab hand)
  (hc : cfg.checkOverlap = false) (htab : chkTab p tab aext actor aidata hand = true)

include Mo in
/-- **An application returns**, from `Progress` at its fuel for internal terms. -/
theorem apply_prog {n : Nat} (hP : Progress f ctx p cfg tab n) {ty : TypeId} {t : TermId}
    {as : List PA} {a : PA} {must : Bool} {c : Nat} {vs : List V} (s : LState × Array RuleId)
    (ha : aApply p tab actor ty t as = some (a, must, c)) (hcn : c ≤ n) (hvs : γL f ctx as vs) :
    ∃ r s', (applyTerm p (sem ctx) cfg n ty t vs).run s = .ok (r, s') := by
  obtain ⟨st, tr⟩ := s
  unfold aApply at ha
  rw [termOfT_eq] at ha
  split at ha
  · exact (γL_any_isBot ‹_› hvs).elim
  cases ht : termOf p t with
  | error e => rw [ht] at ha; cases ha
  | ok term =>
    rw [ht] at ha
    dsimp only at ha
    cases hk : term.kind with
    | enumVariant k =>
      rw [hk] at ha
      simp only [Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl, rfl⟩ := ha
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      refine ⟨some ((sem ctx).mkData ty k vs), (st, tr), ?_⟩
      rw [applyTerm.eq_2]
      simp only [M.run_bind, ht, M.run_liftM_ok, M.except_ok_bind, hk]
      rfl
    | struct =>
      rw [hk] at ha
      simp only [Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl, rfl⟩ := ha
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      refine ⟨some ((sem ctx).mkData ty 0 vs), (st, tr), ?_⟩
      rw [applyTerm.eq_2]
      simp only [M.run_bind, ht, M.run_liftM_ok, M.except_ok_bind, hk]
      rfl
    | decl flags ctor ex =>
      rw [hk] at ha
      cases ctor with
      | none => cases ha
      | some ctor =>
        cases ctor with
        | internal =>
          dsimp only at ha
          split at ha
          · cases ha
          · obtain ⟨e, hfind, he⟩ := Option.map_eq_some_iff.mp ha
            simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl, rfl⟩ := he
            obtain ⟨hmem, het, hle⟩ := tabFind_sound hfind
            obtain ⟨v, st', tr', hrun, -⟩ := hP e hmem hcn ty vs st tr (leL_sound _ _ hle _ hvs)
            rw [het] at hrun
            exact ⟨v, (st', tr'), hrun⟩
        | external fn =>
          dsimp only at ha
          split at ha
          · cases ha
          · rename_i hm
            simp only [Bool.not_eq_true] at hm
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
              obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
              rw [applyTerm.eq_2]
              simp only [M.run_bind, ht, M.run_liftM_ok, M.except_ok_bind, hk, hm,
                Bool.false_eq_true, ↓reduceIte, M.run_get]
              rcases Mo.ctor term as a' mustOk vs st hact hvs with ⟨w, st', hw, -⟩ | ⟨hf, hmf⟩
              · have hw' : (sem ctx).ctor term vs st = .ok (w, st') := hw
                simp only [hw', M.run_bind, M.run_set, M.except_ok_bind, M.run_pure]
                exact ⟨_, _, rfl⟩
              · have hf' : (sem ctx).ctor term vs st = .fail := hf
                subst hmf
                have hpart : flags.isPartial = true := by
                  cases hfp : flags.isPartial
                  · simp [hfp] at hpm
                  · rfl
                simp only [hf', hpart, ↓reduceIte, M.run_pure]
                exact ⟨_, _, rfl⟩

include Mo H hc htab in
/-- **Runs return**, at every fuel below which `Progress` holds. -/
theorem progAt : ∀ n, (∀ m < n, Progress f ctx p cfg tab m) →
    ProgAt f ctx p tab aext actor aidata cfg n := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro e aenv a must c env s ha hc0 _
      have := aExpr_cost_pos ha; omega
    · intro es aenv as must c env s ha hc0 _
      have := aArgs_cost_pos ha; omega
    · intro bs aenv aenv' must c env s ha hc0 _
      have := aBinds_cost_pos ha; omega
    · intro ils aenv envs must c env s ha hc0 _
      have := aIfLets_cost_pos ha; omega
    · intro ins rl envs must c vs s _ hc0 _
      omega
  | succ n ih =>
  intro hP
  have ihn := ih fun m hm => hP m (by omega)
  have pc := pcAt Mo H hc htab n
  have hexpr : ∀ e aenv a must c env s, aExpr p tab actor e aenv = some (a, must, c) →
      c ≤ n + 1 → EnvOK f ctx aenv env →
      ∃ r s', (evalExpr p (sem ctx) cfg (n + 1) e env).run s = .ok (r, s') := by
    intro e aenv a must c env s ha hcn he
    cases e with
    | var ty x =>
      obtain ⟨hx, -, -⟩ := aExpr_var_inv ha
      obtain ⟨w, hw, -⟩ := he.2 x a hx
      exact ⟨_, _, by rw [evalExpr.eq_2, hw]; rfl⟩
    | constBool => exact ⟨_, _, by rw [evalExpr.eq_3]; rfl⟩
    | constInt => exact ⟨_, _, by rw [evalExpr.eq_4]; rfl⟩
    | constPrim ty nm =>
      rw [aExpr.eq_4] at ha
      split at ha
      · rename_i t hp
        have hp' : (sem ctx).prim ty nm = some (.ty t) := hp
        exact ⟨_, _, by rw [evalExpr.eq_5, hp']; rfl⟩
      · cases ha
    | «let» ty bs body =>
      obtain ⟨aenv', m1, c1, m2, c2, hb, hbody, -, rfl⟩ := aExpr_let_inv ha
      obtain ⟨o, s1, h1⟩ := ihn.binds _ _ _ _ _ _ s hb (by omega) he
      rw [evalExpr.eq_6, M.run_bind, h1, M.except_ok_bind]
      cases o with
      | none => exact ⟨_, _, rfl⟩
      | some env' =>
        have hok := (pc.binds _ _ _ _ _ _ _ _ _ hb he h1).1 env' rfl
        exact ihn.expr _ _ _ _ _ _ s1 hbody (by omega) hok
    | term ty t args =>
      obtain ⟨as, m1, c1, m2, c2, hargs, happ, -, rfl⟩ := aExpr_term_inv ha
      obtain ⟨o, s1, h1⟩ := ihn.args _ _ _ _ _ _ s hargs (by omega) he
      rw [evalExpr.eq_7, M.run_bind, h1, M.except_ok_bind]
      cases o with
      | none => exact ⟨_, _, rfl⟩
      | some vs =>
        have hvs := (pc.args _ _ _ _ _ _ _ _ _ hargs he h1).1 vs rfl
        exact apply_prog Mo (hP n (by omega)) s1 happ (by omega) hvs
  have hiflets : ∀ ils aenv envs must c env s,
      aIfLets p tab aext actor aidata ils aenv = some (envs, must, c) → c ≤ n + 1 →
      EnvOK f ctx aenv env →
      ∃ r s', (matchIfLets p (sem ctx) cfg (n + 1) ils env).run s = .ok (r, s') := by
    intro ils aenv envs must c env s ha hcn he
    cases ils with
    | nil => exact ⟨_, _, by rw [matchIfLets.eq_2]; rfl⟩
    | cons il ils =>
      obtain ⟨a, m1, c1, envs1, m2, rs, hae, hpat, hrs, -, -, rfl⟩ := aIfLets_cons_inv ha
      obtain ⟨o, s1, h1⟩ := ihn.expr _ _ _ _ _ _ s hae (by omega) he
      rw [matchIfLets.eq_3, M.run_bind, h1, M.except_ok_bind]
      cases o with
      | none => exact ⟨_, _, rfl⟩
      | some v =>
        have hv := (pc.expr _ _ _ _ _ _ _ _ _ hae he h1).1 v rfl
        obtain ⟨r1, hr1, hok1⟩ := aPat_prog Mo p s1.1 il.lhs a aenv v env envs1 m2 hpat hv he
        dsimp only
        rw [M.run_bind, M.run_get, M.except_ok_bind]
        dsimp only
        rw [M.run_bind, hr1, M.run_liftM_ok, M.except_ok_bind]
        cases r1 with
        | none => exact ⟨_, _, rfl⟩
        | some env1 =>
          obtain ⟨ae, hae', he1⟩ := hok1.1 env1 rfl
          obtain ⟨⟨e2, m3, c3⟩, hy, hyq⟩ := mapM_some_mem hrs ae hae'
          have hc3 : c3 ≤ maxCost (rs.map (·.2.2)) := le_maxCost (List.mem_map_of_mem hy)
          exact ihn.iflets _ _ _ _ _ _ s1 hyq (by omega) he1
  refine ⟨hexpr, ?_, ?_, hiflets, ?_⟩
  · -- evalArgs
    intro es aenv as must c env s ha hcn he
    cases es with
    | nil => exact ⟨_, _, by rw [evalArgs.eq_2]; rfl⟩
    | cons e es =>
      obtain ⟨a, as', m1, c1, m2, c2, hae, haes, -, -, rfl⟩ := aArgs_cons_inv ha
      obtain ⟨o, s1, h1⟩ := ihn.expr _ _ _ _ _ _ s hae (by omega) he
      rw [evalArgs.eq_3, M.run_bind, h1, M.except_ok_bind]
      cases o with
      | none => exact ⟨_, _, rfl⟩
      | some v =>
        obtain ⟨o2, s2, h2⟩ := ihn.args _ _ _ _ _ _ s1 haes (by omega) he
        dsimp only
        rw [M.run_bind, h2, M.except_ok_bind]
        cases o2 <;> exact ⟨_, _, rfl⟩
  · -- evalBinds
    intro bs aenv aenv' must c env s ha hcn he
    cases bs with
    | nil => exact ⟨_, _, by rw [evalBinds.eq_2]; rfl⟩
    | cons b bs =>
      obtain ⟨x, ty, e⟩ := b
      obtain ⟨a, m1, c1, m2, c2, hae, hx, hbs, -, rfl⟩ := aBinds_cons_inv ha
      obtain ⟨o, s1, h1⟩ := ihn.expr _ _ _ _ _ _ s hae (by omega) he
      rw [evalBinds.eq_3, M.run_bind, h1, M.except_ok_bind]
      cases o with
      | none => exact ⟨_, _, rfl⟩
      | some v =>
        have hv := (pc.expr _ _ _ _ _ _ _ _ _ hae he h1).1 v rfl
        dsimp only
        rw [ite_eq_left (he.1 ▸ hx)]
        exact ihn.binds _ _ _ _ _ _ s1 hbs (by omega) (envOK_set he hv x)
  · -- matchRule
    intro ins rl envs must c vs s ha hcn hins
    obtain ⟨envs0, m, rs, hpa, hrs, -, -, rfl⟩ := aRule_inv ha
    obtain ⟨r0, hr0, hok0⟩ := aPatArgs_prog Mo p s.1 rl.args ins _ vs _ envs0 m hpa hins
      (envOK_empty rl.vars.length)
    rw [matchRule.eq_2, M.run_bind, M.run_get, M.except_ok_bind]
    dsimp only
    rw [M.run_bind, hr0, M.run_liftM_ok, M.except_ok_bind]
    cases r0 with
    | none => exact ⟨_, _, rfl⟩
    | some env0 =>
      obtain ⟨ae, hae, he0⟩ := hok0.1 env0 rfl
      obtain ⟨⟨e2, m3, c3⟩, hy, hyq⟩ := mapM_some_mem hrs ae hae
      have hc3 : c3 ≤ maxCost (rs.map (·.2.2)) := le_maxCost (List.mem_map_of_mem hy)
      exact ihn.iflets _ _ _ _ _ _ s hyq (by omega) he0

include hc in
/-- **Rule selection returns**, when the fuel covers `selCost` of the rules it may try. -/
theorem select_prog {term : Term} {ins : List PA} {out : PA} {osome : Bool} {vs : List V}
    (hins : γL f ctx ins vs) :
    ∀ (rs : List Rule) (n : Nat) (cs : List (Nat × Nat)) (s : LState × Array RuleId),
      (∀ m < n, PCAt f ctx p tab aext actor aidata cfg m) →
      (∀ m < n, ProgAt f ctx p tab aext actor aidata cfg m) →
      (reach p tab aext actor aidata ins rs).mapM
        (ruleCost p tab aext actor aidata hand ins out osome) = some cs →
      selCost cs ≤ n →
      ∃ r s', (selectRule p (sem ctx) cfg n term rs vs).run s = .ok (r, s')
  | [], n, cs, s, _, _, hcs, hn => by
    simp only [reach, List.mapM_nil, pure, Option.some.injEq] at hcs
    subst hcs
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [selCost] at hn; omega⟩
    exact ⟨_, _, by rw [selectRule.eq_2]; rfl⟩
  | r :: rs, n, cs, s, pcs, progs, hcs, hn => by
    have hreach : reach p tab aext actor aidata ins (r :: rs) =
        if mustRule p tab aext actor aidata ins r then [r]
        else r :: reach p tab aext actor aidata ins rs := rfl
    have hhead : ∃ ilc rc cs', ruleCost p tab aext actor aidata hand ins out osome r =
        some (ilc, rc) ∧ cs = (ilc, rc) :: cs' ∧
        (mustRule p tab aext actor aidata ins r = false →
          (reach p tab aext actor aidata ins rs).mapM
            (ruleCost p tab aext actor aidata hand ins out osome) = some cs') := by
      rw [hreach] at hcs
      split at hcs
      · rw [List.mapM_cons] at hcs
        obtain ⟨⟨ilc, rc⟩, h1, hcs⟩ := obind_some hcs
        obtain ⟨cs', h2, hcs⟩ := obind_some hcs
        simp only [pure, Option.some.injEq] at hcs
        exact ⟨ilc, rc, cs', h1, hcs.symm, fun h => by simp_all⟩
      · rw [List.mapM_cons] at hcs
        obtain ⟨⟨ilc, rc⟩, h1, hcs⟩ := obind_some hcs
        obtain ⟨cs', h2, hcs⟩ := obind_some hcs
        simp only [pure, Option.some.injEq] at hcs
        exact ⟨ilc, rc, cs', h1, hcs.symm, fun _ => h2⟩
    obtain ⟨ilc, rc, cs', hrc, rfl, hrest⟩ := hhead
    simp only [selCost] at hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨envs, mu, haR, -, -⟩ := ruleCost_inv hrc
    obtain ⟨res, s1, hm⟩ := (progs j (by omega)).mrule _ _ _ _ _ _ s haR (by omega) hins
    rw [selectRule_cons_ok hc (tryRule_ok hm)]
    cases res with
    | some env => exact ⟨_, _, rfl⟩
    | none =>
      cases hmr : mustRule p tab aext actor aidata ins r
      · exact select_prog hins rs (j + 1) cs' s (fun m hm => pcs m (by omega))
          (fun m hm => progs m (by omega)) (hrest hmr) (by omega)
      · exact (mustRule_fail (pcs j (by omega)) hmr hins hm).elim

end Prog

/-! ## The theorem -/

/-- **Progress of the ISLE runs of the table terms.** Under the extern helpers' model `M`, the
hand-checked rules' obligation `H`, overlap checking off and a checked table, every entry of the
table, run at a fuel of at least its own fuel on arguments its inputs describe, returns (never
throws an interpreter error: no unmodeled helper or constant, ill-shaped value, failing
infallible helper, total term without a matching rule, or exhausted fuel), with a value its
output describes, and surely a value if its `osome`. -/
theorem progress {p : Program} {tab : PTab} {aext : TermId → PA → Option (List (List PA) × Bool)}
    {actor : TermId → List PA → Option (PA × Bool)} {aidata : Nat → Option (List PA)}
    {hand : RuleId → Option (Nat × PA)} {cfg : Config}
    (M : Model f ctx aext actor aidata) (H : HandOk f ctx p cfg tab hand)
    (hc : cfg.checkOverlap = false) (htab : chkTab p tab aext actor aidata hand = true) :
    ∀ n, Progress f ctx p cfg tab n := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro e he hfu ty args st tr hins
  obtain ⟨term, flags, ex, cs, ht, hk, hm, hcs, hbound, hex⟩ := chkEntry_inv (chkTab_mem htab he)
  have pcs := pcAt M H hc htab
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have progs : ∀ m ≤ n, ProgAt f ctx p tab aext actor aidata cfg m :=
    fun m hm => progAt M H hc htab m fun m' hm' => ih m' (by omega)
  have hrun : ∃ r s', (applyTerm p (sem ctx) cfg (n + 1) ty e.t args).run (st, tr) = .ok (r, s') := by
    rw [applyTerm_internal_run ht hk hm]
    obtain ⟨sel, s1, hsel⟩ := select_prog hc hins (p.rulesOf e.t) n cs (st, tr)
      (fun m _ => pcs m) (fun m hm => progs m (by omega)) hcs (by omega)
    rw [hsel, Isle.Interp.M.except_ok_bind]
    dsimp only
    cases sel with
    | none =>
      cases hpart : flags.isPartial
      · rw [hpart] at hex
        simp only [Bool.false_and, Bool.false_or] at hex
        exact (select_none_absurd hc (fun m _ => pcs m) hsel hex hins).elim
      · simp only [↓reduceIte, Isle.Interp.M.run_pure]
        exact ⟨_, _, rfl⟩
    | some re =>
      obtain ⟨rl, env⟩ := re
      obtain ⟨hreach, m, hm', hmatch⟩ := select_some_reach hc (fun m _ => pcs m) hsel hins
      obtain ⟨⟨ilc, rc⟩, hmem, hrc⟩ := mapM_some_mem hcs rl hreach
      have hrcn : rc ≤ n := by
        have := le_maxCost (List.mem_map_of_mem (f := (·.2)) hmem)
        omega
      obtain ⟨envs, mu, haR, hhand, hnohand⟩ := ruleCost_inv hrc
      have hev : ∃ ev s2, (evalExpr p (sem ctx) cfg n rl.rhs env).run s1 = .ok (ev, s2) := by
        cases hh : hand rl.id with
        | some ca =>
          obtain ⟨c, a⟩ := ca
          obtain ⟨hrcc, -⟩ := hhand c a hh
          obtain ⟨v, s'', hv, -⟩ := H e he rl (reach_sub hreach) c a hh args hins m (st, tr) env
            s1 hmatch n (by omega)
          exact ⟨_, _, hv⟩
        | none =>
          obtain ⟨ae, hae, heok⟩ := ((pcs m).mrule _ _ _ _ _ _ _ _ _ haR hins hmatch).1 env rfl
          obtain ⟨a, mu', c, hae', -, -, hcrc⟩ := hnohand hh ae hae
          exact (progs n (Nat.le_refl n)).expr _ _ _ _ _ _ s1 hae' (by omega) heok
      obtain ⟨ev, s2, hev⟩ := hev
      rw [Isle.Interp.M.run_bind, hev, Isle.Interp.M.except_ok_bind]
      cases ev with
      | some v => exact ⟨_, _, Isle.Interp.M.run_fire_pure _ _ _⟩
      | none => exact ⟨_, _, rfl⟩
  obtain ⟨r, ⟨st', tr'⟩, hrun⟩ := hrun
  obtain ⟨h1, h2⟩ := (pcs (n + 1)).entry e he ty args (st, tr) r (st', tr') hins hrun
  exact ⟨r, st', tr', hrun, h2, h1⟩

end Backend.Proof.Prg
