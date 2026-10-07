import FV.Backend.Proof.DefGenSound

/-!
# Definedness of the ISLE runs: soundness of the abstract interpreter (proof)

`soundAt`: by induction on the fuel, every abstract evaluation of the terms `T` (whose rules
check, `TabOK`) describes the run (`SoundAt`), given the model facts (`DModel`). The `let` case
closes the binding environment: `γ` reads the environment only at the variables an abstract value
mentions (`γ_agree`) and `evalBinds` changes only the let-bound slots (`evalBinds_frame`).
`dRoot`: a root term's run (`lower`, `lower_branch`) whose rules check, are hand-checked or never
match.
-/

namespace Backend.Proof.DefGen

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Spill Backend.Proof.Kill
  Backend.Proof.DefRun Isle Isle.Aarch64 Isle.Interp

/-! ## Restriction: `γ` reads only the mentioned variables -/

section Restrict
variable {c : SC}

/-- Two environments agree on the variables `xs`. -/
def Agree (xs : List Nat) (env env' : Isle.Interp.Env V) : Prop :=
  ∀ x ∈ xs, env[x]? = env'[x]?

theorem CallDefsOf_agree {D : Nat → Prop} {env env' : Isle.Interp.Env V} {x : Nat}
    (hx : env[x]? = env'[x]?) {ds : List Reg} (h : CallDefsOf c D env x ds) :
    CallDefsOf c D env' x ds := by
  obtain ⟨w, h1, h2⟩ := h
  exact ⟨w, by rw [← hx]; exact h1, h2⟩

mutual
/-- **`γ` depends on the environment only at the mentioned variables.** -/
theorem γ_agree : ∀ (a : A) {D : Nat → Prop} {env env' : Isle.Interp.Env V},
    Agree (mentions a) env env' → ∀ {v : V}, γ c a D env v → γ c a D env' v
  | .top, _, _, _, _, _, h => h
  | .cl _ _, _, _, _, _, _, h => h
  | .wr _, _, _, _, _, _, h => h
  | .ty _ _, _, _, _, _, _, h => h
  | .sym x, _, _, _, hg, _, h => by
    have hx := hg x (by simp [mentions])
    simp only [γ] at h ⊢
    rw [← hx]
    exact h
  | .aft ys b, _, _, _, hg, _, h => fun D' hD hys =>
    γ_agree b (fun x hx => hg x (by simp [mentions, hx]))
      (h D' hD fun y hy w hw => hys y hy w (by rw [← hg y (by simp [mentions, hy])]; exact hw))
  | .data _ _ fs, _, _, _, hg, _, h => by
    obtain ⟨vs, rfl, hl⟩ := h
    exact ⟨vs, rfl, γL_agree fs (fun x hx => hg x (by simpa [mentions] using hx)) hl⟩
  | .regs as, _, _, _, hg, _, h => by
    obtain ⟨rs, rfl, hl⟩ := h
    exact ⟨rs, rfl, γL_agree as (fun x hx => hg x (by simpa [mentions] using hx)) hl⟩
  | .crl xs, _, _, _, hg, _, h => by
    obtain ⟨ds, rfl, ho, hl⟩ := h
    exact ⟨ds, rfl, ho, fun x hx => CallDefsOf_agree (hg x (by simpa [mentions] using hx)) (hl x hx)⟩
  | .cinfo xs, _, _, _, hg, _, h => by
    obtain ⟨ci, rfl, hu, ho, hl⟩ := h
    exact ⟨ci, rfl, hu, ho, fun x hx =>
      CallDefsOf_agree (hg x (by simpa [mentions] using hx)) (hl x hx)⟩
/-- `γL` depends on the environment only at the mentioned variables. -/
theorem γL_agree : ∀ (as : List A) {D : Nat → Prop} {env env' : Isle.Interp.Env V},
    Agree (mentionsL as) env env' → ∀ {vs : List V}, γL c as D env vs → γL c as D env' vs
  | [], _, _, _, _, [], h => h
  | a :: as, _, _, _, hg, _ :: _, h =>
    ⟨γ_agree a (fun x hx => hg x (by simp [mentionsL, hx])) h.1,
     γL_agree as (fun x hx => hg x (by simp [mentionsL, hx])) h.2⟩
  | [], _, _, _, _, _ :: _, h => h.elim
  | _ :: _, _, _, _, _, [], h => h.elim
end

theorem unbind_length : ∀ (xs : List Nat) (e : AEnv), (unbind e xs).length = e.length
  | [], _ => rfl
  | x :: xs, e => by rw [unbind, unbind_length xs]; simp

theorem unbind_get_not : ∀ (xs : List Nat) (e : AEnv) {x : Nat}, x ∉ xs →
    (unbind e xs)[x]? = e[x]?
  | [], _, _, _ => rfl
  | y :: ys, e, x, hx => by
    rw [unbind, unbind_get_not ys _ (fun h => hx (List.mem_cons_of_mem _ h)), List.getElem?_set]
    have : y ≠ x := fun h => hx (h ▸ List.mem_cons_self)
    simp [this]

theorem unbind_get_mem : ∀ (xs : List Nat) (e : AEnv) {x : Nat}, x ∈ xs →
    ∀ a, (unbind e xs)[x]? ≠ some (some a)
  | y :: ys, e, x, hx, a => by
    rw [unbind]
    by_cases h : x ∈ ys
    · exact unbind_get_mem ys _ h a
    · have hxy : x = y := by
        rcases List.mem_cons.mp hx with h' | h'
        · exact h'
        · exact absurd h' h
      subst hxy
      rw [unbind_get_not ys _ h, List.getElem?_set]
      split <;> simp_all

theorem noMention_get {xs : List Nat} {e : AEnv} (h : noMention xs e = true) {x : Nat} {b : A}
    (hx : e[x]? = some (some b)) : ∀ y ∈ mentions b, y ∉ xs := by
  unfold noMention at h
  rw [List.all_eq_true] at h
  have h1 := h _ (List.mem_of_getElem? hx)
  simp only [List.all_eq_true] at h1
  intro y hy hyx
  have h2 := h1 y hy
  simp [hyx] at h2

theorem unboundAt_get {e : AEnv} {x : Nat} (h : unboundAt e x = true) : e[x]? = some none := by
  unfold unboundAt at h
  split at h
  · assumption
  · cases h

theorem letClose_inv {ty : TypeId} {xs : List Nat} {a b : A} {e e' : AEnv}
    (h : letClose ty xs a e = some (b, e')) :
    noMention xs (unbind e xs) = true ∧ e' = unbind e xs ∧ fitsA e F a b = true ∧
      ∃ z, b = tyA z ty := by
  unfold letClose at h
  split at h
  · rename_i hn
    split at h
    · rename_i hf
      cases h
      exact ⟨hn, rfl, hf, false, rfl⟩
    · split at h
      · rename_i hf
        cases h
        exact ⟨hn, rfl, hf, true, rfl⟩
      · cases h
  · cases h

/-- **Leaving a `let`**: the let-bound variables (unbound before) are unbound again, the other
slots are those of the outer environment, and no remaining description mentions a let-bound
variable. -/
theorem EnvOK.letClose {D D' : Nat → Prop} {env env1 : Isle.Interp.Env V} {e e2 : AEnv}
    {xs : List Nat} (he : EnvOK c D env e) (hub : xs.all (unboundAt e) = true)
    (hsz : env1.size = env.size) (hfr : ∀ x, x ∉ xs → env1[x]? = env[x]?)
    (he2 : EnvOK c D' env1 e2) (hnm : noMention xs (unbind e2 xs) = true) :
    EnvOK c D' env (unbind e2 xs) := by
  refine ⟨by rw [unbind_length, he2.1, hsz], fun x => ⟨fun hx => ?_, fun a ha => ?_⟩⟩
  · by_cases hm : x ∈ xs
    · rw [List.all_eq_true] at hub
      exact (he.2 x).1 (unboundAt_get (hub x hm))
    · rw [unbind_get_not _ _ hm] at hx
      rw [← hfr x hm]
      exact (he2.2 x).1 hx
  · by_cases hm : x ∈ xs
    · exact absurd ha (unbind_get_mem _ _ hm a)
    · have ha' := ha
      rw [unbind_get_not _ _ hm] at ha'
      obtain ⟨w, hw, hg⟩ := (he2.2 x).2 a ha'
      refine ⟨w, by rw [← hfr x hm]; exact hw, γ_agree a (fun y hy => ?_) hg⟩
      exact hfr y (noMention_get hnm ha y hy)

end Restrict

/-! ## `evalBinds` changes only the let-bound slots -/

theorem evalBinds_frame {ctx : Ctx} {p : Program} {cfg : Config} :
    ∀ (n : Nat) (bs : List (VarId × TypeId × Isle.Expr)) (env env1 : Isle.Interp.Env V)
      (st st' : LState × Array RuleId),
    (evalBinds p (sem ctx) cfg n bs env).run st = .ok (some env1, st') →
    env1.size = env.size ∧ ∀ x, x ∉ bs.map (·.1) → env1[x]? = env[x]?
  | 0, _, _, _, _, _, h => by rw [evalBinds.eq_1] at h; exact (throw_ok h).elim
  | _ + 1, [], _, _, _, _, h => by
    rw [evalBinds.eq_2] at h
    cases pure_ok h
    exact ⟨rfl, fun _ _ => rfl⟩
  | n + 1, (x, ty, ex) :: bs, env, env1, st, st', h => by
    rw [evalBinds.eq_3] at h
    obtain ⟨o, st1, h1, h2⟩ := bind_ok h
    cases o with
    | none => cases pure_ok h2
    | some v =>
      simp only at h2
      split at h2
      · rename_i hlt
        obtain ⟨hs, hx⟩ := evalBinds_frame n bs _ _ _ _ h2
        refine ⟨by rw [hs]; simp, fun y hy => ?_⟩
        simp only [List.map_cons, List.mem_cons, not_or] at hy
        rw [hx y hy.2, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        simp [Ne.symm hy.1]
      · exact (throw_ok h2).elim

/-! ## Soundness -/

section Sound
variable {p : Program} {ctx : Ctx} {c : SC} {s0 : LState} {T : TermId → Prop} {cfg : Config}

theorem iflet_terms {rl : Rule} (h : ∀ u ∈ ruleTerms rl, T u) :
    ∀ il ∈ rl.iflets, (∀ u ∈ patTerms il.lhs, T u) ∧ ∀ u ∈ exprTerms il.rhs, T u :=
  fun il hil =>
    let h' := ruleTerms_iflets (C := fun _ _ => True) h (fun _ _ => trivial) il hil
    ⟨h'.1, h'.2.1⟩

/-- The match phase of a checked rule. -/
theorem match_step (M : DModel p ctx c s0) {m : Nat}
    (ih : ∀ j, j < m → SoundAt (p := p) (ctx := ctx) (c := c) (s0 := s0) (T := T) cfg j)
    {rl : Rule} {ins : List A} {e0 e1 : AEnv}
    (hT : ∀ u ∈ ruleTerms rl, T u)
    (h0 : aPatArgs p ins rl.args (List.replicate rl.vars.length none) = some e0)
    (h1 : aIfLets p rl.iflets e0 = some e1)
    {vs : List V} {s : LState} {tr : Array RuleId} {env : Isle.Interp.Env V} {s1 : LState}
    {tr1 : Array RuleId}
    (hvs : ∀ env, γL c ins (Dn ctx c s0 s) env vs) (hIs : IsD ctx c s0 s)
    (h : (matchRule p (sem ctx) cfg m rl vs).run (s, tr) = .ok (some env, (s1, tr1))) :
    IsD ctx c s0 s1 ∧ RsD s s1 ∧ EnvOK c (Dn ctx c s0 s1) env e1 := by
  cases m with
  | zero => rw [matchRule.eq_1] at h; exact (throw_ok h).elim
  | succ m =>
  rw [matchRule.eq_2] at h
  obtain ⟨g, s2, h2, h3⟩ := bind_ok h
  cases Isle.Interp.get_ok h2
  simp only at h3
  obtain ⟨o, ⟨s3, tr3⟩, h4, h5⟩ := bind_ok h3
  obtain ⟨_, hma, he⟩ := liftM_ok h4
  cases he
  cases o with
  | none => cases pure_ok h5
  | some env0 =>
    obtain ⟨hE0, -⟩ := aPatArgs_sound M.ext rl.args ins h0 hma (EnvOK.empty _ _)
      (HoldsP.of_γL (hvs _))
    exact (ih m (by omega)).iflets _ _ _ _ _ _ _ _ _ (iflet_terms hT) h1 hE0 hIs h5

/-- A checked rule's run: its match at fuel `m`, its right-hand side at fuel `k`. -/
theorem rule_step (M : DModel p ctx c s0) {m k : Nat}
    (ihm : ∀ j, j < m → SoundAt (p := p) (ctx := ctx) (c := c) (s0 := s0) (T := T) cfg j)
    (ihk : SoundAt (p := p) (ctx := ctx) (c := c) (s0 := s0) (T := T) cfg k)
    {rl : Rule} {ins : List A} {out : A} (hT : ∀ u ∈ ruleTerms rl, T u)
    (hr : aRule p ins out rl = true) {vs : List V} {s : LState} {tr : Array RuleId}
    {env : Isle.Interp.Env V} {s1 : LState} {tr1 : Array RuleId} {r : Option V} {s2 : LState}
    {tr2 : Array RuleId}
    (hvs : ∀ env, γL c ins (Dn ctx c s0 s) env vs) (hIs : IsD ctx c s0 s)
    (hmatch : (matchRule p (sem ctx) cfg m rl vs).run (s, tr) = .ok (some env, (s1, tr1)))
    (hrhs : (evalExpr p (sem ctx) cfg k rl.rhs env).run (s1, tr1) = .ok (r, (s2, tr2))) :
    IsD ctx c s0 s2 ∧ RsD s s2 ∧ ∀ v, r = some v → γ c out (Dn ctx c s0 s2) env v := by
  obtain ⟨e0, e1, a, e2, h0, h1, h2, hf⟩ := aRule_inv hr
  obtain ⟨hIs1, r1, hE1⟩ := match_step M ihm hT h0 h1 hvs hIs hmatch
  obtain ⟨hIs2, r2, hv⟩ := ihk.expr _ _ _ _ _ _ _ _ _ _ (ruleTerms_rhs hT) h2 hE1 hIs1 hrhs
  exact ⟨hIs2, r1.trans r2, fun v hv' =>
    let ⟨hE2, hg⟩ := hv v hv'
    fitsA_sound hE2 hg hf⟩

/-- The application step at fuel `n + 1`. -/
theorem apply_step (M : DModel p ctx c s0) (htab : TabOK p T) (hc : cfg.checkOverlap = false)
    {n : Nat}
    (ih : ∀ m, m < n + 1 → SoundAt (p := p) (ctx := ctx) (c := c) (s0 := s0) (T := T) cfg m)
    (ty : TypeId) (t : TermId) (as : List A) (e e' : AEnv) (a : A)
    (env : Isle.Interp.Env V) (vs : List V) (s : LState) (tr : Array RuleId) (r : Option V)
    (s' : LState) (tr' : Array RuleId)
    (hT : T t) (ha : aApply p ty t as e = some (a, e')) (hvs : γL c as (Dn ctx c s0 s) env vs)
    (he : EnvOK c (Dn ctx c s0 s) env e) (hIs : IsD ctx c s0 s)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty t vs).run (s, tr) = .ok (r, (s', tr'))) :
    IsD ctx c s0 s' ∧ RsD s s' ∧ EnvOK c (Dn ctx c s0 s') env e' ∧
      ∀ v, r = some v → γ c a (Dn ctx c s0 s') env v := by
  unfold aApply at ha
  cases ht : termOf p t with
  | error err =>
    rw [applyTerm.eq_2] at h
    obtain ⟨term', s1, h1, h2⟩ := bind_ok h
    obtain ⟨_, ht', -⟩ := liftM_ok h1
    rw [ht] at ht'; cases ht'
  | ok term =>
    rw [termOf_some ht] at ha
    simp only at ha
    have h0 := h
    rw [applyTerm.eq_2] at h0
    obtain ⟨term', s1, h1, h2⟩ := bind_ok h0
    obtain ⟨_, ht', he1⟩ := liftM_ok h1
    rw [ht] at ht'; cases ht'; cases he1
    cases hk : term.kind with
    | enumVariant k =>
      rw [hk] at ha h2
      cases ha
      cases pure_ok h2
      exact ⟨hIs, RsD.refl _, he, fun v hv => by cases hv; exact ⟨vs, rfl, hvs⟩⟩
    | struct =>
      rw [hk] at ha h2
      cases ha
      cases pure_ok h2
      exact ⟨hIs, RsD.refl _, he, fun v hv => by cases hv; exact ⟨vs, rfl, hvs⟩⟩
    | decl flags ctor ex =>
      cases ctor with
      | none =>
        rw [hk] at h2
        exact (throw_ok h2).elim
      | some cc =>
        cases cc with
        | external fn =>
          rw [hk] at ha h2
          simp only at ha h2
          split at h2
          · exact (throw_ok h2).elim
          · obtain ⟨g, s2, h3, h4⟩ := bind_ok h2
            cases Isle.Interp.get_ok h3
            simp only at h4
            split at h4
            · rename_i v st' hct
              obtain ⟨u, s3, h5, h6⟩ := bind_ok h4
              cases set_ok h5
              cases pure_ok h6
              obtain ⟨hIs', hR, hE', hv⟩ := M.ctor t term as e e' a env vs s _ _ ht ha hvs he hIs hct
              exact ⟨hIs', hR, hE', fun w hw => by cases hw; exact hv⟩
            · rename_i hct
              split at h4
              · cases pure_ok h4
                have := M.ctor_fail t term as e e' a vs s ht ha hct
                subst this
                exact ⟨hIs, RsD.refl _, he, fun w hw => by cases hw⟩
              · exact (throw_ok h4).elim
            · exact (throw_ok h4).elim
        | internal =>
          rw [hk] at ha
          simp only at ha
          cases hm : flags.isMulti with
          | true =>
            rw [hk] at h2
            simp only [hm, ↓reduceIte] at h2
            exact (throw_ok h2).elim
          | false =>
          split at ha
          · rename_i hO
            exact M.oracle t (by simpa using hO) cfg hc (n + 1) ty as e e' a env vs s tr r s' tr'
              ha hvs he hIs h
          · rename_i hO
            have hO' : t ∉ oracles := by simpa using hO
            split at ha
            · rename_i ct hw
              cases ha
              obtain ⟨rfl, hv⟩ := M.wrap t ct hw cfg hc (n + 1) ty vs s tr r s' tr' h
              exact ⟨hIs, RsD.refl _, he, fun v hr => hv v hr as _ env hvs⟩
            · rename_i hw
              have hcase : ∀ (z z' : Bool),
                  (∀ rl ∈ p.rulesOf t, aRule p (term.args.map (tyA z)) (tyA z' term.ret) rl = true) →
                  γL c (term.args.map (tyA z)) (Dn ctx c s0 s) env vs →
                  IsD ctx c s0 s' ∧ RsD s s' ∧ EnvOK c (Dn ctx c s0 s') env e ∧
                    ∀ v, r = some v → γ c (tyA z' term.ret) (Dn ctx c s0 s') env v := by
                intro z z' hall hg
                rcases internal_cases hc ht hk hm h with ⟨rfl, rfl⟩ |
                  ⟨rl, hrl, m, envR, s1, tr1, tr2, hmn, -, hmatch, hrhs⟩
                · exact ⟨hIs, RsD.refl _, he, fun v hv => by cases hv⟩
                · obtain ⟨hIs2, r2, hv2⟩ := rule_step M (fun j hj => ih j (by omega))
                    (ih n (by omega)) (htab t hT hO' hw term ht rl hrl).1 (hall rl hrl)
                    (fun _ => γL_tyA_env hg) hIs hmatch hrhs
                  exact ⟨hIs2, r2, he.mono (Dn_mono hIs r2), fun v hv => γ_tyA_env (hv2 v hv)⟩
              split at ha
              · rename_i hf
                cases ha
                exact hcase false false (fun rl hrl => (htab t hT hO' hw term ht rl hrl).2.1)
                  (fitsAL_sound he hvs hf)
              · split at ha
                · rename_i hf
                  cases ha
                  exact hcase true _ (fun rl hrl => (htab t hT hO' hw term ht rl hrl).2.2)
                    (fitsAL_sound he hvs hf)
                · cases ha

/-- **Soundness at every fuel.** -/
theorem soundAt (M : DModel p ctx c s0) (htab : TabOK p T) (hc : cfg.checkOverlap = false) :
    ∀ n, SoundAt (p := p) (ctx := ctx) (c := c) (s0 := s0) (T := T) cfg n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  cases n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rename_i h <;>
      first
      | (rw [evalExpr.eq_1] at h; exact (throw_ok h).elim)
      | (rw [evalArgs.eq_1] at h; exact (throw_ok h).elim)
      | (rw [evalBinds.eq_1] at h; exact (throw_ok h).elim)
      | (rw [applyTerm.eq_1] at h; exact (throw_ok h).elim)
      | (rw [matchIfLets.eq_1] at h; exact (throw_ok h).elim)
  | succ n =>
  have ihn := ih n (Nat.lt_succ_self n)
  refine ⟨?_, ?_, ?_, apply_step M htab hc ih, ?_⟩
  · -- evalExpr
    intro x e e' a env s tr r s' tr' hT ha he hIs h
    cases x with
    | var ty x =>
      rw [evalExpr.eq_2] at h
      simp only [aExpr] at ha
      split at ha
      · cases ha
        split at h
        · rename_i w hw
          cases pure_ok h
          exact ⟨hIs, RsD.refl _, fun v hv => by cases hv; exact ⟨he, hw⟩⟩
        · exact (throw_ok h).elim
      · cases ha
    | constBool ty b =>
      rw [evalExpr.eq_3] at h
      simp only [aExpr] at ha
      cases ha
      cases pure_ok h
      exact ⟨hIs, RsD.refl _, fun v hv => by cases hv; exact ⟨he, γ_bool b⟩⟩
    | constInt ty i =>
      rw [evalExpr.eq_4] at h
      simp only [aExpr] at ha
      cases ha
      cases pure_ok h
      exact ⟨hIs, RsD.refl _, fun v hv => by cases hv; exact ⟨he, γ_int ty i⟩⟩
    | constPrim ty nm =>
      rw [evalExpr.eq_5] at h
      simp only [aExpr] at ha
      cases ha
      split at h
      · rename_i cv hcp
        cases pure_ok h
        exact ⟨hIs, RsD.refl _, fun v hv => by cases hv; exact ⟨he, γ_prim hcp⟩⟩
      · exact (throw_ok h).elim
    | «let» ty bs body =>
      rw [evalExpr.eq_6] at h
      simp only [aExpr] at ha
      split at ha
      · rename_i hub
        split at ha
        · rename_i e1 hb
          split at ha
          · rename_i a2 e2 hbody
            obtain ⟨hnm, rfl, hfit, z, rfl⟩ := letClose_inv ha
            obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
            obtain ⟨hIs1, r1, hE1⟩ := ihn.binds _ _ _ _ _ _ _ _ _
              (fun u hu => hT u (by simp [exprTerms, hu])) hb he hIs h1
            cases o with
            | none => cases pure_ok h2; exact ⟨hIs1, r1, fun v hv => by cases hv⟩
            | some env1 =>
              obtain ⟨hIs2, r2, hv2⟩ := ihn.expr _ _ _ _ _ _ _ _ _ _
                (fun u hu => hT u (by simp [exprTerms, hu])) hbody (hE1 env1 rfl) hIs1 h2
              refine ⟨hIs2, r1.trans r2, fun v hv => ?_⟩
              obtain ⟨hE2, hg⟩ := hv2 v hv
              obtain ⟨hsz, hfr⟩ := evalBinds_frame _ _ _ _ _ _ h1
              exact ⟨(he.mono (Dn_mono hIs (r1.trans r2))).letClose hub hsz hfr hE2 hnm,
                γ_tyA_env (fitsA_sound hE2 hg hfit)⟩
          · cases ha
        · cases ha
      · cases ha
    | term ty t args =>
      rw [evalExpr.eq_7] at h
      simp only [aExpr] at ha
      split at ha
      · rename_i as e1 hargs
        obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
        obtain ⟨hIs1, r1, hv1⟩ := ihn.args _ _ _ _ _ _ _ _ _ _
          (fun u hu => hT u (by simp [exprTerms, hu])) hargs he hIs h1
        cases o with
        | none => cases pure_ok h2; exact ⟨hIs1, r1, fun v hv => by cases hv⟩
        | some vs =>
          obtain ⟨hE1, hg1⟩ := hv1 vs rfl
          obtain ⟨hIs2, r2, hE2, hv2⟩ := ihn.apply _ _ _ _ _ _ _ _ _ _ _ _ _
            (hT t (by simp [exprTerms])) ha hg1 hE1 hIs1 h2
          exact ⟨hIs2, r1.trans r2, fun v hv => ⟨hE2, hv2 v hv⟩⟩
      · cases ha
  · -- evalArgs
    intro xs e e' as env s tr r s' tr' hT ha he hIs h
    cases xs with
    | nil =>
      rw [evalArgs.eq_2] at h
      simp only [aArgs] at ha
      cases ha
      cases pure_ok h
      exact ⟨hIs, RsD.refl _, fun vs hv => by cases hv; exact ⟨he, trivial⟩⟩
    | cons x xs =>
      rw [evalArgs.eq_3] at h
      simp only [aArgs] at ha
      split at ha
      · rename_i a1 e1 hx
        split at ha
        · rename_i as2 e2 hxs
          cases ha
          obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
          obtain ⟨hIs1, r1, hv1⟩ := ihn.expr _ _ _ _ _ _ _ _ _ _
            (fun u hu => hT u (by simp [exprTermsL, hu])) hx he hIs h1
          cases o with
          | none => cases pure_ok h2; exact ⟨hIs1, r1, fun vs hv => by cases hv⟩
          | some v =>
            obtain ⟨hE1, hg1⟩ := hv1 v rfl
            obtain ⟨o2, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
            obtain ⟨hIs2, r2, hv2⟩ := ihn.args _ _ _ _ _ _ _ _ _ _
              (fun u hu => hT u (by simp [exprTermsL, hu])) hxs hE1 hIs1 h3
            cases o2 with
            | none => cases pure_ok h4; exact ⟨hIs2, r1.trans r2, fun vs hv => by cases hv⟩
            | some vs =>
              cases pure_ok h4
              obtain ⟨hE2, hg2⟩ := hv2 vs rfl
              exact ⟨hIs2, r1.trans r2, fun ws hw => by
                cases hw
                exact ⟨hE2, γ_mono a1 (Dn_mono hIs1 r2) hg1, hg2⟩⟩
        · cases ha
      · cases ha
  · -- evalBinds
    intro bs e e' env s tr r s' tr' hT ha he hIs h
    cases bs with
    | nil =>
      rw [evalBinds.eq_2] at h
      simp only [aBinds] at ha
      cases ha
      cases pure_ok h
      exact ⟨hIs, RsD.refl _, fun env' hv => by cases hv; exact he⟩
    | cons b bs =>
      obtain ⟨x, ty, ex⟩ := b
      rw [evalBinds.eq_3] at h
      simp only [aBinds] at ha
      split at ha
      · rename_i a1 e1 hx
        split at ha
        · rename_i hxe
          obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
          obtain ⟨hIs1, r1, hv1⟩ := ihn.expr _ _ _ _ _ _ _ _ _ _
            (fun u hu => hT u (by simp [bindTerms, hu])) hx he hIs h1
          cases o with
          | none => cases pure_ok h2; exact ⟨hIs1, r1, fun _ hv => by cases hv⟩
          | some v =>
            obtain ⟨hE1, hg1⟩ := hv1 v rfl
            simp only at h2
            split at h2
            · obtain ⟨-, -, hE2⟩ := hE1.bind hxe hg1
              obtain ⟨hIs2, r2, hv2⟩ := ihn.binds _ _ _ _ _ _ _ _ _
                (fun u hu => hT u (by simp [bindTerms, hu])) ha hE2 hIs1 h2
              exact ⟨hIs2, r1.trans r2, hv2⟩
            · exact (throw_ok h2).elim
        · cases ha
      · cases ha
  · -- matchIfLets
    intro ils e e' env s tr env' s' tr' hT ha he hIs h
    cases ils with
    | nil =>
      rw [matchIfLets.eq_2] at h
      simp only [aIfLets] at ha
      cases ha
      cases pure_ok h
      exact ⟨hIs, RsD.refl _, he⟩
    | cons il ils =>
      rw [matchIfLets.eq_3] at h
      simp only [aIfLets] at ha
      obtain ⟨hTl, hTr⟩ := hT il List.mem_cons_self
      split at ha
      · rename_i a1 e1 hx
        split at ha
        · rename_i e2 hp
          obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
          obtain ⟨hIs1, r1, hv1⟩ := ihn.expr _ _ _ _ _ _ _ _ _ _ hTr hx he hIs h1
          cases o with
          | none => cases pure_ok h2
          | some v =>
            obtain ⟨hE1, hg1⟩ := hv1 v rfl
            obtain ⟨g, s2, h3, h4⟩ := bind_ok h2
            cases Isle.Interp.get_ok h3
            simp only at h4
            obtain ⟨o2, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
            obtain ⟨_, hmp, he2⟩ := liftM_ok h5
            cases he2
            cases o2 with
            | none => cases pure_ok h6
            | some env1 =>
              obtain ⟨hE2, -⟩ := aPat_sound M.ext il.lhs a1 hp hmp hE1 hg1
              obtain ⟨hIs2, r2, hE3⟩ := ihn.iflets _ _ _ _ _ _ _ _ _
                (fun il' hil' => hT il' (List.mem_cons_of_mem _ hil')) ha hE2 hIs1 h6
              exact ⟨hIs2, r1.trans r2, hE3⟩
        · cases ha
      · cases ha

/-- **Soundness of an application.** -/
theorem dSound (M : DModel p ctx c s0) (htab : TabOK p T) (hc : cfg.checkOverlap = false) :
    ∀ (n : Nat) (ty : TypeId) (t : TermId) (as : List A) (e e' : AEnv) (a : A)
      (env : Isle.Interp.Env V) (vs : List V) (s : LState) (tr : Array RuleId) (r : Option V)
      (s' : LState) (tr' : Array RuleId),
    T t → aApply p ty t as e = some (a, e') → γL c as (Dn ctx c s0 s) env vs →
    EnvOK c (Dn ctx c s0 s) env e → IsD ctx c s0 s →
    (applyTerm p (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    IsD ctx c s0 s' ∧ RsD s s' ∧ EnvOK c (Dn ctx c s0 s') env e' ∧
      ∀ v, r = some v → γ c a (Dn ctx c s0 s') env v :=
  fun n => (soundAt M htab hc n).apply

/-- **A root term** (internal, non-multi; not necessarily in `T`): each rule is checked
(`aRule p ins out`, its terms in `T`), hand-checked (`Hand`, result predicate `Q`; the hand
obligation gets the fuel of the root run `n = k + 1`, of the right-hand side `k` and of the
committed match `m`), or never matches. -/
theorem dRoot (M : DModel p ctx c s0) (htab : TabOK p T) (hc : cfg.checkOverlap = false)
    (Q : LState → V → Prop) (Hand : Rule → Prop) (ins : List A) (out : A)
    {n : Nat} {ty : TypeId} {t : TermId} {term : Term} {flags : TermFlags}
    {ex : Option Extractor} {vs : List V}
    (ht : termOf p t = .ok term) (hk : term.kind = .decl flags (some .internal) ex)
    (hm : flags.isMulti = false)
    (hrules : ∀ rl ∈ p.rulesOf t,
      ((∀ u ∈ ruleTerms rl, T u) ∧ aRule p ins out rl = true) ∨ Hand rl ∨
        ∀ m st env st1, (matchRule p (sem ctx) cfg m rl vs).run st ≠ .ok (some env, st1))
    (hhand : ∀ rl ∈ p.rulesOf t, Hand rl →
      ∀ k m s tr env s1 tr1 r s2 tr2, n = k + 1 → m + 2 ≤ k →
        k ≤ m + 2 + (p.rulesOf t).length → (∀ env, γL c ins (Dn ctx c s0 s) env vs) →
        IsD ctx c s0 s →
        (matchRule p (sem ctx) cfg m rl vs).run (s, tr) = .ok (some env, (s1, tr1)) →
        (evalExpr p (sem ctx) cfg k rl.rhs env).run (s1, tr1) = .ok (r, (s2, tr2)) →
        IsD ctx c s0 s2 ∧ RsD s s2 ∧ ∀ v, r = some v → Q s2 v)
    {s s' : LState} {tr tr' : Array RuleId} {r : Option V}
    (hvs : ∀ env, γL c ins (Dn ctx c s0 s) env vs) (hIs : IsD ctx c s0 s)
    (h : (applyTerm p (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr'))) :
    IsD ctx c s0 s' ∧ RsD s s' ∧
      ∀ v, r = some v → (∃ env, γ c out (Dn ctx c s0 s') env v) ∨ Q s' v := by
  cases n with
  | zero => rw [applyTerm.eq_1] at h; exact (throw_ok h).elim
  | succ k =>
  rcases internal_cases hc ht hk hm h with ⟨rfl, rfl⟩ |
    ⟨rl, hrl, m, env, s1, tr1, tr2, hmk, hkm, hmatch, hrhs⟩
  · exact ⟨hIs, RsD.refl _, fun v hv => by cases hv⟩
  · rcases hrules rl hrl with ⟨hTr, hr⟩ | hH | hno
    · obtain ⟨hIs2, r2, hv2⟩ := rule_step M (fun j _ => soundAt M htab hc j)
        (soundAt M htab hc k) hTr hr hvs hIs hmatch hrhs
      exact ⟨hIs2, r2, fun v hv => .inl ⟨env, hv2 v hv⟩⟩
    · obtain ⟨hIs2, r2, hv2⟩ :=
        hhand rl hrl hH k m s tr env s1 tr1 r s' tr2 rfl hmk hkm hvs hIs hmatch hrhs
      exact ⟨hIs2, r2, fun v hv => .inr (hv2 v hv)⟩
    · exact absurd hmatch (hno m _ _ _)

end Sound

end Backend.Proof.DefGen
