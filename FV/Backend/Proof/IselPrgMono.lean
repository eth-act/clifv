module

public import FV.Backend.Proof.IselFlowGen

@[expose] public section

/-!
# Generic lemmas about the ISLE interpreter: fuel monotonicity and rule selection

For any program, embedding and configuration:

* `mono`: **fuel monotonicity**: a run of any interpreter function that returns (does not
  throw) returns the same result, in the same state, at every larger fuel (`Mono`);
* `selectRule_some_split`/`selectRule_none_all` (overlap checking off): a selected rule follows
  rules whose match, from the selection's start state at a smaller fuel, failed, and its own
  match succeeded with the returned environment and state; no selection means every rule's match
  failed from the start state;
* `tryRule_ok`, `selectRule_cons_ok`: one step of `tryRule`/`selectRule`, forwards.
-/

namespace Isle.Interp

variable {V σ : Type} {p : Program} {sem : Sem V σ} {cfg : Config}

section Mono
variable {α β : Type}

/-- `y` returns whatever `x` returns, from every state. -/
def Mono (x y : M σ α) : Prop := ∀ s r, x.run s = .ok r → y.run s = .ok r

theorem mono_refl (x : M σ α) : Mono x x := fun _ _ h => h

theorem mono_bind {x x' : M σ α} {f f' : α → M σ β} (h1 : Mono x x')
    (h2 : ∀ a, Mono (f a) (f' a)) : Mono (x >>= f) (x' >>= f') := by
  intro s r h
  rw [M.run_bind] at h ⊢
  cases hx : x.run s with
  | error e => rw [hx] at h; cases h
  | ok q =>
    rw [hx] at h
    rw [h1 s q hx]
    simp only [M.except_ok_bind] at h ⊢
    exact h2 q.1 q.2 r h

theorem mono_throw (e : Err) (y : M σ α) : Mono (throw e) y := fun _ _ h => (throw_ok h).elim

/-- Fuel monotonicity at fuel `n`, for every interpreter function. -/
structure MonoAt (p : Program) (sem : Sem V σ) (cfg : Config) (n : Nat) : Prop where
  expr : ∀ e env, Mono (evalExpr p sem cfg n e env) (evalExpr p sem cfg (n + 1) e env)
  args : ∀ es env, Mono (evalArgs p sem cfg n es env) (evalArgs p sem cfg (n + 1) es env)
  binds : ∀ bs env, Mono (evalBinds p sem cfg n bs env) (evalBinds p sem cfg (n + 1) bs env)
  apply : ∀ ty t vs, Mono (applyTerm p sem cfg n ty t vs) (applyTerm p sem cfg (n + 1) ty t vs)
  mrule : ∀ r vs, Mono (matchRule p sem cfg n r vs) (matchRule p sem cfg (n + 1) r vs)
  iflets : ∀ ils env, Mono (matchIfLets p sem cfg n ils env) (matchIfLets p sem cfg (n + 1) ils env)
  tryR : ∀ r vs, Mono (tryRule p sem cfg n r vs) (tryRule p sem cfg (n + 1) r vs)
  also : ∀ rs vs, Mono (alsoMatching p sem cfg n rs vs) (alsoMatching p sem cfg (n + 1) rs vs)
  sel : ∀ term rs vs, Mono (selectRule p sem cfg n term rs vs)
    (selectRule p sem cfg (n + 1) term rs vs)

/-- **Fuel monotonicity**, one step. -/
theorem monoAt : ∀ n, MonoAt p sem cfg n
  | 0 => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros
    · rw [evalExpr.eq_1]; exact mono_throw _ _
    · rw [evalArgs.eq_1]; exact mono_throw _ _
    · rw [evalBinds.eq_1]; exact mono_throw _ _
    · rw [applyTerm.eq_1]; exact mono_throw _ _
    · rw [matchRule.eq_1]; exact mono_throw _ _
    · rw [matchIfLets.eq_1]; exact mono_throw _ _
    · rw [tryRule.eq_1]; exact mono_throw _ _
    · rw [alsoMatching.eq_1]; exact mono_throw _ _
    · rw [selectRule.eq_1]; exact mono_throw _ _
  | n + 1 => by
    have ih := monoAt n
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e env
      cases e with
      | var => rw [evalExpr.eq_2, evalExpr.eq_2]; exact mono_refl _
      | constBool => rw [evalExpr.eq_3, evalExpr.eq_3]; exact mono_refl _
      | constInt => rw [evalExpr.eq_4, evalExpr.eq_4]; exact mono_refl _
      | constPrim => rw [evalExpr.eq_5, evalExpr.eq_5]; exact mono_refl _
      | «let» ty bs body =>
        rw [evalExpr.eq_6, evalExpr.eq_6]
        refine mono_bind (ih.binds _ _) fun o => ?_
        cases o
        · exact mono_refl _
        · exact ih.expr _ _
      | term ty t args =>
        rw [evalExpr.eq_7, evalExpr.eq_7]
        refine mono_bind (ih.args _ _) fun o => ?_
        cases o
        · exact mono_refl _
        · exact ih.apply _ _ _
    · intro es env
      cases es with
      | nil => rw [evalArgs.eq_2, evalArgs.eq_2]; exact mono_refl _
      | cons e es =>
        rw [evalArgs.eq_3, evalArgs.eq_3]
        refine mono_bind (ih.expr _ _) fun o => ?_
        cases o
        · exact mono_refl _
        · exact mono_bind (ih.args _ _) fun o => by cases o <;> exact mono_refl _
    · intro bs env
      cases bs with
      | nil => rw [evalBinds.eq_2, evalBinds.eq_2]; exact mono_refl _
      | cons b bs =>
        obtain ⟨x, ty, e⟩ := b
        rw [evalBinds.eq_3, evalBinds.eq_3]
        refine mono_bind (ih.expr _ _) fun o => ?_
        cases o
        · exact mono_refl _
        · dsimp only
          split
          · exact ih.binds _ _
          · exact mono_refl _
    · intro ty t vs
      rw [applyTerm.eq_2, applyTerm.eq_2]
      refine mono_bind (mono_refl _) fun term => ?_
      split
      · exact mono_refl _
      · exact mono_refl _
      · exact mono_refl _
      · split
        · exact mono_refl _
        · refine mono_bind (ih.sel _ _ _) fun o => ?_
          rcases o with _ | ⟨r, env⟩
          · exact mono_refl _
          · exact mono_bind (ih.expr _ _) fun o => mono_refl _
      · exact mono_refl _
    · intro r vs
      rw [matchRule.eq_2, matchRule.eq_2]
      refine mono_bind (mono_refl _) fun x => ?_
      obtain ⟨st, tr⟩ := x
      refine mono_bind (mono_refl _) fun o => ?_
      cases o
      · exact mono_refl _
      · exact ih.iflets _ _
    · intro ils env
      cases ils with
      | nil => rw [matchIfLets.eq_2, matchIfLets.eq_2]; exact mono_refl _
      | cons il ils =>
        rw [matchIfLets.eq_3, matchIfLets.eq_3]
        refine mono_bind (ih.expr _ _) fun o => ?_
        cases o
        · exact mono_refl _
        · refine mono_bind (mono_refl _) fun x => ?_
          obtain ⟨st, tr⟩ := x
          refine mono_bind (mono_refl _) fun o => ?_
          cases o
          · exact mono_refl _
          · exact ih.iflets _ _
    · intro r vs
      rw [tryRule.eq_2, tryRule.eq_2]
      refine mono_bind (mono_refl _) fun saved => ?_
      exact mono_bind (ih.mrule _ _) fun o => by cases o <;> exact mono_refl _
    · intro rs vs
      cases rs with
      | nil => rw [alsoMatching.eq_2, alsoMatching.eq_2]; exact mono_refl _
      | cons r rs =>
        rw [alsoMatching.eq_3, alsoMatching.eq_3]
        refine mono_bind (mono_refl _) fun saved => ?_
        refine mono_bind (ih.mrule _ _) fun m => ?_
        refine mono_bind (mono_refl _) fun _ => ?_
        exact mono_bind (ih.also _ _) fun _ => mono_refl _
    · intro term rs vs
      cases rs with
      | nil => rw [selectRule.eq_2, selectRule.eq_2]; exact mono_refl _
      | cons r rs =>
        rw [selectRule.eq_3, selectRule.eq_3]
        refine mono_bind (ih.tryR _ _) fun o => ?_
        cases o
        · exact ih.sel _ _ _
        · dsimp only
          split
          · exact mono_bind (ih.also _ _) fun _ => mono_refl _
          · exact mono_refl _

/-- **Fuel monotonicity of expressions**: a run that returns returns the same at every larger
fuel. -/
theorem evalExpr_mono {n n' : Nat} (hn : n ≤ n') {e : Expr} {env : Env V}
    {s : σ × Array RuleId} {r : Option V × (σ × Array RuleId)}
    (h : (evalExpr p sem cfg n e env).run s = .ok r) :
    (evalExpr p sem cfg n' e env).run s = .ok r := by
  induction hn with
  | refl => exact h
  | step _ ih => exact (monoAt _).expr _ _ _ _ ih

end Mono

/-! ## Rule selection -/

/-- One step of `tryRule`, forwards. -/
theorem tryRule_ok {n : Nat} {r : Rule} {vs : List V} {s s1 : σ × Array RuleId}
    {res : Option (Env V)} (h : (matchRule p sem cfg n r vs).run s = .ok (res, s1)) :
    (tryRule p sem cfg (n + 1) r vs).run s =
      .ok (res, match res with | some _ => s1 | none => s) := by
  rw [tryRule.eq_2]
  simp only [M.run_bind, M.run_get, M.except_ok_bind, h]
  cases res <;> rfl

/-- One step of `selectRule`, forwards (overlap checking off). -/
theorem selectRule_cons_ok (hc : cfg.checkOverlap = false) {n : Nat} {term : Term} {r : Rule}
    {rs : List Rule} {vs : List V} {s s1 : σ × Array RuleId} {res : Option (Env V)}
    (h : (tryRule p sem cfg n r vs).run s = .ok (res, s1)) :
    (selectRule p sem cfg (n + 1) term (r :: rs) vs).run s =
      match res with
      | some env => .ok (some (r, env), s1)
      | none => (selectRule p sem cfg n term rs vs).run s1 := by
  rw [selectRule.eq_3]
  simp only [M.run_bind, h, M.except_ok_bind]
  cases res with
  | none => rfl
  | some env => simp [hc]

/-- **A selected rule follows failed ones.** -/
theorem selectRule_some_split (hc : cfg.checkOverlap = false) :
    ∀ {n : Nat} {term : Term} {rs : List Rule} {vs : List V} {s s' : σ × Array RuleId}
      {r : Rule} {env : Env V},
      (selectRule p sem cfg n term rs vs).run s = .ok (some (r, env), s') →
      ∃ pre post, rs = pre ++ r :: post ∧
        (∀ r' ∈ pre, ∃ m < n, ∃ s1, (matchRule p sem cfg m r' vs).run s = .ok (none, s1)) ∧
        ∃ m < n, (matchRule p sem cfg m r vs).run s = .ok (some env, s')
  | 0, _, _, _, _, _, _, _, h => by rw [selectRule.eq_1] at h; cases h
  | n + 1, _, [], _, _, _, _, _, h => by rw [selectRule.eq_2] at h; cases h
  | n + 1, term, r' :: rs, vs, s, s', r, env, h => by
    cases n with
    | zero =>
      rw [selectRule.eq_3] at h
      simp only [M.run_bind] at h
      rw [tryRule.eq_1] at h; cases h
    | succ k =>
      cases ht : (tryRule p sem cfg (k + 1) r' vs).run s with
      | error e =>
        rw [selectRule.eq_3] at h
        simp only [M.run_bind, ht] at h
        cases h
      | ok q =>
        obtain ⟨res, s1⟩ := q
        rw [selectRule_cons_ok hc ht] at h
        rcases tryRule_run ht with ⟨env', hres, hm⟩ | ⟨hres, hs1⟩
        · subst hres
          simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
          exact ⟨[], rs, rfl, fun _ h => (nomatch h), k, by omega, hm⟩
        · subst hres hs1
          obtain ⟨pre, post, hrs, hpre, m, hm, hmr⟩ := selectRule_some_split hc h
          obtain ⟨-, s2, hfail⟩ := tryRule_none_match ht
          refine ⟨r' :: pre, post, by rw [hrs]; rfl, fun r'' hr'' => ?_, m, by omega, hmr⟩
          rcases List.mem_cons.mp hr'' with rfl | hr''
          · exact ⟨k, by omega, s2, hfail⟩
          · obtain ⟨m', hm', s3, h3⟩ := hpre r'' hr''
            exact ⟨m', by omega, s3, h3⟩

/-- **No selection: every rule failed** (from the start state, at a smaller fuel). -/
theorem selectRule_none_all (hc : cfg.checkOverlap = false) :
    ∀ {n : Nat} {term : Term} {rs : List Rule} {vs : List V} {s s' : σ × Array RuleId},
      (selectRule p sem cfg n term rs vs).run s = .ok (none, s') →
      ∀ r ∈ rs, ∃ m < n, ∃ s1, (matchRule p sem cfg m r vs).run s = .ok (none, s1)
  | 0, _, _, _, _, _, h => by rw [selectRule.eq_1] at h; cases h
  | n + 1, _, [], _, _, _, _ => fun _ h => by cases h
  | n + 1, term, r' :: rs, vs, s, s', h => by
    cases n with
    | zero =>
      rw [selectRule.eq_3] at h
      simp only [M.run_bind] at h
      rw [tryRule.eq_1] at h; cases h
    | succ k =>
      cases ht : (tryRule p sem cfg (k + 1) r' vs).run s with
      | error e =>
        rw [selectRule.eq_3] at h
        simp only [M.run_bind, ht] at h
        cases h
      | ok q =>
        obtain ⟨res, s1⟩ := q
        rw [selectRule_cons_ok hc ht] at h
        cases res with
        | some env => cases h
        | none =>
          obtain ⟨hs1, s2, hfail⟩ := tryRule_none_match ht
          subst hs1
          intro r'' hr''
          rcases List.mem_cons.mp hr'' with rfl | hr''
          · exact ⟨k, by omega, s2, hfail⟩
          · obtain ⟨m', hm', s3, h3⟩ := selectRule_none_all hc h r'' hr''
            exact ⟨m', by omega, s3, h3⟩

end Isle.Interp
