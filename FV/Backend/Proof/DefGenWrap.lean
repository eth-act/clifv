import FV.Backend.Proof.DefGenSound
import FV.Backend.Proof.KillTab

/-!
# Definedness of the ISLE runs: the constructor-tree terms

`dWrap`: the `wrap` field of `DModel program ctx c s0`. A constructor-tree term
(`wrapper program t = some ct`: one rule, no if-lets, parameters bound to distinct variables,
right-hand side a tree of enum variants/structs over those variables) is internal and not multi
(decided over the exported program, `wrapper_internal_ok`); its rule's argument match binds the
`i`-th parameter variable to the `i`-th argument (`matchArgs_binds`) and its right-hand side
builds the value `ctA` describes without touching the lowering state (`ct_eval`).
-/

namespace Backend.Proof.DefGen

open Backend Backend.Proof Isle Isle.Aarch64 Isle.Interp

set_option maxRecDepth 100000

/-- The `i`-th value of a described list is described by the `i`-th abstract value. -/
theorem γL_getD {c : SC} {D : Nat → Prop} {env : Isle.Interp.Env V} :
    ∀ {as : List A} {vs : List V} {i : Nat} {w : V}, γL c as D env vs → vs[i]? = some w →
      γ c (as.getD i .top) D env w
  | [], [], _, _, _, hw => by simp at hw
  | _ :: _, _ :: _, 0, _, h, hw => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
    subst hw
    exact h.1
  | _ :: _, _ :: _, i + 1, _, h, hw => by
    simpa using γL_getD h.2 (by simpa using hw)
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim

theorem bindWild_some {q : Pattern} {x : Nat} (h : bindWild q = some x) :
    ∃ ty ty', q = .bind ty x (.wildcard ty') := by
  unfold bindWild at h
  split at h
  · cases h
    exact ⟨_, _, rfl⟩
  · cases h

/-- **The argument match of a constructor-tree rule** binds the `i`-th parameter variable to
the `i`-th argument and leaves every other slot. -/
theorem matchArgs_binds {p : Program} {ctx : Ctx} {st : LState} :
    ∀ (qs : List Pattern) (xs : List Nat) (vs : List V) (env0 env : Isle.Interp.Env V),
      qs.mapM bindWild = some xs →
      matchArgs p (sem ctx) st qs vs env0 = .ok (some env) →
      (∀ y, y ∉ xs → env[y]? = env0[y]?) ∧
      (xs.Nodup → ∀ (i y : Nat), xs[i]? = some y →
        ∃ w, vs[i]? = some w ∧ env[y]? = some (some w))
  | [], xs, vs, env0, env, hm, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hm
    subst hm
    cases vs with
    | nil =>
      rw [matchArgs.eq_1] at h
      cases h
      exact ⟨fun _ _ => rfl, fun _ i y hy => by simp at hy⟩
    | cons _ _ =>
      rw [matchArgs.eq_3] at h
      all_goals first | cases h | (intros; simp_all)
  | q :: qs, xs, vs, env0, env, hm, h => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hm
    obtain ⟨x, hx, xs', hxs', rfl⟩ := hm
    obtain ⟨ty, ty', rfl⟩ := bindWild_some hx
    cases vs with
    | nil =>
      rw [matchArgs.eq_3] at h
      all_goals first | cases h | (intros; simp_all)
    | cons w ws =>
      rw [matchArgs.eq_2] at h
      rw [matchPat.eq_1] at h
      split at h
      · rename_i hlt
        rw [matchPat.eq_6] at h
        simp only [M.except_pure, M.except_ok_bind] at h
        obtain ⟨hfr, hb⟩ := matchArgs_binds qs xs' ws _ env hxs' h
        have hxx : env0.set! x (some w) = env0.set x (some w) hlt := by
          simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt]
        refine ⟨fun y hy => ?_, fun hnd i y hy => ?_⟩
        · have hy' : y ∉ xs' := fun h' => hy (List.mem_cons_of_mem _ h')
          rw [hfr y hy', hxx, Array.getElem?_set]
          have : x ≠ y := fun h' => hy (h' ▸ List.mem_cons_self)
          simp [this]
        · have hnd' := List.nodup_cons.mp hnd
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
            subst hy
            refine ⟨w, rfl, ?_⟩
            rw [hfr x hnd'.1, hxx, Array.getElem?_set]
            simp
          | succ i =>
            simp only [List.getElem?_cons_succ] at hy ⊢
            exact hb hnd'.2 i y hy
      · cases h

/-- **The right-hand side of a constructor-tree rule** keeps the state and builds the value
`ctA` describes (`ctAL` for argument lists). -/
theorem ct_eval {p : Program} {ctx : Ctx} {c : SC} {cfg : Config} {xs : List Nat} {vs : List V}
    {env : Isle.Interp.Env V}
    (henv : ∀ (i y : Nat), xs[i]? = some y → ∃ w, vs[i]? = some w ∧ env[y]? = some (some w)) :
    ∀ n : Nat,
      (∀ (x : Isle.Expr) (ct : CT) (s : LState) (tr : Array RuleId) (r : Option V)
          (s' : LState) (tr' : Array RuleId),
        ctOf p xs x = some ct →
        (evalExpr p (sem ctx) cfg n x env).run (s, tr) = .ok (r, (s', tr')) →
        s' = s ∧ ∀ v, r = some v → ∀ (as : List A) (D : Nat → Prop) (env' : Isle.Interp.Env V),
          γL c as D env' vs → γ c (ctA as ct) D env' v) ∧
      (∀ (es : List Isle.Expr) (cs : List CT) (s : LState) (tr : Array RuleId)
          (r : Option (List V)) (s' : LState) (tr' : Array RuleId),
        ctOfL p xs es = some cs →
        (evalArgs p (sem ctx) cfg n es env).run (s, tr) = .ok (r, (s', tr')) →
        s' = s ∧ ∀ ws, r = some ws → ∀ (as : List A) (D : Nat → Prop)
          (env' : Isle.Interp.Env V), γL c as D env' vs → γL c (ctAL as cs) D env' ws)
  | 0 => ⟨fun _ _ _ _ _ _ _ _ h => by rw [evalExpr.eq_1] at h; exact (throw_ok h).elim,
      fun _ _ _ _ _ _ _ _ h => by rw [evalArgs.eq_1] at h; exact (throw_ok h).elim⟩
  | n + 1 => by
    have ih := ct_eval (p := p) (ctx := ctx) (c := c) (cfg := cfg) henv n
    refine ⟨fun x ct s tr r s' tr' hc h => ?_, fun es cs s tr r s' tr' hc h => ?_⟩
    · cases x with
      | var ty y =>
        simp only [ctOf] at hc
        obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hc
        obtain ⟨hlt, heq, -⟩ := List.idxOf?_eq_some_iff.mp hi
        obtain ⟨w, hw, hy⟩ := henv i y (by rw [List.getElem?_eq_getElem hlt, heq])
        rw [evalExpr.eq_2] at h
        simp only [hy] at h
        cases pure_ok h
        exact ⟨rfl, fun v hv as D env' hg => by
          cases hv
          exact γL_getD hg hw⟩
      | term ty v es =>
        simp only [ctOf] at hc
        split at hc
        · rename_i k cs hk hcs
          cases hc
          rw [evalExpr.eq_7] at h
          obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
          obtain ⟨rfl, hg1⟩ := ih.2 es cs s tr o s1 tr1 hcs h1
          cases o with
          | none =>
            cases pure_ok h2
            exact ⟨rfl, fun _ hv => by cases hv⟩
          | some ws =>
            simp only at h2
            cases n with
            | zero => rw [applyTerm.eq_1] at h2; exact (throw_ok h2).elim
            | succ m =>
              unfold dataK? at hk
              split at hk
              · rename_i term hterm
                have ht : termOf p v = .ok term := by simp [termOf, hterm]
                rw [applyTerm.eq_2, ht] at h2
                simp only [M.run_bind, M.run_liftM_ok, M.except_ok_bind] at h2
                split at hk
                · rename_i k' hkd
                  cases hk
                  simp only [hkd] at h2
                  cases pure_ok h2
                  exact ⟨rfl, fun v hv as D env' hg => by
                    cases hv
                    exact ⟨ws, rfl, hg1 ws rfl as D env' hg⟩⟩
                · rename_i hkd
                  cases hk
                  simp only [hkd] at h2
                  cases pure_ok h2
                  exact ⟨rfl, fun v hv as D env' hg => by
                    cases hv
                    exact ⟨ws, rfl, hg1 ws rfl as D env' hg⟩⟩
                · cases hk
              · cases hk
        · cases hc
      | _ => simp [ctOf] at hc
    · cases es with
      | nil =>
        simp only [ctOfL, Option.some.injEq] at hc
        subst hc
        rw [evalArgs.eq_2] at h
        cases pure_ok h
        exact ⟨rfl, fun ws hw _ _ _ _ => by cases hw; trivial⟩
      | cons e es =>
        simp only [ctOfL] at hc
        split at hc
        · rename_i c1 cs1 he hes
          cases hc
          rw [evalArgs.eq_3] at h
          obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
          obtain ⟨rfl, hg1⟩ := ih.1 e c1 s tr o s1 tr1 he h1
          cases o with
          | none =>
            cases pure_ok h2
            exact ⟨rfl, fun _ hv => by cases hv⟩
          | some w =>
            simp only at h2
            obtain ⟨o2, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
            obtain ⟨rfl, hg2⟩ := ih.2 es cs1 _ tr1 o2 s2 tr2 hes h3
            cases o2 with
            | none =>
              cases pure_ok h4
              exact ⟨rfl, fun _ hv => by cases hv⟩
            | some ws =>
              cases pure_ok h4
              exact ⟨rfl, fun ws' hw as D env' hg => by
                cases hw
                exact ⟨hg1 w rfl as D env' hg, hg2 ws rfl as D env' hg⟩⟩
        · cases hc

/-- The constructor-tree terms of the program are internal and not multi. -/
def wrapperInternalB (t : TermId) : Bool :=
  (wrapper program t).isNone ||
    match program.term? t with
    | some term => match term.kind with
      | .decl flags (some .internal) _ => !flags.isMulti
      | _ => false
    | none => true

theorem wrapper_internal_ok :
    (List.range program.ruleLists.size).all wrapperInternalB = true := by
  native_decide

theorem wrapper_internal {t : TermId} {ct : CT} (hw : wrapper program t = some ct) {term : Term}
    (ht : termOf program t = .ok term) :
    ∃ flags ex, term.kind = .decl flags (some .internal) ex ∧ flags.isMulti = false := by
  have hlt : t < program.ruleLists.size := by
    unfold wrapper Program.rulesOf at hw
    rcases Nat.lt_or_ge t program.ruleLists.size with hlt | hge
    · exact hlt
    rw [Array.getElem?_eq_none hge] at hw
    simp at hw
  have h := List.all_eq_true.mp wrapper_internal_ok t (List.mem_range.mpr hlt)
  simp only [wrapperInternalB, hw, Option.isNone_some, Bool.false_or,
    Kill.termOf_program_eq ht] at h
  split at h
  · rename_i flags ex hk
    exact ⟨flags, ex, hk, by simpa using h⟩
  · cases h

/-- **The constructor-tree terms** (`DModel.wrap`): the run keeps the state and the value is
described by `ctA` of the arguments' descriptions. -/
theorem dWrap {ctx : Ctx} {c : SC} :
    ∀ (t : TermId) (ct : CT), wrapper program t = some ct → ∀ (cfg : Config),
      cfg.checkOverlap = false → ∀ (n : Nat) (ty : TypeId) (vs : List V) (s : LState)
        (tr : Array RuleId) (r : Option V) (s' : LState) (tr' : Array RuleId),
      (applyTerm program (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
      s' = s ∧ ∀ v, r = some v → ∀ (as : List A) (D : Nat → Prop) (env : Isle.Interp.Env V),
        γL c as D env vs → γ c (ctA as ct) D env v := by
  intro t ct hw cfg hc n ty vs s tr r s' tr' h
  cases n with
  | zero => rw [applyTerm.eq_1] at h; exact (throw_ok h).elim
  | succ k =>
  cases ht : termOf program t with
  | error e =>
    rw [applyTerm.eq_2, ht] at h
    cases h
  | ok term =>
  obtain ⟨flags, ex, hk, hm⟩ := wrapper_internal hw ht
  rcases internal_cases hc ht hk hm h with ⟨rfl, rfl⟩ |
    ⟨rl, hrl, m, env, s1, tr1, tr2, -, -, hmatch, hrhs⟩
  · exact ⟨rfl, fun v hv => by cases hv⟩
  · unfold wrapper at hw
    split at hw
    · rename_i r0 hrs
      rw [hrs, List.mem_singleton] at hrl
      subst hrl
      split at hw
      · rename_i hil
        split at hw
        · rename_i xs hxs
          split at hw
          · rename_i hnd
            have hil' : rl.iflets = [] := List.isEmpty_iff.mp hil
            cases m with
            | zero => rw [matchRule.eq_1] at hmatch; cases hmatch
            | succ m =>
            obtain ⟨env0, hma, hif⟩ := matchRule_some_inv hmatch
            rw [hil'] at hif
            cases m with
            | zero => rw [matchIfLets.eq_1] at hif; cases hif
            | succ m =>
            rw [matchIfLets.eq_2] at hif
            cases pure_ok hif
            obtain ⟨-, hb⟩ := matchArgs_binds rl.args xs vs _ env hxs hma
            exact ct_eval (c := c) (hb hnd) k |>.1 rl.rhs ct s tr r s' tr2 hw hrhs
          · cases hw
        · cases hw
      · cases hw
    · cases hw

end Backend.Proof.DefGen
