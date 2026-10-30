import FV.Backend.Proof.IselGeneric
import FV.Backend.Proof.IselPrgLe
import FV.Backend.Proof.IselPrgModel

/-!
# Progress of the ISLE lowering (V7): patterns

Under the extern helpers' `Model`, the abstract matching `aPat`/`aPatAll`/`aPatArgs` is sound
for the interpreter's `matchPat`/`matchAll`/`matchArgs` (`aPat_prog`, …): from a value the
abstract value describes and an environment the abstract environment describes, matching never
throws, a successful match yields an environment one of the abstract environments describes, and
it surely succeeds when the abstract matching says so (`MatchOK`). Matching uses no fuel, and the
embedding state is arbitrary.
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Interp Isle.Aarch64

variable {f : Clif.Function} {ctx : Ctx}

/-! ## Generic helpers -/

theorem obind_some {α β : Type} {x : Option α} {g : α → Option β} {b : β}
    (h : (x >>= g) = some b) : ∃ a, x = some a ∧ g a = some b := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

theorem mapM_some_mem {α β : Type} {g : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM g = some ys → ∀ x ∈ xs, ∃ y ∈ ys, g x = some y
  | [], _, _ => fun _ h => by cases h
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y0, h0, h⟩ := obind_some h
    obtain ⟨ys', h1, h⟩ := obind_some h
    simp only [pure, Option.some.injEq] at h
    subst h
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨y0, List.mem_cons_self .., h0⟩
    · obtain ⟨y, hy, hg⟩ := mapM_some_mem h1 z hz
      exact ⟨y, List.mem_cons_of_mem _ hy, hg⟩

/-- The maximal cost bounds every member. -/
theorem le_foldl_max : ∀ (cs : List Nat) (b : Nat), b ≤ cs.foldl max b
  | [], _ => Nat.le_refl _
  | c :: cs, b => Nat.le_trans (Nat.le_max_left b c) (le_foldl_max cs (max b c))

theorem mem_le_foldl_max : ∀ {cs : List Nat} {c : Nat}, c ∈ cs → ∀ b, c ≤ cs.foldl max b
  | x :: cs, c, h, b => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right b c) (le_foldl_max cs _)
    · exact mem_le_foldl_max h _

theorem le_maxCost {cs : List Nat} {c : Nat} (h : c ∈ cs) : c ≤ maxCost cs :=
  mem_le_foldl_max h 1

theorem one_le_maxCost (cs : List Nat) : 1 ≤ maxCost cs := le_foldl_max cs 1

/-! ## Match outcomes -/

/-- The outcome `r` of a match is described by `(envs, must)`: a successful match yields an
environment one of `envs` describes, and the match succeeds if `must`. -/
def MatchOK (f : Clif.Function) (ctx : Ctx) (envs : List AEnv) (must : Bool)
    (r : Option (Isle.Interp.Env V)) : Prop :=
  (∀ env', r = some env' → ∃ ae ∈ envs, EnvOK f ctx ae env') ∧ (must = true → r.isSome)

theorem matchOK_none (envs : List AEnv) : MatchOK f ctx envs false none :=
  ⟨fun _ h => (nomatch h), fun h => (nomatch h)⟩

theorem matchOK_cond {aenv : AEnv} {env : Isle.Interp.Env V} (he : EnvOK f ctx aenv env) {c : Bool}
    {envs : List AEnv} {must : Bool} (h1 : c = true → aenv ∈ envs) (h2 : must = true → c = true) :
    MatchOK f ctx envs must (if c then some env else none) := by
  cases c with
  | true => exact ⟨fun e h => by cases h; exact ⟨aenv, h1 rfl, he⟩, fun _ => rfl⟩
  | false => exact ⟨fun _ h => (nomatch h), fun h => (nomatch h2 h)⟩

theorem matchOK_and {envs : List AEnv} {m m' : Bool} {r : Option (Isle.Interp.Env V)}
    (h : MatchOK f ctx envs m r) : MatchOK f ctx envs (m' && m) r :=
  ⟨h.1, fun hm => h.2 (by simp at hm; exact hm.2)⟩

/-- A match from one of the abstract environments of a combination. -/
theorem matchOK_comb {rs : List (List AEnv × Bool)} {y : List AEnv × Bool} (hy : y ∈ rs)
    {r : Option (Isle.Interp.Env V)} (h : MatchOK f ctx y.1 y.2 r) (m : Bool) :
    MatchOK f ctx (comb rs).1 (m && (comb rs).2) r := by
  refine ⟨fun e he => ?_, fun hm => h.2 ?_⟩
  · obtain ⟨ae, hae, hok⟩ := h.1 e he
    exact ⟨ae, List.mem_flatMap.mpr ⟨y, hy, hae⟩, hok⟩
  · simp only [comb, Bool.and_eq_true, List.all_eq_true] at hm
    exact hm.2 y hy

/-! ## The embedding -/

theorem sem_eq_iff {a b : V} : (sem ctx).eq a b = true ↔ a = b := by
  show (a == b) = true ↔ a = b
  exact beq_iff_eq

theorem sem_unData {ty k : Nat} {ws : List V} :
    (sem ctx).unData ty (.data ty k ws) = some (k, ws) := by
  simp [sem]

/-! ## Enum and struct fields -/

theorem joinL_left : ∀ {fs gs hs : List PA}, joinL fs gs = some hs →
    ∀ {ws : List V}, γL f ctx fs ws → γL f ctx hs ws
  | [], [], hs, h, ws, hw => by simp [joinL] at h; subst h; exact hw
  | a :: fs, b :: gs, hs, h, ws, hw => by
    simp only [joinL] at h
    obtain ⟨hs', h1, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨w, ws', rfl, hw1, hw2⟩ := γL_cons_iff.mp hw
    exact ⟨by simp only [γ, γAny]; exact .inl hw1, joinL_left h1 hw2⟩
  | [], _ :: _, _, h, _, _ => by simp [joinL] at h
  | _ :: _, [], _, h, _, _ => by simp [joinL] at h

theorem joinL_right : ∀ {fs gs hs : List PA}, joinL fs gs = some hs →
    ∀ {ws : List V}, γL f ctx gs ws → γL f ctx hs ws
  | [], [], hs, h, ws, hw => by simp [joinL] at h; subst h; exact hw
  | a :: fs, b :: gs, hs, h, ws, hw => by
    simp only [joinL] at h
    obtain ⟨hs', h1, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨w, ws', rfl, hw1, hw2⟩ := γL_cons_iff.mp hw
    exact ⟨by simp only [γ, γAny]; exact .inr (.inl hw1), joinL_right h1 hw2⟩
  | [], _ :: _, _, h, _, _ => by simp [joinL] at h
  | _ :: _, [], _, h, _, _ => by simp [joinL] at h

section Model
variable {aext : TermId → PA → Option (List (List PA) × Bool)}
  {actor : TermId → List PA → Option (PA × Bool)} {aidata : Nat → Option (List PA)}
  (M : Model f ctx aext actor aidata)

set_option linter.unusedSectionVars false in
include M in
mutual
/-- **Enum fields** (`aun`): the value is data of type `ty`; if it is variant `k`, the fields
are described; it is surely variant `k` if `must`. -/
theorem aun_sound (ty k : Nat) (a : PA) (x : Option (List PA)) (m : Bool) (v : V)
    (h : aun aidata ty k a = some (x, m)) (hv : γ f ctx a v) :
    ∃ k' ws, v = .data ty k' ws ∧ (m = true → k = k') ∧
      (k = k' → ∃ fs, x = some fs ∧ γL f ctx fs ws) := by
  unfold aun at h
  split at h
  next => simp [γ] at hv
  next t k0 fs =>
    simp only [γ] at hv
    obtain ⟨ws, rfl, hws⟩ := hv
    by_cases ht : t = ty
    · subst ht
      simp only [beq_self_eq_true, ↓reduceIte] at h
      by_cases hk : k = k0
      · subst hk
        simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨k, ws, rfl, fun _ => rfl, fun _ => ⟨fs, rfl, hws⟩⟩
      · simp only [beq_iff_eq, hk, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨k0, ws, rfl, fun h => (nomatch h), fun h => absurd h hk⟩
    · simp [ht] at h
  next =>
    obtain ⟨k', ws, afs, rfl, hk', hws⟩ := M.idata v hv
    by_cases ht : ty = tyInstData
    · subst ht
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨k', ws, rfl, fun h => (nomatch h), fun e => by subst e; exact ⟨afs, hk', hws⟩⟩
    · simp [ht] at h
  next as =>
    exact aunAlts_sound ty k as x m v h (by simp only [γ] at hv; exact hv)
  next => cases h
termination_by sizeOf a
/-- `aun` of alternatives. -/
theorem aunAlts_sound (ty k : Nat) (as : List PA) (x : Option (List PA)) (m : Bool) (v : V)
    (h : aun.aunAlts aidata ty k as = some (x, m)) (hv : γAny f ctx as v) :
    ∃ k' ws, v = .data ty k' ws ∧ (m = true → k = k') ∧
      (k = k' → ∃ fs, x = some fs ∧ γL f ctx fs ws) := by
  match as, h, hv with
  | [], _, hv => exact hv.elim
  | a :: as, h, hv =>
    rw [aun.aunAlts] at h
    obtain ⟨⟨x1, m1⟩, h1, h⟩ := obind_some h
    obtain ⟨⟨y, m2⟩, h2, h⟩ := obind_some h
    rw [γAny] at hv
    cases x1 with
    | none =>
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rcases hv with hv | hv
      · obtain ⟨k', ws, rfl, -, hk⟩ := aun_sound ty k a none m1 v h1 hv
        refine ⟨k', ws, rfl, fun h => (nomatch h), fun e => ?_⟩
        obtain ⟨fs, hfs, -⟩ := hk e
        cases hfs
      · obtain ⟨k', ws, rfl, -, hk⟩ := aunAlts_sound ty k as _ m2 v h2 hv
        exact ⟨k', ws, rfl, fun h => (nomatch h), hk⟩
    | some fs =>
      cases y with
      | none =>
        simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rcases hv with hv | hv
        · obtain ⟨k', ws, rfl, hm, hk⟩ := aun_sound ty k a (some fs) m1 v h1 hv
          refine ⟨k', ws, rfl, fun e => hm (by simp at e; exact e.1.1), hk⟩
        · obtain ⟨k', ws, rfl, -, hk⟩ := aunAlts_sound ty k as none m2 v h2 hv
          refine ⟨k', ws, rfl, fun e => ?_, fun e => ?_⟩
          · simp only [Bool.and_eq_true, List.isEmpty_iff] at e
            rw [e.2] at hv; exact hv.elim
          · obtain ⟨_, hfs, -⟩ := hk e
            cases hfs
      | some gs =>
        obtain ⟨hs, hj, h⟩ := obind_some h
        simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rcases hv with hv | hv
        · obtain ⟨k', ws, rfl, hm, hk⟩ := aun_sound ty k a (some fs) m1 v h1 hv
          refine ⟨k', ws, rfl, fun e => hm (by simp at e; exact e.1), fun e => ?_⟩
          obtain ⟨fs', hfs, hws⟩ := hk e
          cases hfs
          exact ⟨hs, rfl, joinL_left hj hws⟩
        · obtain ⟨k', ws, rfl, hm, hk⟩ := aunAlts_sound ty k as (some gs) m2 v h2 hv
          refine ⟨k', ws, rfl, fun e => hm (by simp at e; exact e.2), fun e => ?_⟩
          obtain ⟨gs', hgs, hws⟩ := hk e
          cases hgs
          exact ⟨hs, rfl, joinL_right hj hws⟩
termination_by sizeOf as
end

/-- **Struct fields** (`aunS`). -/
theorem aunS_sound {ty : Nat} {a : PA} {fs : List PA} {v : V} (h : aunS ty a = some fs)
    (hv : γ f ctx a v) : ∃ k' ws, v = .data ty k' ws ∧ γL f ctx fs ws := by
  unfold aunS at h
  split at h
  next t k0 fs' =>
    simp only [γ] at hv
    obtain ⟨ws, rfl, hws⟩ := hv
    by_cases ht : t = ty
    · subst ht
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨k0, ws, rfl, hws⟩
    · simp [ht] at h
  next => cases h

theorem matchOK_single {aenv : AEnv} {env : Isle.Interp.Env V} (he : EnvOK f ctx aenv env)
    (c : Bool) : MatchOK f ctx [aenv] false (if c then some env else none) :=
  matchOK_cond he (fun _ => List.mem_singleton_self _) (fun h => (nomatch h))

theorem matchOK_some {aenv : AEnv} {env : Isle.Interp.Env V} (he : EnvOK f ctx aenv env)
    (must : Bool) : MatchOK f ctx [aenv] must (some env) :=
  ⟨fun e h => by cases h; exact ⟨aenv, List.mem_singleton_self _, he⟩, fun _ => rfl⟩

set_option linter.unusedSectionVars false in
include M in
mutual
/-- **Pattern progress**: matching `q` against a value `a` describes never throws; its outcome
is described by `aPat`'s environments and surety. -/
theorem aPat_prog (p : Program) (st : LState) (q : Pattern) (a : PA) (aenv : AEnv) (v : V)
    (env : Isle.Interp.Env V) (envs : List AEnv) (must : Bool)
    (h : aPat p aext aidata a q aenv = some (envs, must)) (hv : γ f ctx a v)
    (he : EnvOK f ctx aenv env) :
    ∃ r, matchPat p (sem ctx) st q v env = .ok r ∧ MatchOK f ctx envs must r := by
  unfold aPat at h
  split at h
  · exact (isBot_sound ‹_› v hv).elim
  rename_i hnb
  clear hnb
  cases q with
  | bind ty x sub =>
    dsimp only at h
    split at h
    · rename_i hx
      obtain ⟨r, hr, hok⟩ := aPat_prog p st sub a _ v _ envs must h hv (envOK_set he hv x)
      refine ⟨r, ?_, hok⟩
      rw [matchPat.eq_1, ite_eq_left (he.1 ▸ hx)]
      exact hr
    · cases h
  | var ty x =>
    dsimp only at h
    split at h
    · rename_i b hb
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨w, hw, -⟩ := he.2 x b hb
      exact ⟨_, by rw [matchPat.eq_2, hw]; rfl, matchOK_single he ((sem ctx).eq v w)⟩
    · cases h
  | constBool ty b =>
    dsimp only at h
    refine ⟨_, by rw [matchPat.eq_3]; rfl, ?_⟩
    split at h
    · rename_i c
      simp only [γ] at hv
      obtain ⟨x, rfl, hx⟩ := hv
      have hxc : c = x := by rcases hx with hx | hx <;> simp_all
      subst hxc
      by_cases hbc : b = c
      · subst hbc
        simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact matchOK_cond he (fun _ => List.mem_singleton_self _) (fun _ => sem_eq_iff.mpr rfl)
      · simp only [beq_iff_eq, hbc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine matchOK_cond he (fun hc => ?_) (fun h => (nomatch h))
        have := sem_eq_iff.mp hc
        simp only [sem, V.bool.injEq] at this
        exact absurd this.symm hbc
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact matchOK_single he _
  | constInt ty i =>
    dsimp only at h
    refine ⟨_, by rw [matchPat.eq_4]; rfl, ?_⟩
    split at h
    · rename_i lo hi
      simp only [γ] at hv
      obtain ⟨j, rfl, hlo, hhi⟩ := hv
      have hsem : ∀ c, (sem ctx).eq (.int j) ((sem ctx).int ty i) = c → (c = true ↔ j = normInt ty i) := by
        intro c hc; subst hc; rw [sem_eq_iff]; simp [sem]
      cases lo <;> cases hi <;> simp only [Bool.or_false, Bool.false_or] at h <;> split at h <;>
        cases h <;> refine matchOK_cond he (fun hc => ?_) (fun hm => ?_)
      all_goals first
        | exact List.mem_singleton_self _
        | (exfalso
           rename_i hcnd
           have hj := (hsem _ rfl).mp hc
           have h1 := hlo
           have h2 := hhi
           simp only [Option.some.injEq, forall_eq', reduceCtorEq, false_implies,
             implies_true] at h1 h2
           simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.false_eq_true] at hcnd <;> omega)
        | (apply (hsem _ rfl).mpr
           have h1 := hlo
           have h2 := hhi
           simp only [Option.some.injEq, forall_eq', reduceCtorEq, false_implies,
             implies_true] at h1 h2
           simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq, reduceCtorEq, false_and,
             and_false, Bool.false_eq_true] at hm <;> omega)
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact matchOK_single he _
  | constPrim ty n =>
    dsimp only at h
    have hp' : (sem ctx).prim ty n = primP ty n := rfl
    cases hp : primP ty n with
    | none => rw [hp] at h; cases h
    | some c =>
      rw [hp] at h
      refine ⟨_, by rw [matchPat.eq_5, hp', hp]; rfl, ?_⟩
      cases c with
      | ty t =>
        dsimp only at h
        cases a with
        | ty ts =>
          dsimp only at h
          simp only [γ] at hv
          obtain ⟨t', ht', rfl⟩ := hv
          by_cases hc : ts.contains t = true
          · rw [ite_eq_left hc] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine matchOK_cond he (fun _ => List.mem_singleton_self _) (fun hm => ?_)
            have := List.all_eq_true.mp hm t' ht'
            simp only [beq_iff_eq] at this
            subst this
            exact sem_eq_iff.mpr rfl
          · rw [ite_eq_right hc] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine matchOK_cond he (fun hq => ?_) (fun h => (nomatch h))
            have := sem_eq_iff.mp hq
            cases this
            exact absurd (List.elem_iff.mpr ht') hc
        | _ =>
          dsimp only at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact matchOK_single he _
      | _ =>
        dsimp only at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact matchOK_single he _
  | wildcard ty =>
    dsimp only at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, by rw [matchPat.eq_6]; rfl, matchOK_some he _⟩
  | and ty ps =>
    dsimp only at h
    rw [matchPat.eq_7]
    exact aPatAll_prog p st ps a aenv v env envs must h hv he
  | term ty t args =>
    dsimp only at h
    rw [matchPat.eq_8]
    cases ht : termOf p t with
    | error e => rw [ht] at h; cases h
    | ok term =>
      rw [ht] at h
      rw [Isle.Interp.M.except_ok_bind]
      dsimp only at h
      cases hk : term.kind with
      | enumVariant k =>
        rw [hk] at h
        dsimp only at h ⊢
        cases hau : aun aidata ty k a with
        | none => rw [hau] at h; cases h
        | some xm =>
          obtain ⟨x, m⟩ := xm
          rw [hau] at h
          obtain ⟨k', ws, rfl, hm, hk'⟩ := aun_sound M ty k a x m v hau hv
          rw [sem_unData]
          dsimp only
          by_cases hkk : k = k'
          · subst hkk
            obtain ⟨fs, rfl, hws⟩ := hk' rfl
            simp only at h
            obtain ⟨⟨e1, m1⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
            simp only [Prod.mk.injEq] at h2
            obtain ⟨rfl, rfl⟩ := h2
            obtain ⟨r, hr, hok⟩ := aPatArgs_prog p st args fs aenv ws env e1 m1 h1 hws he
            exact ⟨r, by simp [hr], matchOK_and hok⟩
          · simp only [beq_iff_eq, hkk, ↓reduceIte]
            have hm' : m = false := by
              cases m
              · rfl
              · exact absurd (hm rfl) hkk
            refine ⟨none, rfl, fun _ h => (nomatch h), fun hmust => ?_⟩
            cases x with
            | none =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              rw [← h.2] at hmust
              cases hmust
            | some fs =>
              obtain ⟨⟨e1, m1⟩, -, h2⟩ := Option.map_eq_some_iff.mp h
              simp only [Prod.mk.injEq] at h2
              rw [← h2.2, hm'] at hmust
              cases hmust
      | struct =>
        rw [hk] at h
        dsimp only at h ⊢
        cases has : aunS ty a with
        | none => rw [has] at h; cases h
        | some fs =>
          rw [has] at h
          simp only at h
          obtain ⟨k', ws, rfl, hws⟩ := aunS_sound has hv
          rw [sem_unData]
          exact aPatArgs_prog p st args fs aenv ws env envs must h hws he
      | decl flags c ex =>
        rw [hk] at h
        cases ex with
        | none => cases c <;> simp at h
        | some ex =>
          cases ex with
          | internal form => cases c <;> simp at h
          | external fn inf =>
            simp only at h ⊢
            cases hmul : flags.isMulti
            · simp only [hmul, Bool.false_eq_true, ↓reduceIte] at h ⊢
              cases hae : aext term.id a with
              | none => rw [hae] at h; cases h
              | some om =>
                obtain ⟨outs, mst⟩ := om
                rw [hae] at h
                simp only at h
                rcases M.ext term a outs mst v st hae hv with ⟨fs, hx, out, hout, hfs⟩ | ⟨hx, hmf⟩
                · have hx' : (sem ctx).extract term v st = .ok fs := hx
                  rw [hx']
                  simp only
                  split at h
                  · cases h
                  obtain ⟨rs, hrs, h2⟩ := Option.map_eq_some_iff.mp h
                  simp only [Prod.mk.injEq] at h2
                  obtain ⟨rfl, rfl⟩ := h2
                  obtain ⟨⟨e1, m1⟩, hy, hyout⟩ := mapM_some_mem hrs out hout
                  obtain ⟨r, hr, hok⟩ := aPatArgs_prog p st args out aenv fs env e1 m1 hyout hfs he
                  exact ⟨r, hr, matchOK_comb hy hok mst⟩
                · have hx' : (sem ctx).extract term v st = .fail := hx
                  rw [hx']
                  subst hmf
                  cases inf
                  · simp only [Bool.false_eq_true, ↓reduceIte]
                    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at h
                    obtain ⟨rs, -, h2⟩ := Option.map_eq_some_iff.mp h
                    simp only [Prod.mk.injEq] at h2
                    obtain ⟨-, rfl⟩ := h2
                    exact ⟨none, rfl, matchOK_none _⟩
                  · simp at h
            · simp [hmul] at h
termination_by sizeOf q
/-- `aPatAll`: every pattern against the same value. -/
theorem aPatAll_prog (p : Program) (st : LState) (qs : List Pattern) (a : PA) (aenv : AEnv)
    (v : V) (env : Isle.Interp.Env V) (envs : List AEnv) (must : Bool)
    (h : aPatAll p aext aidata a qs aenv = some (envs, must)) (hv : γ f ctx a v)
    (he : EnvOK f ctx aenv env) :
    ∃ r, matchAll p (sem ctx) st qs v env = .ok r ∧ MatchOK f ctx envs must r := by
  match qs, h with
  | [], h =>
    rw [aPatAll] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, by rw [matchAll.eq_1]; rfl, matchOK_some he _⟩
  | q :: qs, h =>
    rw [aPatAll] at h
    obtain ⟨⟨envs1, m⟩, h1, h⟩ := obind_some h
    obtain ⟨rs, hrs, h⟩ := obind_some h
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨r1, hr1, hok1⟩ := aPat_prog p st q a aenv v env envs1 m h1 hv he
    rw [matchAll.eq_2, hr1]
    simp only [Isle.Interp.M.except_ok_bind]
    cases r1 with
    | none =>
      refine ⟨none, rfl, fun _ h => (nomatch h), fun hm => ?_⟩
      simp only [Bool.and_eq_true] at hm
      exact absurd (hok1.2 hm.1) (by simp)
    | some env1 =>
      obtain ⟨ae, hae, he1⟩ := hok1.1 env1 rfl
      obtain ⟨⟨e2, m2⟩, hy, hyq⟩ := mapM_some_mem hrs ae hae
      obtain ⟨r, hr, hok⟩ := aPatAll_prog p st qs a ae v env1 e2 m2 hyq hv he1
      exact ⟨r, hr, matchOK_comb hy hok m⟩
termination_by sizeOf qs
/-- `aPatArgs`: patterns against values pointwise. -/
theorem aPatArgs_prog (p : Program) (st : LState) (qs : List Pattern) (as : List PA)
    (aenv : AEnv) (vs : List V) (env : Isle.Interp.Env V) (envs : List AEnv) (must : Bool)
    (h : aPatArgs p aext aidata as qs aenv = some (envs, must)) (hv : γL f ctx as vs)
    (he : EnvOK f ctx aenv env) :
    ∃ r, matchArgs p (sem ctx) st qs vs env = .ok r ∧ MatchOK f ctx envs must r := by
  match qs, as, vs, h, hv with
  | [], [], [], h, _ =>
    rw [aPatArgs] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, by rw [matchArgs.eq_1]; rfl, matchOK_some he _⟩
  | q :: qs, a :: as, v :: vs, h, ⟨hv1, hv2⟩ =>
    rw [aPatArgs] at h
    obtain ⟨⟨envs1, m⟩, h1, h⟩ := obind_some h
    obtain ⟨rs, hrs, h⟩ := obind_some h
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨r1, hr1, hok1⟩ := aPat_prog p st q a aenv v env envs1 m h1 hv1 he
    rw [matchArgs.eq_2, hr1]
    simp only [Isle.Interp.M.except_ok_bind]
    cases r1 with
    | none =>
      refine ⟨none, rfl, fun _ h => (nomatch h), fun hm => ?_⟩
      simp only [Bool.and_eq_true] at hm
      exact absurd (hok1.2 hm.1) (by simp)
    | some env1 =>
      obtain ⟨ae, hae, he1⟩ := hok1.1 env1 rfl
      obtain ⟨⟨e2, m2⟩, hy, hyq⟩ := mapM_some_mem hrs ae hae
      obtain ⟨r, hr, hok⟩ := aPatArgs_prog p st qs as ae vs env1 e2 m2 hyq hv2 he1
      exact ⟨r, hr, matchOK_comb hy hok m⟩
  | [], _ :: _, _, h, _ => simp [aPatArgs] at h
  | _ :: _, [], _, h, _ => simp [aPatArgs] at h
  | [], [], _ :: _, _, hv => exact hv.elim
  | _ :: _, _ :: _, [], _, hv => exact hv.elim
termination_by sizeOf qs
end

end Model

end Backend.Proof.Prg
