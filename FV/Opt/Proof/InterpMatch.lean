import FV.Isle.Interp

/-!
# Soundness of multi-matching (`matchPatN`) as a relation

`PatRel p msem st pat v env env'` says that the pattern `pat` describes the value `v` and that
matching it turns the environment `env` into `env'`: every `bind` extends the environment,
every extractor call is one of the values its (multi-)extractor yields in state `st`. It is a
structural recursion over the pattern, so on the concrete pattern of a rule `simp only
[PatRel, ArgsRel, AllRel]` unfolds it to a formula with one existential per extractor call.

`matchPatN_sound`: every environment `matchPatN` returns is related to the input by `PatRel`.
Rule proofs start from it instead of evaluating the matcher over a symbolic e-graph.
-/

namespace Opt.Proof

open Isle Isle.Interp

/-! ## `bindAll` in `Except` -/

theorem bindAll_ok_mem {ε α β : Type} {f : α → Except ε (List β)} :
    ∀ {l : List α} {r : List β} {b : β}, bindAll f l = .ok r → b ∈ r →
      ∃ a ∈ l, ∃ r', f a = .ok r' ∧ b ∈ r'
  | [], r, b, h, hb => by
    simp only [bindAll] at h
    cases h
    simp at hb
  | a :: as, r, b, h, hb => by
    simp only [bindAll] at h
    cases hfa : f a with
    | error e => rw [hfa] at h; cases h
    | ok bs =>
      rw [hfa] at h
      cases has : bindAll f as with
      | error e => simp only [has] at h; cases h
      | ok cs =>
        simp only [has] at h
        cases h
        rcases List.mem_append.1 hb with hb | hb
        · exact ⟨a, List.mem_cons_self .., bs, hfa, hb⟩
        · obtain ⟨a', ha', r', h1, h2⟩ := bindAll_ok_mem has hb
          exact ⟨a', List.mem_cons_of_mem _ ha', r', h1, h2⟩

section
variable {V σ : Type} (p : Program) (msem : MultiSem V σ)

mutual
/-- `pat` matches `v`, taking `env` to `env'` (one of `matchPatN`'s results). -/
def PatRel (st : σ) : Pattern → V → Env V → Env V → Prop
  | .bind _ x sub, v, env, env' => x < env.size ∧ PatRel st sub v (env.set! x (some v)) env'
  | .var _ x, v, env, env' => env' = env ∧ ∃ w, env[x]? = some (some w) ∧ msem.eq v w = true
  | .constBool _ b, v, env, env' => env' = env ∧ msem.eq v (msem.bool b) = true
  | .constInt ty i, v, env, env' => env' = env ∧ msem.eq v (msem.int ty i) = true
  | .constPrim ty n, v, env, env' => env' = env ∧ ∃ c, msem.prim ty n = some c ∧ msem.eq v c = true
  | .wildcard _, _, env, env' => env' = env
  | .and _ ps, v, env, env' => AllRel st ps v env env'
  | .term ty t args, v, env, env' => ∃ term, termOf p t = .ok term ∧
    match term.kind with
    | .enumVariant k => ∃ fs, msem.unData ty v = some (k, fs) ∧ ArgsRel st args fs env env'
    | .struct => ∃ k fs, msem.unData ty v = some (k, fs) ∧ ArgsRel st args fs env env'
    | .decl flags _ (some (.external _ _)) =>
      if flags.isMulti then
        ∃ fss, msem.extractMulti term v st = .ok fss ∧ ∃ fs ∈ fss, ArgsRel st args fs env env'
      else ∃ fs, msem.extract term v st = .ok fs ∧ ArgsRel st args fs env env'
    | _ => False
/-- Every pattern of an `and` matches the same value, in sequence. -/
def AllRel (st : σ) : List Pattern → V → Env V → Env V → Prop
  | [], _, env, env' => env' = env
  | q :: qs, v, env, env' => ∃ e, PatRel st q v env e ∧ AllRel st qs v e env'
/-- Patterns against values pointwise, in sequence. -/
def ArgsRel (st : σ) : List Pattern → List V → Env V → Env V → Prop
  | [], [], env, env' => env' = env
  | q :: qs, w :: ws, env, env' => ∃ e, PatRel st q w env e ∧ ArgsRel st qs ws e env'
  | _, _, _, _ => False
end

theorem except_pure_eq_ok {ε α : Type} (a b : α) : (pure a : Except ε α) = .ok b ↔ a = b := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst h; rfl

mutual
theorem matchPatN_sound (st : σ) : ∀ (pat : Pattern) (v : V) (env : Env V) (envs : List (Env V))
    (env' : Env V), matchPatN p msem st pat v env = .ok envs → env' ∈ envs →
    PatRel p msem st pat v env env'
  | .bind _ x sub, v, env, envs, env', h, hm => by
    simp only [matchPatN] at h
    split at h
    · exact ⟨by assumption, matchPatN_sound st sub _ _ _ _ h hm⟩
    · cases h
  | .var _ x, v, env, envs, env', h, hm => by
    simp only [matchPatN] at h
    split at h
    · rename_i w hw
      simp only [except_pure_eq_ok] at h
      subst h
      split at hm
      · simp only [List.mem_singleton] at hm
        exact ⟨hm, w, hw, by assumption⟩
      · simp at hm
    · cases h
  | .constBool _ b, v, env, envs, env', h, hm => by
    simp only [matchPatN, except_pure_eq_ok] at h
    subst h
    split at hm
    · simp only [List.mem_singleton] at hm; exact ⟨hm, by assumption⟩
    · simp at hm
  | .constInt ty i, v, env, envs, env', h, hm => by
    simp only [matchPatN, except_pure_eq_ok] at h
    subst h
    split at hm
    · simp only [List.mem_singleton] at hm; exact ⟨hm, by assumption⟩
    · simp at hm
  | .constPrim ty n, v, env, envs, env', h, hm => by
    simp only [matchPatN] at h
    split at h
    · rename_i c hc
      simp only [except_pure_eq_ok] at h
      subst h
      split at hm
      · simp only [List.mem_singleton] at hm; exact ⟨hm, c, hc, by assumption⟩
      · simp at hm
    · cases h
  | .wildcard _, v, env, envs, env', h, hm => by
    simp only [matchPatN, except_pure_eq_ok] at h
    subst h
    simpa [PatRel] using hm
  | .and _ ps, v, env, envs, env', h, hm => by
    simp only [matchPatN] at h
    exact matchAllN_sound st ps v env envs env' h hm
  | .term ty t args, v, env, envs, env', h, hm => by
    simp only [matchPatN] at h
    cases ht : termOf p t with
    | error e => rw [ht] at h; cases h
    | ok term =>
      rw [ht] at h
      simp only [bind, Except.bind] at h
      refine ⟨term, ht, ?_⟩
      split at h
      · rename_i k hk
        rw [hk]
        split at h
        · rename_i k' fs hu
          split at h
          · rename_i hkk
            have : k = k' := by simpa using hkk
            subst this
            exact ⟨fs, hu, matchArgsN_sound st args fs env envs env' h hm⟩
          · simp only [except_pure_eq_ok] at h; subst h; simp at hm
        · cases h
      · rename_i hk
        rw [hk]
        split at h
        · rename_i k' fs hu
          exact ⟨k', fs, hu, matchArgsN_sound st args fs env envs env' h hm⟩
        · cases h
      · rename_i flags c fn inf hk
        rw [hk]
        simp only
        split at h
        · rename_i hmul
          simp only [hmul, ite_true]
          split at h
          · rename_i fss hx
            obtain ⟨fs, hfs, r', h1, h2⟩ := bindAll_ok_mem h hm
            exact ⟨fss, hx, fs, hfs, matchArgsN_sound st args fs env r' env' h1 h2⟩
          · simp only [except_pure_eq_ok] at h; subst h; simp at hm
          · cases h
        · rename_i hmul
          simp only [hmul]
          split at h
          · rename_i fs hx
            exact ⟨fs, hx, matchArgsN_sound st args fs env envs env' h hm⟩
          · split at h
            · cases h
            · simp only [except_pure_eq_ok] at h; subst h; simp at hm
          · cases h
      · cases h
theorem matchAllN_sound (st : σ) : ∀ (ps : List Pattern) (v : V) (env : Env V)
    (envs : List (Env V)) (env' : Env V), matchAllN p msem st ps v env = .ok envs → env' ∈ envs →
    AllRel p msem st ps v env env'
  | [], v, env, envs, env', h, hm => by
    simp only [matchAllN, except_pure_eq_ok] at h
    subst h
    simpa [AllRel] using hm
  | q :: qs, v, env, envs, env', h, hm => by
    simp only [matchAllN, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i es hq
      obtain ⟨e, he, r', h1, h2⟩ := bindAll_ok_mem h hm
      exact ⟨e, matchPatN_sound st q v env es e hq he, matchAllN_sound st qs v e r' env' h1 h2⟩
theorem matchArgsN_sound (st : σ) : ∀ (ps : List Pattern) (vs : List V) (env : Env V)
    (envs : List (Env V)) (env' : Env V), matchArgsN p msem st ps vs env = .ok envs → env' ∈ envs →
    ArgsRel p msem st ps vs env env'
  | [], [], env, envs, env', h, hm => by
    simp only [matchArgsN, except_pure_eq_ok] at h
    subst h
    simpa [ArgsRel] using hm
  | q :: qs, w :: ws, env, envs, env', h, hm => by
    simp only [matchArgsN, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i es hq
      obtain ⟨e, he, r', h1, h2⟩ := bindAll_ok_mem h hm
      exact ⟨e, matchPatN_sound st q w env es e hq he, matchArgsN_sound st qs ws e r' env' h1 h2⟩
  | [], _ :: _, env, envs, env', h, hm => by simp [matchArgsN] at h
  | _ :: _, [], env, envs, env', h, hm => by simp [matchArgsN] at h
end

end

end Opt.Proof
