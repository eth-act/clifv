import FV.Arm.MinTheory
import FV.Backend.Proof.IselPrgDom

/-!
# Progress of the ISLE lowering (V7): soundness of the order and of the splitting

`le_sound`: every value `a` describes, `b` describes when `PA.le a b`; `leL_sound` pointwise.
`isBot_sound`: a pruned abstract value describes nothing. `split_sound`/`splitL_sound`: the cases
of an abstract value (argument list) cover it. Also the basics of `γAny`, `γL` and `EnvOK`.
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Aarch64

variable {f : Clif.Function} {ctx : Ctx}

/-! ## `γAny`, `γL` -/

theorem γAny_iff : ∀ {as : List PA} {v : V}, γAny f ctx as v ↔ ∃ a ∈ as, γ f ctx a v
  | [], v => by simp [γAny]
  | a :: as, v => by
    rw [γAny, γAny_iff]
    simp

theorem γL_nil_iff {vs : List V} : γL f ctx [] vs ↔ vs = [] := by
  cases vs <;> simp [γL]

theorem γL_cons_iff {a : PA} {as : List PA} {vs : List V} :
    γL f ctx (a :: as) vs ↔ ∃ v vs', vs = v :: vs' ∧ γ f ctx a v ∧ γL f ctx as vs' := by
  cases vs with
  | nil => simp [γL]
  | cons w ws => simp only [γL, List.cons.injEq]; exact ⟨fun h => ⟨w, ws, ⟨rfl, rfl⟩, h⟩,
      fun ⟨_, _, ⟨h1, h2⟩, h⟩ => h1 ▸ h2 ▸ h⟩

theorem γL_length : ∀ {as : List PA} {vs : List V}, γL f ctx as vs → as.length = vs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [γL_length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem γL_get : ∀ {as : List PA} {vs : List V}, γL f ctx as vs →
    ∀ (i : Nat) (a : PA) (v : V), as[i]? = some a → vs[i]? = some v → γ f ctx a v
  | [], [], _, _, _, _, h, _ => by cases h
  | a :: as, w :: vs, ⟨h1, h2⟩, i, b, v, ha, hv => by
    cases i with
    | zero => simp at ha hv; subst ha hv; exact h1
    | succ i => exact γL_get h2 i b v (by simpa using ha) (by simpa using hv)
  | [], _ :: _, h, _, _, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _, _, _ => h.elim

/-- Every member of the values is described by a member of the abstract values. -/
theorem γL_mem : ∀ {as : List PA} {vs : List V}, γL f ctx as vs →
    ∀ v ∈ vs, ∃ a ∈ as, γ f ctx a v
  | [], [], _ => fun _ h => by cases h
  | a :: as, w :: vs, ⟨h1, h2⟩ => by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨a, List.mem_cons_self .., h1⟩
    · obtain ⟨b, hb, hbv⟩ := γL_mem h2 v hv
      exact ⟨b, List.mem_cons_of_mem _ hb, hbv⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- An operand leaf of a given count is one of unknown count. -/
theorem opOk_none {k : OK} {n : Option Nat} {o : Opnd} (h : OpOk ctx k n o) : OpOk ctx k none o := by
  cases k
  case funcRef => obtain ⟨fn, ext, h1, h2, h3, _⟩ := h; exact ⟨fn, ext, h1, h2, h3, .inl rfl⟩
  case sig => obtain ⟨s, h1, h2, _⟩ := h; exact ⟨s, h1, h2, .inl rfl⟩
  case exnTable => obtain ⟨s, items, h1, h2, _⟩ := h; exact ⟨s, items, h1, h2, .inl rfl⟩
  case exnTry => obtain ⟨s, items, h1, h2, h3, _⟩ := h; exact ⟨s, items, h1, h2, h3, .inl rfl⟩
  all_goals exact h

deriving instance ReflBEq, LawfulBEq for CTy
deriving instance ReflBEq, LawfulBEq for OK

/-! ## The order -/

/-- A zipped pointwise check of a sound relation is sound for `γL`. -/
theorem zipLe_sound {R : PA → PA → Bool}
    (hR : ∀ a b, R a b = true → ∀ v, γ f ctx a v → γ f ctx b v) :
    ∀ (as bs : List PA), (as.length == bs.length && (as.zip bs).all (fun q => R q.1 q.2)) = true →
      ∀ vs, γL f ctx as vs → γL f ctx bs vs
  | [], [], _, _, hv => hv
  | a :: as, b :: bs, h, v :: vs, ⟨h1, h2⟩ => by
    simp only [List.length_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq,
      Nat.add_right_cancel_iff] at h
    exact ⟨hR a b h.2.1 v h1, zipLe_sound hR as bs
      (by simp only [Bool.and_eq_true, beq_iff_eq]; exact ⟨h.1, h.2.2⟩) vs h2⟩
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | _ :: _, _ :: _, _, [], hv => hv.elim

/-- **The order at any depth is sound.** -/
theorem leF_sound (n : Nat) :
    ∀ (a b : PA), PA.leF n a b = true → ∀ v, γ f ctx a v → γ f ctx b v := by
  induction n with
  | zero => intro a b h; simp [PA.leF] at h
  | succ n ih =>
  intro a b h v hv
  unfold PA.leF at h
  split at h
  next => simp [γ] at hv
  next => simp [γ]
  next =>
    simp only [γ] at hv
    obtain ⟨x, hx, hxv⟩ := γAny_iff.mp hv
    exact ih x b (List.all_eq_true.mp h x hx) v hxv
  next =>
    simp only [γ]
    obtain ⟨y, hy, hyh⟩ := List.any_eq_true.mp h
    exact γAny_iff.mpr ⟨y, hy, ih a y hyh v hv⟩
  next _ _ lo hi lo' hi' =>
    simp only [γ] at hv ⊢
    obtain ⟨i, rfl, hl, hh⟩ := hv
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨i, rfl, ?_, ?_⟩
    · intro l' e; subst e
      cases lo with
      | none => simp at h1
      | some l => simp at h1; exact Int.le_trans h1 (hl l rfl)
    · intro u e; subst e
      cases hi with
      | none => simp at h2
      | some u' => simp at h2; exact Int.le_trans (hh u' rfl) h2
  next _ _ c d =>
    simp only [γ] at hv ⊢
    obtain ⟨x, rfl, hx⟩ := hv
    refine ⟨x, rfl, ?_⟩
    cases d with
    | none => exact .inl rfl
    | some d => simp at h; subst h; exact hx
  next =>
    simp only [γ] at hv ⊢
    obtain ⟨t, ht, rfl⟩ := hv
    exact ⟨t, by simpa using List.all_eq_true.mp h t ht, rfl⟩
  next =>
    simp only [γ] at hv ⊢
    obtain ⟨j, info, rfl, h1, h2, h3, h4⟩ := hv
    simp only [Bool.and_eq_true] at h
    exact ⟨j, info, rfl, h1, ih _ _ h.1 _ h2, ih _ _ h.2 _ h3, h4⟩
  next =>
    simp only [γ] at hv ⊢
    obtain ⟨x, t, rfl, h1, ht⟩ := hv
    exact ⟨x, t, rfl, h1, by simpa using List.all_eq_true.mp h t ht⟩
  next =>
    simp only [γ] at hv ⊢
    obtain ⟨xs, rfl, h1⟩ := hv
    exact ⟨xs, rfl, zipLe_sound ih _ _ h _ h1⟩
  next =>
    simp only [γ] at hv ⊢
    obtain ⟨xs, rfl, h1⟩ := hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have hl := γL_length h1
    rw [List.length_map] at hl
    refine ⟨xs, rfl, hl ▸ h.1, fun x hx => ?_⟩
    obtain ⟨a, ha, hav⟩ := γL_mem h1 (.value x) (List.mem_map_of_mem hx)
    have hva := List.all_eq_true.mp h.2 a ha
    cases a with
    | val ts =>
      simp only [γ] at hav
      obtain ⟨x', t, he, hx', -⟩ := hav
      cases he
      simp [hx']
    | bot => simp [γ] at hav
    | _ => simp [PA.isVal] at hva
  next =>
    simp only [γ] at hv ⊢
    obtain ⟨xs, rfl, h1, h2⟩ := hv
    simp only [decide_eq_true_eq] at h
    exact ⟨xs, rfl, Nat.le_trans h h1, h2⟩
  next => exact hv
  next =>
    simp only [beq_iff_eq] at h
    subst h; exact hv
  next _ _ n m =>
    simp only [γ] at hv ⊢
    obtain ⟨rss, rfl, h1, h2⟩ := hv
    refine ⟨rss, rfl, h1, ?_⟩
    cases m with
    | none => exact .inl rfl
    | some m => simp at h; subst h; exact h2
  next => exact hv
  next _ _ lo n lo' n' =>
    simp only [γ] at hv ⊢
    obtain ⟨ls, rfl, h1, h2⟩ := hv
    refine ⟨ls, rfl, ?_⟩
    cases n with
    | some k =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Option.isNone_iff_eq_none,
        beq_iff_eq] at h
      have hk : k = ls.length := by simpa using h2
      subst hk
      exact ⟨h.1, h.2.elim .inl .inr⟩
    | none =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at h
      exact ⟨Nat.le_trans h.1 h1, .inl h.2⟩
  next =>
    simp only [beq_iff_eq] at h
    subst h; exact hv
  next =>
    simp only [γ] at hv ⊢
    obtain ⟨ws, rfl, h1⟩ := hv
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, hlen⟩, hall⟩ := h
    exact ⟨ws, rfl, zipLe_sound ih _ _
      (by simp only [Bool.and_eq_true, beq_iff_eq]; exact ⟨hlen, hall⟩) _ h1⟩
  next => exact hv
  next _ _ k n k' n' =>
    simp only [γ] at hv ⊢
    obtain ⟨o, rfl, h1⟩ := hv
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨rfl, h2 | rfl⟩ := h
    · subst h2; exact ⟨o, rfl, opOk_none h1⟩
    · exact ⟨o, rfl, h1⟩
  next => cases h

/-- **The order is sound.** -/
theorem le_sound (a b : PA) (h : PA.le a b = true) (v : V) (hv : γ f ctx a v) : γ f ctx b v :=
  leF_sound 64 a b h v hv

/-- **The pointwise order is sound.** -/
theorem leL_sound (as bs : List PA) (h : PA.leL as bs = true) (vs : List V)
    (hv : γL f ctx as vs) : γL f ctx bs vs :=
  zipLe_sound (fun a b h v hv => le_sound a b h v hv) as bs h vs hv

/-! ## Pruning and splitting -/

/-- **A pruned abstract value describes nothing.** -/
theorem isBot_sound {a : PA} (h : a.isBot = true) (v : V) : ¬ γ f ctx a v := by
  unfold PA.isBot at h
  split at h <;> simp [γ, γAny] at h ⊢

/-- Some member of a list of arguments is pruned: the list describes nothing. -/
theorem γL_any_isBot {as : List PA} (hb : as.any PA.isBot = true) {vs : List V}
    (h : γL f ctx as vs) : False := by
  obtain ⟨a, ha, hab⟩ := List.any_eq_true.mp hb
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
  have hl := γL_length h
  have : i < vs.length := by rw [← hl]; exact (List.getElem?_eq_some_iff.mp hi).1
  exact isBot_sound hab vs[i] (γL_get h i a vs[i] hi (List.getElem?_eq_getElem this))

mutual
/-- **The cases of an abstract value cover it.** -/
theorem split_sound (a : PA) (v : V) (h : γ f ctx a v) : ∃ b ∈ PA.split a, γ f ctx b v := by
  unfold PA.split
  split
  next ts =>
    simp only [γ] at h
    obtain ⟨t, ht, rfl⟩ := h
    exact ⟨.ty [t], List.mem_map_of_mem ht, t, List.mem_singleton_self _, rfl⟩
  next ts =>
    simp only [γ] at h
    obtain ⟨x, t, rfl, hx, ht⟩ := h
    exact ⟨.val [t], List.mem_map_of_mem ht, x, t, rfl, hx, List.mem_singleton_self _⟩
  next as =>
    simp only [γ] at h
    exact γAny_iff.mp h
  next =>
    simp only [γ] at h
    obtain ⟨x, rfl, -⟩ := h
    cases x
    · exact ⟨_, List.mem_cons_self .., false, rfl, .inr rfl⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), true, rfl, .inr rfl⟩
  next t d =>
    simp only [γ] at h
    obtain ⟨j, info, rfl, h1, h2, h3, h4⟩ := h
    obtain ⟨t', ht', h2'⟩ := split_sound t _ h2
    obtain ⟨d', hd', h3'⟩ := split_sound d _ h3
    exact ⟨.inst t' d', List.mem_flatMap.mpr ⟨t', ht', List.mem_map_of_mem hd'⟩,
      j, info, rfl, h1, h2', h3', h4⟩
  next t k fs =>
    simp only [γ] at h
    obtain ⟨ws, rfl, h1⟩ := h
    obtain ⟨bs, hbs, h1'⟩ := splitL_sound fs ws h1
    exact ⟨.data t k bs, List.mem_map_of_mem hbs, ws, rfl, h1'⟩
  next as =>
    simp only [γ] at h
    obtain ⟨xs, rfl, h1⟩ := h
    obtain ⟨bs, hbs, h1'⟩ := splitL_sound as _ h1
    exact ⟨.vals bs, List.mem_map_of_mem hbs, xs, rfl, h1'⟩
  next => exact ⟨a, List.mem_singleton_self _, h⟩
termination_by sizeOf a

/-- **The cases of an argument list cover it.** -/
theorem splitL_sound (as : List PA) (vs : List V) (h : γL f ctx as vs) :
    ∃ bs ∈ PA.splitL as, γL f ctx bs vs := by
  match as, vs, h with
  | [], [], _ => exact ⟨[], by simp [PA.splitL], trivial⟩
  | a :: as, v :: vs, ⟨h1, h2⟩ =>
    obtain ⟨b, hb, hbv⟩ := split_sound a v h1
    obtain ⟨bs, hbs, hbsv⟩ := splitL_sound as vs h2
    exact ⟨b :: bs, by rw [PA.splitL]; exact List.mem_flatMap.mpr ⟨b, hb, List.mem_map_of_mem hbs⟩,
      hbv, hbsv⟩
  | [], _ :: _, h => exact h.elim
  | _ :: _, [], h => exact h.elim
termination_by sizeOf as
end

/-! ## Environments -/

/-- The empty environment of a rule. -/
theorem envOK_empty (n : Nat) :
    EnvOK f ctx (List.replicate n none) (Array.replicate n (none : Option V)) := by
  refine ⟨by simp, fun x a hx => ?_⟩
  simp [List.getElem?_replicate] at hx

/-- Binding a variable. -/
theorem envOK_set {aenv : AEnv} {env : Isle.Interp.Env V} (he : EnvOK f ctx aenv env) {a : PA}
    {v : V} (hv : γ f ctx a v) (x : Nat) :
    EnvOK f ctx (aenv.set x (some a)) (env.set! x (some v)) := by
  refine ⟨by simp [he.1], fun y b hy => ?_⟩
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  rw [List.getElem?_set] at hy
  by_cases hyx : x = y
  · subst hyx
    simp only [↓reduceIte] at hy ⊢
    by_cases hlt : x < aenv.length
    · simp only [hlt, ↓reduceIte, Option.some.injEq] at hy
      cases hy
      exact ⟨v, by simp [he.1, hlt], hv⟩
    · simp [hlt] at hy
  · simp only [hyx, ↓reduceIte] at hy ⊢
    exact he.2 y b hy

end Backend.Proof.Prg
