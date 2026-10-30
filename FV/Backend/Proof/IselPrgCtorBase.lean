import FV.Backend.Proof.IselPrgInv
import FV.Backend.Proof.IselPrgOfvSound

/-!
# Progress of the ISLE lowering (V7): facts for the soundness of `actor`

What `IselPrgCtorSound`'s case analysis of the extern constructors needs: the conclusion of
`Model.ctor` for one call (`CtorConcl`) and the property each alternative of `actor`'s dispatch
must have (`ActP`); the meaning of the abstract integers, types and booleans the numeric helpers
of `IselPrgExt` build (`intOp1`, `intOp2`, `boolOp2`, `tyInt`, `exactTest`, `exactTest1`,
`ccFilter`); `mapM` over registers and the fresh registers of `gen_call_output`.
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Aarch64 PA

variable {f : Clif.Function} {ctx : Ctx}

namespace CS

/-- The conclusion of `Model.ctor` for one call with result `r`. -/
def CtorConcl (f : Clif.Function) (ctx : Ctx) (a : PA) (must : Bool) (r : ExtResult (V × LState)) :
    Prop :=
  (∃ w st', r = .ok (w, st') ∧ γ f ctx a w) ∨ (r = .fail ∧ must = false)

/-- What every alternative of `actor`'s dispatch (past the type predicates) satisfies. -/
def ActP (f : Clif.Function) (ctx : Ctx) (id : TermId) (as : List PA) (r : Option (PA × Bool)) :
    Prop :=
  ∀ a must, r = some (a, must) → ∀ (term : Term) (vs : List V) (st : LState), term.id = id →
    γL f ctx as vs → CtorConcl f ctx a must (externCtor ctx term vs st)

theorem fin_ok {a : PA} {must : Bool} {w : V} {st' : LState} (h : γ f ctx a w) :
    CtorConcl f ctx a must (.ok (w, st')) := .inl ⟨w, st', rfl, h⟩

theorem fin_fail {a : PA} {must : Bool} (h : must = false) : CtorConcl f ctx a must .fail :=
  .inr ⟨rfl, h⟩

theorem ite_t {α : Type} {c : Prop} [Decidable c] {x y : α} (h : c) : (if c then x else y) = x := by
  simp [h]

theorem ite_f {α : Type} {c : Prop} [Decidable c] {x y : α} (h : ¬ c) :
    (if c then x else y) = y := by
  simp [h]

/-! ## Meanings -/

theorem γ_intAny (i : Int) : γ f ctx (.int none none) (.int i) := ⟨i, rfl, by simp, by simp⟩

theorem γ_exact (i : Int) : γ f ctx (exact i) (.int i) := ⟨i, rfl, by simp, by simp⟩

theorem γ_range {lo hi i : Int} (h1 : lo ≤ i) (h2 : i ≤ hi) : γ f ctx (range lo hi) (.int i) :=
  ⟨i, rfl, by simpa using h1, by simpa using h2⟩

theorem γ_unit : γ f ctx (.op .unit none) (.op .unit) := ⟨.unit, rfl, rfl⟩

theorem γ_enumAlts {ty : TypeId} {ks : List Nat} {k : Nat} (hk : k ∈ ks) :
    γ f ctx (enumAlts ty ks) (.data ty k []) := by
  simp only [enumAlts, γ]
  rw [γAny_iff]
  exact ⟨.data ty k [], List.mem_map.2 ⟨k, hk, rfl⟩, by simp [γ, γL]⟩

theorem intOf_sh {x : PA} {w : V} {v : Int} (h : x.intOf = some v) (hw : γ f ctx x w) :
    w = .int v := by
  cases x with
  | int lo hi =>
    cases lo with
    | none => simp [intOf] at h
    | some l =>
      cases hi with
      | none => simp [intOf] at h
      | some u =>
        simp only [intOf] at h
        split at h
        · rename_i he
          simp only [beq_iff_eq] at he
          subst he
          simp only [Option.some.injEq] at h
          subst h
          simp only [γ] at hw
          obtain ⟨i, rfl, h1, h2⟩ := hw
          have := h1 l rfl
          have := h2 l rfl
          rw [show i = l by omega]
        · cases h
  | _ => simp [intOf] at h

theorem hiOf_sh {x : PA} {w : V} {n : Int} (h : x.hiOf = some n) (hw : γ f ctx x w) :
    ∃ i, w = .int i ∧ i ≤ n := by
  cases x with
  | int lo u =>
    cases u with
    | none => simp [hiOf] at h
    | some u =>
      simp only [hiOf, Option.some.injEq] at h
      subst h
      simp only [γ] at hw
      obtain ⟨i, rfl, -, h2⟩ := hw
      exact ⟨i, rfl, h2 u rfl⟩
  | _ => simp [hiOf] at h

theorem loOf_sh {x : PA} {w : V} {n : Int} (h : x.loOf = some n) (hw : γ f ctx x w) :
    ∃ i, w = .int i ∧ n ≤ i := by
  cases x with
  | int l hi =>
    cases l with
    | none => simp [loOf] at h
    | some l =>
      simp only [loOf, Option.some.injEq] at h
      subst h
      simp only [γ] at hw
      obtain ⟨i, rfl, h1, -⟩ := hw
      exact ⟨i, rfl, h1 l rfl⟩
  | _ => simp [loOf] at h

theorem tysOf_sh {a : PA} {w : V} {ts : List CTy} (h : a.tysOf = some ts) (hw : γ f ctx a w) :
    ∃ t ∈ ts, w = .ty t := by
  cases a with
  | ty us =>
    simp only [tysOf, Option.some.injEq] at h
    subst h
    simpa only [γ] using hw
  | bot => simp [γ] at hw
  | _ => simp [tysOf] at h

theorem tysAll_sh {a : PA} {w : V} {p : CTy → Bool} (h : tysAll a p = true) (hw : γ f ctx a w) :
    ∃ t, p t = true ∧ w = .ty t := by
  unfold tysAll at h
  cases ht : a.tysOf with
  | none => simp [ht] at h
  | some ts =>
    simp only [ht, List.all_eq_true] at h
    obtain ⟨t, hts, rfl⟩ := tysOf_sh ht hw
    exact ⟨t, h t hts, rfl⟩

theorem val_sh {a : PA} {w : V} (h : isVal a = true) (hw : γ f ctx a w) :
    ∃ x t, w = .value x ∧ ctx.valueType? x = some t := by
  cases a with
  | val ts =>
    simp only [γ] at hw
    obtain ⟨x, t, rfl, ht, -⟩ := hw
    exact ⟨x, t, rfl, ht⟩
  | bot => simp [γ] at hw
  | _ => simp [isVal] at h

/-! ## The numeric helpers -/

theorem intOp1_sh {x a : PA} {must : Bool} {w : V} {g : Int → Int}
    (h : intOp1 x g = some (a, must)) (hw : γ f ctx x w) :
    ∃ i, w = .int i ∧ γ f ctx a (.int (g i)) := by
  unfold intOp1 at h
  split at h
  · rename_i hx
    simp only [cOk, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨i, rfl⟩ := int_sh hx hw
    refine ⟨i, rfl, ?_⟩
    split
    · rename_i v hv
      have := intOf_sh hv hw
      simp only [V.int.injEq] at this
      subst this
      exact γ_exact _
    · exact γ_intAny _
  · cases h

theorem intOp2_sh {x y a : PA} {must : Bool} {wx wy : V} {g : Int → Int → Int}
    (h : intOp2 x y g = some (a, must)) (hx : γ f ctx x wx) (hy : γ f ctx y wy) :
    ∃ i j, wx = .int i ∧ wy = .int j ∧ γ f ctx a (.int (g i j)) := by
  unfold intOp2 at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    simp only [cOk, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨i, rfl⟩ := int_sh hc.1 hx
    obtain ⟨j, rfl⟩ := int_sh hc.2 hy
    refine ⟨i, j, rfl, rfl, ?_⟩
    split
    · rename_i u v hu hv
      have h1 := intOf_sh hu hx
      have h2 := intOf_sh hv hy
      simp only [V.int.injEq] at h1 h2
      subst h1 h2
      exact γ_exact _
    · exact γ_intAny _
  · cases h

theorem boolOp2_sh {x y a : PA} {must : Bool} {wx wy : V} {g : Int → Int → Bool}
    (h : boolOp2 x y g = some (a, must)) (hx : γ f ctx x wx) (hy : γ f ctx y wy) :
    ∃ i j, wx = .int i ∧ wy = .int j ∧ γ f ctx a (.bool (g i j)) := by
  unfold boolOp2 at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    simp only [cOk, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨i, rfl⟩ := int_sh hc.1 hx
    obtain ⟨j, rfl⟩ := int_sh hc.2 hy
    refine ⟨i, j, rfl, rfl, g i j, rfl, ?_⟩
    cases hu : x.intOf with
    | none => simp
    | some u =>
      cases hv : y.intOf with
      | none => simp
      | some v =>
        have h1 := intOf_sh hu hx
        have h2 := intOf_sh hv hy
        simp only [V.int.injEq] at h1 h2
        subst h1 h2
        simp
  · cases h

theorem foldl_min_le : ∀ (l : List Int) (init : Int),
    l.foldl min init ≤ init ∧ ∀ x ∈ l, l.foldl min init ≤ x
  | [], init => ⟨Int.le_refl _, by simp⟩
  | y :: l, init => by
    obtain ⟨h1, h2⟩ := foldl_min_le l (min init y)
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    refine ⟨Int.le_trans h1 (Int.min_le_left _ _), Int.le_trans h1 (Int.min_le_right _ _), h2⟩

theorem foldl_max_ge : ∀ (l : List Int) (init : Int),
    init ≤ l.foldl max init ∧ ∀ x ∈ l, x ≤ l.foldl max init
  | [], init => ⟨Int.le_refl _, by simp⟩
  | y :: l, init => by
    obtain ⟨h1, h2⟩ := foldl_max_ge l (max init y)
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    refine ⟨Int.le_trans (Int.le_max_left _ _) h1, Int.le_trans (Int.le_max_right _ _) h1, h2⟩

theorem tyInt_sh {x a : PA} {must : Bool} {w : V} {g : CTy → Int}
    (h : tyInt x g = some (a, must)) (hw : γ f ctx x w) :
    ∃ t, w = .ty t ∧ γ f ctx a (.int (g t)) := by
  unfold tyInt at h
  split at h
  · rename_i t ts hts
    simp only [cOk, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨u, hu, rfl⟩ := tysOf_sh hts hw
    refine ⟨u, rfl, g u, rfl, ?_, ?_⟩
    · intro l hl
      simp only [Option.some.injEq] at hl
      subst hl
      exact (foldl_min_le _ _).2 _ (List.mem_map_of_mem hu)
    · intro l hl
      simp only [Option.some.injEq] at hl
      subst hl
      exact (foldl_max_ge _ _).2 _ (List.mem_map_of_mem hu)
  · rename_i hts
    obtain ⟨u, hu, -⟩ := tysOf_sh hts hw
    cases hu
  · cases h

theorem exactTest_sh {tA x r a : PA} {must : Bool} {w1 w2 : V} {ok : CTy → Int → Bool}
    (h : exactTest tA x ok r = some (a, must)) (h1 : γ f ctx tA w1) (h2 : γ f ctx x w2) :
    ∃ t i, w1 = .ty t ∧ w2 = .int i ∧ (ok t i = true → a = r) ∧
      (ok t i = false → must = false) := by
  unfold exactTest at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨ts, t, rfl, ht, rfl⟩ := ty_sh hc.1 h1
    obtain ⟨i, rfl⟩ := int_sh hc.2 h2
    refine ⟨t, i, rfl, rfl, ?_⟩
    split at h
    · rename_i us n hus hn
      simp only [tysOf, Option.some.injEq] at hus
      subst hus
      have := intOf_sh hn h2
      simp only [V.int.injEq] at this
      subst this
      dsimp only at h
      split at h
      · rename_i he
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨fun hok => ?_, fun _ => rfl⟩
        have : t ∈ ts.filter (ok · i) := List.mem_filter.2 ⟨ht, hok⟩
        rw [List.isEmpty_iff] at he
        rw [he] at this
        cases this
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨fun _ => rfl, fun hok => ?_⟩
        rw [Bool.eq_false_iff]
        intro hl
        have := List.length_filter_eq_length_iff.1 (beq_iff_eq.1 hl) t ht
        rw [hok] at this
        cases this
    · simp only [cMay, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun _ => rfl, fun _ => rfl⟩
  · cases h

theorem exactTest1_sh {x a : PA} {must : Bool} {w : V} {ok : Int → Option Int}
    (h : exactTest1 x ok = some (a, must)) (hw : γ f ctx x w) :
    ∃ i, w = .int i ∧ (∀ m, ok i = some m → γ f ctx a (.int m)) ∧ (ok i = none → must = false) := by
  unfold exactTest1 at h
  split at h
  · rename_i hc
    obtain ⟨i, rfl⟩ := int_sh hc hw
    refine ⟨i, rfl, ?_⟩
    split at h
    · rename_i n hn
      have := intOf_sh hn hw
      simp only [V.int.injEq] at this
      subst this
      split at h
      · rename_i m hm
        simp only [cOk, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨fun m' hm' => ?_, fun hn => ?_⟩
        · rw [hm] at hm'
          simp only [Option.some.injEq] at hm'
          subst hm'
          exact γ_exact _
        · rw [hm] at hn
          cases hn
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨fun m' hm' => ?_, fun _ => rfl⟩
        rw [hm] at hm'
        cases hm'
    · simp only [cMay, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun m _ => γ_intAny m, fun _ => rfl⟩
  · cases h

theorem ccFilter_sh {cc a : PA} {must : Bool} {w : V} {ok : List Nat}
    (h : ccFilter cc ok = some (a, must)) (hw : γ f ctx cc w) :
    ∃ k, w = .data tyIntCC k [] ∧ (ok.contains k = true → γ f ctx a w) ∧
      (ok.contains k = false → must = false) := by
  unfold ccFilter at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨ks, hks, h⟩ := h
  obtain ⟨k, hk, rfl⟩ := enumsOf_sound hks hw
  refine ⟨k, rfl, ?_⟩
  split at h
  · rename_i he
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun hc => ?_, fun _ => rfl⟩
    have : k ∈ ks.filter (ok.contains ·) := List.mem_filter.2 ⟨hk, hc⟩
    rw [List.isEmpty_iff] at he
    rw [he] at this
    cases this
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun hc => γ_enumAlts (List.mem_filter.2 ⟨hk, hc⟩), fun hc => ?_⟩
    simp only [Bool.eq_false_iff]
    intro hall
    have := List.all_eq_true.1 hall k hk
    rw [hc] at this
    cases this

/-! ## Registers -/

theorem mapM_reg (hP : PInv f ctx) :
    ∀ (ns : List Nat), (∀ x ∈ ns, (ctx.valueType? x).isSome = true) →
      ∃ rs, ns.mapM ctx.valueReg? = some rs ∧ rs.length = ns.length
  | [], _ => ⟨[], rfl, rfl⟩
  | x :: ns, h => by
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (h x (List.mem_cons_self ..))
    obtain ⟨rs, hrs, hl⟩ := mapM_reg hP ns (fun y hy => h y (List.mem_cons_of_mem _ hy))
    refine ⟨.vreg x .int :: rs, ?_, by simp [hl]⟩
    simp [List.mapM_cons, hP.ctxInv.typedReg x t ht, hrs]

theorem single_mapM_eq {g : List Reg → Option Reg} (hg : ∀ r, g [r] = some r) :
    ∀ (rss : List (List Reg)), (∀ rs ∈ rss, rs.length = 1) →
      rss.mapM g = some (rss.map fun rs => rs.headD .xzr)
  | [], _ => rfl
  | rs :: rss, h => by
    match rs, h rs (List.mem_cons_self ..) with
    | [r], _ =>
      have := single_mapM_eq hg rss (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp [List.mapM_cons, hg, this]

theorem single_mapM_ne {g : List Reg → Option Reg} {rss : List (List Reg)} (h : rss.mapM g = none)
    (hg : ∀ r, g [r] = some r) (h1 : ∀ rs ∈ rss, rs.length = 1) : False := by
  rw [single_mapM_eq hg rss h1] at h
  cases h

theorem mapM_some_mem {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM g = some r → ∀ x ∈ l, ∃ y, g x = some y ∧ y ∈ r
  | [], _, _, x, hx => by cases hx
  | a :: l, r, h, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨y, hy, List.mem_cons_self ..⟩
    · obtain ⟨z, hz, hzm⟩ := mapM_some_mem hys x hx
      exact ⟨z, hz, List.mem_cons_of_mem _ hzm⟩

theorem imm12_small {m : Nat} (h : m < 4096) : Imm12.ofNat? m = some ⟨m, false⟩ := by
  unfold Imm12.ofNat?
  simp [mask64, Nat.mod_eq_of_lt (show m < 2 ^ 64 by omega), h]

/-- The fresh singleton entries of `gen_call_output`'s fold (of the classes `g`: typed calls,
S11e5a). -/
theorem foldOut {α : Type} (g : α → RegClass) : ∀ (l : List α) (acc : Array (List Reg)) (st : LState),
    ∃ rss, (l.foldl (fun (x : Array (List Reg) × LState) (p : α) =>
        (x.1.push [(x.2.fresh (g p)).1], (x.2.fresh (g p)).2)) (acc, st)).1.toList =
          acc.toList ++ rss ∧
      rss.length = l.length ∧ ∀ rs ∈ rss, rs.length = 1
  | [], acc, st => ⟨[], by simp, rfl, by simp⟩
  | p :: l, acc, st => by
    obtain ⟨rss, h1, h2, h3⟩ := foldOut g l (acc.push [(st.fresh (g p)).1]) (st.fresh (g p)).2
    refine ⟨[(st.fresh (g p)).1] :: rss, ?_, by simp [h2], ?_⟩
    · simp only [List.foldl_cons]
      rw [h1]
      simp
    · simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨rfl, h3⟩

theorem retRegs_some {n : Nat} (h : n ≤ 8) : retRegs n = some ((List.range n).map Reg.x) := by
  simp [retRegs, h]

end CS

end Backend.Proof.Prg
