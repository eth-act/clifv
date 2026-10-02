import FV.Opt.Legalize128Pass

/-!
# Completeness of `Opt.Legal.check` for `Opt.Legalize128`'s output: the local lemmas

`pureOk_of`: a segment that is the renaming of a well-formed canonical pattern (`PatWF`) passes
`pureOk` as soon as the values it writes are distinct, not inputs, and outputs or fresh. The
legaliser emits each pure pattern exactly that way (temporaries from `fresh`), so this one lemma
covers every `Plan.pure` case.
-/

namespace Opt.Legal.Complete

open Clif Opt.Legalize128 Opt.Legal

/-- `omega` over `ValueId` (an `abbrev` of `Nat` that `omega` does not unfold). -/
macro "vomega" : tactic => `(tactic| ((try simp only [ValueId] at *) <;> omega))

/-! ## Lists -/

theorem inj_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by simp at hx
  | a :: l, h, x, y, hx, hy, e => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · exact absurd ⟨y, hy, e.symm⟩ h.1
    · exact absurd ⟨x, hx, e⟩ h.1
    · exact inj_of_nodup_map h.2 hx hy e

/-! ## Renaming -/

theorem renameInst_congr {σ τ : ValueId → ValueId} :
    ∀ (i : Inst), (∀ c ∈ instOps i, σ c = τ c) → renameInst σ i = renameInst τ i := by
  intro i h
  cases i <;> simp_all [renameInst, instOps]

theorem written_map (τ : ValueId → ValueId) (pat : List Stmt) :
    written (pat.map (renameStmt τ)) = (written pat).map τ := by
  simp [written, renameStmt, List.flatMap_map, List.map_flatMap]

theorem guessTemps_eq (n : Nat) (τ : ValueId → ValueId) :
    ∀ (pat : List Stmt), guessTemps n pat (pat.map (renameStmt τ)) =
      ((written pat).filter (n ≤ ·)).map fun c => (c, τ c)
  | [] => by simp [guessTemps, written]
  | p :: pat => by
    have ih := guessTemps_eq n τ pat
    simp only [guessTemps, written, List.map_cons, List.zip_cons_cons, List.flatMap_cons,
      List.filter_append, List.map_append] at ih ⊢
    rw [ih]
    congr 1
    simp only [renameStmt]
    generalize p.results = rs
    induction rs with
    | nil => simp
    | cons r rs ihr =>
      simp only [List.map_cons, List.zip_cons_cons, List.filter_cons]
      split <;> simp_all

theorem lookup_temps {n : Nat} {τ : ValueId → ValueId} {w : List ValueId} {c : ValueId}
    (hc : c ∈ w) (hn : n ≤ c) : (((w.filter (n ≤ ·)).map fun c => (c, τ c)).lookup c) = some (τ c) := by
  induction w with
  | nil => simp at hc
  | cons a w ih =>
    simp only [List.mem_cons] at hc
    simp only [List.filter_cons]
    by_cases ha : n ≤ a
    · simp only [ha, decide_true, ite_true, List.map_cons, List.lookup_cons]
      by_cases hca : c = a
      · subst hca; simp
      · have : (c == a) = false := by simpa using hca
        rw [this]
        exact ih (hc.resolve_left hca)
    · simp only [ha, decide_false, Bool.false_eq_true, ite_false]
      rcases hc with rfl | hc
      · exact absurd hn ha
      · exact ih hc

/-! ## Well-formed patterns -/

/-- A canonical pattern over `k` inputs and `m` outputs: pure single-result statements, writing
only non-inputs, each id once, every output, and reading only inputs, outputs and written ids. -/
def PatWF (pat : List Stmt) (k m : Nat) : Bool :=
  pat.all (fun st => pureInst st.inst && st.results.length == 1) &&
  (written pat).all (fun c => decide (k ≤ c)) &&
  decide (written pat).Nodup &&
  (List.range m).all (fun i => (written pat).contains (k + i)) &&
  pat.all (fun st => (instOps st.inst).all fun c => decide (c < k + m) || (written pat).contains c)

/-- **A renamed well-formed pattern passes `pureOk`**: its writes are distinct values, none an
input, each an output or fresh. -/
theorem pureOk_of {C : Ctx} {pat : List Stmt} {ins outs : List ValueId} {τ : ValueId → ValueId}
    (hwf : PatWF pat ins.length outs.length = true)
    (hin : ∀ i (h : i < ins.length), τ i = ins[i])
    (hout : ∀ i (h : i < outs.length), τ (ins.length + i) = outs[i])
    (hnd : ((written pat).map τ).Nodup)
    (hdis : ∀ c ∈ written pat, τ c ∉ ins)
    (hfr : ∀ c ∈ written pat, τ c ∈ outs ∨ C.fresh (τ c) = true) :
    pureOk C pat ins outs (pat.map (renameStmt τ)) = true := by
  simp only [PatWF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    List.contains_iff_mem, Bool.or_eq_true, beq_iff_eq] at hwf
  obtain ⟨⟨⟨⟨hpure, hge⟩, hwnd⟩, hall⟩, hops⟩ := hwf
  -- the renaming `pureOk` reads off the segment agrees with `τ` on the pattern's ids
  have hσ : ∀ c, (c < ins.length + outs.length ∨ c ∈ written pat) →
      sigma ins outs (guessTemps (ins.length + outs.length) pat (pat.map (renameStmt τ))) c =
        τ c := by
    intro c hc
    unfold sigma
    by_cases h1 : c < ins.length
    · rw [dite_eq_left_of_eq_true (eq_true h1), hin c h1]
    · rw [dite_eq_right_of_eq_false (eq_false h1)]
      by_cases h2 : c - ins.length < outs.length
      · rw [dite_eq_left_of_eq_true (eq_true h2)]
        have := hout (c - ins.length) h2
        rw [show ins.length + (c - ins.length) = c by omega] at this
        exact this.symm
      · rw [dite_eq_right_of_eq_false (eq_false h2), guessTemps_eq]
        have hcw : c ∈ written pat := hc.resolve_left (by omega)
        rw [lookup_temps hcw (by omega)]
        rfl
  have hren : pat.map (renameStmt (sigma ins outs
      (guessTemps (ins.length + outs.length) pat (pat.map (renameStmt τ))))) =
      pat.map (renameStmt τ) := by
    apply List.map_congr_left
    intro p hp
    simp only [renameStmt]
    congr 1
    · apply List.map_congr_left
      intro c hc
      exact hσ c (.inr (List.mem_flatMap.mpr ⟨p, hp, hc⟩))
    · apply renameInst_congr
      intro c hc
      rcases hops p hp c hc with h | h
      · exact hσ c (.inl h)
      · exact hσ c (.inr h)
  unfold pureOk
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
    bne_iff_ne, ne_eq, List.mem_append, List.mem_range]
  refine ⟨⟨⟨⟨hren.symm, fun st hst => ?_⟩, hge⟩, ?_⟩, ?_⟩
  · have := hpure st hst
    simpa using this
  · intro c hc d hd
    by_cases hcd : c = d
    · exact .inl hcd
    right
    rw [hσ c (.inr hc)]
    rcases hd with hd | hd
    · rw [hσ d (.inl (by omega)), hin d hd]
      intro e
      exact hdis c hc (e ▸ List.getElem_mem _)
    · rw [hσ d (.inr hd)]
      exact fun e => hcd (inj_of_nodup_map hnd hc hd e)
  · intro c hc
    by_cases hn : c < ins.length + outs.length
    · exact .inl hn
    right
    rw [hσ c (.inr hc)]
    rcases hfr c hc with ho | hf
    · exfalso
      obtain ⟨i, hi, e⟩ := List.getElem_of_mem ho
      have hw := hall i hi
      have := inj_of_nodup_map hnd hc hw (by rw [hout i hi, e])
      subst this
      exact hn (Nat.add_lt_add_left hi _)
    · exact hf

/-! ## Lookups under distinct keys -/

theorem lookup_of_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {k : α} {v : β}, (l.map Prod.fst).Nodup → (k, v) ∈ l → l.lookup k = some v
  | [], _, _, _, h => by simp at h
  | (a, b) :: l, k, v, hn, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    simp only [List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · simp [List.lookup]
    · have hka : k ≠ a := fun e => hn.1 ⟨(k, v), h, e⟩
      simp only [List.lookup, show (k == a) = false by simpa using hka]
      exact lookup_of_mem hn.2 h

/-! ## Running the legaliser's monad -/

@[simp] theorem fresh_run (st : St) :
    fresh.run st = .ok (st.next, { st with next := st.next + 1 }) := rfl

@[simp] theorem emitS_run (st : St) (s : Stmt) :
    (emitS s).run st = .ok ((), { st with out := st.out ++ [s] }) := rfl

@[simp] theorem emitN_run (st : St) (l : List Stmt) :
    (emitN l).run st = .ok ((), { st with out := st.out ++ l }) := rfl

@[simp] theorem emitPat_run (st : St) (pat : List Stmt) (ins outs : List ValueId) :
    (emitPat pat ins outs).run st =
      .ok ((), { st with next := st.next + patSpan pat,
                         out := st.out ++ pat.map (renameStmt (patRen ins outs st.next)) }) := rfl

@[simp] theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

@[simp] theorem throw_run {α : Type} (e : String) (st : St) :
    (throw e : M α).run st = .error e := rfl

@[simp] theorem pure_run {α : Type} (a : α) (st : St) : (pure a : M α).run st = .ok (a, st) := rfl

theorem run_bind {α β : Type} {x : M α} {f : α → M β} {st : St} {b : β} {st' : St}
    (h : (x >>= f).run st = .ok (b, st')) :
    ∃ a s, x.run st = .ok (a, s) ∧ (f a).run s = .ok (b, st') := by
  rw [StateT.run_bind] at h
  cases hx : x.run st with
  | error e => rw [hx] at h; cases h
  | ok p => rw [hx] at h; exact ⟨p.1, p.2, rfl, h⟩

theorem pairOf_ok {C : Ctx} {v : ValueId} {st st' : St} {p : ValueId × ValueId}
    (h : (pairOf C v).run st = .ok (p, st')) : C.pair v = some p ∧ st' = st := by
  unfold pairOf at h
  split at h
  · simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨‹_›, rfl⟩
  · simp at h

theorem liftE_ok {α : Type} {r : Except String α} {st st' : St} {a : α}
    (h : (liftE r).run st = .ok (a, st')) : r = .ok a ∧ st' = st := by
  unfold liftE at h
  split at h
  · simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  · simp at h

/-! ## Lists -/

theorem nodup_map_on {α β : Type} {f : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hf, hn => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_on (fun x hx y hy => hf x (by simp [hx]) y (by simp [hy])) hn.2⟩
    obtain ⟨y, hy, e⟩ := List.mem_map.mp hm
    exact hn.1 (hf y (by simp [hy]) a (by simp) e ▸ hy)

theorem nodup_getElem_inj {α : Type} {l : List α} (hn : l.Nodup) {i j : Nat} (hi : i < l.length)
    (hj : j < l.length) (e : l[i] = l[j]) : i = j := by
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd e ((List.pairwise_iff_getElem.mp hn) i j hi hj h)
  · exact h
  · exact absurd e.symm ((List.pairwise_iff_getElem.mp hn) j i hj hi h)

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {k : α} {v : β}
    (h : l.lookup k = some v) : (k, v) ∈ l := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp h
  simp

/-! ## The certificate -/

/-- What completeness needs of the certificate: pair components are distinct values between
`T0` and the zero, and different values have disjoint pairs. -/
structure CGood (C : Ctx) : Prop where
  lt : C.T0 < C.zero
  mem : ∀ v a b, (v, a, b) ∈ C.cert.pairs → C.T0 < a ∧ C.T0 < b ∧ a < C.zero ∧ b < C.zero ∧ a ≠ b
  disj : ∀ v a b w c d, (v, a, b) ∈ C.cert.pairs → (w, c, d) ∈ C.cert.pairs → v ≠ w →
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d

theorem CGood.pair {C : Ctx} (hG : CGood C) {v a b : ValueId} (h : C.pair v = some (a, b)) :
    C.T0 < a ∧ C.T0 < b ∧ a < C.zero ∧ b < C.zero ∧ a ≠ b :=
  hG.mem v a b (lookup_mem h)

theorem CGood.pdisj {C : Ctx} (hG : CGood C) {v w a b c d : ValueId} (hvw : v ≠ w)
    (h1 : C.pair v = some (a, b)) (h2 : C.pair w = some (c, d)) :
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d :=
  hG.disj v a b w c d (lookup_mem h1) (lookup_mem h2) hvw

theorem CGood.comps {C : Ctx} (hG : CGood C) {x : ValueId} (h : x ∈ C.comps) : x < C.zero := by
  simp only [Ctx.comps, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨⟨v, a, b⟩, hm, hx⟩ := h
  obtain ⟨-, -, h1, h2, -⟩ := hG.mem v a b hm
  rcases hx with rfl | rfl
  · exact h1
  · exact h2

/-- Every value above the zero is fresh. -/
theorem CGood.fresh {C : Ctx} (hG : CGood C) {t : ValueId} (h : C.zero < t) : C.fresh t = true := by
  have := hG.lt
  have h3 : C.comps.contains t = false := by
    cases hc : C.comps.contains t
    · rfl
    · exact absurd (hG.comps (List.contains_iff_mem.mp hc)) (by vomega)
  simp only [Ctx.fresh, h3, Bool.not_false, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq,
    bne_iff_ne, ne_eq]
  vomega

theorem certOk_of {C : Ctx} (hG : CGood C) : certOk C = true := by
  have := hG.lt
  simp only [certOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq,
    Bool.or_eq_true, beq_iff_eq]
  refine ⟨⟨by vomega, ?_⟩, ?_⟩
  · rintro ⟨v, a, b⟩ hm
    have := hG.mem v a b hm
    simp only
    vomega
  · rintro ⟨v, a, b⟩ hm ⟨w, c, d⟩ hm'
    by_cases hvw : v = w
    · exact .inl hvw
    · have := hG.disj v a b w c d hm hm' hvw
      simp only
      vomega

/-! ## The legaliser's certificate -/

theorem mem_allocPairs {f : Function} {n v a b : ValueId} (h : (v, a, b) ∈ allocPairs f n) :
    ∃ i, ∃ hi : i < (((defsOf f).filter (·.2.1 == some .i128)).map (·.1)).length,
      v = (((defsOf f).filter (·.2.1 == some .i128)).map (·.1))[i] ∧ a = n + 2 * i ∧
        b = n + 2 * i + 1 := by
  unfold allocPairs at h
  obtain ⟨⟨k, i⟩, hm, e⟩ := List.mem_map.mp h
  obtain ⟨-, hi, hk⟩ := List.mem_zipIdx hm
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  simp only [Nat.zero_add, Nat.sub_zero] at hi hk
  exact ⟨i, hi, hk, rfl, rfl⟩

theorem allocPairs_length (f : Function) (n : ValueId) :
    (allocPairs f n).length = (((defsOf f).filter (·.2.1 == some .i128)).map (·.1)).length := by
  simp [allocPairs]

theorem cgood_alloc (f g : Function) :
    CGood ⟨f, g, { pairs := allocPairs f (maxValueId f + 1),
                   zero := maxValueId f + 1 + 2 * (allocPairs f (maxValueId f + 1)).length }⟩ := by
  refine ⟨?_, fun v a b hm => ?_, fun v a b w c d hm hm' hvw => ?_⟩
  · simp only [Ctx.T0, Ctx.zero]; vomega
  · obtain ⟨i, hi, -, rfl, rfl⟩ := mem_allocPairs hm
    simp only [Ctx.T0, Ctx.zero, allocPairs_length]
    vomega
  · obtain ⟨i, hi, rfl, rfl, rfl⟩ := mem_allocPairs hm
    obtain ⟨j, hj, rfl, rfl, rfl⟩ := mem_allocPairs hm'
    have : i ≠ j := fun e => hvw (by subst e; rfl)
    vomega

/-! ## Images of values -/

/-- The values of `g` a value of `f` stands for: its pair, or itself. -/
def imgOf (C : Ctx) (v : ValueId) : List ValueId :=
  match C.pair v with
  | some (a, b) => [a, b]
  | none => [v]

theorem imgOf_lt {C : Ctx} (hG : CGood C) {v x : ValueId} (hv : v < C.T0) (hx : x ∈ imgOf C v) :
    x < C.zero := by
  unfold imgOf at hx
  have := hG.lt
  split at hx
  · have := hG.pair ‹_›
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> vomega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; vomega

theorem imgOf_nodup {C : Ctx} (hG : CGood C) (v : ValueId) : (imgOf C v).Nodup := by
  unfold imgOf
  split
  · have := hG.pair ‹_›
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_false_eq_true,
      List.nodup_nil, and_true]
    exact this.2.2.2.2
  · simp

theorem imgOf_disj {C : Ctx} (hG : CGood C) {v w x : ValueId} (hv : v < C.T0) (hw : w < C.T0)
    (hvw : v ≠ w) (hx : x ∈ imgOf C v) : x ∉ imgOf C w := by
  unfold imgOf at hx ⊢
  cases hab : C.pair v with
  | some p =>
    obtain ⟨a, b⟩ := p
    rw [hab] at hx
    cases hcd : C.pair w with
    | some q =>
      obtain ⟨c, d⟩ := q
      have := hG.pdisj hvw hab hcd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl <;> vomega
    | none =>
      have := hG.pair hab
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl <;> vomega
  | none =>
    rw [hab] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    cases hcd : C.pair w with
    | some q =>
      obtain ⟨c, d⟩ := q
      have := hG.pair hcd
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      vomega
    | none => simpa using hvw

theorem flatMap_imgOf_nodup {C : Ctx} (hG : CGood C) :
    ∀ {l : List ValueId}, (∀ v ∈ l, v < C.T0) → l.Nodup → (l.flatMap (imgOf C)).Nodup
  | [], _, _ => List.nodup_nil
  | v :: l, hl, hn => by
    rw [List.nodup_cons] at hn
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨imgOf_nodup hG v, flatMap_imgOf_nodup hG (fun w hw => hl w (by simp [hw])) hn.2, ?_⟩
    intro x hx y hy e
    subst e
    obtain ⟨w, hw, hy⟩ := List.mem_flatMap.mp hy
    exact imgOf_disj hG (hl v (by simp)) (hl w (by simp [hw])) (fun e => hn.1 (e ▸ hw)) hx hy

/-! ## Statements of `f` -/

/-- What completeness needs of a statement of `f` (from `Pre`): its values are values of `f`,
its results distinct, and it never reads its own result. -/
structure SFacts (C : Ctx) (s : Stmt) : Prop where
  ops : ∀ x ∈ instOps s.inst, x < C.T0
  res : ∀ r ∈ s.results, r < C.T0
  nd : s.results.Nodup
  self : ∀ x ∈ instOps s.inst, x ∉ s.results

/-! ## Pattern instances -/

/-- **An emitted pattern instance passes `pureOk`**: its outputs are distinct, not inputs, and
inputs and outputs are below the temporaries, which are fresh. -/
theorem pureOk_emit {C : Ctx} (hG : CGood C) {pat : List Stmt} {ins outs : List ValueId}
    {base : ValueId} (hwf : PatWF pat ins.length outs.length = true) (hnd : outs.Nodup)
    (hdis : ∀ o ∈ outs, o ∉ ins) (hins : ∀ x ∈ ins, x < base) (houts : ∀ x ∈ outs, x < base)
    (hb : C.zero < base) :
    pureOk C pat ins outs (pat.map (renameStmt (patRen ins outs base))) = true := by
  have hwf' := hwf
  simp only [PatWF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf'
  obtain ⟨⟨⟨⟨-, hge⟩, hwnd⟩, -⟩, -⟩ := hwf'
  have hτo : ∀ c, ins.length ≤ c → (h : c - ins.length < outs.length) →
      patRen ins outs base c = outs[c - ins.length] := by
    intro c hc h
    simp only [patRen, show ¬c < ins.length by vomega, dite_false, h, dite_true]
  have hτt : ∀ c, ins.length + outs.length ≤ c → patRen ins outs base c = base + c := by
    intro c hc
    simp only [patRen, show ¬c < ins.length by vomega, dite_false,
      show ¬c - ins.length < outs.length by vomega]
  refine pureOk_of hwf (fun i h => by simp [patRen, h]) (fun i h => ?_) ?_ ?_ ?_
  · rw [hτo _ (by vomega) (by simpa using h)]
    simp
  · refine nodup_map_on (fun c hc d hd e => ?_) hwnd
    have hc' := hge c hc
    have hd' := hge d hd
    by_cases h1 : c - ins.length < outs.length <;> by_cases h2 : d - ins.length < outs.length
    · rw [hτo c hc' h1, hτo d hd' h2] at e
      have := nodup_getElem_inj hnd h1 h2 e
      vomega
    · rw [hτo c hc' h1, hτt d (by vomega)] at e
      have := houts _ (List.getElem_mem h1)
      vomega
    · rw [hτt c (by vomega), hτo d hd' h2] at e
      have := houts _ (List.getElem_mem h2)
      vomega
    · rw [hτt c (by vomega), hτt d (by vomega)] at e
      vomega
  · intro c hc
    have hc' := hge c hc
    by_cases h1 : c - ins.length < outs.length
    · rw [hτo c hc' h1]; exact hdis _ (List.getElem_mem h1)
    · rw [hτt c (by vomega)]
      intro hm
      have := hins _ hm
      vomega
  · intro c hc
    have hc' := hge c hc
    by_cases h1 : c - ins.length < outs.length
    · rw [hτo c hc' h1]; exact .inl (List.getElem_mem h1)
    · rw [hτt c (by vomega)]; exact .inr (hG.fresh (by vomega))

/-! ## The canonical patterns are well formed -/

@[simp] theorem wf_unary (op : UnaryOp) : PatWF (Pat.unary op) 2 2 = true := by cases op <;> decide

@[simp] theorem wf_constShift (op : BinaryOp) (n : Nat) : PatWF (Pat.constShift op n) 2 2 = true := by
  unfold Pat.constShift
  dsimp only
  split <;> (repeat' split) <;> rfl

@[simp] theorem wf_varShiftFull (op : BinaryOp) (k : Pat.AmtKind) :
    PatWF (Pat.varShiftFull op k) 3 2 = true := by
  cases op <;> cases k <;> decide

theorem wf_binary {op : BinaryOp} {pat : List Stmt} (h : Pat.binary op = some pat) :
    PatWF pat 4 2 = true := by
  cases op <;> simp [Pat.binary] at h <;> subst h <;> decide

@[simp] theorem wf_shiftNarrow (op : BinaryOp) (t : Ty) :
    PatWF (Pat.shiftNarrow op t) 2 1 = true := by
  cases t <;> rfl

@[simp] theorem wf_icmp (cc : IntCC) : PatWF (Pat.icmp cc) 4 1 = true := by cases cc <;> decide
@[simp] theorem wf_select128c : PatWF Pat.select128c 6 2 = true := by decide
@[simp] theorem wf_select128 : PatWF Pat.select128 5 2 = true := by decide
@[simp] theorem wf_selectc (t : Ty) : PatWF (Pat.selectc t) 4 1 = true := by cases t <;> decide
@[simp] theorem wf_bitselect : PatWF Pat.bitselect 6 2 = true := by decide
@[simp] theorem wf_bmask128c : PatWF Pat.bmask128c 2 2 = true := by decide
@[simp] theorem wf_bmask128 : PatWF Pat.bmask128 1 2 = true := by decide
@[simp] theorem wf_bmaskc (t : Ty) : PatWF (Pat.bmaskc t) 2 1 = true := by cases t <;> decide

@[simp] theorem wf_extend (op : ExtendOp) (w : Bool) : PatWF (Pat.extend op w) 1 2 = true := by
  cases op <;> cases w <;> decide

@[simp] theorem wf_ireduce (t : Ty) : PatWF (Pat.ireduce t) 1 1 = true := by cases t <;> decide
@[simp] theorem wf_copy2 : PatWF Pat.copy2 2 2 = true := by decide
@[simp] theorem wf_cond : PatWF Pat.cond 2 1 = true := by decide

/-! ## Plans -/

/-- What a plan of `planOf` guarantees: a pure plan is a well-formed pattern reading images of
the operands and writing exactly the images of the results; the other plans' operands. -/
def PlanSpec (C : Ctx) (s : Stmt) : Plan → Prop
  | .pure pat ins outs => PatWF pat ins.length outs.length = true ∧
      (∀ x ∈ ins, ∃ o ∈ instOps s.inst, x ∈ imgOf C o) ∧ outs = s.results.flatMap (imgOf C)
  | .load rl rh p _ _ => (∃ r, C.pair r = some (rl, rh)) ∧ p ∈ instOps s.inst ∧ C.plain p = true
  | .div _ _ _ _ _ rl rh => ∃ r, C.pair r = some (rl, rh)
  | .call fn e _ _ rs => C.f.extern? fn = some e ∧ rs = s.results
  | .trap lo hi _ _ => ∃ c ∈ instOps s.inst, C.pair c = some (lo, hi)
  | .callInd => ∃ sig callee args, s.inst = .callIndirect sig callee args
  | _ => True

set_option maxHeartbeats 1000000 in
theorem planOf_spec {C : Ctx} {s : Stmt} {pl : Plan} (h : planOf C s = some pl) :
    PlanSpec C s pl := by
  rcases s with ⟨results, inst⟩
  unfold planOf at h
  split at h <;> split at h
  all_goals (
    dsimp only at *
    subst_vars
    repeat' (first
      | (simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists, Option.some.injEq,
          reduceCtorEq, exists_and_right] at h)
      | split at h
      | (obtain ⟨_, _, _, h⟩ := h)
      | (obtain ⟨_, _, h⟩ := h)
      | (obtain ⟨_, h⟩ := h)))
  all_goals (try subst_vars)
  all_goals (simp_all [PlanSpec, imgOf, instOps, Ctx.plain])
  all_goals first
    | exact wf_binary ‹_›
    | exact ⟨_, ‹_›⟩

/-! ## The legaliser's context and the checker's

The legaliser runs with `⟨f, g0, cert⟩`, `g0` the legalised function without its blocks; the
checker with `⟨f, g, cert⟩`. They agree on everything but `g`'s blocks. -/

theorem pair_congr {C D : Ctx} (h : D.cert = C.cert) : D.pair = C.pair := by
  funext v; simp [Ctx.pair, h]

theorem plain_congr {C D : Ctx} (h : D.cert = C.cert) : D.plain = C.plain := by
  funext v; simp [Ctx.plain, pair_congr h]

theorem fresh_congr {C D : Ctx} (h : D.cert = C.cert) (hf : D.f = C.f) : D.fresh = C.fresh := by
  funext t
  unfold Ctx.fresh Ctx.T0 Ctx.zero Ctx.comps
  rw [h, hf]

theorem expandArgs_congr {C D : Ctx} (h : D.cert = C.cert) (gs : List (List SlotEl))
    (vs : List ValueId) : expandArgs D gs vs = expandArgs C gs vs := by
  induction gs, vs using expandArgs.induct C <;>
    simp_all [expandArgs, plain_congr h, pair_congr h, Ctx.zero]

theorem expandBC_congr {C D : Ctx} (h : D.cert = C.cert) (vs : List ValueId)
    (ps : List (ValueId × Ty)) : expandBC D vs ps = expandBC C vs ps := by
  induction vs, ps using expandBC.induct C <;> simp_all [expandBC, plain_congr h, pair_congr h]

theorem expandTry_congr {C D : Ctx} (h : D.cert = C.cert) (rg : List (List SlotEl))
    (as : List TryArg) (ps : List (ValueId × Ty)) :
    expandTry D rg as ps = expandTry C rg as ps := by
  induction as, ps using expandTry.induct C rg <;> simp_all [expandTry, plain_congr h, pair_congr h]

theorem retsOk_congr {C D : Ctx} (h : D.cert = C.cert) (hf : D.f = C.f)
    (rg : List (List SlotEl)) (rs out : List ValueId) : retsOk D rg rs out = retsOk C rg rs out := by
  induction rg, rs, out using retsOk.induct <;>
    simp_all [retsOk, plain_congr h, pair_congr h, fresh_congr h hf]

theorem pureOk_congr {C D : Ctx} (h : D.cert = C.cert) (hf : D.f = C.f) (pat : List Stmt)
    (ins outs : List ValueId) (seg : List Stmt) : pureOk D pat ins outs seg = pureOk C pat ins outs seg := by
  unfold pureOk
  rw [fresh_congr h hf]

theorem planOf_congr {C D : Ctx} (h : D.cert = C.cert) (hf : D.f = C.f)
    (he : D.g.externs = C.g.externs) (s : Stmt) : planOf D s = planOf C s := by
  obtain ⟨f, g, c⟩ := C
  obtain ⟨f', g', c'⟩ := D
  simp only at h hf he
  subst h hf
  simp only [planOf, Function.extern?, he, Ctx.pair, Ctx.plain, constAmt,
    expandArgs_congr (D := ⟨f', g', c'⟩) (C := ⟨f', g, c'⟩) rfl,
    plain_congr (D := ⟨f', g', c'⟩) (C := ⟨f', g, c'⟩) rfl]
  rfl

theorem segOk_congr {C D : Ctx} (h : D.cert = C.cert) (hf : D.f = C.f)
    (he : D.g.externs = C.g.externs) (hd : D.g.sigDecls = C.g.sigDecls) (s : Stmt) (pl : Plan)
    (seg : List Stmt) : segOk D s pl seg = segOk C s pl seg := by
  cases pl <;> simp only [segOk, Function.extern?, he, hd, hf, pureOk_congr h hf, retsOk_congr h hf,
    fresh_congr h hf]

end Opt.Legal.Complete
