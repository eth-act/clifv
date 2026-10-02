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
macro "vomega" : tactic => `(tactic| ((try simp only [ValueId, FnRef] at *) <;> omega))

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

@[simp] theorem throw_bind_run {α β : Type} (e : String) (f : α → M β) (st : St) :
    ((throw e : M α) >>= f).run st = .error e := rfl

@[simp] theorem except_error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = .error e := rfl

theorem imgOf_plain {C : Ctx} {v : ValueId} (h : C.plain v = true) : imgOf C v = [v] := by
  simp only [Ctx.plain, Option.isNone_iff_eq_none] at h
  simp [imgOf, h]

theorem imgOf_pair {C : Ctx} {v a b : ValueId} (h : C.pair v = some (a, b)) : imgOf C v = [a, b] := by
  simp [imgOf, h]

/-- Values from images of `rs` or allocated in `[n, n')`. -/
def Src (C : Ctx) (rs : List ValueId) (n n' : ValueId) (x : ValueId) : Prop :=
  (∃ r ∈ rs, x ∈ imgOf C r) ∨ (n ≤ x ∧ x < n')

theorem retsOf_spec {C : Ctx} (hG : CGood C) (rg : List (List SlotEl)) (rs : List ValueId) :
    ∀ {st st' : St} {out : List ValueId}, (retsOf C rg rs).run st = .ok (out, st') →
    (∀ r ∈ rs, r < C.T0) → rs.Nodup → C.zero < st.next →
    st'.out = st.out ∧ st.next ≤ st'.next ∧ retsOk C rg rs out = true ∧ out.Nodup ∧
      ∀ x ∈ out, Src C rs st.next st'.next x := by
  induction rg, rs using retsOf.induct C with
  | case1 =>
    intro st st' out h _ _ _
    simp only [retsOf, pure_run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [retsOk]
  | case2 p gs r rs hp ih =>
    intro st st' out h hl hn hz
    simp only [retsOf, hp, ite_true] at h
    obtain ⟨rest, s1, h1, h2⟩ := run_bind h
    simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    rw [List.nodup_cons] at hn
    obtain ⟨o1, n1, ok1, nd1, m1⟩ := ih h1 (fun x hx => hl x (by simp [hx])) hn.2 hz
    have hr := hl r (by simp)
    refine ⟨o1, n1, ?_, ?_, ?_⟩
    · simp [retsOk, hp, ok1]
    · rw [List.nodup_cons]
      refine ⟨fun hm => ?_, nd1⟩
      rcases m1 r hm with ⟨w, hw, hx⟩ | ⟨h3, -⟩
      · exact imgOf_disj hG hr (hl w (by simp [hw])) (fun e => hn.1 (e ▸ hw))
          (by rw [imgOf_plain hp]; simp) hx
      · have := hG.lt; vomega
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact .inl ⟨x, by simp, by rw [imgOf_plain hp]; simp⟩
      · rcases m1 x hx with ⟨w, hw, hx⟩ | h3
        · exact .inl ⟨w, by simp [hw], hx⟩
        · exact .inr h3
  | case3 p gs r rs hp =>
    intro st st' out h
    simp [retsOf, hp] at h
  | case4 gs r rs ih =>
    intro st st' out h hl hn hz
    simp only [retsOf] at h
    obtain ⟨⟨a, b⟩, s0, h0, hk⟩ := run_bind h
    obtain ⟨hab, rfl⟩ := pairOf_ok h0
    obtain ⟨rest, s1, h1, h2⟩ := run_bind hk
    simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    rw [List.nodup_cons] at hn
    obtain ⟨o1, n1, ok1, nd1, m1⟩ := ih h1 (fun x hx => hl x (by simp [hx])) hn.2 hz
    have hr := hl r (by simp)
    have hpab := hG.pair hab
    have hz' := hG.lt
    refine ⟨o1, n1, ?_, ?_, ?_⟩
    · simp [retsOk, hab, ok1]
    · have hnot : ∀ y ∈ [a, b], y ∉ rest := by
        intro y hy hm
        rcases m1 y hm with ⟨w, hw, hx⟩ | ⟨h3, -⟩
        · exact imgOf_disj hG hr (hl w (by simp [hw])) (fun e => hn.1 (e ▸ hw))
            (by rw [imgOf_pair hab]; exact hy) hx
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl <;> vomega
      simp only [List.nodup_cons, List.mem_cons, not_or]
      exact ⟨⟨hpab.2.2.2.2, hnot a (by simp)⟩, hnot b (by simp), nd1⟩
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact .inl ⟨r, by simp, by rw [imgOf_pair hab]; simp⟩
      · exact .inl ⟨r, by simp, by rw [imgOf_pair hab]; simp⟩
      · rcases m1 x hx with ⟨w, hw, hx⟩ | h3
        · exact .inl ⟨w, by simp [hw], hx⟩
        · exact .inr h3
  | case5 gs r rs ih =>
    intro st st' out h hl hn hz
    simp only [retsOf] at h
    obtain ⟨w, s0, h0, h⟩ := run_bind h
    simp only [fresh_run, Except.ok.injEq, Prod.mk.injEq] at h0
    obtain ⟨rfl, rfl⟩ := h0
    obtain ⟨⟨a, b⟩, s0, h0, hk⟩ := run_bind h
    obtain ⟨hab, rfl⟩ := pairOf_ok h0
    obtain ⟨rest, s1, h1, h2⟩ := run_bind hk
    simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    rw [List.nodup_cons] at hn
    obtain ⟨o1, n1, ok1, nd1, m1⟩ := ih h1 (fun x hx => hl x (by simp [hx])) hn.2 (by simp; vomega)
    simp only at o1 n1 m1
    have hr := hl r (by simp)
    have hpab := hG.pair hab
    have hz' := hG.lt
    refine ⟨o1, by vomega, ?_, ?_, ?_⟩
    · simp [retsOk, hab, ok1, hG.fresh hz]
    · have hnot : ∀ y ∈ [a, b], y ∉ rest := by
        intro y hy hm
        rcases m1 y hm with ⟨w, hw, hx⟩ | ⟨h3, -⟩
        · exact imgOf_disj hG hr (hl w (by simp [hw])) (fun e => hn.1 (e ▸ hw))
            (by rw [imgOf_pair hab]; exact hy) hx
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl <;> vomega
      have hw : st.next ∉ rest := by
        intro hm
        rcases m1 _ hm with ⟨w, hw, hx⟩ | ⟨h3, -⟩
        · have := imgOf_lt hG (hl w (by simp [hw])) hx
          vomega
        · vomega
      simp only [List.nodup_cons, List.mem_cons, not_or]
      exact ⟨⟨by vomega, by vomega, hw⟩, ⟨hpab.2.2.2.2, hnot a (by simp)⟩, hnot b (by simp), nd1⟩
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | rfl | hx
      · exact .inr ⟨Nat.le_refl _, by vomega⟩
      · exact .inl ⟨r, by simp, by rw [imgOf_pair hab]; simp⟩
      · exact .inl ⟨r, by simp, by rw [imgOf_pair hab]; simp⟩
      · rcases m1 x hx with ⟨w, hw, hx⟩ | h3
        · exact .inl ⟨w, by simp [hw], hx⟩
        · exact .inr ⟨by vomega, h3.2⟩
  | case6 t x h1 h2 h3 h4 =>
    intro st st' out h
    rw [retsOf] at h
    · simp at h
    all_goals assumption



theorem go_plain : ∀ (ps : List AbiParam) (k : Nat), (∀ p ∈ ps, p.ty ≠ .i128) →
    expandGroups.go ps k = .ok (ps.map fun p => [SlotEl.val p])
  | [], _, _ => rfl
  | p :: ps, k, h => by
    have hp : (p.ty == .i128) = false := by simpa using h p (by simp)
    simp only [expandGroups.go, hp, Bool.false_eq_true, ite_false]
    rw [go_plain ps _ (fun q hq => h q (by simp [hq]))]
    rfl

theorem sigExp_plain {d : Signature} (h : sig128 d = false) : sigExp d = some d := by
  simp only [sig128, List.any_eq_false, beq_iff_eq, List.mem_append] at h
  simp only [sigExp, expandSig, expandGroups, go_plain d.params 0 (fun p hp => h p (.inl hp)),
    go_plain d.returns 0 (fun p hp => h p (.inr hp))]
  simp only [bind, Except.bind, pure, Except.pure, Except.toOption, List.flatMap_map]
  congr
  · simp [elTy]
  · simp [elTy]

/-- What the legaliser's `g` declares: `f`'s externs and signature declarations, expanded, and
the `__*ti3` helpers. -/
structure GOk (C : Ctx) : Prop where
  ext : ∀ fn e, C.f.extern? fn = some e →
    ∃ s', sigExp e.sig = some s' ∧ C.g.extern? fn = some { e with sig := s' }
  helper : ∀ fn e, (fn, e) ∈ helperExts C.f → C.g.extern? fn = some e
  decl : ∀ i d, C.f.sigDecls.lookup i = some d → ∃ d', sigExp d = some d' ∧
    C.g.sigDecls.lookup i = some d'

theorem emitPlan_spec {C : Ctx} (hG : CGood C) (hO : GOk C) {s : Stmt} (hs : SFacts C s)
    {pl : Plan} (hpl : planOf C s = some pl)
    (hci : ∀ sig callee args, s.inst = .callIndirect sig callee args →
      C.g.sigDecls.lookup sig = C.f.sigDecls.lookup sig)
    {st st' : St} (hz : C.zero < st.next) (h : (emitPlan C s pl).run st = .ok ((), st')) :
    ∃ seg, st'.out = st.out ++ seg ∧ st.next ≤ st'.next ∧ seg.length = pl.len ∧
      segOk C s pl seg = true := by
  have hsp := planOf_spec hpl
  have hz' := hG.lt
  cases pl with
  | same =>
    simp only [emitPlan, emitS_run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨[s], rfl, Nat.le_refl _, rfl, by simp [segOk]⟩
  | callInd =>
    simp only [emitPlan, emitS_run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨sig, callee, args, hi⟩ := hsp
    refine ⟨[s], rfl, Nat.le_refl _, rfl, ?_⟩
    simp [segOk, hi, hci sig callee args hi]
  | pure pat ins outs =>
    simp only [emitPlan, emitPat_run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨hwf, hins, rfl⟩ := hsp
    refine ⟨_, rfl, Nat.le_add_right _ _, by simp [Plan.len], ?_⟩
    simp only [segOk]
    refine pureOk_emit hG hwf (flatMap_imgOf_nodup hG hs.res hs.nd) (fun o ho hm => ?_)
      (fun x hx => ?_) (fun x hx => ?_) hz
    · obtain ⟨r, hr, hor⟩ := List.mem_flatMap.mp ho
      obtain ⟨y, hy, hoy⟩ := hins o hm
      exact imgOf_disj hG (hs.ops y hy) (hs.res r hr) (fun e => hs.self y hy (e ▸ hr)) hoy hor
    · obtain ⟨y, hy, hxy⟩ := hins x hx
      have := imgOf_lt hG (hs.ops y hy) hxy
      vomega
    · obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.mp hx
      have := imgOf_lt hG (hs.res r hr) hxr
      vomega
  | load rl rh p fl off =>
    simp only [emitPlan, emitN_run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨⟨r, hr⟩, hp, -⟩ := hsp
    have hpr := hG.pair hr
    have hpT := hs.ops p hp
    refine ⟨_, rfl, Nat.le_refl _, rfl, ?_⟩
    simp only [segOk, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact ⟨hpr.2.2.2.2, by vomega⟩
  | store xl xh p fl off =>
    simp only [emitPlan, emitN_run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨_, rfl, Nat.le_refl _, rfl, by simp [segOk]⟩
  | div op xl xh yl yh rl rh =>
    simp only [emitPlan] at h
    split at h
    · rename_i fn e hfind
      simp only [emitS_run, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have he : e = helperExt op := by simpa using List.find?_some hfind
      have hm := List.mem_of_find?_eq_some hfind
      obtain ⟨r, hr⟩ := hsp
      have := hG.pair hr
      refine ⟨_, rfl, Nat.le_refl _, rfl, ?_⟩
      simp [segOk, hO.helper fn e hm, he, this.2.2.2.2]
    · simp at h
  | call fn e args rg rs =>
    simp only [emitPlan] at h
    obtain ⟨results, s1, h1, h2⟩ := run_bind h
    simp only [emitS_run, Except.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨-, rfl⟩ := h2
    obtain ⟨he, rfl⟩ := hsp
    obtain ⟨o1, n1, ok1, nd1, -⟩ := retsOf_spec hG rg s.results h1 hs.res hs.nd hz
    obtain ⟨s', hs', hg⟩ := hO.ext fn e he
    refine ⟨[{ results, inst := .call fn args }], by simp [o1], n1, rfl, ?_⟩
    simp [segOk, ok1, nd1, hs', hg]
  | trap lo hi nz code =>
    simp only [emitPlan] at h
    obtain ⟨c, s0, h0, h⟩ := run_bind h
    simp only [fresh_run, Except.ok.injEq, Prod.mk.injEq] at h0
    obtain ⟨rfl, rfl⟩ := h0
    obtain ⟨u, s1, h1, h2⟩ := run_bind h
    simp only [emitPat_run, Except.ok.injEq, Prod.mk.injEq] at h1
    obtain ⟨-, rfl⟩ := h1
    simp only [emitS_run, Except.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨-, rfl⟩ := h2
    obtain ⟨y, hy, hlh⟩ := hsp
    have hp := hG.pair hlh
    have hyT := hs.ops y hy
    have hpo : pureOk C Pat.cond [lo, hi] [st.next]
        (Pat.cond.map (renameStmt (patRen [lo, hi] [st.next] (st.next + 1)))) = true := by
      refine pureOk_emit hG (by simp) (by simp) (fun o ho hm => ?_) (fun x hx => ?_)
        (fun x hx => ?_) (by vomega)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho hm
        subst ho
        rcases hm with e | e <;> vomega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> vomega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        subst hx; vomega
    refine ⟨Pat.cond.map (renameStmt (patRen [lo, hi] [st.next] (st.next + 1))) ++
      [{ results := [], inst := if nz then .trapnz st.next code else .trapz st.next code }],
      by simp [List.append_assoc], by simp; vomega, by simp [Plan.len], ?_⟩
    have hf := hG.fresh (t := st.next) hz
    cases nz <;> simp [segOk, List.getLast?_append, hf, hpo]

/-- No `call_indirect` with an `i128` signature (`Pre`). -/
def CiPlain (C : Ctx) (s : Stmt) : Prop :=
  ∀ sig callee args, s.inst = .callIndirect sig callee args → ∀ d,
    C.f.sigDecls.lookup sig = some d → sig128 d = false

theorem rewriteStmt_spec {C : Ctx} (hG : CGood C) (hO : GOk C) {s : Stmt} (hs : SFacts C s)
    (hci : CiPlain C s) {st st' : St} (hz : C.zero < st.next)
    (h : (rewriteStmt C s).run st = .ok ((), st')) :
    ∃ pl seg, planOf C s = some pl ∧ st'.out = st.out ++ seg ∧ st.next ≤ st'.next ∧
      seg.length = pl.len ∧ segOk C s pl seg = true := by
  have hemit : (emitStmt C s).run st = .ok ((), st') →
      (∀ sig callee args, s.inst = .callIndirect sig callee args →
        C.g.sigDecls.lookup sig = C.f.sigDecls.lookup sig) →
      ∃ pl seg, planOf C s = some pl ∧ st'.out = st.out ++ seg ∧ st.next ≤ st'.next ∧
        seg.length = pl.len ∧ segOk C s pl seg = true := by
    intro he hci'
    unfold emitStmt at he
    split at he
    · rename_i pl hpl
      obtain ⟨seg, h1, h2, h3, h4⟩ := emitPlan_spec hG hO hs hpl hci' hz he
      exact ⟨pl, seg, hpl, h1, h2, h3, h4⟩
    · simp at he
  unfold rewriteStmt at h
  split at h
  · rename_i sig callee args hi
    split at h
    · rename_i d hd
      have h128 := hci sig callee args hi d hd
      simp only [h128, Bool.false_eq_true, ite_false] at h
      refine hemit h fun sig' callee' args' hi' => ?_
      rw [hi] at hi'
      cases hi'
      obtain ⟨d', hd', hg⟩ := hO.decl sig d hd
      rw [sigExp_plain h128] at hd'
      cases hd'
      rw [hg, hd]
    · simp at h
  · refine hemit h fun sig callee args hi => ?_
    rename_i hni
    exact absurd hi (hni sig callee args)

/-- The legaliser's context `C` and the checker's `D` agree but on `g`'s blocks. -/
structure Agree (C D : Ctx) : Prop where
  f : D.f = C.f
  cert : D.cert = C.cert
  ext : D.g.externs = C.g.externs
  decls : D.g.sigDecls = C.g.sigDecls

theorem rewriteBody_spec {C D : Ctx} (A : Agree C D) (hG : CGood C) (hO : GOk C) :
    ∀ (ss : List Stmt), (∀ s ∈ ss, SFacts C s ∧ CiPlain C s) → ∀ {st st' : St},
    C.zero < st.next → (rewriteBody C ss).run st = .ok ((), st') →
    ∃ segs, st'.out = st.out ++ segs ∧ st.next ≤ st'.next ∧
      ∀ t ts t', codeOk D ss t (segs ++ ts) t' = termOk D t ts t'
  | [], _, st, st', _, h => by
    simp only [rewriteBody, pure_run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨[], by simp, Nat.le_refl _, fun t ts t' => by simp [codeOk]⟩
  | s :: ss, hss, st, st', hz, h => by
    simp only [rewriteBody] at h
    obtain ⟨u, s1, h1, h2⟩ := run_bind h
    obtain ⟨hs, hci⟩ := hss s (by simp)
    obtain ⟨pl, seg, hpl, o1, n1, hl, hok⟩ := rewriteStmt_spec hG hO hs hci hz h1
    obtain ⟨segs, o2, n2, hc⟩ := rewriteBody_spec A hG hO ss (fun x hx => hss x (by simp [hx]))
      (by vomega) h2
    refine ⟨seg ++ segs, by simp [o2, o1], by vomega, fun t ts t' => ?_⟩
    rw [codeOk, planOf_congr A.cert A.f A.ext, hpl]
    simp only [List.append_assoc, List.take_left' hl, List.drop_left' hl,
      segOk_congr A.cert A.f A.ext A.decls, hok, Bool.true_and, hc]

/-! ## Block parameters -/

theorem entryParams_spec {C : Ctx} (hG : CGood C) (gs : List (List SlotEl))
    (ps : List (ValueId × Ty)) :
    ∀ {st st' : St} {out : List (ValueId × Ty)}, (entryParams C gs ps).run st = .ok (out, st') →
    (∀ p ∈ ps, p.1 < C.T0) → (ps.map (·.1)).Nodup → C.zero < st.next →
    st'.out = st.out ∧ st.next ≤ st'.next ∧ entryParamsOk C gs ps out = true ∧
      (out.map (·.1)).Nodup ∧ ∀ x ∈ out.map (·.1), Src C (ps.map (·.1)) st.next st'.next x := by
  induction gs, ps using entryParams.induct C with
  | case1 =>
    intro st st' out h _ _ _
    simp only [entryParams, pure_run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [entryParamsOk]
  | case2 p gs v t ps hp ih =>
    intro st st' out h hl hn hz
    simp only [entryParams, hp, ite_true] at h
    obtain ⟨rest, s1, h1, h2⟩ := run_bind h
    simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    simp only [List.map_cons, List.nodup_cons] at hn
    obtain ⟨o1, n1, ok1, nd1, m1⟩ := ih h1 (fun x hx => hl x (by simp [hx])) hn.2 hz
    have hr : v < C.T0 := hl (v, t) (by simp)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    refine ⟨o1, n1, ?_, ?_, ?_⟩
    · simp [entryParamsOk, hp, ok1]
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, nd1⟩
      rcases m1 v hm with ⟨w, hw, hx⟩ | ⟨h3, -⟩
      · exact imgOf_disj hG hr (by
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw
            exact hl q (by simp [hq])) (fun e => hn.1 (e ▸ hw))
          (by rw [imgOf_plain hp.2]; simp) hx
      · have := hG.lt; vomega
    · intro x hx
      simp only [List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact .inl ⟨x, by simp, by rw [imgOf_plain hp.2]; simp⟩
      · rcases m1 x hx with ⟨w, hw, hx⟩ | h3
        · exact .inl ⟨w, by simp only [List.map_cons, List.mem_cons]; exact .inr hw, hx⟩
        · exact .inr h3
  | case3 p gs v t ps hp =>
    intro st st' out h
    simp [entryParams, hp] at h
  | case4 gs v t ps ht ih =>
    intro st st' out h hl hn hz
    simp only [entryParams, ht, ite_true] at h
    obtain ⟨⟨a, b⟩, s0, h0, hk⟩ := run_bind h
    obtain ⟨hab, rfl⟩ := pairOf_ok h0
    obtain ⟨rest, s1, h1, h2⟩ := run_bind hk
    simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    simp only [List.map_cons, List.nodup_cons] at hn
    obtain ⟨o1, n1, ok1, nd1, m1⟩ := ih h1 (fun x hx => hl x (by simp [hx])) hn.2 hz
    have hr : v < C.T0 := hl (v, t) (by simp)
    have hpab := hG.pair hab
    have hz' := hG.lt
    refine ⟨o1, n1, ?_, ?_, ?_⟩
    · simp only [beq_iff_eq] at ht
      simp [entryParamsOk, ht, hab, ok1]
    · have hnot : ∀ y ∈ [a, b], y ∉ rest.map (·.1) := by
        intro y hy hm
        rcases m1 y hm with ⟨w, hw, hx⟩ | ⟨h3, -⟩
        · exact imgOf_disj hG hr (by
              obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw
              exact hl q (by simp [hq])) (fun e => hn.1 (e ▸ hw))
            (by rw [imgOf_pair hab]; exact hy) hx
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl <;> vomega
      simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or]
      exact ⟨⟨hpab.2.2.2.2, hnot a (by simp)⟩, hnot b (by simp), nd1⟩
    · intro x hx
      simp only [List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact .inl ⟨v, by simp, by rw [imgOf_pair hab]; simp⟩
      · exact .inl ⟨v, by simp, by rw [imgOf_pair hab]; simp⟩
      · rcases m1 x hx with ⟨w, hw, hx⟩ | h3
        · exact .inl ⟨w, by simp only [List.map_cons, List.mem_cons]; exact .inr hw, hx⟩
        · exact .inr h3
  | case5 gs v t ps ht =>
    intro st st' out h
    simp [entryParams, ht] at h
  | case6 gs v t ps ht ih =>
    intro st st' out h hl hn hz
    simp only [entryParams, ht, ite_true] at h
    obtain ⟨w, s0, h0, h⟩ := run_bind h
    simp only [fresh_run, Except.ok.injEq, Prod.mk.injEq] at h0
    obtain ⟨rfl, rfl⟩ := h0
    obtain ⟨⟨a, b⟩, s0, h0, hk⟩ := run_bind h
    obtain ⟨hab, rfl⟩ := pairOf_ok h0
    obtain ⟨rest, s1, h1, h2⟩ := run_bind hk
    simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    simp only [List.map_cons, List.nodup_cons] at hn
    obtain ⟨o1, n1, ok1, nd1, m1⟩ := ih h1 (fun x hx => hl x (by simp [hx])) hn.2 (by simp; vomega)
    simp only at o1 n1 m1
    have hr : v < C.T0 := hl (v, t) (by simp)
    have hpab := hG.pair hab
    have hz' := hG.lt
    refine ⟨o1, by vomega, ?_, ?_, ?_⟩
    · simp only [beq_iff_eq] at ht
      simp [entryParamsOk, ht, hab, ok1, hG.fresh hz]
    · have hnot : ∀ y ∈ [a, b], y ∉ rest.map (·.1) := by
        intro y hy hm
        rcases m1 y hm with ⟨w, hw, hx⟩ | ⟨h3, -⟩
        · exact imgOf_disj hG hr (by
              obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw
              exact hl q (by simp [hq])) (fun e => hn.1 (e ▸ hw))
            (by rw [imgOf_pair hab]; exact hy) hx
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl <;> vomega
      have hw : st.next ∉ rest.map (·.1) := by
        intro hm
        rcases m1 _ hm with ⟨w, hw, hx⟩ | ⟨h3, -⟩
        · have := imgOf_lt hG (by
              obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw
              exact hl q (by simp [hq])) hx
          vomega
        · vomega
      simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or]
      exact ⟨⟨by vomega, by vomega, hw⟩, ⟨hpab.2.2.2.2, hnot a (by simp)⟩, hnot b (by simp), nd1⟩
    · intro x hx
      simp only [List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | rfl | rfl | hx
      · exact .inr ⟨Nat.le_refl _, by vomega⟩
      · exact .inl ⟨v, by simp, by rw [imgOf_pair hab]; simp⟩
      · exact .inl ⟨v, by simp, by rw [imgOf_pair hab]; simp⟩
      · rcases m1 x hx with ⟨w, hw, hx⟩ | h3
        · exact .inl ⟨w, by simp only [List.map_cons, List.mem_cons]; exact .inr hw, hx⟩
        · exact .inr ⟨by vomega, h3.2⟩
  | case7 gs v t ps ht =>
    intro st st' out h
    simp [entryParams, ht] at h
  | case8 t x h1 h2 h3 h4 =>
    intro st st' out h
    rw [entryParams] at h
    · simp at h
    all_goals assumption

theorem blockParams_spec {C : Ctx} (hG : CGood C) (ps : List (ValueId × Ty)) :
    ∀ {st st' : St} {out : List (ValueId × Ty)}, (blockParams C ps).run st = .ok (out, st') →
    (∀ p ∈ ps, p.1 < C.T0) → (ps.map (·.1)).Nodup →
    st' = st ∧ paramsOk C ps out = true ∧ (out.map (·.1)).Nodup ∧
      ∀ x ∈ out.map (·.1), ∃ v ∈ ps.map (·.1), x ∈ imgOf C v := by
  induction ps using blockParams.induct C with
  | case1 =>
    intro st st' out h _ _
    simp only [blockParams, pure_run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [paramsOk]
  | case2 v t ps ht ih =>
    intro st st' out h hl hn
    simp only [blockParams, ht, ite_true] at h
    obtain ⟨⟨a, b⟩, s0, h0, hk⟩ := run_bind h
    obtain ⟨hab, rfl⟩ := pairOf_ok h0
    obtain ⟨rest, s1, h1, h2⟩ := run_bind hk
    simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    simp only [List.map_cons, List.nodup_cons] at hn
    obtain ⟨rfl, ok1, nd1, m1⟩ := ih h1 (fun x hx => hl x (by simp [hx])) hn.2
    have hr : v < C.T0 := hl (v, t) (by simp)
    have hpab := hG.pair hab
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp [paramsOk, ht, hab, ok1]
    · have hnot : ∀ y ∈ [a, b], y ∉ rest.map (·.1) := by
        intro y hy hm
        obtain ⟨w, hw, hx⟩ := m1 y hm
        exact imgOf_disj hG hr (by
              obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw
              exact hl q (by simp [hq])) (fun e => hn.1 (e ▸ hw))
            (by rw [imgOf_pair hab]; exact hy) hx
      simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or]
      exact ⟨⟨hpab.2.2.2.2, hnot a (by simp)⟩, hnot b (by simp), nd1⟩
    · intro x hx
      simp only [List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact ⟨v, by simp, by rw [imgOf_pair hab]; simp⟩
      · exact ⟨v, by simp, by rw [imgOf_pair hab]; simp⟩
      · obtain ⟨w, hw, hx⟩ := m1 x hx
        exact ⟨w, by simp only [List.map_cons, List.mem_cons]; exact .inr hw, hx⟩
  | case3 v t ps ht hp ih =>
    intro st st' out h hl hn
    simp only [blockParams, ht, hp, ite_true, Bool.false_eq_true, ite_false] at h
    obtain ⟨rest, s1, h1, h2⟩ := run_bind h
    simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    simp only [List.map_cons, List.nodup_cons] at hn
    obtain ⟨rfl, ok1, nd1, m1⟩ := ih h1 (fun x hx => hl x (by simp [hx])) hn.2
    have hr : v < C.T0 := hl (v, t) (by simp)
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp [paramsOk, ht, hp, ok1]
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, nd1⟩
      obtain ⟨w, hw, hx⟩ := m1 v hm
      exact imgOf_disj hG hr (by
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw
            exact hl q (by simp [hq])) (fun e => hn.1 (e ▸ hw))
          (by rw [imgOf_plain hp]; simp) hx
    · intro x hx
      simp only [List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨x, by simp, by rw [imgOf_plain hp]; simp⟩
      · obtain ⟨w, hw, hx⟩ := m1 x hx
        exact ⟨w, by simp only [List.map_cons, List.mem_cons]; exact .inr hw, hx⟩
  | case4 v t ps ht hp =>
    intro st st' out h
    simp [blockParams, ht, hp] at h

/-! ## Terminators -/

theorem entryId_congr {C D : Ctx} (A : Agree C D) : D.entryId? = C.entryId? := by
  simp [Ctx.entryId?, A.f]

theorem rewriteBC_spec {C D : Ctx} (A : Agree C D) {bc bc' : BlockCall} {st st' : St}
    (h : (rewriteBC C bc).run st = .ok (bc', st')) : st' = st ∧ bcOk D bc bc' = true := by
  unfold rewriteBC at h
  split at h
  · simp at h
  · rename_i hne
    split at h
    · rename_i B hB
      split at h
      · rename_i args hargs
        simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, ?_⟩
        simp only [beq_iff_eq] at hne
        simp [bcOk, entryId_congr A, hne, A.f, hB, expandBC_congr A.cert, hargs]
      · simp at h
    · simp at h

theorem mapM_rewriteBC_spec {C D : Ctx} (A : Agree C D) :
    ∀ {tbl tbl' : List BlockCall} {st st' : St},
    (tbl.mapM (rewriteBC C)).run st = .ok (tbl', st') →
    st' = st ∧ tbl.length = tbl'.length ∧ (tbl.zip tbl').all (fun (a, b) => bcOk D a b) = true
  | [], tbl', st, st', h => by
    simp only [List.mapM_nil, pure_run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | bc :: tbl, tbl', st, st', h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, s1, h1, h⟩ := run_bind h
    obtain ⟨rest, s2, h2, h3⟩ := run_bind h
    simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    obtain ⟨rfl, hb⟩ := rewriteBC_spec A h1
    obtain ⟨rfl, hl, ha⟩ := mapM_rewriteBC_spec A h2
    exact ⟨rfl, by simp [hl], by simp [hb, ha]⟩

theorem ite_throw_ok {c : Prop} [Decidable c] {e : String} {st st' : St} {u : Unit}
    (h : (if c then (throw e : M Unit) else pure ()).run st = .ok (u, st')) : ¬c ∧ st' = st := by
  split at h
  · simp at h
  · simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨‹_›, h.2.symm⟩

theorem rewriteTerm_spec {C D : Ctx} (A : Agree C D) (hG : CGood C) (hO : GOk C)
    {t : Terminator} (ht : ∀ x ∈ termOps t, x < C.T0)
    (hnt : ∀ c args et, t ≠ .tryCallIndirect c args et)
    {rg : List (List SlotEl)} (hrg : groups C.f.sig.returns = some rg) {st st' : St}
    {t' : Terminator} (hz : C.zero < st.next) (h : (rewriteTerm C rg t).run st = .ok (t', st')) :
    ∃ ts, st'.out = st.out ++ ts ∧ st.next ≤ st'.next ∧
      (C.zero < D.g.freshValue → termOk D t ts t' = true) := by
  have hz' := hG.lt
  cases t with
  | jump bc =>
    simp only [rewriteTerm] at h
    obtain ⟨bc', s1, h1, h2⟩ := run_bind h
    simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    obtain ⟨rfl, hb⟩ := rewriteBC_spec A h1
    exact ⟨[], by simp, Nat.le_refl _, fun _ => by simp [termOk, hb]⟩
  | brif c bt be =>
    simp only [rewriteTerm] at h
    have hcT := ht c (by simp [termOps])
    split at h
    · rename_i lo hi hlh
      obtain ⟨c0, s0, h0, h⟩ := run_bind h
      simp only [fresh_run, Except.ok.injEq, Prod.mk.injEq] at h0
      obtain ⟨rfl, rfl⟩ := h0
      obtain ⟨u, s5, h5, h⟩ := run_bind h
      simp only [emitPat_run, Except.ok.injEq, Prod.mk.injEq] at h5
      obtain ⟨-, rfl⟩ := h5
      obtain ⟨c1, s6, h6, h⟩ := run_bind h
      simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h6
      obtain ⟨rfl, rfl⟩ := h6
      obtain ⟨t2, s2, h2, h⟩ := run_bind h
      obtain ⟨e2, s3, h3, h4⟩ := run_bind h
      simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h4
      obtain ⟨rfl, rfl⟩ := h4
      obtain ⟨rfl, hb2⟩ := rewriteBC_spec A h2
      obtain ⟨rfl, hb3⟩ := rewriteBC_spec A h3
      have hp := hG.pair hlh
      have hpo : pureOk C Pat.cond [lo, hi] [st.next]
          (Pat.cond.map (renameStmt (patRen [lo, hi] [st.next] (st.next + 1)))) = true := by
        refine pureOk_emit hG (by simp) (by simp) (fun o ho hm => ?_) (fun x hx => ?_)
          (fun x hx => ?_) (by vomega)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho hm
          subst ho
          rcases hm with e | e <;> vomega
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl <;> vomega
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          subst hx; vomega
      refine ⟨_, rfl, by simp; vomega, fun _ => ?_⟩
      simp [termOk, hb2, hb3, pair_congr A.cert, hlh, fresh_congr A.cert A.f, hG.fresh hz,
        pureOk_congr A.cert A.f, hpo]
    · rename_i hnone
      obtain ⟨c1, s6, h6, h⟩ := run_bind h
      simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h6
      obtain ⟨rfl, rfl⟩ := h6
      obtain ⟨t2, s2, h2, h⟩ := run_bind h
      obtain ⟨e2, s3, h3, h4⟩ := run_bind h
      simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h4
      obtain ⟨rfl, rfl⟩ := h4
      obtain ⟨rfl, hb2⟩ := rewriteBC_spec A h2
      obtain ⟨rfl, hb3⟩ := rewriteBC_spec A h3
      refine ⟨[], by simp, Nat.le_refl _, fun _ => ?_⟩
      simp [termOk, hb2, hb3, pair_congr A.cert, hnone, plain_congr A.cert, Ctx.plain]
  | brTable x d tbl =>
    simp only [rewriteTerm] at h
    split at h
    · rename_i hx
      obtain ⟨d', s1, h1, h⟩ := run_bind h
      obtain ⟨tbl', s2, h2, h3⟩ := run_bind h
      simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h3
      obtain ⟨rfl, rfl⟩ := h3
      obtain ⟨rfl, hb⟩ := rewriteBC_spec A h1
      obtain ⟨rfl, hl, ha⟩ := mapM_rewriteBC_spec A h2
      refine ⟨[], by simp, Nat.le_refl _, fun _ => ?_⟩
      simp [termOk, plain_congr A.cert, hx, hb, hl, ha]
    · simp at h
  | ret vs =>
    simp only [rewriteTerm] at h
    split at h
    · rename_i vs' hvs
      simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨[], by simp, Nat.le_refl _, fun _ => ?_⟩
      simp [termOk, A.f, hrg, expandArgs_congr A.cert, hvs]
    · simp at h
  | returnCall fn args => simp [rewriteTerm] at h
  | trap c =>
    simp only [rewriteTerm, pure_run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp, Nat.le_refl _, fun _ => by simp [termOk]⟩
  | tryCall fn args et =>
    simp only [rewriteTerm] at h
    split at h
    rotate_left
    · simp at h
    rename_i e he
    split at h
    rotate_left
    · simp at h
    rename_i d' hd'
    obtain ⟨s', s1, h1, k1⟩ := run_bind h
    obtain ⟨hs', rfl⟩ := liftE_ok h1
    obtain ⟨gs, s2, h2, k2⟩ := run_bind k1
    obtain ⟨hgs, rfl⟩ := liftE_ok h2
    obtain ⟨rgs, s3, h3, k3⟩ := run_bind k2
    obtain ⟨hrgs, rfl⟩ := liftE_ok h3
    split at k3
    · simp at k3
    rename_i htys
    split at k3
    · simp at k3
    rename_i hent
    split at k3
    · simp at k3
    rename_i hfv0
    have k6 := k3
    split at k6
    rotate_left
    · simp at k6
    rename_i B hB
    split at k6
    rotate_left
    · simp at k6
    rename_i args' hargs
    split at k6
    rotate_left
    · simp at k6
    rename_i nargs hnargs
    obtain ⟨items, s7, h7, k7⟩ := run_bind k6
    obtain ⟨-, rfl⟩ := liftE_ok h7
    simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at k7
    obtain ⟨rfl, rfl⟩ := k7
    obtain ⟨s'', hs'', hge⟩ := hO.ext fn e he
    have hs'2 : sigExp e.sig = some s' := by rw [sigExp, hs']; rfl
    rw [hs'2] at hs''
    cases hs''
    have hgD : D.g.extern? fn = some { e with sig := s' } := by
      rw [← hge]; simp [Function.extern?, A.ext]
    have hcomps : C.zero < D.g.freshValue → ∀ a ∈ D.comps, a < D.g.freshValue := fun hfv a ha => by
      have hc : D.comps = C.comps := by simp [Ctx.comps, A.cert]
      rw [hc] at ha
      have := hG.comps ha
      vomega
    have hT0 : D.T0 = C.T0 := by simp [Ctx.T0, A.f]
    have hzD : D.zero = C.zero := by simp [Ctx.zero, A.cert]
    simp only [Bool.not_eq_true', Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at htys hent hfv0
    refine ⟨[], by simp, Nat.le_refl _, fun hfv => ?_⟩
    simp only [termOk, List.isEmpty_nil, beq_self_eq_true, Bool.true_and, entryId_congr A, A.f, he,
      A.decls, hd', hB, hs'2, groups, hgs, hrgs, Except.toOption, hgD, expandArgs_congr A.cert,
      hargs, expandTry_congr A.cert, hnargs, hT0, hzD, htys, List.all_eq_true]
    simp only [bne_iff_ne, ne_eq, hent, not_false_eq_true, decide_eq_true_eq, hfv0, Bool.true_and,
      Bool.and_eq_true, true_and, beq_iff_eq]
    refine ⟨⟨⟨by vomega, by vomega⟩, List.all_eq_true.mpr fun a ha => decide_eq_true (hcomps hfv a ha)⟩, ?_⟩
    simp
  | tryCallIndirect c args et => exact absurd rfl (hnt c args et)

/-! ## Blocks -/

theorem entryParamsOk_congr {C D : Ctx} (h : D.cert = C.cert) (hf : D.f = C.f)
    (gs : List (List SlotEl)) (ps ps' : List (ValueId × Ty)) :
    entryParamsOk D gs ps ps' = entryParamsOk C gs ps ps' := by
  induction gs, ps, ps' using entryParamsOk.induct <;>
    simp_all [entryParamsOk, plain_congr h, pair_congr h, fresh_congr h hf]

theorem paramsOk_congr {C D : Ctx} (h : D.cert = C.cert) (ps ps' : List (ValueId × Ty)) :
    paramsOk D ps ps' = paramsOk C ps ps' := by
  induction ps, ps' using paramsOk.induct C <;>
    simp_all [paramsOk, plain_congr h, pair_congr h]

/-- What completeness needs of a block of `f` (from `Pre`). -/
structure BFacts (C : Ctx) (b : Block) : Prop where
  params : ∀ p ∈ b.params, p.1 < C.T0
  pnd : (b.params.map (·.1)).Nodup
  body : ∀ s ∈ b.body, SFacts C s ∧ CiPlain C s
  term : ∀ x ∈ termOps b.term, x < C.T0
  noTryInd : ∀ c args et, b.term ≠ .tryCallIndirect c args et

theorem rewriteBlock_spec {C D : Ctx} (A : Agree C D) (hG : CGood C) (hO : GOk C)
    {pg rg : List (List SlotEl)} (hpg : groups C.f.sig.params = some pg)
    (hrg : groups C.f.sig.returns = some rg) {isEntry : Bool} {b : Block} (hb : BFacts C b)
    {st st' : St} {b' : Block} (hz : C.zero < st.next)
    (h : (rewriteBlock C pg rg isEntry b).run st = .ok (b', st')) :
    st.next ≤ st'.next ∧ (isEntry = true → ∃ rest, b'.body = C.zeroStmt :: rest) ∧
      (C.zero < D.g.freshValue → blockOk D isEntry b b' = true) := by
  have hzD : D.zeroStmt = C.zeroStmt := by simp [Ctx.zeroStmt, Ctx.zero, A.cert]
  unfold rewriteBlock at h
  obtain ⟨u0, s0, h0, k0⟩ := run_bind h
  simp only [StateT.run_modify, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h0
  obtain ⟨-, rfl⟩ := h0
  cases isEntry with
  | true =>
    simp only [ite_true] at k0
    obtain ⟨ps, s1, h1, k1⟩ := run_bind k0
    obtain ⟨o1, n1, ok1, nd1, -⟩ := entryParams_spec hG pg b.params h1 hb.params hb.pnd hz
    obtain ⟨u2, s2, h2, k2⟩ := run_bind k1
    simp only [emitS_run, Except.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨-, rfl⟩ := h2
    obtain ⟨⟨⟩, s3, h3, k3⟩ := run_bind k2
    obtain ⟨segs, o3, n3, hc⟩ := rewriteBody_spec A hG hO b.body hb.body (by simp; vomega) h3
    obtain ⟨t', s4, h4, k4⟩ := run_bind k3
    obtain ⟨ts, o4, n4, ht⟩ := rewriteTerm_spec A hG hO hb.term hb.noTryInd hrg (by vomega) h4
    obtain ⟨s5, s6, h5, k5⟩ := run_bind k4
    simp only [StateT.run_get, Except.ok.injEq, Prod.mk.injEq] at h5
    obtain ⟨rfl, rfl⟩ := h5
    simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at k5
    obtain ⟨rfl, rfl⟩ := k5
    simp only at o1 o3 o4 n3 n4 ⊢
    refine ⟨by vomega, fun _ => ⟨segs ++ ts, by simp [o4, o3, o1]⟩, fun hfv => ?_⟩
    simp only [blockOk, beq_self_eq_true, Bool.true_and, nd1, decide_true, ite_true, A.f, hpg,
      o4, o3, o1, List.nil_append, List.singleton_append, entryParamsOk_congr A.cert A.f, ok1,
      hzD]
    simp [hc, ht hfv, ok1]
  | false =>
    simp only [Bool.false_eq_true, ite_false] at k0
    obtain ⟨ps, s1, h1, k1⟩ := run_bind k0
    obtain ⟨rfl, ok1, nd1, -⟩ := blockParams_spec hG b.params h1 hb.params hb.pnd
    obtain ⟨⟨⟩, s3, h3, k3⟩ := run_bind k1
    obtain ⟨segs, o3, n3, hc⟩ := rewriteBody_spec A hG hO b.body hb.body (by simp; vomega) h3
    obtain ⟨t', s4, h4, k4⟩ := run_bind k3
    obtain ⟨ts, o4, n4, ht⟩ := rewriteTerm_spec A hG hO hb.term hb.noTryInd hrg (by vomega) h4
    obtain ⟨s5, s6, h5, k5⟩ := run_bind k4
    simp only [StateT.run_get, Except.ok.injEq, Prod.mk.injEq] at h5
    obtain ⟨rfl, rfl⟩ := h5
    simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at k5
    obtain ⟨rfl, rfl⟩ := k5
    simp only at o3 o4 n3 n4 ⊢
    refine ⟨by vomega, fun h => absurd h (by simp), fun hfv => ?_⟩
    simp only [blockOk, beq_self_eq_true, Bool.true_and, nd1, decide_true, Bool.false_eq_true,
      ite_false, paramsOk_congr A.cert, ok1, o4, o3, List.nil_append, hc, ht hfv]

theorem rewriteBlocks_spec {C D : Ctx} (A : Agree C D) (hG : CGood C) (hO : GOk C)
    {pg rg : List (List SlotEl)} (hpg : groups C.f.sig.params = some pg)
    (hrg : groups C.f.sig.returns = some rg) :
    ∀ (bs : List Block) (isEntry : Bool) {st st' : St} {bs' : List Block},
    (∀ b ∈ bs, BFacts C b) → C.zero < st.next →
    (rewriteBlocks C pg rg isEntry bs).run st = .ok (bs', st') →
    bs'.length = bs.length ∧
      (isEntry = true → ∀ b' ∈ bs'.head?, ∃ rest, b'.body = C.zeroStmt :: rest) ∧
      (C.zero < D.g.freshValue →
        ∀ b ∈ bs.head?, ∀ b' ∈ bs'.head?, blockOk D isEntry b b' = true) ∧
      (C.zero < D.g.freshValue →
        ((bs.drop 1).zip (bs'.drop 1)).all (fun (x, y) => blockOk D false x y) = true)
  | [], _, st, st', bs', _, _, h => by
    simp only [rewriteBlocks, pure_run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | b :: bs, isEntry, st, st', bs', hbs, hz, h => by
    simp only [rewriteBlocks] at h
    obtain ⟨b', s1, h1, k1⟩ := run_bind h
    obtain ⟨rest, s2, h2, k2⟩ := run_bind k1
    simp only [pure_run, Except.ok.injEq, Prod.mk.injEq] at k2
    obtain ⟨rfl, rfl⟩ := k2
    obtain ⟨n1, hz1, ok1⟩ := rewriteBlock_spec A hG hO hpg hrg (hbs b (by simp)) hz h1
    obtain ⟨l2, -, ok2, ok3⟩ := rewriteBlocks_spec A hG hO hpg hrg bs false
      (fun x hx => hbs x (by simp [hx])) (by vomega) h2
    refine ⟨by simp [l2], fun he b'' hb'' => ?_, fun hfv x hx y hy => ?_, fun hfv => ?_⟩
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb''
      subst hb''
      exact hz1 he
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx hy
      subst hx hy
      exact ok1 hfv
    · simp only [List.drop_one, List.tail_cons]
      cases bs with
      | nil => simp
      | cons c cs =>
        cases rest with
        | nil => simp at l2
        | cons c' cs' =>
          have := ok2 hfv c (by simp) c' (by simp)
          have := ok3 hfv
          simp only [List.drop_one, List.tail_cons] at this
          simp [*]

/-! ## The function -/

theorem sublist_flatMap_of_mem {α β : Type} {f : α → List β} :
    ∀ {l : List α} {x : α}, x ∈ l → (f x).Sublist (l.flatMap f)
  | a :: l, x, h => by
    rw [List.flatMap_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact List.sublist_append_left _ _
    · exact (sublist_flatMap_of_mem h).trans (List.sublist_append_right _ _)

theorem defsOf_keys (f : Function) : (defsOf f).map (·.1) =
    f.blocks.flatMap fun b => b.params.map (·.1) ++ b.body.flatMap (·.results) := by
  simp only [defsOf, blockDefs, stmtDefs, List.map_flatMap, List.map_append, List.map_map]
  congr 1
  funext b
  congr 1
  · simp [Function.comp_def]

theorem le_foldl {α β : Type} (F : β → α → β) (le : β → β → Prop) (hrefl : ∀ m, le m m)
    (htrans : ∀ a b c, le a b → le b c → le a c) (hF : ∀ m x, le m (F m x)) :
    ∀ (l : List α) (m : β), le m (l.foldl F m)
  | [], m => hrefl m
  | x :: l, m => htrans _ _ _ (hF m x) (le_foldl F le hrefl htrans hF l (F m x))

theorem le_foldl_max {α : Type} (g : α → Nat) :
    ∀ (l : List α) (m : Nat), m ≤ l.foldl (fun a e => max a (g e)) m :=
  le_foldl _ (· ≤ ·) Nat.le_refl (fun _ _ _ => Nat.le_trans) (fun _ _ => Nat.le_max_left _ _)

theorem mem_le_foldl_max {α : Type} (g : α → Nat) :
    ∀ {l : List α} {x : α} (m : Nat), x ∈ l → g x ≤ l.foldl (fun a e => max a (g e)) m
  | y :: l, x, m, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right _ _) (le_foldl_max g l _)
    · exact mem_le_foldl_max g _ h

/-- The zero is a value of the legalised function (the first statement of its entry block). -/
theorem zero_lt_freshValue {g : Function} {b : Block} {bs : List Block} {z : ValueId}
    {i : Inst} {rest : List Stmt} (hg : g.blocks = b :: bs)
    (hb : b.body = { results := [z], inst := i } :: rest) : z < g.freshValue := by
  unfold Function.freshValue
  rw [hg, List.foldl_cons]
  refine Nat.lt_of_lt_of_le ?_ (le_foldl _ (· ≤ ·) Nat.le_refl (fun _ _ _ => Nat.le_trans)
    (fun m b => ?_) bs _)
  · simp only [hb, List.foldl_cons, List.foldl_nil]
    refine Nat.lt_of_lt_of_le ?_ (le_foldl _ (· ≤ ·) Nat.le_refl (fun _ _ _ => Nat.le_trans)
      (fun m st => le_foldl_max (fun r => r + 1) st.results m) rest _)
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self z) (Nat.le_max_right _ _)
  · exact Nat.le_trans (le_foldl_max (fun p => p.1 + 1) b.params m)
      (le_foldl _ (· ≤ ·) Nat.le_refl (fun _ _ _ => Nat.le_trans)
        (fun m st => le_foldl_max (fun r => r + 1) st.results m) b.body _)

theorem expandExterns_spec : ∀ {es es' : List (FnRef × ExtFunc)}, expandExterns es = .ok es' →
    es'.map (·.1) = es.map (·.1) ∧ ∀ fn e, es.lookup fn = some e →
      ∃ s', sigExp e.sig = some s' ∧ es'.lookup fn = some { e with sig := s' }
  | [], es', h => by
    simp only [expandExterns, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  | (r, e) :: es, es', h => by
    simp only [expandExterns] at h
    cases hs : expandSig e.sig with
    | error err => rw [hs] at h; cases h
    | ok s =>
      rw [hs] at h
      cases hr : expandExterns es with
      | error err => simp [hr, bind, Except.bind] at h
      | ok rest =>
        simp only [hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨hk, hl⟩ := expandExterns_spec hr
        refine ⟨by simp [hk], fun fn e' he' => ?_⟩
        by_cases hfn : fn = r
        · subst hfn
          simp only [List.lookup_cons, beq_self_eq_true, Option.some.injEq] at he' ⊢
          subst he'
          exact ⟨s, by simp [sigExp, hs, Except.toOption], rfl⟩
        · have hb : (fn == r) = false := by simpa using hfn
          simp only [List.lookup_cons, hb] at he' ⊢
          exact hl fn e' he'

theorem expandSigDecls_spec : ∀ {ds ds' : List (Nat × Signature)}, expandSigDecls ds = .ok ds' →
    ∀ i d, ds.lookup i = some d → ∃ d', sigExp d = some d' ∧ ds'.lookup i = some d'
  | [], ds', h => by simp
  | (j, d) :: ds, ds', h => by
    simp only [expandSigDecls] at h
    cases hs : expandSig d with
    | error err => rw [hs] at h; cases h
    | ok s =>
      rw [hs] at h
      cases hr : expandSigDecls ds with
      | error err => simp [hr, bind, Except.bind] at h
      | ok rest =>
        simp only [hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        intro i d' hd'
        by_cases hij : i = j
        · subst hij
          simp only [List.lookup_cons, beq_self_eq_true, Option.some.injEq] at hd' ⊢
          subst hd'
          exact ⟨s, by simp [sigExp, hs, Except.toOption], rfl⟩
        · have hb : (i == j) = false := by simpa using hij
          simp only [List.lookup_cons, hb] at hd' ⊢
          exact expandSigDecls_spec hr i d' hd'

theorem lt_maxFnRef {f : Function} {r : FnRef} (h : r ∈ f.externs.map (·.1)) : r < maxFnRef f := by
  obtain ⟨⟨r', e⟩, hm, rfl⟩ := List.mem_map.mp h
  have := mem_le_foldl_max (fun (e : FnRef × ExtFunc) => e.1) 0 hm
  exact Nat.lt_succ_of_le this

theorem helperExts_keys_eq (f : Function) : (helperExts f).map (·.1) =
    (List.range' 0 (helperNames f).length).map (maxFnRef f + 1 + ·) := by
  rw [← List.zipIdx_map_snd 0 (helperNames f), List.map_map]
  simp only [helperExts, List.map_map]
  rfl

theorem helperExts_keys (f : Function) :
    ((helperExts f).map (·.1)).Nodup ∧ ∀ r ∈ (helperExts f).map (·.1), maxFnRef f < r := by
  rw [helperExts_keys_eq]
  refine ⟨nodup_map_on (f := fun x => maxFnRef f + 1 + x)
    (fun x _ y _ e => by vomega) List.nodup_range', fun r hr => ?_⟩
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr
  vomega

/-! ## Completeness -/

/-- **The preconditions of completeness**: `f` mentions `i128` (otherwise `function128Cert`
returns `f` itself), the `f`-only conjuncts of `check` (distinct definitions, every value id
below `maxValueId f`), no statement reads its own result, and the two constructs the legaliser
expands outside `check` do not occur: `call_indirect` with an `i128` signature and
`try_call_indirect`. -/
structure Pre (f : Function) : Prop where
  mentions : mentions128 f = true
  defs : ((defsOf f).map (·.1)).Nodup
  ids : ∀ v ∈ idsOf f, v < maxValueId f
  noSelf : ∀ b ∈ f.blocks, ∀ s ∈ b.body, ∀ x ∈ instOps s.inst, x ∉ s.results
  callInd : ∀ b ∈ f.blocks, ∀ s ∈ b.body, ∀ sig callee args,
    s.inst = .callIndirect sig callee args → ∀ d, f.sigDecls.lookup sig = some d → sig128 d = false
  noTryInd : ∀ b ∈ f.blocks, ∀ c args et, b.term ≠ .tryCallIndirect c args et

theorem bfacts_of_pre {f : Function} (hp : Pre f) {C : Ctx} (hf : C.f = f) {b : Block}
    (hb : b ∈ f.blocks) : BFacts C b := by
  have hT : C.T0 = maxValueId f := by simp [Ctx.T0, hf]
  have hid : ∀ v, (v ∈ b.params.map (·.1) ∨ (∃ s ∈ b.body, v ∈ s.results ∨ v ∈ instOps s.inst) ∨
      v ∈ termOps b.term) → v < C.T0 := by
    intro v hv
    rw [hT]
    refine hp.ids v ?_
    simp only [idsOf, List.mem_flatMap, List.mem_append]
    refine ⟨b, hb, ?_⟩
    rcases hv with hv | ⟨s, hs, hv⟩ | hv
    · exact .inl (.inl hv)
    · exact .inl (.inr ⟨s, hs, by simpa using hv⟩)
    · exact .inr hv
  have hkeys : (b.params.map (·.1) ++ b.body.flatMap (·.results)).Nodup := by
    have := hp.defs
    rw [defsOf_keys] at this
    exact (sublist_flatMap_of_mem (f := fun b : Block => b.params.map (·.1) ++
      b.body.flatMap (·.results)) hb).nodup this
  refine ⟨fun p hp' => hid p.1 (.inl (List.mem_map.mpr ⟨p, hp', rfl⟩)),
    (List.sublist_append_left _ _).nodup hkeys, fun s hs => ⟨⟨fun x hx => hid x (.inr (.inl
      ⟨s, hs, .inr hx⟩)), fun r hr => hid r (.inr (.inl ⟨s, hs, .inl hr⟩)), ?_,
      hp.noSelf b hb s hs⟩, fun sig callee args hi d hd => hp.callInd b hb s hs sig callee args hi d
        (by rw [← hf]; exact hd)⟩,
    fun x hx => hid x (.inr (.inr hx)), hp.noTryInd b hb⟩
  exact ((sublist_flatMap_of_mem (f := (·.results)) hs).trans
    (List.sublist_append_right _ _)).nodup hkeys

/-- The legaliser's certificate. -/
def certOf (f : Function) : Cert :=
  { pairs := allocPairs f (maxValueId f + 1),
    zero := maxValueId f + 1 + 2 * (allocPairs f (maxValueId f + 1)).length }

theorem gok_of {f g0 : Function} {es : List (FnRef × ExtFunc)} {ds : List (Nat × Signature)}
    (hes : expandExterns f.externs = .ok es) (hds : expandSigDecls f.sigDecls = .ok ds)
    (he : g0.externs = es ++ helperExts f) (hd : g0.sigDecls = ds) (c : Cert) :
    GOk ⟨f, g0, c⟩ := by
  obtain ⟨hk, hl⟩ := expandExterns_spec hes
  obtain ⟨hnd, hgt⟩ := helperExts_keys f
  refine ⟨fun fn e hfe => ?_, fun fn e hm => ?_, fun i d hdi => ?_⟩
  · obtain ⟨s', hs', hl'⟩ := hl fn e hfe
    exact ⟨s', hs', by simp [Function.extern?, he, List.lookup_append, hl']⟩
  · have hfn := hgt fn (List.mem_map.mpr ⟨(fn, e), hm, rfl⟩)
    have hnone : es.lookup fn = none := by
      rw [List.lookup_eq_none_iff]
      intro p hp
      have : p.1 ∈ f.externs.map (·.1) := by rw [← hk]; exact List.mem_map.mpr ⟨p, hp, rfl⟩
      have := lt_maxFnRef this
      simp only [bne_iff_ne, ne_eq]
      intro e; vomega
    simp [Function.extern?, he, List.lookup_append, hnone, lookup_of_mem hnd hm]
  · obtain ⟨d', hd', hl'⟩ := expandSigDecls_spec hds i d hdi
    exact ⟨d', hd', by simpa [hd] using hl'⟩

theorem check_of_run {f g0 : Function} {pg rg : List (List SlotEl)} {bs' : List Block}
    {st' : St} (hp : Pre f) (hne : f.blocks ≠ [])
    (hname : g0.name = f.name) (hslots : g0.slots = f.slots) (hglob : g0.globals = f.globals)
    (hsig : sigExp f.sig = some g0.sig) (hO : GOk ⟨f, g0, certOf f⟩)
    (hpg : groups f.sig.params = some pg) (hrg : groups f.sig.returns = some rg)
    (hrun : (rewriteBlocks ⟨f, g0, certOf f⟩ pg rg true f.blocks).run
      { next := (certOf f).zero + 1 } = .ok (bs', st')) :
    check f { g0 with blocks := bs' } (certOf f) = true := by
  have A : Agree ⟨f, g0, certOf f⟩ ⟨f, { g0 with blocks := bs' }, certOf f⟩ := ⟨rfl, rfl, rfl, rfl⟩
  have hG : CGood ⟨f, g0, certOf f⟩ := cgood_alloc f g0
  have hGD : CGood ⟨f, { g0 with blocks := bs' }, certOf f⟩ := cgood_alloc f _
  obtain ⟨hlen, hhead, hok1, hok2⟩ := rewriteBlocks_spec A hG hO hpg hrg f.blocks true
    (fun b hb => bfacts_of_pre hp rfl hb) (by simp [Ctx.zero]) hrun
  obtain ⟨b, bs, hfb⟩ : ∃ b bs, f.blocks = b :: bs := by
    cases hf : f.blocks with
    | nil => exact absurd hf hne
    | cons b bs => exact ⟨b, bs, rfl⟩
  rw [hfb] at hlen hok1 hok2
  obtain ⟨b', bs'', rfl⟩ : ∃ b' bs'', bs' = b' :: bs'' := by
    cases bs' with
    | nil => simp at hlen
    | cons b' bs'' => exact ⟨b', bs'', rfl⟩
  obtain ⟨rest, hrest⟩ := hhead rfl b' (by simp)
  have hfv : (⟨f, g0, certOf f⟩ : Ctx).zero < ({ g0 with blocks := b' :: bs'' } : Function).freshValue :=
    zero_lt_freshValue (bs := bs'') rfl hrest
  have h1 := hok1 hfv b (by simp) b' (by simp)
  have h2 := hok2 hfv
  simp only [List.drop_one, List.tail_cons] at h2
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
  unfold check
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, hfb]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨hname, hslots⟩, hglob⟩, hsig⟩, hp.defs⟩, fun v hv => hp.ids v hv⟩, certOk_of hGD⟩,
    by simp [hlen]⟩, h1, List.all_eq_true.mp h2⟩

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases hx : x with
  | error e => rw [hx] at h; cases h
  | ok a => rw [hx] at h; exact ⟨a, rfl, h⟩

/-- **Completeness of `Opt.Legal.check`**: the validator accepts every legalisation of a function
satisfying `Pre`. -/
theorem check_complete {f g : Function} {cert : Cert} (hp : Pre f)
    (h : function128Cert f = .ok (g, cert)) : check f g cert = true := by
  simp only [function128Cert, hp.mentions, Bool.not_true, Bool.false_eq_true, ite_false] at h
  split at h
  · cases h
  rename_i hne
  obtain ⟨sig, hsig, h⟩ := except_bind_ok h
  obtain ⟨es, hes, h⟩ := except_bind_ok h
  obtain ⟨ds, hds, h⟩ := except_bind_ok h
  obtain ⟨pg, hpg, h⟩ := except_bind_ok h
  obtain ⟨rg, hrg, h⟩ := except_bind_ok h
  obtain ⟨⟨bs', st'⟩, hrun, h⟩ := except_bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hpg' : groups f.sig.params = some pg := by simp [groups, hpg, Except.toOption]
  have hrg' : groups f.sig.returns = some rg := by simp [groups, hrg, Except.toOption]
  exact check_of_run (g0 := { f with sig := sig, externs := es ++ helperExts f, sigDecls := ds })
    (st' := st') hp (by simpa using hne) rfl rfl rfl
    (by simp [sigExp, hsig, Except.toOption]) (gok_of hes hds rfl rfl _) hpg' hrg' hrun

end Opt.Legal.Complete
