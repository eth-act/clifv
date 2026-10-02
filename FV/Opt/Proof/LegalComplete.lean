import FV.Opt.Legal

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

/-! ## Running the legaliser's monad -/

@[simp] theorem fresh_run (st : St) : fresh.run st = .ok (st.next, { st with next := st.next + 1 }) :=
  rfl

@[simp] theorem emit1_run (st : St) (r : ValueId) (i : Inst) :
    (emit1 r i).run st = .ok ((), { st with out := st.out ++ [{ results := [r], inst := i }] }) :=
  rfl

@[simp] theorem emitS_run (st : St) (s : Stmt) :
    (emitS s).run st = .ok ((), { st with out := st.out ++ [s] }) := rfl

@[simp] theorem emitN_run (st : St) (l : List Stmt) :
    (emitN l).run st = .ok ((), { st with out := st.out ++ l }) := rfl

@[simp] theorem kI64_run (st : St) (n : Int) :
    (kI64 n).run st = .ok (st.next, { st with next := st.next + 1, out := st.out ++ [({ results := [st.next], inst := .iconst .i64 (BitVec.ofInt 64 n) } : Stmt)] }) := rfl

@[simp] theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

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

/-! ## Invariants of the legaliser's state -/

/-- `m` preserves `P` when it succeeds. -/
def Pres {α : Type} (P : St → Prop) (m : M α) : Prop :=
  ∀ st r st', P st → m.run st = .ok (r, st') → P st'

theorem pres_pure {α : Type} (P : St → Prop) (a : α) : Pres P (pure a) := by
  intro st r st' h e
  simp only [StateT.run_pure] at e
  cases e; exact h

theorem pres_bind {α β : Type} {P : St → Prop} {x : M α} {f : α → M β} (hx : Pres P x)
    (hf : ∀ a, Pres P (f a)) : Pres P (x >>= f) := by
  intro st r st' h e
  rw [StateT.run_bind] at e
  cases hr : x.run st with
  | error err => rw [hr] at e; cases e
  | ok p =>
    rw [hr] at e
    exact hf p.1 p.2 r st' (hx st p.1 p.2 h (by rw [hr])) e

theorem pres_forIn {γ β : Type} {P : St → Prop} (f : γ → β → M (ForInStep β)) :
    ∀ (l : List γ), (∀ x ∈ l, ∀ b, Pres P (f x b)) → ∀ b, Pres P (forIn l b f)
  | [], _, b => by simpa using pres_pure P b
  | x :: l, hf, b => by
    rw [List.forIn_cons]
    refine pres_bind (hf x (by simp) b) fun r => ?_
    cases r with
    | done b' => exact pres_pure P b'
    | yield b' => exact pres_forIn f l (fun y hy => hf y (by simp [hy])) b'

theorem pres_modify {P : St → Prop} (g : St → St) (hg : ∀ s, P s → P (g s)) :
    Pres P (modify g : M Unit) := by
  intro st r st' h e
  simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run,
    pure, Except.pure, Except.ok.injEq] at e
  cases e; exact hg st h

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

/-- A definition of `f` determines `tyOf` under distinct definitions. -/
theorem tyOf_of_mem {f : Function} (hn : ((defsOf f).map (·.1)).Nodup) {v : ValueId}
    {t : Option Ty} {i : Option Inst} (h : (v, t, i) ∈ defsOf f) : tyOf f v = t := by
  simp [tyOf, lookup_of_mem hn h]

theorem tyOf_param {f : Function} (hn : ((defsOf f).map (·.1)).Nodup) {b : Block}
    (hb : b ∈ f.blocks) {v : ValueId} {t : Ty} (hv : (v, t) ∈ b.params) : tyOf f v = some t :=
  tyOf_of_mem hn (i := none) (List.mem_flatMap.mpr ⟨b, hb, by
    simp only [blockDefs, List.mem_append, List.mem_map]
    exact .inl ⟨(v, t), hv, rfl⟩⟩)

theorem tyOf_result {f : Function} (hn : ((defsOf f).map (·.1)).Nodup) {b : Block}
    (hb : b ∈ f.blocks) {s : Stmt} (hs : s ∈ b.body) {ts : List Ty}
    (hts : s.inst.resultTypes (sigOfF f) (declOfF f) = some ts) {r : ValueId} {t : Ty}
    (hr : (r, t) ∈ s.results.zip ts) : tyOf f r = some t := by
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hr
  simp only [List.length_zip] at hi
  simp only [List.getElem_zip, Prod.mk.injEq] at e
  refine tyOf_of_mem hn (i := some s.inst) (List.mem_flatMap.mpr ⟨b, hb, ?_⟩)
  simp only [blockDefs, List.mem_append]
  right
  refine List.mem_flatMap.mpr ⟨s, hs, ?_⟩
  simp only [stmtDefs, hts, List.mem_map]
  refine ⟨(r, i), ?_, ?_⟩
  · rw [List.mem_iff_getElem?]
    exact ⟨i, by simp [List.getElem?_zipIdx, e.1, List.getElem?_eq_getElem (by omega : i < s.results.length)]⟩
  · simp [Option.bind, List.getElem?_eq_getElem (by omega : i < ts.length), e.2]

/-! ## `phaseA1`: pairs of `i128` values -/

/-- The pairs: of `i128` values of `f`, fresh (above `maxValueId f`, below `next`), two
different components, and different values have disjoint pairs. -/
structure PInv (f : Function) (st : St) : Prop where
  next : maxValueId f < st.next
  pair : ∀ v a b, st.pair[v]? = some (a, b) → tyOf f v = some .i128 ∧ maxValueId f < a ∧
    a < st.next ∧ maxValueId f < b ∧ b < st.next ∧ a ≠ b
  disj : ∀ v w a b c d : ValueId, v ≠ w → st.pair[v]? = some (a, b) → st.pair[w]? = some (c, d) →
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d

/-- Allocating a fresh pair for an `i128` value keeps `PInv`. -/
theorem pinv_insert {f : Function} {st : St} (h : PInv f st) {v : ValueId}
    (hv : tyOf f v = some .i128) :
    PInv f { st with next := st.next + 2, pair := st.pair.insert v (st.next, st.next + 1) } := by
  refine ⟨by have := h.next; vomega, fun w a b hw => ?_, fun w w' a b c d hne hw hw' => ?_⟩
  · simp only [Std.HashMap.getElem?_insert] at hw
    split at hw
    · rename_i e
      simp only [beq_iff_eq] at e
      subst e
      cases hw
      exact ⟨hv, h.next, by vomega, by have := h.next; vomega, by vomega, by vomega⟩
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.pair w a b hw
      exact ⟨h1, h2, by vomega, h4, by vomega, h6⟩
  · simp only [Std.HashMap.getElem?_insert] at hw hw'
    split at hw <;> split at hw'
    · rename_i e e'
      simp only [beq_iff_eq] at e e'
      exact absurd (e.symm.trans e') hne
    · cases hw
      obtain ⟨-, -, h3, -, h5, -⟩ := h.pair w' c d hw'
      exact ⟨by vomega, by vomega, by vomega, by vomega⟩
    · cases hw'
      obtain ⟨-, -, h3, -, h5, -⟩ := h.pair w a b hw
      exact ⟨by vomega, by vomega, by vomega, by vomega⟩
    · exact h.disj w w' a b c d hne hw hw'

theorem pinv_congr {f : Function} {st st' : St} (h : PInv f st) (h1 : st'.next = st.next)
    (h2 : st'.pair = st.pair) : PInv f st' := by
  obtain ⟨hn, hp, hd⟩ := h
  exact ⟨h1 ▸ hn, fun v a b hv => h1 ▸ hp v a b (h2 ▸ hv), fun v w a b c d hne hv hw =>
    hd v w a b c d hne (h2 ▸ hv) (h2 ▸ hw)⟩

/-- Allocating and recording the pair of an `i128` value. -/
theorem pres_allocInsert {f : Function} {v : ValueId} (hv : tyOf f v = some .i128) :
    Pres (PInv f) (do
      let p ← allocPair
      modify fun s => { s with pair := s.pair.insert v p }
      pure (ForInStep.yield PUnit.unit) : M (ForInStep PUnit)) := by
  intro st r st' h e
  simp only [allocPair, StateT.run_bind, fresh_run, except_ok_bind, StateT.run_pure,
    StateT.run_modify] at e
  simp only [pure, Except.pure] at e
  cases e
  have := pinv_insert h hv
  exact pinv_congr this (by simp [Nat.add_assoc]) rfl

/-- **`phaseA1`** allocates fresh, disjoint pairs, only for `i128` values. -/
theorem phaseA1_pinv {f : Function} (hn : ((defsOf f).map (·.1)).Nodup) :
    Pres (PInv f) (phaseA1 f) := by
  unfold phaseA1
  dsimp only
  refine pres_bind (pres_forIn _ _ ?_ _) fun _ => pres_pure _ _
  intro b hb _
  refine pres_bind (pres_forIn _ _ (fun x hx _ => ?_) _) fun _ =>
    pres_bind (pres_forIn _ _ (fun s hs _ => ?_) _) fun _ => pres_pure _ _
  · split
    · rename_i ht
      simp only [beq_iff_eq] at ht
      exact pres_allocInsert (tyOf_param hn hb (show (x.1, Ty.i128) ∈ b.params by rw [← ht]; exact hx))
    · exact pres_pure _ _
  · have hmod : ∀ (g : St → St), (∀ st, (g st).next = st.next ∧ (g st).pair = st.pair) →
        Pres (PInv f) (modify g : M Unit) := fun g hg =>
      pres_modify g fun st h => pinv_congr h (hg st).1 (hg st).2
    have hlast : Pres (PInv f) (match s.inst with
        | Inst.call _ _ => (pure (ForInStep.yield PUnit.unit) : M (ForInStep PUnit))
        | Inst.callIndirect _ _ _ => pure (ForInStep.yield PUnit.unit)
        | _ => match Inst.resultTypes (fun r => Option.map (fun x => x.sig) (List.lookup r f.externs))
              (fun s => List.lookup s f.sigDecls) s.inst with
          | some ts => do
            forIn (s.results.zip ts) PUnit.unit fun x _ =>
              match x with
              | (r, t) =>
                if (t == Ty.i128) = true then do
                  let p ← allocPair
                  modify fun st => { st with pair := st.pair.insert r p }
                  pure (ForInStep.yield PUnit.unit)
                else pure (ForInStep.yield PUnit.unit)
            pure (ForInStep.yield PUnit.unit)
          | _ => pure (ForInStep.yield PUnit.unit)) := by
      split
      · exact pres_pure _ _
      · exact pres_pure _ _
      · split
        · rename_i ts hts
          refine pres_bind (pres_forIn _ _ (fun x hx _ => ?_) _) fun _ => pres_pure _ _
          rcases x with ⟨r, t⟩
          simp only
          split
          · rename_i ht
            simp only [beq_iff_eq] at ht
            subst ht
            exact pres_allocInsert (tyOf_result hn hb hs hts hx)
          · exact pres_pure _ _
        · exact pres_pure _ _
    have hloop : ∀ (l : List ValueId) (g : ValueId → St → St),
        (∀ r st, (g r st).next = st.next ∧ (g r st).pair = st.pair) →
        Pres (PInv f) (forIn l PUnit.unit fun r _ => do
          modify (g r)
          pure (ForInStep.yield PUnit.unit) : M PUnit) := fun l g hg =>
      pres_forIn _ l (fun r _ _ => pres_bind (hmod _ (hg r)) fun _ => pres_pure _ _) _
    split
    · refine pres_bind (hloop _ _ (fun _ _ => ⟨rfl, rfl⟩)) fun _ => ?_
      split
      · exact pres_bind (hloop _ _ (fun _ _ => ⟨rfl, rfl⟩)) fun _ => hlast
      · exact hlast
    · split
      · exact pres_bind (hloop _ _ (fun _ _ => ⟨rfl, rfl⟩)) fun _ => hlast
      · exact hlast

end Opt.Legal.Complete
