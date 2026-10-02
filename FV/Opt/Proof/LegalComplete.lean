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

end Opt.Legal.Complete
