import FV.Opt.Proof.LegalSem

/-!
# Register-file updates and the source invariant across a statement

`Regs.setMany` facts, and preservation of `SrcInv` (the source values agree with their unique
definitions in `f`) across a non-call statement of `f` and across a branch into a block of `f`.
-/

namespace Opt.Legal

open Clif

theorem setMany_len {ρ ρ' : Regs} {rs : List ValueId} {vs : List Val}
    (h : ρ.setMany rs vs = some ρ') : rs.length = vs.length := by
  induction rs generalizing ρ vs with
  | nil => cases vs <;> simp [Regs.setMany] at h ⊢
  | cons r rs ih =>
    cases vs with
    | nil => simp [Regs.setMany] at h
    | cons v vs => simp only [Regs.setMany_cons] at h; simp [ih h]

theorem setMany_of_len (ρ : Regs) {rs : List ValueId} {vs : List Val}
    (h : rs.length = vs.length) : ∃ ρ', ρ.setMany rs vs = some ρ' := by
  induction rs generalizing ρ vs with
  | nil => cases vs <;> simp_all
  | cons r rs ih =>
    cases vs with
    | nil => simp at h
    | cons v vs => simp only [Regs.setMany_cons]; exact ih _ (by simpa using h)

theorem setMany_other {ρ ρ' : Regs} {rs : List ValueId} {vs : List Val}
    (h : ρ.setMany rs vs = some ρ') {v : ValueId} (hv : v ∉ rs) : ρ' v = ρ v := by
  induction rs generalizing ρ vs with
  | nil => cases vs <;> simp_all [Regs.setMany]
  | cons r rs ih =>
    cases vs with
    | nil => simp [Regs.setMany] at h
    | cons x vs =>
      simp only [Regs.setMany_cons] at h
      simp only [List.mem_cons, not_or] at hv
      rw [ih h hv.2, Regs.set_other _ _ hv.1]

theorem setMany_get {ρ ρ' : Regs} {rs : List ValueId} {vs : List Val}
    (h : ρ.setMany rs vs = some ρ') (hnd : rs.Nodup) {i : Nat} {r : ValueId}
    (hi : rs[i]? = some r) : ρ' r = vs[i]? := by
  induction rs generalizing ρ vs i with
  | nil => simp at hi
  | cons r0 rs ih =>
    cases vs with
    | nil => simp [Regs.setMany] at h
    | cons x vs =>
      simp only [Regs.setMany_cons] at h
      simp only [List.nodup_cons] at hnd
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        rw [setMany_other h hnd.1]; simp
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi ⊢
        exact ih h hnd.2 hi

/-- A value set by `setMany` is one of the bound values, at the same position. -/
theorem setMany_mem {ρ ρ' : Regs} {rs : List ValueId} {vs : List Val}
    (h : ρ.setMany rs vs = some ρ') (hnd : rs.Nodup) {v : ValueId} (hv : v ∈ rs) :
    ∃ i : Nat, rs[i]? = some v ∧ ρ' v = vs[i]? := by
  obtain ⟨i, hi, hiv⟩ := List.getElem_of_mem hv
  exact ⟨i, by simp [hi, hiv], setMany_get h hnd (by simp [hi, hiv])⟩

theorem sublist_flatMap {α β : Type} {l : List α} {a : α} (g : α → List β) (h : a ∈ l) :
    (g a).Sublist (l.flatMap g) := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact List.sublist_append_left _ _
    · exact (ih h).trans (List.sublist_append_right _ _)

/-- The results of a statement of `f` are distinct (definitions are unique). -/
theorem results_nodup {f : Function} (hnd : ((defsOf f).map (·.1)).Nodup) {B : Block}
    (hB : B ∈ f.blocks) {s : Stmt} (hs : s ∈ B.body) : s.results.Nodup := by
  have h1 : (stmtDefs f s).Sublist (defsOf f) :=
    ((sublist_flatMap (stmtDefs f) hs).trans (List.sublist_append_right _ _)).trans
      (sublist_flatMap (blockDefs f) hB)
  have h2 := hnd.sublist (h1.map (·.1))
  have : (stmtDefs f s).map (·.1) = s.results := by
    simp only [stmtDefs, List.map_map]
    have e : ((fun x : ValueId × Option Ty × Option Inst => x.fst) ∘ fun x : ValueId × Nat =>
        (x.fst, (Inst.resultTypes (sigOfF f) (declOfF f) s.inst).bind fun y => y[x.snd]?,
          some s.inst)) = fun x => x.fst := rfl
    rw [e]; simp
  rwa [this] at h2


end Opt.Legal
