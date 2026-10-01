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

theorem evalInst_resultTypes {fr : Frame} {m : Mem} {i : Inst} {vals : List Val} {m' : Mem}
    (h : evalInst fr m i = .ok (vals, m')) (sigOf : FnRef → Option Signature)
    (declOf : Nat → Option Signature) : ∃ tys, i.resultTypes sigOf declOf = some tys := by
  cases i <;> simp only [Inst.resultTypes, Option.some.injEq, exists_eq'] <;>
    simp only [evalInst, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
  · obtain ⟨t2, ht2, -⟩ := h; simp [ht2]
  · obtain ⟨t2, ht2, -⟩ := h; simp [ht2]
  · cases h
  · cases h

/-- **The source invariant across a non-call statement of `f`.** -/
theorem srcInv_stmt {f : Function} (hnd : ((defsOf f).map (·.1)).Nodup) {B : Block}
    (hB : B ∈ f.blocks) {s : Stmt} (hs : s ∈ B.body) {fr : Frame} {m m' : Mem}
    {vals : List Val} {regs : Regs} (hinv : SrcInv f fr.regs)
    (h : evalInst fr m s.inst = .ok (vals, m'))
    (hset : fr.regs.setMany s.results vals = some regs) : SrcInv f regs := by
  intro v x hx
  by_cases hv : v ∈ s.results
  · obtain ⟨i, hi, hvi⟩ := setMany_mem hset (results_nodup hnd hB hs) hv
    rw [hx] at hvi
    have hl := lookup_of_mem hnd (mem_defsOf_stmt hB hs hi)
    obtain ⟨tys, htys⟩ := evalInst_resultTypes h (sigOfF f) (declOfF f)
    have hty := evalInst_types h htys
    have hxt : tys[i]? = some x.ty := by
      rw [← hty, List.getElem?_map, ← hvi]; rfl
    refine ⟨?_, ?_, ?_⟩
    · refine .inr ?_
      simp only [tyOf, hl, htys, Option.bind_some]; exact hxt
    · intro c hc
      simp only [constOf, defInst, hl, Option.bind_some] at hc
      split at hc
      · rename_i t k hk
        simp only [Option.some.injEq] at hk hc
        rw [hk] at h
        simp only [evalInst, Res.pure_eq_ok, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        have : i = 0 := by
          have := (List.getElem?_eq_some_iff.1 hvi.symm).1; simp at this; omega
        subst this; simp at hvi; subst hvi; exact hc
      · cases hc
    · intro c hc
      simp only [concatConst, defInst, hl, Option.bind_some] at hc
      split at hc
      · rename_i lo hi' hk
        simp only [Option.some.injEq] at hk
        rw [hk] at h
        simp only [evalInst, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.pure_eq_ok, Prod.mk.injEq,
          Frame.getAs] at h
        obtain ⟨t2, ht2, l, ⟨xl, hxl, hl2⟩, hh, -, h3, -⟩ := h
        simp only [Ty.double?, Option.some.injEq] at ht2
        subst ht2
        subst h3
        have hi0 : i = 0 := by
          have := (List.getElem?_eq_some_iff.1 hvi.symm).1; simp at this; omega
        subst hi0
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hvi
        subst hvi
        simp only [Frame.get, Res.ofOption_eq_ok] at hxl
        have hdl := (hinv lo xl hxl).2.1 c hc
        obtain ⟨tx, bx⟩ := xl
        simp only [Val.as?] at hl2
        split at hl2
        · rename_i heq
          subst heq
          simp only [Option.some.injEq] at hl2
          subst hl2
          simp only [Sem.iconcat] at hdl ⊢
          rw [← hdl, BitVec.toNat_setWidth, BitVec.toNat_append, Nat.shiftLeft_eq]
          have := bx.isLt
          simp only [show Ty.i64.width = 64 from rfl] at this ⊢
          rw [Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt this,
            show Ty.i128.width = 128 from rfl]
          omega
        · cases hl2
      · cases hc
  · rw [setMany_other hset hv] at hx; exact hinv v x hx


end Opt.Legal
