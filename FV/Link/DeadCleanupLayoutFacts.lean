import FV.Link.DeadCleanupImage
import FV.Link.LayoutFacts
namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck Backend LinkSpec
theorem pipeT_layout {f : Clif.Function} {k : Nat} {b : BitVec 64} {o : Lean.Json} {a : Art}
    (h : pipeCleanupT f k b o = .ok a) : a.fa.layout = .ok a.fb ∧ a.base = b := by
  unfold pipeCleanupT at h
  rcases h1 : lowerFunction f with _ | vc <;> simp only [h1, bind, Except.bind] at h
  · cases h
  rcases h2 : prepare (Backend.DeadCleanup.prune vc) with _ | vcp <;> simp only [h2] at h
  · cases h
  rcases h3 : lowerAllocReady vcp (raAnswer vcp o) with _ | af <;> simp only [h3] at h
  · cases h
  rcases h4 : emitFunc k af with _ | fa <;> simp only [h4] at h
  · cases h
  rcases h5 : fa.layout with _ | fb <;> simp only [h5] at h
  · cases h
  cases h
  exact ⟨h5, rfl⟩

theorem tab_length (S : LinkSpec) :
    (tabOf S.inputCleanup.resultsCleanupT).length = S.funcs.length := by
  simp [tabOf, LinkInput.resultsCleanupT]

/-- The `i`-th placed function's name is the placement's (`namesOkB`). -/
theorem names_getElem! {S : LinkSpec} (hn : S.namesOkB (tabOf S.inputCleanup.resultsCleanupT) = true) {i : Nat}
    (hi : i < S.funcs.length) : S.names[i]! = S.funcs[i].func.name := by
  have hs' := congrArg (·[i]?) (of_decide_eq_true hn)
  simp only [tabOf, LinkInput.resultsCleanupT, inputCleanup_funcs, List.map_map, List.getElem?_map,
    List.getElem?_take, hi, ite_true, List.getElem?_eq_getElem hi,
    Option.map_some, Function.comp_def] at hs'
  rw [getElem!_pos S.names i (List.getElem?_eq_some_iff.1 hs'.symm).1]
  exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hs'.symm)

/-- The `i`-th entry of the compiled table: the `i`-th function of the input, compiled at its
load address (`hr`: the pipeline accepts every function). -/
theorem tab_entry {S : LinkSpec} (hr : S.inputCleanup.resultsCleanupT.all (·.2.toBool) = true) {i : Nat}
    (hi : i < S.funcs.length) :
    ∃ fi a, S.funcs[i]? = some fi ∧
      pipeCleanupT fi.func fi.k (BitVec.ofNat 64 (S.inputCleanup.baseOf fi.func.name)) (raJ fi.ra fi.j) =
        .ok a ∧ (tabOf S.inputCleanup.resultsCleanupT)[i]? = some (fi.func, a) := by
  have hl : i < S.funcs.length := hi
  let fi := S.funcs[i]
  refine ⟨fi, getOk (pipeCleanupT fi.func fi.k (BitVec.ofNat 64 (S.inputCleanup.baseOf fi.func.name))
    (raJ fi.ra fi.j)), List.getElem?_eq_getElem hl, ?_, ?_⟩
  · apply getOk_eq
    have hl' : i < S.inputCleanup.resultsCleanupT.length := by simpa [LinkInput.resultsCleanupT] using hl
    have := List.all_eq_true.1 hr _ (List.getElem_mem hl')
    simpa only [LinkInput.resultsCleanupT, List.getElem_map, inputCleanup_funcs] using this
  · simp only [tabOf, LinkInput.resultsCleanupT, inputCleanup_funcs, List.map_map, List.getElem?_map,
      List.getElem?_eq_getElem hl]
    rfl

/-- **A placed function's entry**: the `i`-th function, at its placed address, with the
placement's name (`namesOkB`) and `sizes[i]` words (`sizesOkB`), compiled by the pipeline (its
layout). -/
theorem tab_placed {S : LinkSpec} (hp : S.placeOkB = true)
    (hr : S.inputCleanup.resultsCleanupT.all (·.2.toBool) = true)
    (hn : S.namesOkB (tabOf S.inputCleanup.resultsCleanupT) = true)
    (hs : S.sizesOkB (tabOf S.inputCleanup.resultsCleanupT) = true) :
    ∀ i < S.funcs.length, ∃ e, (tabOf S.inputCleanup.resultsCleanupT)[i]? = some e ∧
      e.2.base = BitVec.ofNat 64 (S.R + (offs S.sizes 0)[i]!) ∧
      e.2.fb.words.size = S.sizes[i]! ∧ e.1.name = S.names[i]! ∧
      e.2.fa.layout = .ok e.2.fb := by
  intro i hi
  have hP := placeOk_of hp
  obtain ⟨fi, a, hfi, ha, ht⟩ := tab_entry hr (i := i) (by omega)
  rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hfi
  subst hfi
  have hn := names_getElem! hn hi
  obtain ⟨hl, hb⟩ := pipeT_layout ha
  refine ⟨_, ht, ?_, ?_, hn.symm, hl⟩
  · rw [hb, ← hn, inputCleanup_baseOf_name hP hi]
  · have hs' := congrArg (·[i]?) (of_decide_eq_true hs)
    simp only [List.getElem?_map, List.getElem?_take, hi, ite_true, ht, Option.map_some] at hs'
    have hi' : i < S.sizes.length := by rw [hP.sizesLen]; exact hi
    rw [getElem!_pos S.sizes i hi', ← Option.some.inj (hs'.trans (List.getElem?_eq_getElem hi'))]


end Link.DeadCleanup
