import FV.Link.UnwFnsComplete
import FV.E2E.DeadCleanupUnwindWitness

/-!
# Witness: the completeness theorems of the unwinding checks apply (S10g, #404)

On `E2E.DeadCleanupUnwindWitness`'s `try_call` function `tc` (a `tag0` handler, a landing pad,
a frame): the premises of `callSites_complete`, `padsNonzero_complete` and
`unwindRows_complete` hold (`native_decide` on their decidable forms), so the theorems give the
checks on its compiled code.
-/

namespace Link.EhCheck.Complete.Witness

open Backend Backend.Proof E2E E2E.DeadCleanupUnwindWitness

/-- `HandlersOk`, decided. -/
def handlersOkB (af : AFunc) : Bool :=
  af.calls.all fun c => match c with
    | some ti => ti.handlers.all fun h =>
        (match h with | .tag n _ => decide (n ≤ 1) | .default _ => false) &&
          (List.range af.blocks.size).any fun b => (af.blocks[b]?.map (·.1)) == some h.label
    | none => true

theorem handlersOk_of {af : AFunc} (h : handlersOkB af = true) : HandlersOk af := by
  intro ti hti hd hhd
  have h1 := List.all_eq_true.1 h _ hti
  simp only [List.all_eq_true, Bool.and_eq_true, List.any_eq_true, List.mem_range] at h1
  obtain ⟨htag, b, hb, hl⟩ := h1 hd hhd
  refine ⟨?_, ?_⟩
  · cases hd with
    | tag n l => exact ⟨n, l, rfl, by simpa using htag⟩
    | default l => cases htag
  · cases hbb : af.blocks[b]? with
    | none => rw [hbb] at hl; cases hl
    | some p =>
      rw [hbb] at hl
      simp only [Option.map_some, beq_iff_eq, Option.some.injEq] at hl
      exact ⟨b, p.2, by rw [hbb, ← hl]⟩

/-- `PadsOk`, decided. -/
def padsOkB (af : AFunc) (l0 : Label) : Bool :=
  af.calls.all fun c => match c with
    | some ti => !ti.handlers.isEmpty && ti.handlers.all fun h => h.label != l0
    | none => true

theorem padsOk_of {af : AFunc} {l0 : Label} (h : padsOkB af l0 = true) : PadsOk af l0 := by
  intro ti hti
  have h1 := List.all_eq_true.1 h _ hti
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
    bne_iff_ne, ne_eq] at h1
  exact ⟨h1.1, h1.2⟩

/-- The entry blocks of the prepared code and of the allocation. -/
def vb0 : VBlock := vcp.blocks[0]!
def items0 : Array RItem := rf.blocks[0]!

/-- The receipt of the premises. -/
def premises : Bool :=
  (vcp.blocks[0]? == some vb0) && (rf.blocks[0]? == some items0) && handlersOkB af &&
    padsOkB af vb0.label && decide (4 * fb.words.size < 2 ^ 32) && !af.saves.isEmpty

set_option maxRecDepth 100000 in
theorem premises_true : premises = true := by native_decide

theorem premises_facts :
    vcp.blocks[0]? = some vb0 ∧ rf.blocks[0]? = some items0 ∧ HandlersOk af ∧
      PadsOk af vb0.label ∧ 4 * fb.words.size < 2 ^ 32 ∧ af.saves ≠ [] := by
  have h := premises_true
  simp only [premises, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true',
    List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, handlersOk_of h3, padsOk_of h4, h6, h7⟩

theorem compiled : lowerRFunc vcp rf = .ok af ∧ emitFunc 0 af = .ok fa ∧ fa.layout = .ok fb := by
  obtain ⟨-, -, -, ⟨-, -, -, -, -, hal, hem, hla⟩, -⟩ := facts
  exact ⟨hal, hem, hla⟩

/-- **`callSites_complete` applies** to `tc` (a `try_call` with a landing pad). -/
theorem callSites_applies : ∃ l, callSites af fa = .ok l :=
  callSites_complete compiled.2.1 premises_facts.2.2.1

/-- No alias of `tc`'s emitted code resolves to the entry block (decided). -/
theorem aliasEntry_true : aliasEntryOkB af fa = true := by native_decide

/-- **`padsNonzero_complete` applies** to `tc`. -/
theorem padsNonzero_applies : padsNonzeroB af fa = true :=
  padsNonzero_complete compiled.1 compiled.2.1 compiled.2.2 premises_facts.1 premises_facts.2.1
    premises_facts.2.2.2.1 aliasEntry_true

/-- **`unwindRows_complete` applies** to `tc` (whose prologue pushes callee-saved registers:
`af.saves ≠ []`). -/
theorem unwindRows_applies : unwindRows af fa = .ok (prologueRows ++ pushRows af.saves 8) :=
  unwindRows_complete compiled.1 compiled.2.1 compiled.2.2 premises_facts.2.2.2.2.1
    premises_facts.1 premises_facts.2.1

/-- The prepared code's `try_call` premise and the allocation's block count, decided. -/
def premisesV : Bool := tryInfoOkB vcp && (rf.blocks.size == vcp.blocks.size)

set_option maxRecDepth 100000 in
theorem premisesV_true : premisesV = true := by native_decide

/-- **`handlersOk_of_tryInfo`/`padsOk_of_tryInfo` apply** to `tc`: its prepared code meets
`TryInfoOk`, so `callSites` and `padsNonzeroB` hold of its emitted code. -/
theorem tryInfo_applies : (∃ l, callSites af fa = .ok l) ∧ padsNonzeroB af fa = true := by
  have h := premisesV_true
  simp only [premisesV, Bool.and_eq_true, beq_iff_eq] at h
  have ht := tryInfoOk_of h.1
  exact ⟨callSites_complete compiled.2.1 (handlersOk_of_tryInfo compiled.1 h.2 ht),
    padsNonzero_complete compiled.1 compiled.2.1 compiled.2.2 premises_facts.1 premises_facts.2.1
      (padsOk_of_tryInfo compiled.1 ht premises_facts.1) aliasEntry_true⟩

end Link.EhCheck.Complete.Witness
