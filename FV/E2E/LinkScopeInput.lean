import FV.E2E.LinkScopeInputDefs
import FV.E2E.LinkScope
import FV.E2E.SizeIn
import FV.Backend.Proof.IselPrgDriver
import FV.Backend.Proof.PrepareTotal

/-! # The input conditions without running the compiler (V7)

`InScopeP` (`FV/E2E/LinkScopeDefs.lean`) decides `lowersB` per function by running
`lowerFunction` and `prepare`. Here that conjunct follows from conditions on the CLIF function
alone (`fnScopeInB`, `InScopeIn`, `FV/E2E/LinkScopeInputDefs.lean`):

* `lowersB_of_input`: `lowerFunction` succeeds (`Prg.lowerFunction_ok_input`, the ISLE progress
  analysis), `prepare` succeeds on its output (`Prep.prepare_ok`), the prepared VCode meets
  `spillSizeOkB` (`spillSizeOkB_of_sizeOkB`);
* `fnScopeB_of_input`, `inScopeP_of_input`: `fnScopeInB g → fnScopeB g`,
  `InScopeIn I → InScopeP I`.

`inScopeP_of_input` is the conversion for every theorem taking `InScopeP` (the totality theorems
`compileExe_total_reach_input`, `FV/Link/ExeInputReachIn.lean` and
`FV/Link/ExeInputReachCleanupIn.lean`; `crate_correct_inScope*`). The dead-instruction cleanup
pipeline uses the same `fnScopeB`: its `prepare (prune vc)` succeeds from `prepare vc`
(`prune_prepare_ok`), so `Prep.prepare_ok` covers it.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver

/-- **`lowersB` from the input conditions**: for a function in the lowering's scope whose extends
widen, which meets the size bound and the driver's and instruction selector's conditions,
`lowerFunction` and `prepare` succeed and the prepared VCode meets `spillSizeOkB`. -/
theorem lowersB_of_input {f : Clif.Function} (hE : Compile.functionE f = true)
    (hsig : sigAbiOk f.sig = true) (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (har : Spill.arityOkB f = true) (hent : Spill.entryParamsB f = true)
    (hw : extendsWidenB f = true) (hsz : sizeOkB f = true) (hdrv : driverInB f = true)
    (hin : Prg.iselInB f = true) : lowersB f = true := by
  obtain ⟨vc, hl⟩ := Prg.lowerFunction_ok_input hE hsig hd hs har hent hw hdrv hin
  obtain ⟨vcp, hp⟩ := Prep.prepare_ok hd hs hl
  unfold lowersB
  rw [hw, hl]
  simp only [hp, Bool.true_and]
  exact spillSizeOkB_of_sizeOkB hs hsz hl hp

/-- `fnScopeInB`'s conjuncts. -/
theorem fnScopeIn_parts {g : Clif.Function} (h : fnScopeInB g = true) :
    Compile.functionE g = true ∧
    (sigAbiOk g.sig && g.externs.all (fun e => sigAbiOk e.2.sig)) = true ∧ indSigsOk g = true ∧
    decide (regLocs g.sig).Nodup = true ∧ (regLocs g.sig).all (·.isArgReg) = true ∧
    g.sig.params.all (fun p => decide (p.ty.width ≤ 64)) = true ∧ linkFreeB g = true ∧
    dominatedB g = true ∧ lowerScopeB g = true ∧ Spill.arityOkB g = true ∧
    extendsWidenB g = true ∧ sizeOkB g = true ∧ driverInB g = true ∧ Prg.iselInB g = true ∧
    Spill.entryParamsB g = true := by
  simp only [fnScopeInB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, ⟨⟨⟨h11, h12⟩, h13⟩, h14⟩⟩,
    h15⟩ := h
  exact ⟨h1, by simpa [Bool.and_eq_true] using h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15⟩

/-- **The per-function input conditions imply `fnScopeB`.** -/
theorem fnScopeB_of_input {g : Clif.Function} (h : fnScopeInB g = true) : fnScopeB g = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := fnScopeIn_parts h
  have hsig : sigAbiOk g.sig = true := by
    simp only [Bool.and_eq_true] at h2
    exact h2.1
  have hl := lowersB_of_input h1 hsig h8 h9 h10 h15 h11 h12 h13 h14
  simp only [fnScopeB, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hl, h15, Bool.and_self]

/-- **`InScopeIn` implies `InScopeP`**: every theorem taking `InScopeP I` holds under the input
conditions decided on the CLIF program alone. -/
theorem inScopeP_of_input {I : LinkInput} (h : InScopeIn I = true) : InScopeP I = true := by
  simp only [InScopeIn, Bool.and_eq_true, List.all_eq_true] at h
  simp only [InScopeP, Bool.and_eq_true, List.all_eq_true]
  exact ⟨h.1, fun g hg => fnScopeB_of_input (h.2 g hg)⟩

end E2E.LinkCheck
