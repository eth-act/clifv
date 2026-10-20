import FV.E2E.LinkScopeT
import FV.E2E.LinkOutCleanupT
import FV.E2E.LinkScope
import FV.E2E.SpillKillFree
import FV.Backend.Proof.SpillInstCheckComplete
import FV.Backend.Proof.FormsCoverComplete

/-! # The integer input conditions are typed ones (S11e5 Stage C, slice 8)

`inScopePT_of_inScopeP : InScopeP I = true → InScopePT I = true`: every per-function condition
of the typed scope (`fnScopeTB`) holds on subset-E input, from the integer chain's facts:

* the typed movement scope and checks: `functionET_of_functionE`, `storeTypedB_of_functionE`,
  `tryArgClassOk_of_functionE`, `lowerScopeTB_of_lowerScopeB`;
* `resClassOkB`: the integer `resClassOk_of_lowerScope` and the decider's completeness
  (`resClassOkB_of`);
* the typed spill chain's run-time deciders on the lowering and its prepared code (`lowersTB`):
  `ctlSpillB` from the integer control forms' `ctlSpillHyp` (`Spill.ctlSpillB_of`),
  `formsCoveredB default` from `formsCovered_complete`, `killFreeB` from `spillKillFree`.

`outOkT_of_inScopeP : InScopeP I → linkerOkB I → OutOkT I`: the output checks of the typed link
hold on the compiler's results of integer input (the integer chain's own-output facts,
`chks_resultsT`; a subset-E function returns integers).
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver

/-- **Completeness of `resClassOkB`.** -/
theorem resClassOkB_of {f : Clif.Function} (h : Spill.ResClassOk f) : Spill.resClassOkB f = true := by
  unfold Spill.resClassOkB
  split
  · rename_i ctx ranges st0 hb
    split
    · rename_i bl hl
      refine List.all_eq_true.mpr fun BL hBL => List.all_eq_true.mpr fun ss hss =>
        List.all_eq_true.mpr fun rr hrr => ?_
      obtain ⟨bi, hbi⟩ := List.mem_iff_getElem?.mp hBL
      rw [List.getElem?_zip_eq_some] at hbi
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hss
      rw [List.getElem?_zip_eq_some] at hj
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hrr
      rw [List.getElem?_zip_eq_some] at hk
      obtain ⟨r, rs⟩ := rr
      dsimp only
      split
      · rename_i o c
        exact beq_iff_eq.mpr (h ctx ranges st0 bl hb hl bi BL.1 BL.2 j ss.1 ss.2 hbi.1 hbi.2 hj.1 hj.2
          k r o c hk.1 hk.2)
      · rfl
    · rfl
  · rfl

/-- **`lowersTB` on integer input**: `lowersB` and the integer chain's facts give the typed spill
chain's run-time deciders. -/
theorem lowersTB_of_fnScope {g : Clif.Function} (h : fnScopeB g = true) : lowersTB g = true := by
  obtain ⟨-, -, -, -, -, -, -, hd, hs, har, hlw, -⟩ := fnScope_parts h
  obtain ⟨hw, vc, vcp, hl, hp, hsz⟩ := lowersB_spec hlw
  have hsub := inSubset_of_fnScope h { funcs := [] }
  have hS := lowerScope_of hs
  have hD := dominated_of hd
  have hctl : Spill.ctlSpillB vc = true := Spill.ctlSpillB_of (ctlSpillHyp hsub hD hS hl)
  have hcov : formsCoveredB default vcp = true :=
    (formsCoveredB_iff _ _).2 (formsCovered_complete hS hl hp _)
  have hk : Spill.killFreeB vcp = true :=
    spillKillFree _ g vc vcp hsub (Spill.arityOk_of har) hD hS hl hp
  unfold lowersTB
  rw [hl]
  simp only [hp, hw, hsz, hctl, hcov, hk, Bool.and_self]

/-- **The typed per-function conditions on integer input.** -/
theorem fnScopeTB_of_fnScopeB {g : Clif.Function} (h : fnScopeB g = true) : fnScopeTB g = true := by
  have hlo := lowersTB_of_fnScope h
  obtain ⟨hE, habi, hind, hnd, harg, hw, hfree, hd, hs, har, -, hen⟩ := fnScope_parts h
  have hrc : Spill.resClassOkB g = true :=
    resClassOkB_of (Spill.resClassOk_of_lowerScope (lowerScope_of hs))
  unfold fnScopeTB
  simp only [Compile.functionET_of_functionE hE, Compile.storeTypedB_of_functionE hE,
    Compile.tryArgClassOk_of_functionE hE, habi.1, List.all_eq_true.mpr fun e he => habi.2 e he,
    hind, decide_eq_true hnd, List.all_eq_true.mpr harg,
    List.all_eq_true.mpr fun p hp => decide_eq_true (hw p hp), hfree, hd,
    lowerScopeTB_of_lowerScopeB hs, har, hrc, hlo, hen, Bool.and_self]

/-- **Integer specialization of the typed input scope**: `InScopeP` implies `InScopePT`. -/
theorem inScopePT_of_inScopeP {I : LinkInput} (h : InScopeP I = true) : InScopePT I = true := by
  simp only [InScopeP, InScopePT, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨h.1, fun g hg => fnScopeTB_of_fnScopeB (h.2 g hg)⟩

/-- The returns of a subset-E function are integers. -/
theorem returns_isInt_of_functionE {g : Clif.Function} (hE : Compile.functionE g = true) :
    ∀ p ∈ g.sig.returns, p.ty.isInt = true := by
  intro q hq
  simp only [Compile.functionE, Compile.sigE, Bool.and_eq_true, List.all_eq_true] at hE
  have := hE.1.1.1.2 q hq
  simp only [Compile.tyE, Bool.and_eq_true] at this
  exact this.1

/-- **Integer specialization of the output checks**: `OutOkT` holds on the compiler's results of
an integer in-scope input whose link the linker's facts describe. -/
theorem outOkT_of_inScopeP {I : LinkInput} (hin : InScopeP I = true) (hlk : linkerOkB I = true) :
    OutOkT I = true := by
  unfold OutOkT outOkTR
  refine List.all_eq_true.2 fun e he => ?_
  have key := List.all_eq_true.1 (chks_resultsT spillDefinedHyp hin hlk he)
  obtain ⟨fi, hfi, h1, -⟩ := mem_resultsT he
  have hsc : fnScopeB e.1 = true := by
    simp only [InScopeP, Bool.and_eq_true, List.all_eq_true] at hin
    rw [h1]; exact hin.2 _ (List.mem_map_of_mem hfi)
  have hE := (fnScope_parts hsc).1
  rw [List.all_eq_true]
  intro c hc
  simp only [outChksT, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact key _ (by simp [chks, staticChks])
  · exact key _ (by simp [chks, staticChks])
  · exact key _ (by simp [chks, staticChks])
  · exact key _ (by simp [chks, staticChks])
  · exact key _ (by simp [chks, linkChks, LinkInput.withDepth])
  · exact key _ (by simp [chks, linkChks, LinkInput.withDepth])
  · simp [hE]
  · simp only [calleeIntChk, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true]
    exact .inr (returns_isInt_of_functionE hE)

/-- **Integer specialization of the cleanup output checks**: `OutOkTCleanup` holds on the cleanup
results of an integer in-scope input whose link the linker's facts describe. -/
theorem outOkTCleanup_of_inScopeP {I : LinkInput} (hin : InScopeP I = true)
    (hlk : linkerOkR I I.resultsCleanupT = true) : OutOkTCleanup I = true := by
  unfold OutOkTCleanup outOkTR
  refine List.all_eq_true.2 fun e he => ?_
  have key := List.all_eq_true.1 (chks_resultsCleanupT spillDefinedHyp hin hlk he)
  obtain ⟨fi, hfi, h1, -⟩ := mem_resultsCleanupT he
  have hsc : fnScopeB e.1 = true := by
    simp only [InScopeP, Bool.and_eq_true, List.all_eq_true] at hin
    rw [h1]; exact hin.2 _ (List.mem_map_of_mem hfi)
  have hE := (fnScope_parts hsc).1
  rw [List.all_eq_true]
  intro c hc
  simp only [outChksT, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact key _ (by simp [chksWith, staticChksWith])
  · exact key _ (by simp [chksWith, staticChksWith])
  · exact key _ (by simp [chksWith, staticChksWith])
  · exact key _ (by simp [chksWith, staticChksWith])
  · exact key _ (by simp [chksWith, linkChks, LinkInput.withDepth])
  · exact key _ (by simp [chksWith, linkChks, LinkInput.withDepth])
  · simp [hE]
  · simp only [calleeIntChk, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true]
    exact .inr (returns_isInt_of_functionE hE)

end E2E.LinkCheck
