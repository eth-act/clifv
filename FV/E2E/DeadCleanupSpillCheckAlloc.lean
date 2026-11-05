import FV.E2E.SpillCheckAlloc
import FV.E2E.DeadCleanupAlloc
import FV.Backend.Proof.DeadCleanupPreparedAvailability
import FV.Backend.Proof.CleanupStageAvail

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- (`hp` is about the production cleanup stage `cleanupStage f vc`, formerly `prune vc`.) -/
theorem spillCheckAlloc_sets_cleanup {p : Clif.Program} {f : Clif.Function}
    {vc vcp : VCode} (hsub : InSubset p f) (har : Spill.ArityOk f) (hd : Dominated f)
    (hs : LowerScope f) (hl : lowerFunction f = .ok vc) (hp : Backend.prepare (cleanupStage f vc) = .ok vcp)
    (hDs : ∃ D, Spill.SpillAvail vcp D ∧ ∀ v, D 0 v = false) :
    checkAlloc vcp (spillAlloc vcp) = .ok () := by
  obtain ⟨D, hav, hD0⟩ := hDs
  have hloc := spillLocal_cleanup hsub har hd hs hl hp
  have hdom := cleanupStage_prepDomain f (prepDomain_of_lower hs hl hs.nonempty)
  obtain ⟨succs, preds, hcfg⟩ := Spill.cfg_ok_of_prepare hp hdom
  have hE := hloc.2.2 succs preds hcfg
  have hN : Spill.stN vcp = 128 + 2 * (spillAlloc vcp).spillSlots := by
    unfold Spill.stN; rw [Spill.spillAlloc_slots]
  have hctx : Spill.spillCtx vcp succs = ⟨vcp, succs, spillAlloc vcp, 128 + 2 * (spillAlloc vcp).spillSlots⟩ := by
    unfold Spill.spillCtx; rw [hN]
  have hpos : 0 < vcp.blocks.size := Nat.pos_of_ne_zero hE.entry.1
  refine CheckComplete.checkAlloc_complete (W := Spill.insOf vcp succs preds D) hcfg
    (Spill.spillAlloc_size vcp) hE.entry.2.1 hE.entry.2.2
    (by rw [Spill.spillAlloc_saved]; exact fun r h => h) ?_ (prepare_reach hp hdom hcfg)
    ⟨rfl, hE.entry.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- every instruction has an operand view
    intro vb hvb i hi
    obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hvb
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
    rw [Array.getElem?_toList] at hb hk
    obtain ⟨ops, hops, -⟩ := hloc.1 b vb k i hb hk
    exact ⟨ops, hops⟩
  · -- successors are blocks
    intro b s hs'
    obtain ⟨hb, _, _, _, -, -, hlab⟩ := Prep.succ_of (Prep.cfg_spec hcfg) hs'
    exact ⟨hb, (Prep.lab_some hlab).1⟩
  · -- operand vregs have a class
    intro b vb hvb i hi ops hops o ho
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
    rw [Array.getElem?_toList] at hk
    exact (Array.getElem?_eq_some_iff.mp (hloc.2.1.1 b vb k i ops hvb hk hops o ho)).1
  · -- parameters have a class
    intro s sb hsb r hr n hn
    obtain ⟨m, cl, rfl, hm⟩ := hloc.2.1.2 s sb hsb r (List.mem_append_left _ hr)
    have : m = n := Except.ok.inj hn
    subst this
    exact (Array.getElem?_eq_some_iff.mp hm).1
  · -- the witness in-states
    intro b hb
    exact ⟨_, Spill.insOf_get hb, by unfold Spill.inState; rw [Spill.size_mkState, hN]⟩
  · intro b hb
    have := Spill.verify_block hcfg hloc hav hb
    rwa [hctx] at this
  · -- the entry in-state holds no vreg: below `entryState`
    refine ⟨_, Spill.insOf_get hpos, Spill.le_of_mem fun l s hm => ?_⟩
    obtain ⟨hm, i, hi, hlt⟩ := Spill.mem_get_mkState hm
    cases l with
    | reg r =>
      rcases Spill.inReg_mem hm with ⟨-, hr, rfl⟩ | ⟨y, hy, -⟩
      · exact entry_mem_entryState hr hi (by rw [← hN]; exact hlt)
      · rw [Spill.entryPairs_nil hE.entry.2.1] at hy; cases hy
    | save r => exact absurd (Spill.inSave_mem hm).1 (by simp)
    | stack n cl =>
      obtain ⟨v, -, -, -, hv⟩ := Spill.inStack_mem hm
      rw [hD0 v] at hv
      cases hv

/-- The old definite-assignment hypothesis supplies an empty-entry witness for
cleanup, rather than introducing a new hypothesis about the cleaned pipeline. (About the
production cleanup stage's prepared code `stagePrepared f vc vcp`, formerly
`preparedCleanup vc vcp`: the compiler now runs Cranelift's skip first.) -/
theorem spillDefined_cleanup (hD : SpillDefinedHyp) {p : Clif.Program} {f : Clif.Function}
    {vc vcp : VCode} (hsub : InSubset p f) (har : Spill.ArityOk f) (hd : Dominated f)
    (hs : LowerScope f) (hen : Spill.entryParamsB f = true) (hl : lowerFunction f = .ok vc)
    (hp : Backend.prepare vc = .ok vcp) :
    ∃ D, Spill.SpillAvail (stagePrepared f vc vcp) D ∧ ∀ v, D 0 v = false := by
  obtain ⟨D, hav, hD0⟩ := hD p f vc vcp hsub har hd hs hen hl hp
  have hdom := prepDomain_of_lower hs hl hs.nonempty
  obtain ⟨D', hav', hD0'⟩ :=
    skipPrepared_spillAvail (f := f) hdom (Spill.classesOkM_lower hs hl) hp hav hD0
  have hps : Backend.prepare (skipStage f vc) = .ok (mapBlocks (skipBlock (stageMask f vc)) vcp) := by
    rw [prepare_skipStage, hp]; rfl
  exact ⟨restrictedD (skipStage f vc) D',
    preparedCleanup_spillAvail (skipStage_prepDomain f hdom)
      (skipStage_classes f (Spill.classesOkM_lower hs hl)) hps D' hav',
    restrictedD_entry_empty (skipStage f vc) D' hD0'⟩

/-- Checker acceptance after cleanup under exactly the old definite-assignment
hypothesis and raw successful preparation. (About `stagePrepared f vc vcp`, the production
cleanup stage's prepared code, formerly `preparedCleanup vc vcp`.) -/
theorem spillCheckAlloc_cleanup (hD : SpillDefinedHyp) {p : Clif.Program} {f : Clif.Function}
    {vc vcp : VCode} (hsub : InSubset p f) (har : Spill.ArityOk f) (hd : Dominated f)
    (hs : LowerScope f) (hen : Spill.entryParamsB f = true) (hl : lowerFunction f = .ok vc)
    (hp : Backend.prepare vc = .ok vcp) :
    checkAlloc (stagePrepared f vc vcp) (spillAlloc (stagePrepared f vc vcp)) = .ok () :=
  spillCheckAlloc_sets_cleanup hsub har hd hs hl (cleanupStage_prepare_ok hp)
    (spillDefined_cleanup hD hsub har hd hs hen hl hp)

end E2E
