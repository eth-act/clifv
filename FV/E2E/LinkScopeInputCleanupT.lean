import FV.E2E.LinkScopeInputT
import FV.E2E.DeadCleanupLinkScope
import FV.E2E.DeadCleanupTotalT

/-! # The dead-cleanup pipeline's per-function totality on the typed input scope
(S11e5 Stage C, slice 8)

`pipeCleanupT_okT`: `pipeT_okT` for the cleanup pipeline `pipeCleanupT` (`lowerFunction`,
`prepare (prune vc)`, `lowerAllocReady`, `emitFunc`, `layout`): it succeeds on every function of
`fnScopeInTB`, whatever the untrusted allocator answered, with the artifact passing the typed
lowering validator, the `prepare` validator on the pruned code, `AllocChecked` and the covered
forms. A subset-E function goes through `pipeCleanupT_ok`; any other through `Prep.prepare_okT`
and `backend_total_emit_cleanupT`, from `lowerOutTB`'s facts on `prepare`'s raw output (no new
input condition). `resultsCleanupT_ok_inT`: every function of an `InScopeInT` crate compiles
with cleanup; `resultsCleanupT_ok_input`: the integer `InScopeIn` conclusion through it.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.DeadCleanup

/-- **The cleanup pipeline succeeds on every function of the typed input scope**, whatever the
untrusted allocator answered (`o`), and its artifact passes the typed lowering validator
(`lowerCheckT`), the `prepare` validator on the code of the production cleanup stage
(`cleanupStage g a.vc`, formerly `prune a.vc`), `AllocChecked` and the covered forms. Outside
subset E the skip does not run (`skipStage`), so there the stage is `prune`. -/
theorem pipeCleanupT_okT {g : Clif.Function} (h : fnScopeInTB g = true) (k : Nat)
    (base : BitVec 64) (o : Lean.Json) :
    ∃ a, pipeCleanupT g k base o = .ok a ∧ lowerCheckT g a.vc = true ∧
      prepCheck (cleanupStage g a.vc) a.vcp = true ∧ AllocChecked a.vcp a.rf ∧
      FormsCovered ⟨a.fa.k, a.af.slotBase⟩ a.vcp := by
  by_cases hE : Compile.functionE g = true
  · have hsc := fnScopeB_of_input (fnScopeInB_of_fnScopeInTB h hE)
    obtain ⟨-, -, -, -, -, -, -, hd, hs, -⟩ := fnScope_parts hsc
    obtain ⟨a, ha, -, hpc, hca, hcov⟩ := pipeCleanupT_ok hsc spillDefinedHyp k base o
    obtain ⟨hl, -⟩ := pipeCleanupT_spec ha
    exact ⟨a, ha, lowerCheckT_complete_int (dominated_of hd) (lowerScope_of hs) hl, hpc,
      allocChecked_of_checkAlloc hca, hcov⟩
  · obtain ⟨-, -, htc, habi, hext, hind, -, -, -, -, hd, hs, har, -, -, -, -, -, hor⟩ :=
      fnScopeInT_parts h
    obtain ⟨hrc, hout⟩ := hor.resolve_left hE
    obtain ⟨vc, hl, hcs, hpost⟩ := lowerOutTB_spec hout
    have hD := dominated_of hd
    have hS := lowerScopeT_of hs
    obtain ⟨vcp, hp⟩ := Prep.prepare_okT hD hS hl
    obtain ⟨hem, hfc, -, hci⟩ := hpost vcp hp
    have hk := killFreeB_of_scopeT hd hs habi hext hind har htc hl hp
    have hcov := (formsCoveredB_iff _ _).mp hfc
    have hst : cleanupStage g vc = prune vc := by simp [cleanupStage, skipStage, hE]
    have hp' : Backend.prepare (cleanupStage g vc) = .ok (preparedCleanup vc vcp) := by
      rw [hst]; exact prune_prepare_ok hp
    obtain ⟨hacc, af, ha, fa, fb, he, hla⟩ := backend_total_emit_cleanupT hD hS (arityOk_of har)
      htc (resClassOk_of_resClassOkB hrc) hl hp (ctlSpill_of_ctlSpillB hcs) hcov hk
      (ctlInsts_of_ctlInstsB hci) hem (raAnswer (preparedCleanup vc vcp) o) k
    refine ⟨⟨k, vc, preparedCleanup vc vcp, allocResult (preparedCleanup vc vcp)
        (readyAnswer (preparedCleanup vc vcp) (raAnswer (preparedCleanup vc vcp) o)), af, fa, fb,
        base⟩, ?_, lowerCheckT_complete hD hS hl,
      Prep.prepCheck_complete hp' (cleanupStage_prepDomain g (prepDomain_ofT hD hS hl)), hacc,
      formsCovered_ctx (preparedCleanup_formsCovered hcov) _⟩
    simp [pipeCleanupT, pipeTWithLowering, Backend.Stock.D0.defaultLower_eq_legacy, hl, hp', ha,
      he, hla, bind, Except.bind, pure, Except.pure]

/-- **Every function of a crate in the typed input scope compiles with cleanup**
(`resultsT_ok_inT` for `resultsCleanupT`). -/
theorem resultsCleanupT_ok_inT {I : LinkInput} (hin : InScopeInT I = true) :
    I.resultsCleanupT.all (·.2.toBool) = true := by
  simp only [InScopeInT, Bool.and_eq_true, List.all_eq_true] at hin
  rw [List.all_eq_true]
  intro e he
  obtain ⟨fi, hfi, rfl⟩ := List.mem_map.1 he
  have hsc := hin.2 fi.func (List.mem_map_of_mem hfi)
  obtain ⟨a, ha, -⟩ := pipeCleanupT_okT hsc fi.k (BitVec.ofNat 64 (I.baseOf fi.func.name))
    (raJ fi.ra fi.j)
  simp only [ha]
  rfl

/-- **Integer corollary**: every function of an `InScopeIn` crate compiles with cleanup, through
the typed theorem (`inScopeInT_of_inScopeIn`). -/
theorem resultsCleanupT_ok_input {I : LinkInput} (hin : InScopeIn I = true) :
    I.resultsCleanupT.all (·.2.toBool) = true :=
  resultsCleanupT_ok_inT (inScopeInT_of_inScopeIn hin)

end E2E.LinkCheck
