import FV.E2E.DeadCleanupWitness
import FV.E2E.DeadCleanupSpillCheckAlloc
import FV.E2E.DeadCleanupPreparedSize
import FV.E2E.DeadCleanupStageLink

namespace E2E.DeadCleanupCompletenessWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

private def readFreeB (vc : VCode) : Bool := vc.blocks.all fun b => b.insts.all fun i =>
  match i.operands with
  | .error _ => false
  | .ok ops => ops.all fun o => o.kind != .use

private theorem readFree_spillAvail {vc : VCode} (hf : readFreeB vc = true) :
    Spill.SpillAvail vc (fun _ _ => false) := by
  constructor
  · intro ss ps hc b vb k i ops hb hi hops o ho hu
    have hinst := (array_all_iff _ _).1 ((array_all_iff _ _).1 hf b vb hb) k i hi
    simp only [hops] at hinst
    have h := (Array.all_eq_true_iff_forall_mem.mp hinst) o (Array.mem_toList_iff.mp ho)
    simp [hu] at h
  · intro ss ps hc b vb succ s sb hb hs hmem hsb v hd
    cases hd

/-- A fixed test receipt for the original raw preparation of the same source
as `DeadCleanupWitness`; it is not imported by production correctness roots. -/
private def checks : Bool :=
  match lowerFunction DeadCleanupWitness.source with
  | .error _ => false
  | .ok vc => match Backend.prepare vc with
    | .error _ => false
    | .ok raw => readFreeB raw && spillSizeOkB raw

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem checks_true : checks = true := by native_decide

/-- The same actual source run jointly satisfies baseline preparation, size,
definite assignment and the cleaned allocator checker, with real deletion. (About the production
cleanup stage's prepared code `stagePrepared`, formerly `preparedCleanup vc raw`.) -/
theorem baseline_and_cleanup_checks :
    InSubset ({ funcs := [] } : Clif.Program) DeadCleanupWitness.source ∧
    Dominated DeadCleanupWitness.source ∧ LowerScope DeadCleanupWitness.source ∧
    Spill.ArityOk DeadCleanupWitness.source ∧
    ∃ vc raw, lowerFunction DeadCleanupWitness.source = .ok vc ∧
      Backend.prepare vc = .ok raw ∧
      Spill.SpillAvail raw (fun _ _ => false) ∧ spillSizeOkB raw = true ∧
      checkAlloc (stagePrepared DeadCleanupWitness.source vc raw)
        (spillAlloc (stagePrepared DeadCleanupWitness.source vc raw)) = .ok () ∧
      spillSizeOkB (stagePrepared DeadCleanupWitness.source vc raw) = true ∧
      (prune vc).blocks[0]!.insts.size < vc.blocks[0]!.insts.size := by
  obtain ⟨hd, hs, har, vc, vcp, af, fa, fb, hcomp, hshr⟩ := DeadCleanupWitness.compiled_exists
  have hsub : InSubset ({ funcs := [] } : Clif.Program) DeadCleanupWitness.source :=
    InSubset.of_verifiable DeadCleanupWitness.input_conditions.1 (fun _ => rfl)
  have hh := checks_true
  simp only [checks, hcomp.lower] at hh
  cases hp : Backend.prepare vc with
  | error e => simp [hp] at hh
  | ok raw =>
    simp only [hp, Bool.and_eq_true] at hh
    have hav := readFree_spillAvail hh.1
    have hdom := prepDomain_of_lower hs hcomp.lower hs.nonempty
    obtain ⟨ss, ps, hc⟩ := Spill.cfg_ok_of_prepare hp hdom
    refine ⟨hsub, hd, hs, har, vc, raw, hcomp.lower, hp, hav, hh.2, ?_,
      stagePrepared_spillSizeOkB _ vc raw hc hh.2, hshr⟩
    obtain ⟨D', hav', hD0'⟩ := skipPrepared_spillAvail (f := DeadCleanupWitness.source) hdom
      (Spill.classesOkM_lower hs hcomp.lower) hp hav (fun _ => rfl)
    have hps : Backend.prepare (skipStage DeadCleanupWitness.source vc) =
        .ok (mapBlocks (skipBlock (stageMask DeadCleanupWitness.source vc)) raw) := by
      rw [prepare_skipStage, hp]; rfl
    exact spillCheckAlloc_sets_cleanup hsub har hd hs hcomp.lower (cleanupStage_prepare_ok hp)
      ⟨restrictedD (skipStage DeadCleanupWitness.source vc) D',
        preparedCleanup_spillAvail (skipStage_prepDomain _ hdom)
          (skipStage_classes _ (Spill.classesOkM_lower hs hcomp.lower)) hps D' hav',
        restrictedD_entry_empty _ D' hD0'⟩

end E2E.DeadCleanupCompletenessWitness
