import FV.E2E.DeadCleanupFinal
import FV.E2E.LowerDirect
import FV.Backend.Proof.SpillEdges
import FV.E2E.DeadCleanupCover
import FV.E2E.SizeDefs
import FV.Backend.Proof.IselEmitDefs

namespace E2E.DeadCleanupWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- A real source function with an unused selected constant and a return. -/
def source : Clif.Function :=
  { name := "cleanup_witness", sig := {}, blocks :=
      [{ id := 0, body := [{ results := [0], inst := .iconst .i64 17#64 }], term := .ret [] }] }

/-- Closed compilation through cleanup, allocation, emission and layout. -/
def checks : Bool :=
  dominatedB source && lowerScopeB source && Spill.arityOkB source &&
  (Backend.verifiable source && extendsWidenB source && sizeOkB source) &&
  match lowerFunction source with
  | .error _ => false
  | .ok vc =>
    lowerCheck source vc && decide ((prune vc).blocks[0]!.insts.size < vc.blocks[0]!.insts.size) &&
    match Backend.prepare (prune vc) with
    | .error _ => false
    | .ok vcp =>
      prepCheck (prune vc) vcp && (checkAlloc vcp (spillAlloc vcp)).isOk &&
      match lowerRFunc vcp (spillAlloc vcp) with
      | .error _ => false
      | .ok af => match emitFunc 0 af with
        | .error _ => false
        | .ok fa => fa.layout.isOk

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The compiler path is inhabited and really removes a selected instruction,
using the baseline fixed-witness convention (`lowerWitness_checks`).
This closed test receipt is not used by any compiler correctness theorem. -/
theorem checks_true : checks = true := by native_decide

/-- All source and pipeline premises are jointly inhabited by a compiler run
that removes an instruction and produces laid-out machine code. -/
theorem compiled_exists :
    Dominated source ∧ LowerScope source ∧ Spill.ArityOk source ∧
    ∃ vc vcp af fa fb,
      CompiledCleanup source 0 vc vcp (spillAlloc vcp) af fa fb ∧
      (prune vc).blocks[0]!.insts.size < vc.blocks[0]!.insts.size := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hd, hs⟩, har⟩, _⟩, h⟩ := h
  refine ⟨dominated_of hd, lowerScope_of hs, Spill.arityOk_of har, ?_⟩
  cases hl : lowerFunction source with
  | error e => rw [hl] at h; cases h
  | ok vc =>
    rw [hl] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hlo, hshr⟩, h⟩ := h
    cases hp : Backend.prepare (prune vc) with
    | error e => rw [hp] at h; cases h
    | ok vcp =>
      rw [hp] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hpr, hck⟩, h⟩ := h
      have hc : checkAlloc vcp (spillAlloc vcp) = .ok () := by
        cases he : checkAlloc vcp (spillAlloc vcp) with
        | error e => rw [he] at hck; cases hck
        | ok u => cases u; rfl
      cases ha : lowerRFunc vcp (spillAlloc vcp) with
      | error e => rw [ha] at h; cases h
      | ok af =>
        rw [ha] at h
        simp only at h
        cases he : emitFunc 0 af with
        | error e => rw [he] at h; cases h
        | ok fa =>
          rw [he] at h
          simp only at h
          cases hb : fa.layout with
          | error e => rw [hb] at h; cases h
          | ok fb =>
            exact ⟨vc, vcp, af, fa, fb, ⟨hl, hlo, hp, hpr, hc, ha, he, hb⟩, hshr⟩

/-- The source subset, widening and size premises are satisfied by the very same
closed compilation witness, jointly with dominance, scope and arity. -/
theorem input_conditions : Backend.verifiable source = true ∧
    extendsWidenB source = true ∧ sizeOkB source = true := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true] at h
  exact ⟨h.1.2.1.1, h.1.2.1.2, h.1.2.2⟩

/-- The closed compiler receipt also supplies form coverage for the prepared
code, with arbitrary slot and local-label parameters as in the final theorem. -/
theorem compiled_covered_exists :
    InSubset ({ funcs := [] } : Clif.Program) source ∧
    ∃ vc vcp af fa fb, CompiledCleanup source 0 vc vcp (spillAlloc vcp) af fa fb ∧
      (∀ ctx, FormsCovered ctx vcp) ∧
      (prune vc).blocks[0]!.insts.size < vc.blocks[0]!.insts.size := by
  obtain ⟨_, hs, _, vc, vcp, af, fa, fb, hc, hshr⟩ := compiled_exists
  refine ⟨InSubset.of_verifiable input_conditions.1 (fun _ => rfl),
    vc, vcp, af, fa, fb, hc, ?_, hshr⟩
  intro ctx
  exact formsCovered_cleanup_complete hs hc.lower hc.prepare ctx

end E2E.DeadCleanupWitness
