import FV.E2E.DeadCleanupLinkCheck

namespace E2E.LinkCheck.LoweringPipeline
open Backend

theorem pipe_legacy (f : Clif.Function) (k : Nat) (base : BitVec 64) (o : Lean.Json) :
    pipeWithLowering lowerFunction (fun _ => id) f k base o = pipe f k base o := by
  simp only [pipe, pipeWithLowering, Backend.Stock.D0.defaultLower_eq_legacy]

theorem pipeT_legacy (f : Clif.Function) (k : Nat) (base : BitVec 64) (o : Lean.Json) :
    pipeTWithLowering lowerFunction (fun _ => id) f k base o = pipeT f k base o := by
  simp only [pipeT, pipeTWithLowering, Backend.Stock.D0.defaultLower_eq_legacy]

theorem pipeCleanup_legacy (f : Clif.Function) (k : Nat) (base : BitVec 64) (o : Lean.Json) :
    pipeWithLowering lowerFunction cleanupStage f k base o = pipeCleanup f k base o := by
  simp only [pipeCleanup, pipeWithLowering, Backend.Stock.D0.defaultLower_eq_legacy]

theorem pipeCleanupT_legacy (f : Clif.Function) (k : Nat) (base : BitVec 64) (o : Lean.Json) :
    pipeTWithLowering lowerFunction cleanupStage f k base o = pipeCleanupT f k base o := by
  simp only [pipeCleanupT, pipeTWithLowering, Backend.Stock.D0.defaultLower_eq_legacy]

/-- Pointwise equality preserves successes, errors and all artifact fields, for
arbitrary allocator answers and input settings. No successful-output test is used. -/
theorem pipeWithLowering_congr {lower other : Clif.Function → Except String VCode}
    (same : ∀ f, lower f = other f) (stage : Clif.Function → VCode → VCode)
    (f : Clif.Function) (k : Nat) (base : BitVec 64) (o : Lean.Json) :
    pipeWithLowering lower stage f k base o = pipeWithLowering other stage f k base o := by
  simp only [pipeWithLowering, same]

theorem pipeTWithLowering_congr {lower other : Clif.Function → Except String VCode}
    (same : ∀ f, lower f = other f) (stage : Clif.Function → VCode → VCode)
    (f : Clif.Function) (k : Nat) (base : BitVec 64) (o : Lean.Json) :
    pipeTWithLowering lower stage f k base o = pipeTWithLowering other stage f k base o := by
  simp only [pipeTWithLowering, same]

private def source : Clif.Function := {
  name := "consumer_compatibility"
  sig := { params := [⟨.i64, .none, .normal⟩], returns := [⟨.i64, .none, .normal⟩] }
  blocks := [{ id := 0, params := [(0, .i64)], term := .ret [0] }] }

/-- Inhabited source, all metadata and allocator answers, both cleanup modes and
both allocation modes. This witnesses compatibility, not pipeline totality. -/
theorem legacy_consumer_witness (k : Nat) (base : BitVec 64) (o : Lean.Json) :
    pipeWithLowering lowerFunction (fun _ => id) source k base o = pipe source k base o ∧
    pipeTWithLowering lowerFunction (fun _ => id) source k base o = pipeT source k base o ∧
    pipeWithLowering lowerFunction cleanupStage source k base o = pipeCleanup source k base o ∧
    pipeTWithLowering lowerFunction cleanupStage source k base o = pipeCleanupT source k base o ∧
    (∀ f, lowerFunction f = lowerFunction f) := by
  exact ⟨pipe_legacy .., pipeT_legacy .., pipeCleanup_legacy .., pipeCleanupT_legacy .., fun _ => rfl⟩

#print axioms pipe_legacy
#print axioms pipeT_legacy
#print axioms pipeCleanup_legacy
#print axioms pipeCleanupT_legacy
#print axioms pipeWithLowering_congr
#print axioms pipeTWithLowering_congr
#print axioms legacy_consumer_witness
end E2E.LinkCheck.LoweringPipeline
