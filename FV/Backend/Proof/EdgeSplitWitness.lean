import FV.Backend.Proof.EdgeSplitSound
import FV.E2E.RegLevelDriverSem

/-! Non-vacuity of the edge-split transport: real Stock code whose `brif` passes block
arguments is not legacy-compatible, actual edge splitting accepts it with one edge block per
argument-carrying edge, and the transport applies for the concrete VCode semantics. -/

namespace Backend.Proof.EdgeSplitFixture
open Backend Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- The entry branches on its parameter; each side passes a different value to a block
parameter that it returns. -/
def function : Clif.Function := {
  name := "split_edge_args"
  sig := { params := [⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i64)], body := [⟨[1],.binary .iadd .i64 0 0⟩],
      term := .brif 0 ⟨1,[1]⟩ ⟨2,[0]⟩ },
    { id := 1, params := [(2,.i64)], body := [], term := .ret [2] },
    { id := 2, params := [(3,.i64)], body := [], term := .ret [3] }] }

private def checks : Bool :=
  match Stock.lower function with
  | .error _ => false
  | .ok result =>
    !edgeLegacyCompatibleB result.code result.edgeArgs &&
    match splitEdgesChecked result.code result.edgeArgs with
    | .ok split => split.code.blocks.size == result.code.blocks.size + 2
    | .error _ => false

-- witness: native_decide (the fixed function's lowering and its edge split only)
private theorem checks_true : checks = true := by native_decide

theorem split_edges_witness (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    ∃ result split,Stock.lower function = .ok result ∧
      edgeLegacyCompatibleB result.code result.edgeArgs = false ∧
      splitEdgesChecked result.code result.edgeArgs = .ok split ∧
      split.code.blocks.size = result.code.blocks.size + 2 ∧
      ∀ (MR : MemRelTW Arm.ArmState) slots ρ w o,
        RunOkABIAt function result.code result.edgeArgs (csem F ctx X) MR slots ⟨0,0,ρ,w⟩ o →
          RunOkABI function split.code (csem F ctx X) MR slots ⟨0,0,ρ,w⟩ o := by
  have h := checks_true
  unfold checks at h
  cases run : Stock.lower function with
  | error message => rw [run] at h; cases h
  | ok result =>
    rw [run,Bool.and_eq_true] at h
    obtain ⟨incompatible,rest⟩ := h
    cases splitRun : splitEdgesChecked result.code result.edgeArgs with
    | error message => rw [splitRun] at rest; cases rest
    | ok split =>
      rw [splitRun] at rest
      refine ⟨result,split,rfl,by simpa using incompatible,splitRun,by simpa using rest,?_⟩
      intro MR slots ρ w o source
      exact RunOkABIAt.split (driverSem_csem F ctx X).toDriverSemG splitRun source

end Backend.Proof.EdgeSplitFixture
