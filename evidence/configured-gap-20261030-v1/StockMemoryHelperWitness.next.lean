import FV.Backend.Proof.StockMemoryHelperProjection
import FV.Backend.Proof.StockMemorySelection

/-! Draft positive witness for the next memory batch. -/
namespace Backend.Stock.Proof.MemoryHelpers
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000

private def address : V :=
  .data 89 VIdx.AMode.UnsignedOffset [.reg (.vreg 192 .int),.op (.uimm12Scaled 0)]
private def flags : Clif.MemFlags := {trapCode := none}

/-- An actual helper succeeds, emits the load, and retains every scheduling field. -/
theorem integer_helpers_complete_witness :
    ∃ next trace,
      (applyTerm program (Stock.sem sinkCtx) {} 100 27 533
        [address,.op (.memFlags flags)]).run (sinkState,#[]) =
          .ok (some (.reg (sinkState.base.fresh .int).1),next,trace) ∧
      next = {sinkState with base := next.base} ∧
      projectResult State.base ((applyTerm program (Stock.sem sinkCtx) {} 100 27 533
        [address,.op (.memFlags flags)]).run (sinkState,#[])) =
        (applyTerm program (Backend.sem sinkCtx) {} 100 27 533
          [address,.op (.memFlags flags)]).run (sinkState.base,#[]) := by
  have actual := Memory.stock_uload32_helper data_program sinkCtx (cfg := {}) rfl
    sinkState #[] 80 address (.op (.memFlags flags))
    (.load .uload32 (sinkState.base.fresh .int).1 (.unsignedOffset (.vreg 192 .int) 0) flags) rfl
  have projected := integer_helpers_project_and_preserve sinkCtx {} rfl 100 27 533
    (by decide) [address,.op (.memFlags flags)] sinkState #[]
  exact ⟨_,_,actual,projected.2 _ _ _ actual,projected.1⟩

end Backend.Stock.Proof.MemoryHelpers
