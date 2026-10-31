import FV.Backend.Proof.StockMemoryHelperProjection
import FV.Backend.Proof.StockMemoryHelperContracts
import FV.Backend.Proof.StockMemorySelection

/-! Draft positive witness for the next memory batch. -/
namespace Backend.Stock.Proof.MemoryHelpers
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

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

private def loadWitnessOk (kind : IntegerLoad) : Bool :=
  match (applyTerm program (Stock.sem sinkCtx) {} 100 27 kind.term
      [address,.op (.memFlags flags)]).run (sinkState,#[]) with
  | .ok (some _,_,_) => true
  | _ => false

private theorem loads_succeed (kind : IntegerLoad) : loadWitnessOk kind = true := by
  cases kind <;> decide +kernel

/-- Every load variant has an actual execution with its complete contract. -/
theorem integer_loads_complete_witness (kind : IntegerLoad) :
    ∃ out next trace instruction,
      ApplyInternal program (Stock.sem sinkCtx) {} 99 27 kind.term
        [address,.op (.memFlags flags)] (sinkState,#[]) out (next,trace) ∧
      MInst.ofV (.data 58 kind.tag
        [.reg (sinkState.base.fresh .int).1,address,.op (.memFlags flags)]) =
          some instruction ∧
      out = .reg (sinkState.base.fresh .int).1 ∧
      next = {sinkState with base := (sinkState.base.fresh .int).2.emit instruction} := by
  have checked := loads_succeed kind
  unfold loadWitnessOk at checked
  cases actual : (applyTerm program (Stock.sem sinkCtx) {} 100 27 kind.term
      [address,.op (.memFlags flags)]).run (sinkState,#[]) with
  | error error => rw [actual] at checked; cases checked
  | ok result =>
    obtain ⟨out,next,trace⟩ := result
    rw [actual] at checked
    cases out with
    | none => cases checked
    | some out =>
      have run : ApplyInternal program (Stock.sem sinkCtx) {} 99 27 kind.term
          [address,.op (.memFlags flags)] (sinkState,#[]) out (next,trace) := actual
      obtain ⟨instruction,decoded,value,frame⟩ :=
        integer_load_contract kind sinkCtx rfl (by decide) run
      exact ⟨out,next,trace,instruction,run,decoded,value,frame⟩

private def storeWitnessOk (kind : IntegerStore) : Bool :=
  match (applyTerm program (Stock.sem sinkCtx) {} 100 46 kind.term
      [address,.op (.memFlags flags),.reg (.vreg 193 .int)]).run (sinkState,#[]) with
  | .ok (some _,_,_) => true
  | _ => false

private theorem stores_succeed (kind : IntegerStore) : storeWitnessOk kind = true := by
  cases kind <;> decide +kernel

/-- Every store variant has an actual side-effect payload and unchanged state. -/
theorem integer_stores_complete_witness (kind : IntegerStore) :
    ∃ out next trace,
      ApplyInternal program (Stock.sem sinkCtx) {} 99 46 kind.term
        [address,.op (.memFlags flags),.reg (.vreg 193 .int)]
        (sinkState,#[]) out (next,trace) ∧
      out = .data 46 0 [.data 58 kind.tag
        [.reg (.vreg 193 .int),address,.op (.memFlags flags)]] ∧ next = sinkState := by
  have checked := stores_succeed kind
  unfold storeWitnessOk at checked
  cases actual : (applyTerm program (Stock.sem sinkCtx) {} 100 46 kind.term
      [address,.op (.memFlags flags),.reg (.vreg 193 .int)]).run (sinkState,#[]) with
  | error error => rw [actual] at checked; cases checked
  | ok result =>
    obtain ⟨out,next,trace⟩ := result
    rw [actual] at checked
    cases out with
    | none => cases checked
    | some out =>
      have run : ApplyInternal program (Stock.sem sinkCtx) {} 99 46 kind.term
          [address,.op (.memFlags flags),.reg (.vreg 193 .int)]
          (sinkState,#[]) out (next,trace) := actual
      exact ⟨out,next,trace,run,integer_store_contract kind sinkCtx rfl (by decide) run⟩

end Backend.Stock.Proof.MemoryHelpers
