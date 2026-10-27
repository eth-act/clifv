import FV.Backend.Proof.StockMemorySourceExecution
import FV.Backend.Proof.StockMemoryBodyFixture

namespace Backend.Stock.Memory.LoadFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def initial : Clif.State := ⟨{frame with body := [⟨[2],.load .load .i32 flags 0 0⟩]},[],heap⟩
private def final : Clif.State := ⟨{initial.frame with regs := initial.frame.regs.set 2 ⟨.i32,2779096485⟩,body := []},[],heap⟩
private theorem family : OrdinaryBody.OrdinaryInst (.load .load .i32 flags 0 0) := by
  constructor
  · intro fn args impossible; cases impossible
  · intro sig callee args impossible; cases impossible

/-- The actual executable heap load inhabits the additive ordinary source-step
theorem at its real retained source position. -/
theorem ordinary_load_step_witness :
    ∃ input : RecordInput,IndexedSourceInst Clif.Env.empty {funcs := []} function input.event.ctx input.event.block
      input.record.inst (0,initial.frame,heap) (1,final.frame,heap) := by
  obtain ⟨input⟩ := record_input
  obtain ⟨term,body,split⟩ := input.body_split
  have current : input.record.inst = blockStart function input.event.block+0 := by
    rw [input.atBlock]
    exact input.current
  exact ⟨input,OrdinaryBody.actual_ordinary_source_step input.run input.events split
    (record := input.record) (j := 0) (stm := ⟨[2],.load .load .i32 flags 0 0⟩)
    rfl current family (s := initial) (t := final) rfl rfl⟩

/-- A successful original load-and-return run supplies the complete body steps,
exact residual fuel, and unchanged source frame fields through the new variant. -/
theorem ordinary_load_body_execution_witness :
    ∃ (input : RecordInput) (t : Clif.State) (left : Nat),left+1=2 ∧
      Clif.runLoop Clif.Env.empty {funcs := []} left t = .returned [⟨.i32,2779096485⟩] heap ∧
      t.frame.body = [] ∧
      SourceSteps (IndexedSourceInst Clif.Env.empty {funcs := []} function input.event.ctx input.event.block)
        [blockStart function input.event.block] (0,initial.frame,heap) (1,t.frame,t.mem) ∧
      OrdinaryBody.SourceFrameEq initial t := by
  obtain ⟨input⟩ := record_input
  obtain ⟨term,body,split⟩ := input.body_split
  have all : ∀ stm ∈ function.blocks[1]!.body,OrdinaryBody.OrdinaryInst stm.inst := by
    intro stm member
    have equal := List.mem_singleton.mp member
    subst stm
    exact family
  obtain ⟨t,left,total,ends,empty,steps,frameEq⟩ := OrdinaryBody.actual_ordinary_source_execution_frame
    input.run input.events split all (s := initial) (fuel := 2) (j := 0) (by decide) rfl (by rfl)
  refine ⟨input,t,left,?_,ends,empty,?_,frameEq⟩
  · simpa [function] using total
  · simpa [function,List.range',initial] using steps

end Backend.Stock.Memory.LoadFixture
