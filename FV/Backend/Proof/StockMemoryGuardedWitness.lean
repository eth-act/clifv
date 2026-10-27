import FV.Backend.Proof.StockMemoryRecordWitness

namespace Backend.Stock.Memory.LoadFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def sourceFrame : Clif.Frame :=
  {frame with body := [⟨[2],.load .load .i32 flags 0 0⟩]}
private def initialRegs (_ : Nat) : CV := ofX 4096
private def afterFrame : Clif.Frame :=
  {sourceFrame with regs := sourceFrame.regs.set 2 ⟨.i32,2779096485⟩,body := []}

private theorem input_dfg (input : RecordInput) : DFGCons input.event.ctx sourceFrame := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases zero : x = 0
    · subst x
      rw [input.parameter] at defined
      cases defined
    · simp [sourceFrame,frame,Clif.Regs.set,Clif.Regs.empty,zero] at lookup
  · intro x t v typed lookup
    by_cases zero : x = 0
    · subst x
      have pointer := (stock_lower_record_context input.run scope input.events).1.addr64
        _ _ _ 0 input.source input.clif rfl
      have equal := Option.some.inj (pointer.symm.trans typed)
      subst t
      cases lookup
      rfl
    · simp [sourceFrame,frame,Clif.Regs.set,Clif.Regs.empty,zero] at lookup

private theorem input_held (input : RecordInput) (needed : Nat → Prop) :
    ValuesHeld needed input.event.ctx sourceFrame (fun k => initialRegs (aliasNum input.result.final.alias k)) := by
  intro y required val lookup
  by_cases zero : y = 0
  · subst y
    have equal : val = ⟨.i64,4096⟩ := Option.some.inj lookup.symm
    subst val
    exact ⟨192,input.pointer,rfl⟩
  · simp [sourceFrame,frame,Clif.Regs.set,Clif.Regs.empty,zero] at lookup

/-- Actual retained load code reads the live nonzero heap, installs its final
result and transfers guarded availability to the real original source-step frame. -/
theorem guarded_load_source_witness (X : ExtSem) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (ρ' : Nat → CV) (w' : Arm.ArmState),
      Stock.lower function = .ok result ∧ event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      seqRun (csem relation.F ⟨0,0⟩ X) (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        initialRegs world = some (.fall ρ' w') ∧
      relation.holds function sourceFrame.slots heap w' ∧ VHolds ⟨.i32,2779096485⟩ (ρ' 194) ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst (sourceFrame,heap) (afterFrame,heap) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf function (availIn function result.ctx) 1 1) event.ctx afterFrame
        (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨input⟩ := record_input
  have operands : ValueHeld input.event.ctx sourceFrame
      (fun k => initialRegs (aliasNum input.result.final.alias k)) 0 :=
    input_held input (fun _ => True) 0 trivial
  obtain ⟨ρ',w',executed,same,memory,value,installed⟩ := stock_lower_parameter_load_values
    input.run scope dominated input.events input.records
    (bi := 1) (j := 0) (b := function.blocks[1]!) (stm := ⟨[2],.load .load .i32 flags 0 0⟩)
    rfl rfl input.current input.source input.clif input.results rfl input.mapped input.parameter input.pointer
    input.recorded input.emitted (n := 0) input.evalRun input.rootRun
    (E2E.mrStable_holds relation function)
    (memRefines_csem relation.F ⟨0,0⟩ X rfl (fun _ _ h => by cases h))
    (E2E.memRelOk_holds relation function) (fr := sourceFrame) memory_world (input_dfg input)
    operands (input_held input _) (by decide) (show Clif.evalInst sourceFrame heap
      (.load .load .i32 flags 0 0) = .ok ([⟨.i32,2779096485⟩],heap) from rfl)
  have sourceEval : instOutcome Clif.Env.empty {funcs := []} sourceFrame heap
      (.load .load .i32 flags 0 0) = .ok ([⟨.i32,2779096485⟩],heap) := rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (sourceFrame,heap) (afterFrame,heap) :=
    ⟨input.info,.load .load .i32 flags 0 0,[⟨.i32,2779096485⟩],
      sourceFrame.regs.set 2 ⟨.i32,2779096485⟩,[],input.source,input.clif,
      by rw [input.results]; rfl,sourceEval,by rw [input.results]; rfl,rfl⟩
  have sourceHeld := source_single_result_values input.source input.clif input.results sourceStep sourceEval installed
  exact ⟨input.result,input.event,input.record,ρ',w',input.run,input.events,input.records,executed,memory,
    by simpa only [input.frontier] using value,sourceStep,sourceHeld⟩

end Backend.Stock.Memory.LoadFixture
