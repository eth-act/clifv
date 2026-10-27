import FV.Backend.Proof.StockMemoryRecordWitness
import FV.Backend.Proof.StockMemorySelectedWitness
import FV.Backend.Proof.StockMemoryScanRefines

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

private theorem input_source_step (input : RecordInput) :
    SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (sourceFrame,heap) (afterFrame,heap) := by
  have sourceEval : instOutcome Clif.Env.empty {funcs := []} sourceFrame heap
      (.load .load .i32 flags 0 0) = .ok ([⟨.i32,2779096485⟩],heap) := rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (sourceFrame,heap) (afterFrame,heap) :=
    ⟨input.info,.load .load .i32 flags 0 0,[⟨.i32,2779096485⟩],
      sourceFrame.regs.set 2 ⟨.i32,2779096485⟩,[],input.source,input.clif,
      by rw [input.results]; rfl,sourceEval,by rw [input.results]; rfl,rfl⟩
  exact sourceStep

private theorem input_restricted_dfg (input : RecordInput) :
    DFGCons input.event.ctx (restrict sourceFrame (availOf function (availIn function input.result.ctx) 1 0)) := by
  have required := stock_lower_load_operand_coverage input.run scope dominated input.events input.records
    (bi := 1) (j := 0) (b := function.blocks[1]!) (stm := ⟨[2],.load .load .i32 flags 0 0⟩)
    rfl rfl input.current input.source input.clif input.results input.mapped input.parameter input.pointer
    input.recorded input.emitted input.selected
  have frameEq : restrict sourceFrame (availOf function (availIn function input.result.ctx) 1 0) = sourceFrame := by
    unfold restrict
    congr 1
    funext y
    by_cases zero : y = 0
    · subst y
      simp only [required.2,ite_true]
      rfl
    · simp [sourceFrame,frame,Clif.Regs.set,Clif.Regs.empty,zero]
  have dfg : DFGCons input.event.ctx (restrict sourceFrame (availOf function (availIn function input.result.ctx) 1 0)) := by
    rw [frameEq]
    exact input_dfg input
  exact dfg

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
  have sourceStep := input_source_step input
  have dfg := input_restricted_dfg input
  obtain ⟨v,ρ',w',evaluated,executed,same,memory,value,sourceHeld⟩ := stock_lower_load_source_step
    input.run scope dominated input.events input.records
    (bi := 1) (j := 0) (b := function.blocks[1]!) (stm := ⟨[2],.load .load .i32 flags 0 0⟩)
    rfl rfl input.current input.source input.clif input.results rfl input.mapped input.parameter input.pointer
    input.recorded input.emitted input.selected
    (E2E.mrStable_holds relation function)
    (memRefines_csem relation.F ⟨0,0⟩ X rfl (fun _ _ h => by cases h))
    (E2E.memRelOk_holds relation function) (fr := sourceFrame) memory_world dfg
    (input_held input _) sourceStep
  have valuesEq : [v] = [⟨.i32,2779096485⟩] := (Prod.mk.inj (Clif.Res.ok.inj (evaluated.symm.trans rfl))).1
  have valueEq := (List.cons.inj valuesEq).1
  subst v
  exact ⟨input.result,input.event,input.record,ρ',w',input.run,input.events,input.records,executed,memory,
    by simpa only [input.frontier] using value,sourceStep,sourceHeld⟩

/-- The actual indexed scan consumes an inhabited original source step and
restricted-DFG/memory guard, producing its complete post-scan guard. -/
theorem guarded_load_scan_witness (X : ExtSem) :
    ∃ (input : RecordInput) (ρ' : Nat → CV) (w' : Arm.ArmState),
      ScanFallRefines (IndexedSourceInst Clif.Env.empty {funcs := []} function input.event.ctx 1)
        (csem relation.F ⟨0,0⟩ X) input.result.final.alias
        (GuardedScanRel function input.result input.event.ctx 1 (relation.holds function)) input.record ∧
      seqRun (csem relation.F ⟨0,0⟩ X) (input.record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve input.result.final.alias (input.result.final.alias.size+1))))
        initialRegs world = some (.fall ρ' w') ∧
      GuardedScanRel function input.result input.event.ctx 1 (relation.holds function) input.record.input
        (1,afterFrame,heap) ρ' w' := by
  obtain ⟨input⟩ := record_input
  have normal := stock_lower_load_scan_fall_refines input.run scope dominated input.events input.records
    (bi := 1) (j := 0) (b := function.blocks[1]!) (stm := ⟨[2],.load .load .i32 flags 0 0⟩)
    rfl rfl input.current input.source input.clif input.results rfl input.mapped input.parameter input.pointer
    input.recorded input.emitted input.selected
    (E2E.mrStable_holds relation function)
    (memRefines_csem relation.F ⟨0,0⟩ X rfl (fun _ _ h => by cases h))
    (E2E.memRelOk_holds relation function) (env := Clif.Env.empty) (cp := {funcs := []})
  have source : IndexedSourceInst Clif.Env.empty {funcs := []} function input.event.ctx 1 input.record.inst
      (0,sourceFrame,heap) (1,afterFrame,heap) := ⟨input.current,rfl,input_source_step input⟩
  have before : GuardedScanRel function input.result input.event.ctx 1 (relation.holds function)
      input.record.output.state (0,sourceFrame,heap) initialRegs world :=
    ⟨rfl,input_restricted_dfg input,memory_world,input_held input _⟩
  obtain ⟨ρ',w',executed,post⟩ := normal _ _ source initialRegs world before
  exact ⟨input,ρ',w',normal,executed,post⟩

end Backend.Stock.Memory.LoadFixture
