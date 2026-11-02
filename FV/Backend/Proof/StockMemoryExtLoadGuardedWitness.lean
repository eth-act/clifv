import FV.Backend.Proof.StockMemoryExtLoadRecordFixture
import FV.Backend.Proof.StockMemoryExtLoadSourceValues
import FV.Backend.Proof.StockMemoryExtLoadPairedRecord
import FV.E2E.Main
import FV.E2E.Guarded

namespace Backend.Stock.Memory.ExtendedRoots.Fixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def payload : Kind → Nat
  | .unsigned8 => 165 | .signed8 => 2^64-91
  | .unsigned16 => 42405 | .signed16 => 2^64-23131
  | .unsigned32 => 2779096485 | .signed32 => 2^64-1515870811
private def value (kind : Kind) : Clif.Val := Clif.Val.ofNat .i64 (payload kind)
private def sourceFrame (kind : Kind) : Clif.Frame := {
  func := function kind
  regs := Clif.Regs.empty.set 0 ⟨.i64,4096⟩
  slots := []
  body := [⟨[2],.load kind.sourceOp .i64 flags 0 0⟩]
  term := .ret [2] }
private def afterFrame (kind : Kind) : Clif.Frame :=
  {sourceFrame kind with regs := (sourceFrame kind).regs.set 2 (value kind),body := []}
private def initialRegs (_ : Nat) : CV := ofX 4096
private def heap : Clif.Mem := {allocs := [⟨4096,8,false⟩],bytes := fun _ => some 165}
private def world : Arm.ArmState := {Arm.ArmState.default with mem := fun _ => 165}
private def otherWorld : Arm.ArmState := Arm.write_base_gpr 10#5 17 world
private def relation : E2E.Rel := ⟨fun _ => False,fun _ => none,0,0⟩

private theorem source_eval (kind : Kind) :
    Clif.evalInst (sourceFrame kind) heap (.load kind.sourceOp .i64 flags 0 0) =
      .ok ([value kind],heap) := by
  cases kind <;> rfl

private theorem memory_world (kind : Kind) :
    relation.holds (function kind) (sourceFrame kind).slots heap world := by
  refine ⟨⟨?_,?_,rfl⟩,?_,outRel_zero _ _ _⟩
  · intro a b valid byte
    have equal : (165 : BitVec 8) = b := Option.some.inj byte
    subst b
    rfl
  · intro a n valid
    have bound : 4096 ≤ a ∧ a+n ≤ 4104 := by
      simpa [heap,Clif.Mem.valid,Clif.Alloc.contains] using valid
    exact ⟨by omega,fun _ _ h => h⟩
  · intro id b present
    cases present

private theorem other_memory (kind : Kind) :
    relation.holds (function kind) (sourceFrame kind).slots heap otherWorld := by
  refine ⟨⟨?_,(memory_world kind).1.valid,rfl⟩,?_,outRel_zero _ _ _⟩
  · intro a b valid byte
    exact (memory_world kind).1.bytes a b valid byte
  · intro id b present
    cases present

private theorem input_dfg {kind : Kind} (input : RecordInput kind) :
    DFGCons input.event.ctx (sourceFrame kind) := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases zero : x = 0
    · subst x
      rw [input.parameter] at defined
      cases defined
    · simp [sourceFrame,Clif.Regs.set,Clif.Regs.empty,zero] at lookup
  · intro x t v typed lookup
    by_cases zero : x = 0
    · subst x
      have pointer := (stock_lower_record_context input.run (scope kind) input.events).1.addr64
        _ _ _ 0 input.source input.clif rfl
      have equal := Option.some.inj (pointer.symm.trans typed)
      subst t
      cases lookup
      rfl
    · simp [sourceFrame,Clif.Regs.set,Clif.Regs.empty,zero] at lookup

private theorem input_held {kind : Kind} (input : RecordInput kind) (needed : Nat → Prop) :
    ValuesHeld needed input.event.ctx (sourceFrame kind)
      (fun k => initialRegs (aliasNum input.result.final.alias k)) := by
  intro y required val lookup
  by_cases zero : y = 0
  · subst y
    have equal : val = ⟨.i64,4096⟩ := Option.some.inj lookup.symm
    subst val
    exact ⟨192,input.pointer,rfl⟩
  · simp [sourceFrame,Clif.Regs.set,Clif.Regs.empty,zero] at lookup

private theorem input_source_step {kind : Kind} (input : RecordInput kind) :
    SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (sourceFrame kind,heap) (afterFrame kind,heap) := by
  have outcome : instOutcome Clif.Env.empty {funcs := []} (sourceFrame kind) heap
      (.load kind.sourceOp .i64 flags 0 0) = .ok ([value kind],heap) := by
    simpa only [instOutcome] using source_eval kind
  exact ⟨input.info,.load kind.sourceOp .i64 flags 0 0,[value kind],
    (sourceFrame kind).regs.set 2 (value kind),[],input.source,input.clif,
    by rw [input.results]; rfl,outcome,by rw [input.results]; rfl,rfl⟩

private theorem input_restricted_dfg {kind : Kind} (input : RecordInput kind) :
    DFGCons input.event.ctx (restrict (sourceFrame kind)
      (availOf (function kind) (availIn (function kind) input.result.ctx) 0 0)) := by
  have required := stock_lower_extending_load_operand_coverage kind input.run (scope kind) (dominated kind)
    input.events input.records (bi := 0) (j := 0) (b := (function kind).blocks[0]!)
    (stm := ⟨[2],.load kind.sourceOp .i64 flags 0 0⟩)
    rfl rfl input.current input.source input.clif input.results input.mapped input.parameter input.pointer
    input.recorded input.emitted
  have frameEq : restrict (sourceFrame kind)
      (availOf (function kind) (availIn (function kind) input.result.ctx) 0 0) = sourceFrame kind := by
    unfold restrict
    congr 1
    funext y
    by_cases zero : y = 0
    · subst y
      simp only [required.2,ite_true]
      rfl
    · simp [sourceFrame,Clif.Regs.set,Clif.Regs.empty,zero]
  rw [frameEq]
  exact input_dfg input

/-- Each kind has actual source-step transfer on a live initialized nonzero heap.
The original restricted DFG and guarded value premises are inhabited. -/
theorem extending_guarded_source_witness (kind : Kind) (X : ExtSem) :
    ∃ (input : RecordInput kind) (ρ' : Nat → CV) (w' : Arm.ArmState),
      seqRun (csem relation.F ⟨0,0⟩ X) (input.record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve input.result.final.alias (input.result.final.alias.size+1))))
        initialRegs world = some (.fall ρ' w') ∧
      relation.holds (function kind) (sourceFrame kind).slots heap w' ∧
      VHolds (value kind) (ρ' 194) ∧
      SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
        (sourceFrame kind,heap) (afterFrame kind,heap) ∧
      ValuesHeld (fun y => Demanded input.record.input y ∧
        y ∈ availOf (function kind) (availIn (function kind) input.result.ctx) 0 1)
        input.event.ctx (afterFrame kind) (fun k => ρ' (aliasNum input.result.final.alias k)) := by
  obtain ⟨input⟩ := record_input kind
  have sourceStep := input_source_step input
  obtain ⟨v,ρ',w',evaluated,executed,same,memory,held⟩ := stock_lower_extending_load_source_step kind
    input.run (scope kind) (dominated kind) input.events input.records
    (bi := 0) (j := 0) (b := (function kind).blocks[0]!)
    (stm := ⟨[2],.load kind.sourceOp .i64 flags 0 0⟩)
    rfl rfl input.current input.source input.clif input.results rfl input.mapped input.parameter input.pointer
    input.recorded input.emitted (mrStable_holds relation (function kind))
    (memRefines_csem relation.F ⟨0,0⟩ X rfl (fun _ _ h => by cases h))
    (memRelOk_holds relation (function kind)) (memory_world kind) (input_restricted_dfg input)
    (input_held input _) sourceStep
  have valuesEq : [v] = [value kind] :=
    (Prod.mk.inj (Clif.Res.ok.inj (evaluated.symm.trans (source_eval kind)))).1
  have valueEq := (List.cons.inj valuesEq).1
  subst v
  exact ⟨input,ρ',w',executed,memory,by simpa only [input.frontier] using held.1,sourceStep,held.2⟩

private def allowed (a : BitVec 64) : Prop :=
  ∃ n,heap.valid n 1 = true ∧ (heap.bytes n).isSome = true ∧ a = BitVec.ofNat 64 n
private theorem initialized : InitIn allowed heap := by
  intro a valid byte
  exact ⟨a,valid,byte,rfl⟩
private noncomputable abbrev guarded (X : ExtSem) : Sem :=
  csemG relation.F ⟨0,0⟩ X allowed (fun _ => none) [] [] 0 (fun _ _ _ _ => False)

/-- Distinct machine worlds execute every retained-kind record with the same
exact virtual file under read permissions derived from the original heap. -/
theorem extending_guarded_pair_witness (kind : Kind) (X : ExtSem) :
    Arm.r (.GPR 10#5) otherWorld ≠ Arm.r (.GPR 10#5) world ∧
      ∃ (input : RecordInput kind) (ρ' : Nat → CV) (t t' : Arm.ArmState),
        seqRun (guarded X) (input.record.output.emitted.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve input.result.final.alias (input.result.final.alias.size+1))))
          initialRegs world = some (.fall ρ' t) ∧
        seqRun (guarded X) (input.record.output.emitted.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve input.result.final.alias (input.result.final.alias.size+1))))
          initialRegs otherWorld = some (.fall ρ' t') ∧
        SameWorld relation.F t world ∧ SameWorld relation.F t' otherWorld := by
  refine ⟨by decide +kernel,?_⟩
  obtain ⟨input⟩ := record_input kind
  have operands := input_held input (fun _ => True) 0 trivial
  obtain ⟨ρ',t,t',first,second,same,otherSame⟩ := stock_lower_extending_load_paired_record kind
    input.run (scope kind) (dominated kind) input.events input.records input.source input.clif input.results
    input.mapped input.parameter input.pointer input.recorded input.emitted
    (isem := guarded X) (ρ := initialRegs)
    (memRefinesR_csemG (ctx := ⟨0,0⟩) (X := X) (syms := fun _ => none)
      rfl (fun _ _ h => by cases h))
    (memRelOk_holds relation (function kind)) (memory_world kind) (other_memory kind) initialized
    (input_dfg input) operands (source_eval kind)
  exact ⟨input,ρ',t,t',first,second,same,otherSame⟩

end Backend.Stock.Memory.ExtendedRoots.Fixture
