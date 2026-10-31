import FV.Backend.Proof.StockMemoryStoreRecordFixture
import FV.E2E.Main
import FV.E2E.Guarded

namespace Backend.Stock.Memory.StoreRoots.Fixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def value (kind : Kind) : Clif.Val := Clif.Val.ofNat kind.sourceTy 37
private def sourceFrame (kind : Kind) : Clif.Frame := {
  func := function kind
  regs := (Clif.Regs.empty.set 0 ⟨.i64,4096⟩).set 1 (value kind)
  slots := []
  body := [⟨[],.store kind.sourceOp kind.sourceTy flags 1 0 0⟩]
  term := .ret [] }
private def afterFrame (kind : Kind) : Clif.Frame := {sourceFrame kind with body := []}
private def initialRegs (n : Nat) : CV := if n = 192 then ofX 4096 else if n = 193 then ofX 37 else ofX 0
private def heap : Clif.Mem := {allocs := [⟨4096,8,false⟩],bytes := fun _ => some 165}
private def afterHeap (kind : Kind) : Clif.Mem :=
  heap.writeBits false 4096 (kind.sourceOp.size kind.sourceTy) (value kind).bits
private def world : Arm.ArmState := {Arm.ArmState.default with mem := fun _ => 165}
private def relation : E2E.Rel := ⟨fun _ => False,fun _ => none,0,0⟩
private def allowed (a : BitVec 64) : Prop :=
  ∃ n,heap.valid n 1 = true ∧ (heap.bytes n).isSome = true ∧ a = BitVec.ofNat 64 n
private noncomputable abbrev guarded (X : ExtSem) : Sem :=
  csemG relation.F ⟨0,0⟩ X allowed (fun _ => none) [] [] 0 (fun _ _ _ _ => False)

private theorem source_eval (kind : Kind) :
    Clif.evalInst (sourceFrame kind) heap (.store kind.sourceOp kind.sourceTy flags 1 0 0) =
      .ok ([],afterHeap kind) := by
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

private theorem input_dfg {kind : Kind} (input : RecordInput kind) :
    DFGCons input.event.ctx (sourceFrame kind) := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases zero : x = 0
    · subst x
      rw [input.pointerParameter] at defined
      cases defined
    · by_cases one : x = 1
      · subst x
        rw [input.valueParameter] at defined
        cases defined
      · simp [sourceFrame,Clif.Regs.set,Clif.Regs.empty,zero,one] at lookup
  · intro x t v typed lookup
    by_cases zero : x = 0
    · subst x
      have pointer := (stock_lower_record_context input.run (scope kind) input.events).1.addr64
        _ _ _ 0 input.source input.clif rfl
      have equal := Option.some.inj (pointer.symm.trans typed)
      subst t
      have same : v = ⟨.i64,4096⟩ := by simpa [sourceFrame,Clif.Regs.set,Clif.Regs.empty] using lookup.symm
      subst v
      rfl
    · by_cases one : x = 1
      · subst x
        have equal := Option.some.inj (input.valueType.symm.trans typed)
        subst t
        have same : v = value kind := by simpa [sourceFrame,Clif.Regs.set,Clif.Regs.empty] using lookup.symm
        subst v
        rfl
      · simp [sourceFrame,Clif.Regs.set,Clif.Regs.empty,zero,one] at lookup

private theorem input_held {kind : Kind} (input : RecordInput kind) (needed : Nat → Prop) :
    ValuesHeld needed input.event.ctx (sourceFrame kind)
      (fun k => initialRegs (aliasNum input.result.final.alias k)) := by
  intro y required val lookup
  by_cases zero : y = 0
  · subst y
    have same : val = ⟨.i64,4096⟩ := by simpa [sourceFrame,Clif.Regs.set,Clif.Regs.empty] using lookup.symm
    subst val
    refine ⟨192,input.pointerMapped,?_⟩
    dsimp only
    rw [input.pointerAlias]
    rfl
  · by_cases one : y = 1
    · subst y
      have same : val = value kind := by simpa [sourceFrame,Clif.Regs.set,Clif.Regs.empty] using lookup.symm
      subst val
      refine ⟨193,input.valueMapped,?_⟩
      dsimp only
      rw [input.valueAlias]
      cases kind <;> rfl
    · simp [sourceFrame,Clif.Regs.set,Clif.Regs.empty,zero,one] at lookup

private theorem input_source_step {kind : Kind} (input : RecordInput kind) :
    SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (sourceFrame kind,heap) (afterFrame kind,afterHeap kind) := by
  have outcome : instOutcome Clif.Env.empty {funcs := []} (sourceFrame kind) heap
      (.store kind.sourceOp kind.sourceTy flags 1 0 0) = .ok ([],afterHeap kind) := by
    simpa only [instOutcome] using source_eval kind
  exact ⟨input.info,.store kind.sourceOp kind.sourceTy flags 1 0 0,[],(sourceFrame kind).regs,[],
    input.source,input.clif,by rw [input.results]; rfl,outcome,by rw [input.results]; rfl,rfl⟩

private theorem input_restricted_dfg {kind : Kind} (input : RecordInput kind) :
    DFGCons input.event.ctx (restrict (sourceFrame kind)
      (availOf (function kind) (availIn (function kind) input.result.ctx) 0 0)) := by
  have required := stock_lower_integer_store_operand_coverage kind input.run (scope kind) (dominated kind)
    input.events input.records (bi := 0) (j := 0) (b := (function kind).blocks[0]!)
    (stm := ⟨[],.store kind.sourceOp kind.sourceTy flags 1 0 0⟩)
    rfl rfl input.current input.source input.clif input.typed input.pointerParameter input.pointerMapped
    input.valueMapped input.recorded input.emitted
  have same : restrict (sourceFrame kind)
      (availOf (function kind) (availIn (function kind) input.result.ctx) 0 0) = sourceFrame kind := by
    unfold restrict
    congr 1
    funext y
    by_cases zero : y = 0
    · subst y
      simp only [(required 0 (Or.inr rfl)).2,ite_true]
      rfl
    · by_cases one : y = 1
      · subst y
        simp only [(required 1 (Or.inl rfl)).2,ite_true]
        rfl
      · simp [sourceFrame,Clif.Regs.set,Clif.Regs.empty,zero,one]
  rw [same]
  exact input_dfg input

/-- All seven store roots have an actual guarded source-step witness that changes memory and preserves every virtual register. -/
theorem integer_store_guarded_source_witness (kind : Kind) (X : ExtSem) :
    ∃ (input : RecordInput kind) (w' : Arm.ArmState),
      seqRun (guarded X) (input.record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve input.result.final.alias (input.result.final.alias.size+1))))
        initialRegs world = some (.fall initialRegs w') ∧
      relation.holds (function kind) (afterFrame kind).slots (afterHeap kind) w' ∧
      Arm.read_mem 4096 w' = 37 ∧ Arm.read_mem 4096 world ≠ Arm.read_mem 4096 w' ∧
      SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
        (sourceFrame kind,heap) (afterFrame kind,afterHeap kind) ∧
      ValuesHeld (fun y => Demanded input.record.input y ∧
        y ∈ availOf (function kind) (availIn (function kind) input.result.ctx) 0 1)
        input.event.ctx (afterFrame kind) (fun k => initialRegs (aliasNum input.result.final.alias k)) := by
  obtain ⟨input⟩ := record_input kind
  have step := input_source_step input
  obtain ⟨pv,w',pointer,evaluated,executed,same,memory,held⟩ := stock_lower_integer_store_source_step_of_store kind
    input.run (scope kind) (dominated kind) input.events input.records
    (bi := 0) (j := 0) (b := (function kind).blocks[0]!)
    (stm := ⟨[],.store kind.sourceOp kind.sourceTy flags 1 0 0⟩)
    rfl rfl input.current input.source input.clif input.typed input.pointerParameter input.pointerMapped
    input.valueMapped input.recorded input.emitted (mrStable_holds relation (function kind))
    (store_refines_of_memR (memRefinesR_csemG (ctx := ⟨0,0⟩) (X := X) (syms := fun _ => none)
      rfl (fun _ _ h => by cases h)))
    (memRelOk_holds relation (function kind)) (memory_world kind) (input_restricted_dfg input)
    (input_held input _) step
  have valid : (afterHeap kind).valid 4096 1 = true := by cases kind <;> rfl
  have byte : (afterHeap kind).bytes 4096 = some 37 := by cases kind <;> rfl
  have written := (memRelOk_holds relation (function kind)).bytes _ _ _ 4096 37 memory valid byte
  refine ⟨input,w',executed,memory,written,?_,step,held⟩
  change Arm.read_mem (BitVec.ofNat 64 4096) world ≠ Arm.read_mem (BitVec.ofNat 64 4096) w'
  rw [written]
  decide +kernel

end Backend.Stock.Memory.StoreRoots.Fixture
