import FV.E2E.StockMemoryPairedBody
import FV.Backend.Proof.StockMemoryBodyFixture
import FV.Backend.Proof.StockMemoryPairedRecord
import FV.Backend.Proof.StockMemoryRecordWitness
import FV.Backend.Proof.StockMemoryLoadWitness
import FV.E2E.Guarded

namespace E2E.StockMemoryReadWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
open Backend.Stock.Memory.LoadFixture
set_option autoImplicit false
set_option Elab.async false

/-- The permitted bytes are derived entirely from the original source heap. -/
private def allowed (a : BitVec 64) : Prop :=
  ∃ n,heap.valid n 1 = true ∧ (heap.bytes n).isSome = true ∧ a = BitVec.ofNat 64 n
private theorem initialized : InitIn allowed heap := by
  intro a valid byte
  exact ⟨a,valid,byte,rfl⟩
private def otherWorld : Arm.ArmState := Arm.write_base_gpr 10#5 17 world
private theorem other_memory : relation.holds function frame.slots heap otherWorld := by
  refine ⟨⟨?_,memory_world.1.valid,rfl⟩,?_,outRel_zero _ _ _⟩
  · intro a b valid byte; exact memory_world.1.bytes a b valid byte
  · intro id b present; cases present
private noncomputable abbrev guarded (X : ExtSem) : Sem :=
  csemG relation.F ⟨0,0⟩ X allowed (fun _ => none) [] [] 0 (fun _ _ _ _ => False)

/-- The original initialized heap supplies the existing guarded semantics' read
permissions. Two distinct worlds execute exactly one machine load output; the
witness uses the actual guarded evaluator, not a true read-permission predicate. -/
theorem guarded_paired_load_witness (X : ExtSem) :
    Arm.r (.GPR 10#5) otherWorld ≠ Arm.r (.GPR 10#5) world ∧
      ∃ out t t',guarded X
          (.load .uload32 (.vreg 194 .int) (.unsignedOffset (.vreg 192 .int) 0) flags)
          [ofX 4096] world = some ([out],t,.next) ∧
        guarded X
          (.load .uload32 (.vreg 194 .int) (.unsignedOffset (.vreg 192 .int) 0) flags)
          [ofX 4096] otherWorld = some ([out],t',.next) ∧
        SameWorld relation.F t world ∧ SameWorld relation.F t' otherWorld := by
  refine ⟨by decide +kernel,?_⟩
  apply load_source_result_pairR
    (memRefinesR_csemG (ctx := ⟨0,0⟩) (X := X) (syms := fun _ => none)
      rfl (fun _ _ h => by cases h))
    (memRelOk_holds relation function) memory_world other_memory initialized (fr := frame)
    (op := .load) (ty := .i32) (p := 0) (off := 0) (cm' := heap)
    (vals := [⟨.i32,2779096485⟩]) (by decide) rfl (by decide)
  · intro pv pointer
    have same : pv = ⟨.i64,4096⟩ := Option.some.inj pointer.symm
    subst pv
    rfl
  · intro pv pointer
    have same : pv = ⟨.i64,4096⟩ := Option.some.inj pointer.symm
    subst pv
    rfl
  · exact source_load

private theorem initial_dfg (input : RecordInput) {fr : Clif.Frame}
    (regs : fr.regs = frame.regs) : DFGCons input.event.ctx fr := by
  constructor
  · intro x j info cl v defined found original pure lookup
    rw [regs] at lookup
    by_cases zero : x = 0
    · subst x; rw [input.parameter] at defined; cases defined
    · simp [frame,Clif.Regs.set,Clif.Regs.empty,zero] at lookup
  · intro x ty v typed lookup
    rw [regs] at lookup
    by_cases zero : x = 0
    · subst x
      have pointer := (stock_lower_record_context input.run scope input.events).1.addr64 _ _ _ 0 input.source input.clif rfl
      have equal := Option.some.inj (pointer.symm.trans typed)
      subst ty
      cases lookup
      rfl
    · simp [frame,Clif.Regs.set,Clif.Regs.empty,zero] at lookup

/-- Actual whole lowering, retained record and final193→194 binding inhabit
paired guarded execution with one identical resulting virtual file. No emitted
code, selected rule or final alias certificate is supplied separately. -/
theorem guarded_actual_record_pair_witness (X : ExtSem) :
    ∃ (input : RecordInput) (ρ' : Nat → CV) (t t' : Arm.ArmState),
      seqRun (guarded X) (input.record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve input.result.final.alias (input.result.final.alias.size+1))))
        (fun _ => ofX 4096) world = some (.fall ρ' t) ∧
      seqRun (guarded X) (input.record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve input.result.final.alias (input.result.final.alias.size+1))))
        (fun _ => ofX 4096) otherWorld = some (.fall ρ' t') ∧
      SameWorld relation.F t world ∧ SameWorld relation.F t' otherWorld := by
  obtain ⟨input⟩ := record_input
  have operands : ValueHeld input.event.ctx frame
      (fun k => (fun _ => ofX 4096) (aliasNum input.result.final.alias k)) 0 := by
    intro value lookup
    have same : value = ⟨.i64,4096⟩ := Option.some.inj lookup.symm
    subst value
    exact ⟨192,input.pointer,rfl⟩
  obtain ⟨ρ',t,t',first,second,same,otherSame⟩ := stock_lower_load_paired_record
    input.run scope dominated input.events input.records input.source input.clif input.results
    input.mapped input.parameter input.pointer input.recorded input.emitted
    (isem := guarded X) (ρ := fun _ => ofX 4096)
    (memRefinesR_csemG (ctx := ⟨0,0⟩) (X := X) (syms := fun _ => none)
      rfl (fun _ _ h => by cases h))
    (memRelOk_holds relation function) memory_world other_memory initialized
    (initial_dfg input rfl) operands source_load
  exact ⟨input,ρ',t,t',first,second,same,otherSame⟩

private def sourceFrame : Clif.Frame := {frame with body := [⟨[2],.load .load .i32 flags 0 0⟩]}
private def afterFrame : Clif.Frame := {sourceFrame with regs := sourceFrame.regs.set 2 ⟨.i32,2779096485⟩,body := []}

private theorem input_scan_packet (input : RecordInput) :
    IndexedSourceInst Clif.Env.empty {funcs := []} function input.event.ctx 1 input.record.inst
      (0,sourceFrame,heap) (1,afterFrame,heap) ∧
    ∀ (st : Backend.Stock.State) w,relation.holds function sourceFrame.slots heap w →
      GuardedScanRel function input.result input.event.ctx 1 (relation.holds function)
        st (0,sourceFrame,heap) (fun _ => ofX 4096) w := by
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (sourceFrame,heap) (afterFrame,heap) :=
    ⟨input.info,.load .load .i32 flags 0 0,[⟨.i32,2779096485⟩],
      sourceFrame.regs.set 2 ⟨.i32,2779096485⟩,[],input.source,input.clif,
      by rw [input.results]; rfl,rfl,by rw [input.results]; rfl,rfl⟩
  have indexed : IndexedSourceInst Clif.Env.empty {funcs := []} function input.event.ctx 1 input.record.inst
      (0,sourceFrame,heap) (1,afterFrame,heap) := ⟨input.current,rfl,sourceStep⟩
  have needed := stock_lower_load_operand_coverage input.run scope dominated input.events input.records
    (bi := 1) (j := 0) (b := function.blocks[1]!) (stm := ⟨[2],.load .load .i32 flags 0 0⟩)
    rfl rfl input.current input.source input.clif input.results input.mapped input.parameter input.pointer
    input.recorded input.emitted (stock_lower_load_i32_selected_id input.run scope input.events input.records
      input.source input.clif input.recorded input.emitted)
  have frameEq : restrict sourceFrame (availOf function (availIn function input.result.ctx) 1 0) = sourceFrame := by
    unfold restrict
    congr 1
    funext y
    by_cases zero : y = 0
    · subst y; simp only [needed.2,ite_true]; rfl
    · simp [sourceFrame,frame,Clif.Regs.set,Clif.Regs.empty,zero]
  have defined : DFGCons input.event.ctx (restrict sourceFrame (availOf function (availIn function input.result.ctx) 1 0)) := by
    rw [frameEq]
    exact initial_dfg input rfl
  have values : ∀ st,ValuesHeld (fun y => Demanded st y ∧
      y ∈ availOf function (availIn function input.result.ctx) 1 0) input.event.ctx sourceFrame
      (fun k => (fun _ => ofX 4096) (aliasNum input.result.final.alias k)) := by
    intro st y required value lookup
    by_cases zero : y = 0
    · subst y
      have same : value = ⟨.i64,4096⟩ := Option.some.inj lookup.symm
      subst value
      exact ⟨192,input.pointer,rfl⟩
    · simp [sourceFrame,frame,Clif.Regs.set,Clif.Regs.empty,zero] at lookup
  exact ⟨indexed,fun st w memory => ⟨rfl,defined,memory,values st⟩⟩

/-- The paired indexed source scan has inhabited original frame/DFG/value/memory
premises and retains both complete post-source guards, on the actual final code. -/
theorem guarded_actual_source_scan_pair_witness (X : ExtSem) :
    ∃ (input : RecordInput) (ρ' : Nat → CV) (t t' : Arm.ArmState),
      seqRun (guarded X) (input.record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve input.result.final.alias (input.result.final.alias.size+1))))
        (fun _ => ofX 4096) world = some (.fall ρ' t) ∧
      seqRun (guarded X) (input.record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve input.result.final.alias (input.result.final.alias.size+1))))
        (fun _ => ofX 4096) otherWorld = some (.fall ρ' t') ∧
      GuardedScanRel function input.result input.event.ctx 1 (relation.holds function)
        input.record.input (1,afterFrame,heap) ρ' t ∧
      GuardedScanRel function input.result input.event.ctx 1 (relation.holds function)
        input.record.input (1,afterFrame,heap) ρ' t' := by
  obtain ⟨input⟩ := record_input
  obtain ⟨indexed,before⟩ := input_scan_packet input
  obtain ⟨ρ',t,t',first,second,post,otherPost⟩ := StockMemory.stock_lower_load_scan_pair
    input.run scope dominated input.events input.records
    (bi := 1) (j := 0) (b := function.blocks[1]!) (stm := ⟨[2],.load .load .i32 flags 0 0⟩)
    rfl rfl input.current input.source input.clif input.results rfl input.mapped input.parameter input.pointer
    input.recorded input.emitted (mrStable_holds relation function)
    (memRefines_csem relation.F ⟨0,0⟩ X (syms := fun _ => none) rfl (fun _ _ h => by cases h))
    (memRelOk_holds relation function)
    (memRefinesR_csemG (ctx := ⟨0,0⟩) (X := X) (syms := fun _ => none)
      rfl (fun _ _ h => by cases h))
    (fun _ _ _ _ h => (csemG_sub h).2.2)
    _ _ indexed (fun _ => ofX 4096) world otherWorld initialized
    (before input.record.output.state world memory_world) (before input.record.output.state otherWorld other_memory)
  exact ⟨input,ρ',t,t',first,second,post,otherPost⟩

private def noExternal : ExtSem := ⟨fun _ _ _ => none,fun _ _ => 0,0,fun _ _ => Arm.PState.zero⟩

/-- A closed positive instance of the existing generic paired scan interface:
actual final code, live initialized heap, distinct worlds, original RelW and
both complete source guards. The TLS premise has an explicit constant model. -/
theorem pairsem_scan_interface_witness :
    ∃ (input : RecordInput) (ρ' : Nat → CV) (q : W2),
      seqRun (pairSem (csem relation.F ⟨0,0⟩ noExternal))
        (input.record.output.emitted.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve input.result.final.alias (input.result.final.alias.size+1))))
        (fun _ => ofX 4096) (world,otherWorld) = some (.fall ρ' q) ∧
      StockMemory.PairedScanRel function input.result input.event.ctx 1 relation 0 (fun _ => True)
        input.record.input (1,afterFrame,heap) ρ' q := by
  obtain ⟨input⟩ := record_input
  obtain ⟨indexed,before⟩ := input_scan_packet input
  have memory : RelW relation function 0 sourceFrame.slots heap world := ⟨memory_world,by simp [spv,Arm.r,Arm.read_base_gpr,Arm.read_store,world,Arm.ArmState.default],by simp only [Arm.r,Arm.read_base_error,world,Arm.ArmState.default]⟩
  have otherMemory : RelW relation function 0 sourceFrame.slots heap otherWorld := ⟨other_memory,by simp [spv,Arm.r,Arm.read_base_gpr,Arm.read_store,otherWorld,Arm.write_base_gpr,Arm.write_store,world,Arm.ArmState.default],by simp only [Arm.r,Arm.read_base_error,otherWorld,Arm.write_base_gpr,world,Arm.ArmState.default]⟩
  have firstGuard := before input.record.output.state world memory_world
  have secondGuard := before input.record.output.state otherWorld other_memory
  have first : GuardedScanRel function input.result input.event.ctx 1 (RelW relation function 0)
      input.record.output.state (0,sourceFrame,heap) (fun _ => ofX 4096) world :=
    ⟨firstGuard.1,firstGuard.2.1,memory,firstGuard.2.2.2⟩
  have second : GuardedScanRel function input.result input.event.ctx 1 (RelW relation function 0)
      input.record.output.state (0,sourceFrame,heap) (fun _ => ofX 4096) otherWorld :=
    ⟨secondGuard.1,secondGuard.2.1,otherMemory,secondGuard.2.2.2⟩
  have worlds : SameWorld (Zof relation.F (fun _ => True) heap) world otherWorld := by
    simpa only [otherWorld,Arm.w] using (SameWorld.refl (Zof relation.F (fun _ => True) heap) world).w_right
      (f := .GPR 10#5) (v := 17) (by change (10 < 29 ∧ 10 ≠ 18) ∨ 10 = 30; decide)
  have tls : XTls relation.F noExternal := by intro Z n w w' subset same; rfl
  obtain ⟨ρ',q,executed,post⟩ := StockMemory.stock_lower_load_paired_scan
    input.run scope dominated input.events input.records
    (bi := 1) (j := 0) (b := function.blocks[1]!) (stm := ⟨[2],.load .load .i32 flags 0 0⟩)
    rfl rfl input.current input.source input.clif input.results rfl input.mapped input.parameter input.pointer
    input.recorded input.emitted (Γ := relation) (c := 0) (D := fun _ => True) (fc := ⟨0,0⟩)
    rfl (fun _ _ h => by cases h) tls _ _ indexed (fun _ => ofX 4096) (world,otherWorld)
    ⟨first,second,worlds⟩
  exact ⟨input,ρ',q,executed,post⟩

private theorem paired_before (input : RecordInput) (st : Backend.Stock.State) :
    StockMemory.PairedScanRel function input.result input.event.ctx 1 relation 0 (fun _ => True)
      st (0,sourceFrame,heap) (fun _ => ofX 4096) (world,otherWorld) := by
  have memory : RelW relation function 0 sourceFrame.slots heap world :=
    ⟨memory_world,by simp [spv,Arm.r,Arm.read_base_gpr,Arm.read_store,world,Arm.ArmState.default],
      by simp only [Arm.r,Arm.read_base_error,world,Arm.ArmState.default]⟩
  have otherMemory : RelW relation function 0 sourceFrame.slots heap otherWorld :=
    ⟨other_memory,by simp [spv,Arm.r,Arm.read_base_gpr,Arm.read_store,otherWorld,Arm.write_base_gpr,Arm.write_store,world,Arm.ArmState.default],
      by simp only [Arm.r,Arm.read_base_error,otherWorld,Arm.write_base_gpr,world,Arm.ArmState.default]⟩
  have first := (input_scan_packet input).2 st world memory_world
  have second := (input_scan_packet input).2 st otherWorld other_memory
  refine ⟨⟨first.1,first.2.1,memory,first.2.2.2⟩,⟨second.1,second.2.1,otherMemory,second.2.2.2⟩,?_⟩
  simpa only [otherWorld,Arm.w] using (SameWorld.refl (Zof relation.F (fun _ => True) heap) world).w_right
    (f := .GPR 10#5) (v := 17) (by change (10 < 29 ∧ 10 ≠ 18) ∨ 10 = 30; decide)

/-- Complete actual paired body execution uses source-only body classification,
original inherited pointer metadata and a real source step on the live heap. -/
theorem complete_paired_body_witness :
    ∃ (input : RecordInput) (term : Backend.Stock.ScanRecord) (body : Backend.Stock.BlockScan)
      (ρ' : Nat → CV) (q : W2),
      SourceBodySplit function input.event function.blocks[1]! term body ∧
      seqRun (pairSem (csem relation.F ⟨0,0⟩ noExternal))
        (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve input.result.final.alias (input.result.final.alias.size+1))))
        (fun _ => ofX 4096) (world,otherWorld) = some (.fall ρ' q) ∧
      StockMemory.PairedScanRel function input.result input.event.ctx input.event.block relation 0 (fun _ => True)
        term.output.state (1,afterFrame,heap) ρ' q := by
  obtain ⟨input⟩ := record_input
  have atBlock : function.blocks[input.event.block]? = some function.blocks[1]! := by rw [input.atBlock]; rfl
  have tls : XTls relation.F noExternal := by intro Z n w w' subset same; rfl
  obtain ⟨term,body,split,bodyRun⟩ := StockMemory.stock_single_load_return_paired_body
    input.run scope dominated input.events atBlock rfl rfl (pi := 0) (pb := function.blocks[0]!) rfl
    (by decide) (Γ := relation) (c := 0) (D := fun _ => True) (fc := ⟨0,0⟩)
    rfl (fun _ _ h => by cases h) tls (env := Clif.Env.empty) (cp := {funcs := []})
  have indexed := (input_scan_packet input).1
  rw [input.current] at indexed
  have steps : SourceSteps (IndexedSourceInst Clif.Env.empty {funcs := []} function input.event.ctx input.event.block)
      ((List.range function.blocks[1]!.body.length).map (blockStart function input.event.block+·))
      (0,sourceFrame,heap) (1,afterFrame,heap) := by
    rw [input.atBlock]
    change SourceSteps _ [1] _ _
    exact .cons indexed (.nil _)
  have before : StockMemory.PairedScanRel function input.result input.event.ctx input.event.block relation 0 (fun _ => True)
      input.event.output.state (0,sourceFrame,heap) (fun _ => ofX 4096) (world,otherWorld) := by
    rw [input.atBlock]
    exact paired_before input input.event.output.state
  obtain ⟨ρ',q,executed,post⟩ := bodyRun _ _ steps (fun _ => ofX 4096) (world,otherWorld) before
  exact ⟨input,term,body,ρ',q,split,executed,post⟩

end E2E.StockMemoryReadWitness
