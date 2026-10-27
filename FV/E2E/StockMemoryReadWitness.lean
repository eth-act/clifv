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

private theorem initial_dfg (input : RecordInput) : DFGCons input.event.ctx frame := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases zero : x = 0
    · subst x; rw [input.parameter] at defined; cases defined
    · simp [frame,Clif.Regs.set,Clif.Regs.empty,zero] at lookup
  · intro x ty v typed lookup
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
    (initial_dfg input) operands source_load
  exact ⟨input,ρ',t,t',first,second,same,otherSame⟩

end E2E.StockMemoryReadWitness
