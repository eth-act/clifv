import FV.Backend.Proof.StockArithmeticBodyRefines
import FV.Backend.Proof.StockScalarAddScanWitness

namespace Backend.Stock.Proof.ArithmeticBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- A real nonempty source and real retained event inhabit derived arithmetic
family coverage. Fixed trace facts are confined to this nonvacuity witness. -/
theorem actual_arithmetic_families_witness :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (b : Clif.Block)
      (term : ScanRecord) (body : BlockScan),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
      event ∈ result.blockScans.toList ∧ f.blocks = [b] ∧ b.body ≠ [] ∧
      SourceBodySplit f event b term body ∧
      ∀ record ∈ body.records, SelectAddSubOrOmittedRecord f event.ctx event.block record := by
  obtain ⟨run,scope,dominated,events,records,scanned,oldFamilies,source,execution⟩ :=
    ScalarAddScanWitness.actual_scan_body_witness
  let b := (ScalarAdd.source "scalar_add_scan" .systemVI64 []).blocks[0]!
  have family : ∀ stm ∈ b.body, ∃ subtract : Bool, ∃ ty x y,
      stm.inst = .binary (if subtract then .isub else .iadd) ty x y := by
    intro stm member
    change stm ∈ [⟨[2],.binary .iadd .i64 0 1⟩] at member
    have eq := List.mem_singleton.mp member
    subst stm
    exact ⟨false,.i64,0,1,rfl⟩
  obtain ⟨term,body,split,families⟩ := actual_arithmetic_families run scope (b := b) rfl family events
  exact ⟨_,_,_,b,term,body,run,scope,dominated,events,rfl,by decide,split,families⟩

/-- The derived arithmetic body theorem executes a real nonempty source step
with dirty machine inputs and establishes its guarded postcondition. -/
theorem actual_arithmetic_execution_witness :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (b : Clif.Block)
      (term : ScanRecord) (body : BlockScan) (s t : SourcePoint) (registers : Nat → CV),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
      event ∈ result.blockScans.toList ∧ f.blocks = [b] ∧ b.body ≠ [] ∧
      SourceBodySplit f event b term body ∧
      SourceSteps (IndexedSourceInst Clif.Env.empty {funcs := []} f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block + ·)) s t ∧
      ∀ w, GuardedScanRel f result event.ctx event.block
        (fun _ cm _ => cm = Clif.Mem.empty) event.output.state s registers w ∧
        ∃ ρ' w', seqRun ispec (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) registers w =
            some (.fall ρ' w') ∧
          GuardedScanRel f result event.ctx event.block
            (fun _ cm _ => cm = Clif.Mem.empty) term.output.state t ρ' w' := by
  obtain ⟨run,scope,dominated,events,records,scanned,oldFamilies,source,oldExecution⟩ :=
    ScalarAddScanWitness.actual_scan_body_witness
  obtain ⟨oldBlock,oldTerm,oldBody,oldSplit,oldFamily,behaviour⟩ :=
    ScalarAddScanWitness.actual_body_split_witness
  let b := (ScalarAdd.source "scalar_add_scan" .systemVI64 []).blocks[0]!
  have family : ∀ stm ∈ b.body, ∃ subtract : Bool, ∃ ty x y,
      stm.inst = .binary (if subtract then .isub else .iadd) ty x y := by
    intro stm member
    change stm ∈ [⟨[2],.binary .iadd .i64 0 1⟩] at member
    have eq := List.mem_singleton.mp member
    subst stm
    exact ⟨false,.i64,0,1,rfl⟩
  have self : Refines (fun _ => True) ispec :=
    fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have stable : MRStable (fun _ => True) (fun _ cm _ => cm = Clif.Mem.empty) := by
    intro _ _ _ _ _ h
    exact h
  obtain ⟨term,body,split,semantics⟩ := actual_arithmetic_body_refines
    run scope dominated (b := b) rfl family events self stable
  have steps := SourceSteps.cons source (SourceSteps.nil _)
  exact ⟨_,_,_,b,term,body,_,_,_,run,scope,dominated,events,rfl,by decide,split,
    by
      rw [ScalarAddScanWitness.actual_event_block]
      change SourceSteps _ [0] _ _
      exact steps,
    by
      intro w
      have pre := (behaviour w).1
      refine ⟨pre,semantics _ _ ?_ _ w pre⟩
      rw [ScalarAddScanWitness.actual_event_block]
      change SourceSteps _ [0] _ _
      exact steps⟩

end Backend.Stock.Proof.ArithmeticBody
