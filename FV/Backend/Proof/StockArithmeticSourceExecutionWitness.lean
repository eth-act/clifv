import FV.Backend.Proof.StockArithmeticSourceExecution
import FV.Backend.Proof.StockScalarAddScanWitness
namespace Backend.Stock.Proof.ArithmeticBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Complete actual reference-return and dirty-input machine-body witness
for the runLoop-derived source-step and body-simulation theorems. -/
theorem actual_arithmetic_runLoop_body_witness :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (b : Clif.Block)
      (term : ScanRecord) (body : BlockScan) (s t : Clif.State) (left : Nat) (registers : Nat → CV),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
      event ∈ result.blockScans.toList ∧ f.blocks = [b] ∧ b.body ≠ [] ∧
      SourceBodySplit f event b term body ∧ s.frame.func = f ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 2 s = .returned [⟨.i64,12⟩] Clif.Mem.empty ∧
      left + b.body.length = 2 ∧
      Clif.runLoop Clif.Env.empty {funcs := []} left t = .returned [⟨.i64,12⟩] Clif.Mem.empty ∧
      t.frame.body = [] ∧
      ∀ w, GuardedScanRel f result event.ctx event.block
        (fun _ cm _ => cm = Clif.Mem.empty) event.output.state (0,s.frame,s.mem) registers w ∧
        ∃ ρ' w', seqRun ispec (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) registers w =
            some (.fall ρ' w') ∧
          GuardedScanRel f result event.ctx event.block
            (fun _ cm _ => cm = Clif.Mem.empty) term.output.state (b.body.length,t.frame,t.mem) ρ' w' := by
  obtain ⟨run,scope,dominated,events,records,scanned,oldFamilies,source,execution⟩ :=
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
  let start : Clif.State := ⟨ScalarAdd.Source.frame "scalar_add_scan" .systemVI64 [] 7 5,[],Clif.Mem.empty⟩
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 2 start =
      .returned [⟨.i64,12⟩] Clif.Mem.empty := rfl
  have self : Refines (fun _ => True) ispec :=
    fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have stable : MRStable (fun _ => True) (fun _ cm _ => cm = Clif.Mem.empty) := by
    intro _ _ _ _ _ h
    exact h
  obtain ⟨term,body,t,left,split,total,ends,empty,semantics⟩ :=
    actual_arithmetic_runLoop_body_refines run scope dominated (b := b) rfl family events
      (s := start) rfl returned self stable
  exact ⟨_,_,_,b,term,body,start,t,left,_,run,scope,dominated,events,rfl,by decide,split,rfl,
    returned,total,ends,empty,by
      intro w
      have pre := (behaviour w).1
      exact ⟨pre,semantics _ w pre⟩⟩

end Backend.Stock.Proof.ArithmeticBody
