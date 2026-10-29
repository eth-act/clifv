module

public import FV.Backend.Proof.StockArithmeticSourceRefines
public import FV.Backend.Proof.StockScalarAddScanWitness

@[expose] public section

namespace Backend.Stock.Proof.ArithmeticBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- A real retained source slot and successful reference evaluator transition
inhabit the source-step bridge, with no source-step certificate assumed. -/
theorem actual_arithmetic_source_step_witness :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (b : Clif.Block)
      (term : ScanRecord) (body : BlockScan) (record : ScanRecord) (s t : Clif.State),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      SourceBodySplit f event b term body ∧ s.frame.func = f ∧ s.frame.body ≠ [] ∧
      Clif.step Clif.Env.empty {funcs := []} s = .next t ∧
      IndexedSourceInst Clif.Env.empty {funcs := []} f event.ctx event.block record.inst
        (0,s.frame,s.mem) (1,t.frame,t.mem) := by
  obtain ⟨run,scope,dominated,events,records,scanned,oldFamilies,source,execution⟩ :=
    ScalarAddScanWitness.actual_scan_body_witness
  let actualRecord := (fun {r : ScanRecord} {rs : List ScanRecord} (_ : r ∈ rs) => r) records
  obtain ⟨current,clif,results,mapped,recorded,emitted,tail⟩ := ScalarAddScanWitness.facts
  let b := (ScalarAdd.source "scalar_add_scan" .systemVI64 []).blocks[0]!
  have family : ∀ stm ∈ b.body, ∃ subtract : Bool, ∃ ty x y,
      stm.inst = .binary (if subtract then .isub else .iadd) ty x y := by
    intro stm member
    change stm ∈ [⟨[2],.binary .iadd .i64 0 1⟩] at member
    have eq := List.mem_singleton.mp member
    subst stm
    exact ⟨false,.i64,0,1,rfl⟩
  obtain ⟨term,body,split,families⟩ := actual_arithmetic_families run scope (b := b) rfl family events
  let start : Clif.State := ⟨ScalarAdd.Source.frame "scalar_add_scan" .systemVI64 [] 7 5,[],Clif.Mem.empty⟩
  let finish : Clif.State := {start with frame := {start.frame with regs := start.frame.regs.set 2 ⟨.i64,12⟩,body := []}}
  have reference : Clif.step Clif.Env.empty {funcs := []} start = .next finish := rfl
  have index : actualRecord.inst = blockStart (ScalarAdd.source "scalar_add_scan" .systemVI64 []) 0 + 0 := by simpa [blockStart] using current
  let actualEvent := (fun {e : BlockScanEvent} {es : List BlockScanEvent} (_ : e ∈ es) => e) events
  have index' : actualRecord.inst = blockStart (ScalarAdd.source "scalar_add_scan" .systemVI64 []) actualEvent.block + 0 := by
    change actualRecord.inst = blockStart _ actualEvent.block + 0
    have block : actualEvent.block = 0 := ScalarAddScanWitness.actual_event_block
    rw [block]
    exact index
  have actual := actual_arithmetic_source_step run events split (record := actualRecord)
    (j := 0) (stm := ⟨[2],.binary .iadd .i64 0 1⟩) rfl index' false rfl (s := start) rfl reference
  exact ⟨_,_,_,b,term,body,actualRecord,start,finish,run,scope,dominated,events,records,split,rfl,by decide,reference,actual⟩

end Backend.Stock.Proof.ArithmeticBody
