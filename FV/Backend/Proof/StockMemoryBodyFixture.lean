import FV.Backend.Proof.StockMemoryRecordWitness

namespace Backend.Stock.Memory.LoadFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The actual load record belongs to the nonentry source block. This follows
from the whole-run body positions, without another fixed native check. -/
theorem RecordInput.atBlock (input : RecordInput) : input.event.block = 1 := by
  obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split input.run scope input.events
  have bound : input.event.block < 2 := by
    have inside := lt_of_getElem? split.block
    simpa [function] using inside
  apply Classical.byContradiction
  intro different
  have zero : input.event.block = 0 := by omega
  have same : b = function.blocks[0]! := Option.some.inj (split.block.symm.trans (by rw [zero]; rfl))
  subst b
  have member := input.records
  rw [split.records] at member
  rcases List.mem_cons.mp member with isTerm | inBody
  · have index : input.record.inst = 0 := by
      rw [isTerm,split.termInst,split.termIndex,zero]
      rfl
    have impossible : (1 : Nat) = 0 := input.current.symm.trans index
    omega
  · obtain ⟨j,stm,statement,current⟩ := split.positions input.record inBody
    change ([] : List Clif.Stmt)[j]? = some stm at statement
    simp at statement

theorem RecordInput.body_split (input : RecordInput) :
    ∃ term body,SourceBodySplit function input.event function.blocks[1]! term body := by
  obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split input.run scope input.events
  have same : b = function.blocks[1]! := Option.some.inj (split.block.symm.trans (by rw [input.atBlock]; rfl))
  subst b
  exact ⟨term,body,split⟩

theorem RecordInput.body_record (input : RecordInput) {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit function input.event function.blocks[1]! term body) :
    input.record ∈ body.records := by
  have member := input.records
  rw [split.records] at member
  rcases List.mem_cons.mp member with isTerm | inBody
  · have index : input.record.inst = 2 := by
      rw [isTerm,split.termInst,split.termIndex,input.atBlock]
      rfl
    have impossible : (1 : Nat) = 2 := input.current.symm.trans index
    omega
  · exact inBody

theorem RecordInput.body_records (input : RecordInput) {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit function input.event function.blocks[1]! term body) :
    body.records = [input.record] := by
  have indices : sourceBodyIndices function input.event.block function.blocks[1]! = [1] := by
    rw [input.atBlock]
    rfl
  have scanned := split.scanned
  rw [indices] at scanned
  cases scanned with
  | cons head tail =>
    cases tail
    have member := input.body_record split
    exact congrArg (fun r => [r]) (List.mem_singleton.mp member).symm

end Backend.Stock.Memory.LoadFixture
