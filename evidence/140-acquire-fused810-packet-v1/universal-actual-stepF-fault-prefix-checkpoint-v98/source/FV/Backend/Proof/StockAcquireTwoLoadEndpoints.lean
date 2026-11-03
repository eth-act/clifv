import FV.Backend.Proof.StockAcquireTwoLoadPrefixFixture

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- The first retained consumer identifies the first original load without an endpoint certificate. -/
theorem first_consumer_endpoints {event : BlockScanEvent} {record : ScanRecord}
    (entryBlock : event.block = 0) (current : record.inst = 2)
    (R : SourceEndpointReceipt function event record) :
    R.producerIndex = 0 ∧ R.consumerIndex = 2 ∧ R.producer = 0 ∧
      R.value = 63 ∧ R.pointer = 7 ∧ R.ty = .i8 ∧ R.flags = ({} : Clif.MemFlags) := by
  have originalBlock : function.blocks[0]? = some function.blocks[0]! := by decide
  have actualBlock := R.blockAt
  rw [entryBlock] at actualBlock
  have blockEq := Option.some.inj (originalBlock.symm.trans actualBlock)
  have consumer := R.current
  simp only [current,entryBlock,blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] at consumer
  have consumerAt := R.consumerAt
  rw [← blockEq,← consumer] at consumerAt
  have consumerStmt : R.consumerStmt = ⟨[100],.extend .uextend .i64 63⟩ := by
    simpa [function] using consumerAt.symm
  have extension := R.extension
  rw [consumerStmt] at extension
  have value : R.value = 63 := (Clif.Inst.extend.inj extension.symm).2.2
  have bound := R.before
  rw [← consumer] at bound
  have cases : R.producerIndex = 0 ∨ R.producerIndex = 1 := by omega
  rcases cases with first | second
  · have producerAt := R.producerAt
    rw [← blockEq,first] at producerAt
    have producerStmt : R.producerStmt = ⟨[63],.atomicLoad .i8 {} 7⟩ := by
      simpa [function] using producerAt.symm
    have atomic := R.atomic
    rw [producerStmt] at atomic
    have ⟨ty,flags,pointer⟩ := Clif.Inst.atomicLoad.inj atomic.symm
    have position := R.position
    simp only [entryBlock,blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add,first] at position
    exact ⟨first,consumer.symm,position,value,pointer,ty,flags⟩
  · have producerAt := R.producerAt
    rw [← blockEq,second] at producerAt
    have producerStmt : R.producerStmt = ⟨[64],.atomicLoad .i8 {} 31⟩ := by
      simpa [function] using producerAt.symm
    have result := R.result
    simp [producerStmt,value] at result

/-- The second retained consumer identifies the second original load and its unchanged fault flags. -/
theorem second_consumer_endpoints {event : BlockScanEvent} {record : ScanRecord}
    (entryBlock : event.block = 0) (current : record.inst = 3)
    (R : SourceEndpointReceipt function event record) :
    R.producerIndex = 1 ∧ R.consumerIndex = 3 ∧ R.producer = 1 ∧
      R.value = 64 ∧ R.pointer = 31 ∧ R.ty = .i8 ∧ R.flags = ({} : Clif.MemFlags) := by
  have originalBlock : function.blocks[0]? = some function.blocks[0]! := by decide
  have actualBlock := R.blockAt
  rw [entryBlock] at actualBlock
  have blockEq := Option.some.inj (originalBlock.symm.trans actualBlock)
  have consumer := R.current
  simp only [current,entryBlock,blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] at consumer
  have consumerAt := R.consumerAt
  rw [← blockEq,← consumer] at consumerAt
  have consumerStmt : R.consumerStmt = ⟨[101],.extend .uextend .i64 64⟩ := by
    simpa [function] using consumerAt.symm
  have extension := R.extension
  rw [consumerStmt] at extension
  have value : R.value = 64 := (Clif.Inst.extend.inj extension.symm).2.2
  have bound := R.before
  rw [← consumer] at bound
  have cases : R.producerIndex = 0 ∨ R.producerIndex = 1 ∨ R.producerIndex = 2 := by omega
  rcases cases with first | second | third
  · have producerAt := R.producerAt
    rw [← blockEq,first] at producerAt
    have producerStmt : R.producerStmt = ⟨[63],.atomicLoad .i8 {} 7⟩ := by
      simpa [function] using producerAt.symm
    have result := R.result
    simp [producerStmt,value] at result
  · have producerAt := R.producerAt
    rw [← blockEq,second] at producerAt
    have producerStmt : R.producerStmt = ⟨[64],.atomicLoad .i8 {} 31⟩ := by
      simpa [function] using producerAt.symm
    have atomic := R.atomic
    rw [producerStmt] at atomic
    have ⟨ty,flags,pointer⟩ := Clif.Inst.atomicLoad.inj atomic.symm
    have position := R.position
    simp only [entryBlock,blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add,second] at position
    exact ⟨second,consumer.symm,position,value,pointer,ty,flags⟩
  · have producerAt := R.producerAt
    rw [← blockEq,third] at producerAt
    have producerStmt : R.producerStmt = ⟨[100],.extend .uextend .i64 63⟩ := by
      simpa [function] using producerAt.symm
    have atomic := R.atomic
    simp [producerStmt] at atomic

end Backend.Stock.Proof.AcquireTwoLoadPrefix
