import FV.Backend.Proof.StockMemoryStoreClass
import FV.Backend.Proof.StockMemoryStoreRecordFixture

namespace E2E.StockMemoryStoreFunctionWitness
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
open Backend.Stock.Memory.StoreRoots Backend.Stock.Memory.StoreRoots.Fixture
theorem source_class_witness (kind : Kind) : SingleClass kind kind.sourceTy (function kind) := by
  refine ⟨scope kind,dominated kind,(by cases kind <;> rfl),rfl,?_,?_⟩
  · intro loc member
    have locations : locsOf (function kind).sig = [ArgLoc.reg (.x 0),ArgLoc.reg (.x 1)] := by cases kind <;> rfl
    rw [locations] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact ⟨_,rfl⟩
  · exact ⟨(function kind).blocks[0]!,1,0,flags,kind.sourceTy,rfl,rfl,rfl,
      (by simp [function]),(by simp [function]),(by cases kind <;> intro h <;> first | rfl | cases h),rfl⟩
end E2E.StockMemoryStoreFunctionWitness
