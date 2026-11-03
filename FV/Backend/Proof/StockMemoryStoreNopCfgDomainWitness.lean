import FV.Backend.Proof.StockMemoryStoreNopTwoBlockDomain
import FV.Backend.Proof.StockMemoryStoreNopCfgFixture

namespace Backend.Stock.Memory.StoreNopCfgFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory.StoreRoots
set_option autoImplicit false
set_option Elab.async false

/-- All seven source fixtures satisfy the original memory-capable contract. -/
theorem domain (kind : Kind) : Domain (function kind) := by
  apply domain_of_two_block_nop_store_return kind kind.sourceTy (scope kind) (dominated kind)
    (by cases kind <;> rfl) rfl (entry := (function kind).blocks[0]!)
    (target := (function kind).blocks[1]!) rfl ?_ rfl (storeIndex := 1) rfl ?_ rfl
    (by simp [function]) (valueTy := kind.sourceTy) (by simp [function]) ?_ rfl
  · intro stm member
    have same : stm = ⟨[],.nop⟩ := by simpa [function] using member
    subst stm
    rfl
  · intro j stm found
    have indices : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
      have bound := lt_of_getElem? found
      simp [function] at bound
      omega
    rcases indices with rfl | rfl | rfl | rfl
    all_goals simp [function] at found; subst stm; simp
  · cases kind <;> intro h <;> first | rfl | cases h

-- witness: native_decide
/-- The complete contract coexists with a successful actual Stock run. -/
theorem domain_and_lower_witness (kind : Kind) :
    Domain (function kind) ∧ ∃ result,Stock.lower (function kind) = .ok result := by
  refine ⟨domain kind,?_⟩
  have success := lowered kind
  cases run : Stock.lower (function kind) with
  | error error => rw [run] at success; cases success
  | ok result => exact ⟨result,rfl⟩

end Backend.Stock.Memory.StoreNopCfgFixture
