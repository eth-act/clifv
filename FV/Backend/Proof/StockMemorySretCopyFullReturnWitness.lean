import FV.Backend.Proof.StockMemorySretCopyFullReturn
import FV.Backend.Proof.StockMemorySretCopyCheckWitness

namespace Backend.Stock.Memory.SretCopy.FullReturnFixture
open Backend.Stock.Memory.StoreRoots.ComputedFixture (function)
/-- The unchanged original captured source inhabits the stronger function contract. -/
theorem captured_sret_full_return_domain : FullReturnDomain function := by
  obtain ⟨result,run,checked,source,old⟩ := Backend.Stock.MemorySretCopy.Fixture.captured_sret_check_witness
  exact source.full_returns
end Backend.Stock.Memory.SretCopy.FullReturnFixture
