import FV.Backend.Proof.StockMemorySretCopyEntryValue
import FV.Backend.Proof.StockMemorySretCopyCheckWitness

namespace Backend.Stock.Memory.SretCopy.EntryValueFixture
open Backend.Stock.Memory.StoreRoots.ComputedFixture (function)
theorem original_captured_sret_argument_domain : SretArgumentReturnDomain function := by
  obtain ⟨result,run,checked,source,old⟩ := Backend.Stock.MemorySretCopy.Fixture.captured_sret_check_witness
  exact source.sret_arguments
end Backend.Stock.Memory.SretCopy.EntryValueFixture
namespace Backend.Stock.Memory.SretCopy.EntryValueFixture
open Backend.Stock.Memory.StoreRoots.ComputedFixture (function)
theorem original_captured_x8_argument_domain : X8ArgumentReturnDomain function := by
  obtain ⟨result,run,checked,source,old⟩ := Backend.Stock.MemorySretCopy.Fixture.captured_sret_check_witness
  apply source.x8_return_arguments
  rw [Backend.Stock.Memory.SretCopy.Fixture.captured_sret_source_shape_witness]
  rfl
end Backend.Stock.Memory.SretCopy.EntryValueFixture
