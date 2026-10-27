import FV.Backend.Proof.StockMemoryContract
import FV.Backend.Proof.StockParameterInput
namespace Backend.Stock.Memory
/-- A complete actual source/Stock fixture inhabits the new variant; the load
case and its memory relation are a separate next obligation. -/
theorem existing_source_witness : Domain Proof.ParameterCfg.Fixture.function :=
  domain_of_scalar Proof.ParameterCfg.Fixture.original_domain_witness
end Backend.Stock.Memory
