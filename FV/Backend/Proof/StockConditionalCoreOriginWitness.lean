import FV.Backend.Proof.StockConditionalCoreOrigin
import FV.Backend.Proof.StockConditionalCallsWitness
import FV.Backend.Proof.StockOriginalBlockOrigin
import FV.Backend.Proof.StockEntryCode

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

/-- A complete original-scope conditional source inhabits the retained core
origin theorem at its real entry, with actual backward scan and branch state.
This uses the whole driver result rather than a separately executed helper. -/
theorem conditional_core_origin_witness :
    ∃ (result : Result) (ranges : Array (Nat × Nat)) (input : State) (data : V)
      (core : LoweredBlockCore),
      Stock.lower ConditionalCalls.sourceFunction = .ok result ∧
      LowerScope ConditionalCalls.sourceFunction ∧ Dominated ConditionalCalls.sourceFunction ∧
      lowerBlockCore result.ctx result.order ConditionalCalls.sourceFunction
        ConditionalCalls.sourceFunction.blocks[0]! 0 ranges[0]!.1 ranges[0]!.2
        data result.order.successors[0]! input = .ok core ∧
      core.scan ∈ result.blockScans.toList ∧
      Nonempty (CoreOrigin
        {Driver.termCtx result.ctx (ranges[0]!.2-1) data with tryRegs := input.tryRegs[ranges[0]!.2-1]!}
        ConditionalCalls.sourceFunction 0 (ranges[0]!.2-1) result.order.successors[0]! input core) := by
  obtain ⟨result,out,next,trace,run,scope,dominated,_⟩ := ConditionalCalls.source_calls_fixture_witness
  have tag := (stock_lower_entry_code run scope).1
  obtain ⟨ranges,params,input,data,core,block,preludeCode,coreRun,assembled,build,sizes,prepared,
    events,atBlock,rawCode,placed⟩ := stock_lower_original_block_scan_assembly run tag
  have term : ConditionalCalls.sourceFunction.blocks[0]!.term = .brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩ := rfl
  exact ⟨result,ranges,input,data,core,run,scope,dominated,coreRun,events,
    conditional_core_origin term coreRun⟩

end Backend.Stock.Proof.ConditionalValues
