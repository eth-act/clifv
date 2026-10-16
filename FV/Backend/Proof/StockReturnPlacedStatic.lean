import FV.Backend.Proof.StockReturnStatic
import FV.Backend.Proof.StockBlockCode
namespace Backend.Stock.Proof.ReturnPlacedStaticDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ReturnStaticDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
/-- The actual retained original return occurs at an actual returned VCode
instruction position and meets SpillInstOk after final resolution. Complete
helper, pin, emitted-decision and placement certificates derive internally. -/
theorem stock_lower_return_instruction_static {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {xs : List Nat} (ret : b.term = .ret xs)
    {record : ScanRecord} (records : record ∈ event.output.records) (terminal : record.inst = event.termInst) :
    ∃ (label : Nat) (vb : VBlock) (k : Nat) (rs ps : List Reg),
      result.code.blocks[label]? = some vb ∧
      vb.insts[k]? = some ((.rets (rs.zip ps) : MInst).mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ∧
      returnPins f rs.length = some ps ∧
      SpillInstOk ((.rets (rs.zip ps) : MInst).mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) := by
  obtain ⟨rs,ps,mapped,virtual,pins,code,gen,raw,resolved⟩ :=
    stock_lower_return_record_static run scope events block ret records terminal
  obtain ⟨label,vb,before,after,placed,factor⟩ := stock_lower_record_code run events records
  refine ⟨label,vb,before.size,rs,ps,placed,?_,pins,?_⟩
  · rw [factor,code]
    simp only [Array.map_push,Array.map_empty,Array.getElem?_append,Array.size_append,Array.size_push,Array.size_empty]
    simp
  · apply resolved
    rw [code]
    simp
end Backend.Stock.Proof.ReturnPlacedStaticDraft
