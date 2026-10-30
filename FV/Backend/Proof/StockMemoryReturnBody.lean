import FV.Backend.Proof.StockMemoryAutoScan
import FV.Backend.Proof.StockMemoryReturnSpec

namespace Backend.Stock.Memory
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem parameter_definition {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b) {x : Nat}
    (parameter : x ∈ b.params.map (·.1)) : event.ctx.defInst? x = none :=
  stock_lower_source_parameter_definition run dominated events block parameter


/-- Original singleton load/return syntax derives the complete guarded body
proof, including retention, actual selection, result/pointer mappings and final
aliases. The pointer can be inherited from a different original source block.
No retained-record, selected-rule or emitted-code certificate is a premise. -/
theorem stock_single_load_return_body {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {x z : Nat} {flags : Clif.MemFlags}
    (singleton : b.body = [⟨[z],.load .load .i32 flags x 0⟩]) (ret : b.term = .ret [z])
    {pi : Nat} {pb : Clif.Block} (parameterBlock : f.blocks[pi]? = some pb)
    (parameter : x ∈ pb.params.map (·.1))
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Backend.Proof.Sem}
    {MR : MemRelT} (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR) {env : Clif.Env} {cp : Clif.Program} :
    ∃ (term : ScanRecord) (body : BlockScan),SourceBodySplit f event b term body ∧
      ∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block+·)) s s' →
        ∀ ρ w,GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w →
          ∃ ρ' w',seqRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
              some (.fall ρ' w') ∧
            GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w' := by
  obtain ⟨spec⟩ := stock_single_load_return_spec run scope dominated events block singleton ret parameterBlock parameter
  have statement : b.body[0]? = some ⟨[z],.load .load .i32 flags x 0⟩ := by simp [singleton]
  have normal := stock_lower_load_scan_fall_refines_auto run scope dominated events spec.records block statement spec.current
    spec.source spec.clif spec.results rfl spec.mapped spec.parameter spec.pointer spec.recorded spec.emitted
    stable memorySem memoryOk (env := env) (cp := cp)
  refine ⟨spec.term,spec.body,spec.split,?_⟩
  have each : ∀ r ∈ spec.body.records,ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block)
      isem result.final.alias (GuardedScanRel f result event.ctx event.block MR) r := by
    intro r present
    have same : r = spec.record := by simpa only [spec.bodyRecords,List.mem_singleton] using present
    subst r
    exact normal
  intro s s' steps ρ w held
  apply spec.split.scanned.fall_refines each s s'
  · simpa only [sourceBodyIndices,List.reverse_reverse] using steps
  · simpa only [spec.split.state] using held

end Backend.Stock.Memory
