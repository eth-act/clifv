import FV.Backend.Proof.StockMemoryAutoScan
import FV.Backend.Proof.StockReturnedSourceRetention

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
    (parameter : x ∈ b.params.map (·.1)) : event.ctx.defInst? x = none := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,
    label,nodeBi,data,core,build,ordered,initial,empty,parts,folded,
    final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,oldBuild,spec,view⟩ := buildCtx_source build
  have defs : event.ctx.valDef = original.valDef := by
    rw [eventEq,(stock_lowerBlockCore_scanOrigin coreRun).2.1]
    exact view.valDef
  simpa only [Ctx.defInst?,defs] using defInst_par spec.facts dominated.ssa block parameter

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
  have statement : b.body[0]? = some ⟨[z],.load .load .i32 flags x 0⟩ := by simp [singleton]
  obtain ⟨term,record,body,step,split,member,current,unsunk,actual,records,recorded,emitted⟩ :=
    stock_lower_returned_definition_emitted run scope dominated events block statement (z := z)
      (by simp) ret (by simp)
  obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events split statement current
  obtain ⟨emission,emissionRun,scan⟩ := stock_emitted_scan actual recorded emitted
  have atInst : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def,source,Option.getD_some]
  obtain ⟨r,mapped⟩ := ArithmeticBody.emission_result_mapped emissionRun (by rw [atInst,results])
  have inv := (stock_lower_record_context run scope events).1
  obtain ⟨a,rfl⟩ := inv.valueReg z r mapped
  obtain ⟨nreg,pointer⟩ := inv.typedReg x _ (inv.addr64 _ _ _ x source clif rfl)
  have noDefinition := parameter_definition run dominated events parameterBlock parameter
  have normal := stock_lower_load_scan_fall_refines_auto run scope dominated events records block statement current
    source clif results rfl mapped noDefinition pointer recorded emitted stable memorySem memoryOk
    (env := env) (cp := cp)
  have bodyRecords : body.records = [record] := by
    have scanned := split.scanned
    simp only [sourceBodyIndices,singleton,List.length_cons,List.length_nil,List.range_succ,
      List.range_zero,List.nil_append,List.map_cons,List.map_nil,List.reverse_cons,
      List.reverse_nil,List.nil_append,Nat.add_zero] at scanned
    cases scanned with
    | cons head tail =>
      cases tail
      exact congrArg (fun r => [r]) (List.mem_singleton.mp member).symm
  refine ⟨term,body,split,?_⟩
  have each : ∀ r ∈ body.records,ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block)
      isem result.final.alias (GuardedScanRel f result event.ctx event.block MR) r := by
    intro r present
    have same : r = record := by simpa only [bodyRecords,List.mem_singleton] using present
    subst r
    exact normal
  intro s s' steps ρ w held
  apply split.scanned.fall_refines each s s'
  · simpa only [sourceBodyIndices,List.reverse_reverse] using steps
  · simpa only [split.state] using held

end Backend.Stock.Memory
