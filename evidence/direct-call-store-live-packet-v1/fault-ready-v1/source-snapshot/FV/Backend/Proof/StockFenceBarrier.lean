import FV.Backend.Proof.StockFenceMetadataPositive
import FV.Backend.Proof.StockFenceRecordExact
import FV.Backend.Proof.StockPureDriverUnsunk
import FV.Backend.Proof.StockMemorySourceExecution

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

/-- Original context construction assigns every colored source a positive color. -/
theorem buildCtx_colored_positive {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial))
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (colored : Stock.colored stm.inst = true) :
    initial.entryColor[blockStart f bi+j]! ≠ 0 := by
  obtain ⟨original,st0,requests,oldBuild,alloc,finished⟩ := buildCtx_allocation build
  have spec := ctxSpec_of oldBuild
  obtain ⟨info,present,source,results⟩ := spec.facts.stmt bi b j stm block statement
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have range : ranges[bi]!.1 = blockStart f bi := by
    simp only [getElem!_def,spec.ranges bi b block,Option.getD_some]
  have positive := FenceColors.sourceMetadata_colored_positive original ranges
    (by rw [spec.func]; exact block) statement colored (by rw [range]; exact inside)
  have state := congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.2.2) finished
  dsimp only at state
  rw [state]
  change (sourceMetadata original ranges).entryColor[blockStart f bi+j]! ≠ 0
  rw [← range]
  exact positive

/-- Every actual fence record restores its genuine positive ordering color.
All metadata, source positions and retained-state facts come from the real run. -/
theorem stock_lower_fence_barrier {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} (found : event.ctx.insts[record.inst]? = some info)
    (source : info.clif = some .fence) :
    record.input.entryColor[record.inst]! ≠ 0 ∧
      record.output.state.color = some record.input.entryColor[record.inst]! := by
  obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have inBody : record ∈ body.records := by
    rw [split.records] at records
    rcases List.mem_cons.mp records with same | member
    · have different := stock_fence_source_not_term run events found source
      exact False.elim (different (by rw [same,split.termInst]))
    · exact member
  obtain ⟨j,stm,statement,current⟩ := split.positions record inBody
  obtain ⟨actual,present,original,results⟩ := ArithmeticBody.body_source_info run events split statement current
  have same : actual = info := Option.some.inj (present.symm.trans found)
  subst actual
  have fence : stm.inst = .fence := Option.some.inj (original.symm.trans source)
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  have positive := buildCtx_colored_positive build split.block statement (by rw [fence]; rfl)
  have colors := (((stock_lower_zeroColorLe run).2 event events).2 record records).1.1
  have beforePositive : record.input.entryColor[record.inst]! ≠ 0 := by
    rw [colors,current]
    exact positive
  obtain ⟨step,recorded,emitted,resultRegs,last,code,frame⟩ :=
    stock_lower_fence_record_exact run scope events records found source
  refine ⟨beforePositive,?_⟩
  rw [frame]
  simp only [scanState,show (record.input.entryColor[record.inst]! != 0) = true from by
    simpa only [bne_iff_ne] using beforePositive,ite_true]

/-- An effect accepted immediately after a real fence uses its adjacent color.
Unresolved deferred effects remain explicit; this theorem does not erase them. -/
theorem stock_lower_fence_effect_color {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} (found : event.ctx.insts[record.inst]? = some info)
    (original : info.clif = some .fence) {v i : Nat}
    (accepted : Stock.source event.ctx record.output.state v = some (i,true))
    (effect : record.output.state.entryColor[i]! ≠ 0) :
    record.input.entryColor[record.inst]! = record.input.entryColor[i]!+1 := by
  have boundary := (stock_lower_fence_barrier run scope events records found original).2
  have adjacent := (source_effect_eligible accepted effect).2.2.2
  have colors := (stock_scan_zeroColorLe (stock_fence_record_execute run events records)).1
  rw [boundary,colors] at adjacent
  exact Option.some.inj adjacent

end Backend.Stock.Proof
