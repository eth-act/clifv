module

public import FV.Backend.Proof.StockOriginalBlockOrigin
public import FV.Backend.Proof.StockJumpCode
public import FV.Backend.Proof.StockQuietBlockWitness
public import FV.Backend.Proof.StockOrdinaryCfg
public import FV.Backend.Proof.StockEntryCode

@[expose] public section

namespace Backend.Stock.Proof.ControlWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch collectOutgoing scanBlock lowerBlockCore

private abbrev function := QuietBlockWitness.function
private def jumpData : V := .data 152 15 [.data 151 0 [],.blockCalls [0]]

/-- The actual entry core in a real two-block whole-driver run ends in the
singleton jump, after its real source scan. No finite code-shape fact is assumed. -/
theorem actual_jump_core_code_witness : ∃ result ranges input core label,
    Stock.lower function = .ok result ∧ LowerScope function ∧
    Stock.buildCtx function = .ok (result.ctx,ranges,result.initial) ∧
    lowerBlockCore result.ctx result.order function function.blocks[0]! 0 ranges[0]!.1 ranges[0]!.2
      jumpData result.order.successors[0]! input = .ok core ∧
    result.order.successors[0]!.toList = [label] ∧ core.scan.isBranch = true ∧
    core.code = core.scan.output.code ++ #[.jump label] := by
  obtain ⟨result,oldEvent,oldRecord,run,scope,rest⟩ := QuietBlockWitness.actual_block_record_witness
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  obtain ⟨ranges,params,input,data,core,block,preludeCode,coreRun,assembled,build,prepared,placed,suffix⟩ :=
    OrdinaryCfg.stock_lower_original_code_origin run tag
  have expected : Coverage.blockData function function.blocks[0]!.term = .ok jumpData := by
    with_unfolding_all rfl
  have dataEq : data = jumpData := Except.ok.inj (prepared.symm.trans expected)
  rw [dataEq] at coreRun
  obtain ⟨original,st0,oldBuild,spec,view⟩ := buildCtx_source build
  have expectedRange := spec.ranges 0 function.blocks[0]! rfl
  have start : blockStart function 0 = 0 := rfl
  have length : function.blocks[0]!.body.length = 2 := rfl
  rw [start,length] at expectedRange
  have range : ranges[0]! = (0,3) := by
    simp only [getElem!_def,expectedRange]
  have placeholder : result.ctx.insts[2]? = some ⟨.op .unit,[],[],none⟩ := by
    rw [view.insts]
    exact spec.facts.term 0 function.blocks[0]! rfl
  have bound : ranges[0]!.2-1 < result.ctx.insts.size := by
    rw [range]
    exact (Array.getElem?_eq_some_iff.mp placeholder).1
  obtain ⟨label,labels,branch,code⟩ := Control.stock_jump_core_code
    (bc := ⟨10,[1,6]⟩) rfl bound coreRun
  exact ⟨result,ranges,input,core,label,run,scope,build,coreRun,labels,branch,code⟩

private theorem core_jump_branch {ctx : Ctx} {order : Order} {f : Clif.Function}
    {b : Clif.Block} {bi start stop : Nat} {data : V} {targets : Array Nat}
    {input : State} {output : LoweredBlockCore} {bc : Clif.BlockCall}
    (term : b.term = .jump bc)
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok output) :
    output.scan.isBranch = true := by
  unfold lowerBlockCore at run
  dsimp only at run
  simp only [term] at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure,Functor.map,Except.map] at run
    | split at run
  all_goals cases run; rfl

/-- The actual entry body's split has an empty branch scan chunk; outgoing
argument demand survives that chunk before the separately emitted jump. -/
theorem actual_branch_body_code_witness : ∃ result event term body,
    Stock.lower function = .ok result ∧ LowerScope function ∧
    event ∈ result.blockScans.toList ∧ event.block = 0 ∧
    SourceBodySplit function event function.blocks[0]! term body ∧ event.isBranch = true ∧
    event.output.code = body.code ∧ term.output.state.demand = term.input.demand := by
  obtain ⟨result,oldEvent,oldRecord,run,scope,rest⟩ := QuietBlockWitness.actual_block_record_witness
  obtain ⟨ranges,params,input,data,core,raw,vb,sizes,build,coreRun,assembled,events,placed,code⟩ :=
    stock_lower_entry_assembly run scope
  have zero : core.scan.block = 0 := (stock_lowerBlockCore_scanOrigin coreRun).2.2.1
  obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have same : b = function.blocks[0]! := Option.some.inj (split.block.symm.trans (by rw [zero]; rfl))
  subst b
  have branch := core_jump_branch (bc := ⟨10,[1,6]⟩) rfl coreRun
  have actual := Control.stock_branch_scan_body_code split branch
  exact ⟨result,core.scan,term,body,run,scope,events,zero,split,branch,actual⟩

/-- Source split and returned code come from the same actual original node,
including canonical ABI widths and source terminator preparation. -/
theorem actual_original_scan_assembly_witness :
    ∃ result ranges params input data core block preludeCode term body,
      Stock.lower function = .ok result ∧ LowerScope function ∧
      Stock.buildCtx function = .ok (result.ctx,ranges,result.initial) ∧
      sigParamBytes function.sig = .ok params ∧
      lowerBlockCore result.ctx result.order function function.blocks[0]! 0 ranges[0]!.1 ranges[0]!.2
        data result.order.successors[0]! input = .ok core ∧
      assembleOriginalBlock result.ctx function function.blocks[0]! 0 0 result.order.successors[0]!
        core.outgoing params core.state.uses core.code = .ok block ∧
      Coverage.blockData function function.blocks[0]!.term = .ok data ∧
      core.scan ∈ result.blockScans.toList ∧ core.scan.block = 0 ∧
      SourceBodySplit function core.scan function.blocks[0]! term body ∧
      block.insts = preludeCode ++ core.code ∧
      result.code.blocks[0]? = some {block with
        insts := block.insts.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))
        params := block.params.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))
        branchArgs := block.branchArgs.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))} := by
  obtain ⟨result,oldEvent,oldRecord,run,scope,rest⟩ := QuietBlockWitness.actual_block_record_witness
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  obtain ⟨ranges,params,input,data,core,block,preludeCode,coreRun,assembled,build,sizes,prepared,
    events,atEntry,suffix,placed⟩ := stock_lower_original_block_scan_assembly run tag
  obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have same : b = function.blocks[0]! := Option.some.inj (split.block.symm.trans (by rw [atEntry]; rfl))
  subst b
  exact ⟨result,ranges,params,input,data,core,block,preludeCode,term,body,run,scope,build,sizes,
    coreRun,assembled,prepared,events,atEntry,split,suffix,placed⟩

end Backend.Stock.Proof.ControlWitness
