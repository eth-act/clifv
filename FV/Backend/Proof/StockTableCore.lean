import FV.Backend.Proof.StockTableValues
import FV.Backend.Proof.StockConditionalCoreOrigin
import FV.Backend.Proof.StockOriginalBlockOrigin
import FV.Backend.Proof.StockRecordContext
import FV.Backend.Proof.StockSelectScanRefines

/-! The retained `br_table` emission of a real Stock lowering (#140, CB-14a).

The core of an original block whose terminator is `br_table x` retains the branch emission of its
named `lower_branch` run (`table_core_calls`, `table_core_origin`, the `br_table` forms of
`conditional_core_calls` and `conditional_core_origin`). In the actual terminator context the slot
holds `tableData x`, so for an `i32` index and at most 4096 successors the retained emission is
exactly `tableCode d ts r n`, with `n` the frontier of the core input, and the core output frontier
is `n + 2` (`stock_lower_table_core`). From values held at the emission output, the resolved
retained code stops at its `jt_sequence` on the `branchIdx` edge of the source index
(`CoreOrigin.table_values`), with the initial register file, so the guarded frame holds at the stop
world (`LastTableExecution.guarded`). -/

namespace Backend.Stock.Proof.TableBranch
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 ConditionalValues
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch collectOutgoing scanBlock

private theorem emission_origin {ctx : Ctx} {f : Clif.Function} {x : Nat}
    {dc : Clif.BlockCall} {tbl : List Clif.BlockCall} {bi ti : Nat} {targets : Array Nat}
    {input : State} {emission : BranchEmission}
    (run : emitBranch ctx f (.brTable x dc tbl) bi ti targets input = .ok emission) :
    ∃ out trace,Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets.toList]
        {input with current := some ti,color := none,base.emitted := #[]} =
        .ok (some out,emission.state,trace) ∧
      emission.code = emission.state.base.emitted := by
  unfold emitBranch at run
  dsimp only at run
  cases call : Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets.toList]
      {input with current := some ti,color := none,base.emitted := #[]} with
  | error message => simp only [call,bind,Except.bind] at run; cases run
  | ok q =>
    obtain ⟨out,next,trace⟩ := q
    simp only [call,bind,Except.bind] at run
    cases out with
    | none => simp at run
    | some out =>
      simp only [Option.isNone_some,Bool.false_eq_true,ite_false,branchCode,
        pure,Except.pure,bind,Except.bind] at run
      cases run
      exact ⟨out,trace,rfl,rfl⟩

/-- Invert the actual core of a `br_table` block once: its retained branch emission, outgoing
argument call and backward scan boundary. -/
theorem table_core_calls {ctx : Ctx} {order : Order} {f : Clif.Function}
    {b : Clif.Block} {bi start stop : Nat} {data : V} {targets : Array Nat}
    {input : State} {core : LoweredBlockCore} {x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    (term : b.term = .brTable x dc tbl)
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core) :
    ∃ (emission : BranchEmission) (afterEdges : State),
      core.branch = some emission ∧
      emitBranch {Driver.termCtx ctx (stop-1) data with tryRegs := input.tryRegs[stop-1]!}
        f (.brTable x dc tbl) bi (stop-1) targets input = .ok emission ∧
      collectOutgoing ctx order bi targets emission.state = .ok (afterEdges,core.outgoing) ∧
      core.scan.input = {afterEdges with color := some afterEdges.endColor[bi]!} ∧
      core.scan.ctx = {Driver.termCtx ctx (stop-1) data with tryRegs := input.tryRegs[stop-1]!} ∧
      core.scan.isBranch = true ∧ core.code = core.scan.output.code ++ emission.code := by
  let actualCtx : Ctx := {Driver.termCtx ctx (stop-1) data with tryRegs := input.tryRegs[stop-1]!}
  unfold lowerBlockCore at run
  dsimp only at run
  simp only [term] at run
  cases branchCall : emitBranch actualCtx f (.brTable x dc tbl) bi (stop-1) targets input with
  | error message =>
    dsimp only [actualCtx,Driver.termCtx] at branchCall
    simp only [branchCall,Functor.map,Except.map,bind,Except.bind] at run
    cases run
  | ok emission =>
    dsimp only [actualCtx,Driver.termCtx] at branchCall
    simp only [branchCall,Functor.map,Except.map,bind,Except.bind,Option.map_some,Option.getD_some] at run
    cases outgoing : collectOutgoing ctx order bi targets emission.state with
    | error message => simp only [outgoing,bind,Except.bind] at run; cases run
    | ok pair =>
      obtain ⟨next,args⟩ := pair
      simp only [outgoing,bind,Except.bind] at run
      cases scanned : scanBlock actualCtx bi (stop-1) true
          (((Array.range (stop-start)).map (start+·)).reverse.toList)
          {next with color := some next.endColor[bi]!} with
      | error message =>
        dsimp only [actualCtx,Driver.termCtx] at scanned
        simp only [scanned,bind,Except.bind] at run
        cases run
      | ok scan =>
        dsimp only [actualCtx,Driver.termCtx] at scanned
        simp only [scanned,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at run
        cases run
        exact ⟨emission,next,rfl,rfl,outgoing,rfl,rfl,rfl,rfl⟩

/-- The retained branch of the actual core of a `br_table` block is its named branch run, with the
first-match selection derived. -/
theorem table_core_origin {ctx : Ctx} {order : Order} {f : Clif.Function}
    {b : Clif.Block} {bi start stop : Nat} {data : V} {targets : Array Nat}
    {input : State} {core : LoweredBlockCore} {x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    (term : b.term = .brTable x dc tbl)
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core) :
    Nonempty (CoreOrigin
      {Driver.termCtx ctx (stop-1) data with tryRegs := input.tryRegs[stop-1]!}
      f bi (stop-1) targets input core) := by
  obtain ⟨emission,afterEdges,retained,branchCall,outgoing,scanInput,scanCtx,branchScan,combined⟩ :=
    table_core_calls term run
  obtain ⟨out,trace,call,emitted⟩ := emission_origin branchCall
  obtain ⟨selected⟩ := stock_named_branch_selection call
  exact ⟨⟨emission,out,trace,call,selected,retained,emitted,combined,branchScan⟩⟩

/-- **The retained emission of a real `br_table` block.** For an original block of a real Stock
lowering whose terminator is `br_table x` on an `i32` index with at most 4096 successors, the actual
core retains its named branch run in the actual terminator context, whose slot holds `tableData x`
and which satisfies `MappedCtxInv`. The retained code is exactly `tableCode d ts r n`, with the
successors `d :: ts`, `r` the register of `x` and `n` the frontier of the core input, and the
emission output frontier is `n + 2`. -/
theorem stock_lower_table_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {label bi : Nat}
    (tag : result.order.nodes[label]? = some (.original bi)) {b : Clif.Block}
    (block : f.blocks[bi]? = some b) {x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    (termShape : b.term = .brTable x dc tbl) (typeX : result.ctx.valueType? x = some (.int 32))
    (small : result.order.successors[label]!.size ≤ 4096) :
    ∃ (ranges : Array (Nat × Nat)) (input : State) (core : LoweredBlockCore)
      (origin : CoreOrigin {Driver.termCtx result.ctx (ranges[bi]!.2-1) (tableData x) with
          tryRegs := input.tryRegs[ranges[bi]!.2-1]!}
        f bi (ranges[bi]!.2-1) result.order.successors[label]! input core),
      Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) ∧
      lowerBlockCore result.ctx result.order f b bi ranges[bi]!.1 ranges[bi]!.2 (tableData x)
        result.order.successors[label]! input = .ok core ∧
      core.scan ∈ result.blockScans.toList ∧ core.scan.block = bi ∧
      core.scan.ctx = {Driver.termCtx result.ctx (ranges[bi]!.2-1) (tableData x) with
        tryRegs := input.tryRegs[ranges[bi]!.2-1]!} ∧
      MappedCtxInv f core.scan.ctx ∧
      core.scan.ctx.insts[ranges[bi]!.2-1]? = some ⟨tableData x,[],[],none⟩ ∧
      core.scan.ctx.valueType? x = some (.int 32) ∧
      ∃ d ts r,result.order.successors[label]!.toList = d :: ts ∧ result.ctx.valueReg? x = some r ∧
        origin.emission.code = (tableCode d ts r input.base.nextVreg).toArray ∧
        origin.emission.state.base.nextVreg = input.base.nextVreg+2 := by
  obtain ⟨ranges,params,input,data,core,raw,preludeCode,coreRun,assembled,build,sizes,prepared,
    events,atBlock,rawCode,placed⟩ := stock_lower_original_block_scan_assembly run tag
  have sourceValue : f.blocks[bi]! = b := by rw [List.getElem!_eq_getElem?_getD,block]; rfl
  rw [sourceValue] at coreRun prepared
  have expected : Coverage.blockData f b.term = .ok (tableData x) := by
    rw [termShape]
    with_unfolding_all rfl
  have dataEq := Except.ok.inj (prepared.symm.trans expected)
  subst dataEq
  obtain ⟨origin⟩ := table_core_origin termShape coreRun
  obtain ⟨emission,afterEdges,retained,branchCall,outgoing,scanInput,scanCtx,branchScan,combined⟩ :=
    table_core_calls termShape coreRun
  have inv := (stock_lower_record_context run scope events).1
  obtain ⟨original,st0,oldBuild,ctxSpec,view⟩ := buildCtx_source build
  have range : ranges[bi]! = (blockStart f bi,blockStart f bi+b.body.length+1) := by
    simp only [getElem!_def,ctxSpec.ranges bi b block]
  have placeholder : result.ctx.insts[blockStart f bi+b.body.length]? = some ⟨.op .unit,[],[],none⟩ := by
    rw [view.insts]
    exact ctxSpec.facts.term bi b block
  have bound : ranges[bi]!.2-1 < result.ctx.insts.size := by
    have inside := (Array.getElem?_eq_some_iff.mp placeholder).1
    rw [range]
    dsimp only
    omega
  have slot : core.scan.ctx.insts[ranges[bi]!.2-1]? = some ⟨tableData x,[],[],none⟩ := by
    rw [scanCtx]
    change (result.ctx.insts.set! (ranges[bi]!.2-1) ⟨tableData x,[],[],none⟩)[ranges[bi]!.2-1]? = _
    simp only [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt bound]
  have typeHere : core.scan.ctx.valueType? x = some (.int 32) := by rw [scanCtx]; exact typeX
  have slotActual := slot
  rw [scanCtx] at slotActual
  have typeActual := typeHere
  rw [scanCtx] at typeActual
  have labelsSmall : result.order.successors[label]!.toList.length ≤ 4096 := by
    simpa only [Array.length_toList] using small
  obtain ⟨d,ts,r,labelsEq,mapped,_,_,emitted,frontier⟩ := table_named_code slotActual typeActual labelsSmall origin.call
  refine ⟨ranges,input,core,origin,build,coreRun,events,atBlock,scanCtx,inv,slot,typeHere,
    d,ts,r,labelsEq,mapped,?_,frontier⟩
  rw [origin.emitted,emitted]
  simp

/-- **A table execution keeps the guarded frame.** The register file at the stop is the initial one
and the world differs only in the flags, so a guarded relation of the initial register file and
world holds at the stop world. -/
theorem LastTableExecution.guarded {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    {labels : List Label} {code : List MInst} {target : Nat} {ρ : Nat → CV} {world : Arm.ArmState}
    (execution : LastTableExecution F isem labels code target ρ world) {MR : MemRelT}
    (stable : MRStable F MR) {f : Clif.Function} {result : Result} {ctx : Ctx} {bi : Nat}
    {st : State} {s : SourcePoint} (post : GuardedScanRel f result ctx bi MR st s ρ world) :
    ∃ index inst ops prefixWorld outs endWorld,
      seqRun isem code ρ world = some (.stop index inst ops ρ prefixWorld outs endWorld (.goto target)) ∧
      index+1 = code.length ∧ GuardedScanRel f result ctx bi MR st s ρ endWorld ∧
      inst.targets = labels ∧ inst.isTerminator = true := by
  obtain ⟨index,inst,ops,prefixWorld,outs,endWorld,machine,last,nf,targets,terminal⟩ := execution
  exact ⟨index,inst,ops,prefixWorld,outs,endWorld,machine,last,
    ⟨post.1,post.2.1,stable _ _ _ _ nf post.2.2.1,post.2.2.2⟩,targets,terminal⟩

end Backend.Stock.Proof.TableBranch

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 TableBranch
set_option autoImplicit false

/-- **The retained `br_table` emission takes the edge of the source index.** For a core origin in a
context with `MappedCtxInv` whose slot holds `tableData x`, an `i32` index and at most 4096
successors, values held for the values demanded at the emission output make the resolved retained
code stop at its last instruction, the `jt_sequence` with the successors as targets, on the
`branchIdx` edge `tableTarget bits.toNat ts.length`, with the initial register file and the same
world but for the flags. This is the core form of `comparison_branch_values_last`. -/
theorem CoreOrigin.table_values {ctx : Ctx} {f : Clif.Function} {bi ti : Nat} {targets : Array Nat}
    {input : State} {core : LoweredBlockCore} (origin : CoreOrigin ctx f bi ti targets input core)
    (inv : MappedCtxInv f ctx) {x : Nat} (slot : ctx.insts[ti]? = some ⟨tableData x,[],[],none⟩)
    (typeX : ctx.valueType? x = some (.int 32)) (small : targets.size ≤ 4096)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {bits : BitVec 32} (getX : fr.getAs x .i32 = .ok bits)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ input.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < input.demand.size)
    (held : ValuesHeld (Demanded origin.emission.state) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ d ts,targets.toList = d :: ts ∧
      origin.emission.state.base.nextVreg = input.base.nextVreg+2 ∧
      (∀ m ∈ origin.emission.code.toList,∀ k ∈ vdefs m,
        input.base.nextVreg ≤ k ∧ k < origin.emission.state.base.nextVreg) ∧
      ∀ world,LastTableExecution F isem targets.toList (origin.emission.code.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))))
        (tableTarget bits.toNat ts.length) ρ world := by
  have labelsSmall : targets.toList.length ≤ 4096 := by simpa only [Array.length_toList] using small
  obtain ⟨d,ts,code,labelsEq,emitted,frontier,defs,execution⟩ :=
    table_named_values inv slot typeX labelsSmall origin.call refines getX bounded extent held
  have actual : origin.emission.code.toList = code := by
    rw [origin.emitted]
    have buffers := congrArg Array.toList emitted
    simpa only [Array.toList_append,Array.toList_empty,List.toList_toArray,List.nil_append] using buffers
  refine ⟨d,ts,labelsEq,frontier,?_,?_⟩
  · rw [actual]; exact defs
  · rw [actual]; exact execution

end Backend.Stock.Proof.ConditionalValues
