import FV.Backend.Proof.StockTableBody
import FV.Backend.Proof.StockTableIntervals
import FV.Backend.Proof.StockBranchFreshDefs
import FV.Backend.Proof.StockConditionalCoreDemand
import FV.Backend.Proof.StockGraphEdges
import FV.Backend.Proof.StockSelectedGraph

/-! Branch values and the branch interval of a `br_table` block (#140, CB-14b).

A `br_table x dc tbl` block has `tbl.length + 1` successor labels (`table_successor_count`). For an
`i32` index and at most 4096 successors:

* The core input of a `TableBodySpec` is at or above the initial frontier, and the resolved
  register of every available value is outside the branch interval from the core input to the
  emission output (`TableBodySpec.branch_alias_outside`). The traversal core of the scan has the
  label of the block (`stock_lower_available_alias_outside_labelled_branch`), so it has the same
  successors, and `table_fixed_allocation` gives the same core input frontier.
* The resolved retained emission stops at its `jt_sequence` on the `branchIdx` edge, with the
  register file and the guarded frame of the body's end (`TableBodySpec.table_branch_values_last`).
  The emission output frontier is the core input plus two: the scan-input frontier is input + 2.
* The `jt_sequence` writes its two temporaries after the stop. They are in the branch interval, so
  the register update at the stop keeps every register outside it
  (`TableBodySpec.table_stop_update_frame`), the guarded frame
  (`TableBodySpec.guarded_of_table_update`) and every carried value
  (`TableBodySpec.table_carry_of_update`). -/

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.TableBranch
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch

/-- **A `br_table` block has one successor label per table entry and one for the default.** -/
theorem table_successor_count {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {label bi : Nat} {b : Clif.Block} {x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.original bi)) (block : f.blocks[bi]? = some b)
    (termShape : b.term = .brTable x dc tbl) :
    result.order.successors[label]!.size = tbl.length+1 := by
  have lastEntry : (dests b.term)[tbl.length]? = some ((dc :: tbl)[tbl.length]'(by simp)) := by
    simp only [termShape,dests]
    exact List.getElem?_eq_getElem _
  obtain ⟨_,_,_,_,successor,_⟩ := stock_lower_selected_successor run scope tag block lastEntry
  have lower : tbl.length < result.order.successors[label]!.size := (Array.getElem?_eq_some_iff.mp successor).1
  cases row : result.order.successors[label]? with
  | none =>
    have empty : result.order.successors[label]! = #[] := by simp only [getElem!_def,row]; rfl
    rw [empty] at lower
    simp at lower
  | some ss =>
    have actual : result.order.successors[label]! = ss := by simp only [getElem!_def,row,Option.getD_some]
    rw [actual] at lower ⊢
    have upper : ¬ tbl.length+1 < ss.size := by
      intro beyond
      obtain ⟨b',id,args,target,block',destination,_,_⟩ :=
        stock_lower_indexed_successor_origin run tag row (Array.getElem?_eq_getElem beyond)
      rw [block] at block'
      cases block'
      have length : (destinations b.term).length = tbl.length+1 := by
        simp [termShape,destinations]
      have inside := (List.getElem?_eq_some_iff.mp destination).1
      omega
    omega

/-- The emission demand is below the scan input demand of a `br_table` core. -/
theorem table_core_emission_demand {ctx : Ctx} {order : Order} {f : Clif.Function}
    {b : Clif.Block} {bi start stop : Nat} {data : V} {targets : Array Nat}
    {input : State} {core : LoweredBlockCore} {x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    (term : b.term = .brTable x dc tbl)
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core)
    (origin : CoreOrigin
      {Driver.termCtx ctx (stop-1) data with tryRegs := input.tryRegs[stop-1]!}
      f bi (stop-1) targets input core) :
    ∀ (value : Nat),origin.emission.state.demand[value]! ≤ core.scan.input.demand[value]! := by
  obtain ⟨emission,afterEdges,retained,branchCall,outgoing,scanInput,scanCtx,branchScan,combined⟩ :=
    table_core_calls term run
  have same : emission = origin.emission := Option.some.inj (retained.symm.trans origin.retained)
  intro value
  rw [scanInput,← same]
  exact CfgDemand.outgoing_demand_mono outgoing value

/-- The scan input of the retained `br_table` core is the output frontier of its emission. -/
theorem TableBodySpec.scan_input_frontier {f : Clif.Function} {result : Result} {b : Clif.Block}
    {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (termShape : b.term = .brTable x dc tbl) :
    spec.core.scan.input.base.nextVreg = spec.origin.emission.state.base.nextVreg := by
  obtain ⟨emission,afterEdges,retained,branchCall,outgoing,scanInput,scanCtx,branchScan,combined⟩ :=
    table_core_calls termShape spec.coreRun
  have same : emission = spec.origin.emission := Option.some.inj (retained.symm.trans spec.origin.retained)
  rw [same] at outgoing
  rw [scanInput]
  exact congrArg LState.nextVreg (outgoing_base_extent outgoing).1

/-- The prepared data of a `br_table x` block is `tableData x`. -/
theorem TableBodySpec.data_eq {f : Clif.Function} {result : Result} {b : Clif.Block}
    {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (termShape : b.term = .brTable x dc tbl) : spec.data = tableData x := by
  have expected : Coverage.blockData f b.term = .ok (tableData x) := by
    rw [termShape]
    with_unfolding_all rfl
  exact Except.ok.inj (spec.prepared.symm.trans expected)

/-- The terminator slot of the actual context of a `br_table x` block holds `tableData x`. -/
theorem TableBodySpec.table_slot {f : Clif.Function} {result : Result} {b : Clif.Block}
    {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brTable x dc tbl) :
    {Driver.termCtx result.ctx (spec.ranges[bi]!.2-1) spec.data with
      tryRegs := spec.input.tryRegs[spec.ranges[bi]!.2-1]!}.insts[spec.ranges[bi]!.2-1]? =
      some ⟨tableData x,[],[],none⟩ := by
  obtain ⟨original,st0,oldBuild,ctxSpec,view⟩ := buildCtx_source spec.build
  have range : spec.ranges[bi]! = (blockStart f bi,blockStart f bi+b.body.length+1) := by
    simp only [getElem!_def,ctxSpec.ranges bi b block]
  have placeholder : result.ctx.insts[blockStart f bi+b.body.length]? = some ⟨.op .unit,[],[],none⟩ := by
    rw [view.insts]
    exact ctxSpec.facts.term bi b block
  have bound : spec.ranges[bi]!.2-1 < result.ctx.insts.size := by
    have inside := (Array.getElem?_eq_some_iff.mp placeholder).1
    rw [range]
    dsimp only
    omega
  change (result.ctx.insts.set! (spec.ranges[bi]!.2-1) ⟨spec.data,[],[],none⟩)[spec.ranges[bi]!.2-1]? = _
  simp only [spec.data_eq termShape,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt bound]

/-- **The branch interval of a `TableBodySpec`.** For an `i32` index and at most 4096 successors,
the core input is at or above the initial frontier, and the resolved register of every value
available at any source point is below the core input or at or above the emission output. The
traversal core of the scan has the label of the block, so it has the same successors, and the
fixed allocation of the table rule gives it the same input frontier. -/
theorem TableBodySpec.branch_alias_outside {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brTable x dc tbl) (typeX : result.ctx.valueType? x = some (.int 32))
    (small : result.order.successors[label]!.size ≤ 4096) :
    result.initial.base.nextVreg ≤ spec.input.base.nextVreg ∧
      ∀ {bi' j y key : Nat},y ∈ availOf f (availIn f result.ctx) bi' j →
        result.ctx.valueReg? y = some (.vreg key .int) →
        aliasNum result.final.alias key < spec.input.base.nextVreg ∨
          spec.origin.emission.state.base.nextVreg ≤ aliasNum result.final.alias key := by
  obtain ⟨label',start,stop,data,input,core,labelled,coreRun,scanEq,capped,below,outside⟩ :=
    stock_lower_available_alias_outside_labelled_branch run scope dominated spec.events
  have block : f.blocks[bi]? = some b := by simpa only [spec.atBlock] using spec.split.block
  have sameLabel : label' = label := stock_blockOrder_original_unique (stock_lower_order run)
    (fun h => scope.nonempty (List.length_eq_zero_iff.mp h)) (by rw [labelled,spec.atBlock]) tag
  subst label'
  have blockEq : f.blocks[spec.core.scan.block]! = b := by
    rw [spec.atBlock,List.getElem!_eq_getElem?_getD,block]
    rfl
  rw [blockEq] at coreRun
  obtain ⟨origin⟩ := table_core_origin termShape coreRun
  obtain ⟨emission,afterEdges,retained,branchCall,outgoing,scanInput,scanCtx,branchScan,combined⟩ :=
    table_core_calls termShape coreRun
  have sameEmission : emission = origin.emission := Option.some.inj (retained.symm.trans origin.retained)
  rw [sameEmission] at outgoing
  have travOrigin := stock_lowerBlockCore_scanOrigin coreRun
  have specOrigin := stock_lowerBlockCore_scanOrigin spec.coreRun
  have ctxEq : {Driver.termCtx result.ctx (stop-1) data with tryRegs := input.tryRegs[stop-1]!} =
      {Driver.termCtx result.ctx (spec.ranges[bi]!.2-1) spec.data with
        tryRegs := spec.input.tryRegs[spec.ranges[bi]!.2-1]!} := by
    rw [← travOrigin.2.1,scanEq,specOrigin.2.1]
  have tiEq : stop-1 = spec.ranges[bi]!.2-1 := by
    rw [← travOrigin.2.2.2.1,scanEq,specOrigin.2.2.2.1]
  have travCall : Stock.runTerm {Driver.termCtx result.ctx (spec.ranges[bi]!.2-1) spec.data with
        tryRegs := spec.input.tryRegs[spec.ranges[bi]!.2-1]!} "lower_branch"
      [.inst (spec.ranges[bi]!.2-1),.labels result.order.successors[label]!.toList]
      {input with current := some (spec.ranges[bi]!.2-1),color := none,base.emitted := #[]} =
      .ok (some origin.out,origin.emission.state,origin.trace) := by
    rw [← ctxEq,← tiEq]
    exact origin.call
  have slot := spec.table_slot block termShape
  have typeHere : {Driver.termCtx result.ctx (spec.ranges[bi]!.2-1) spec.data with
      tryRegs := spec.input.tryRegs[spec.ranges[bi]!.2-1]!}.valueType? x = some (.int 32) := typeX
  have labelsSmall : result.order.successors[label]!.toList.length ≤ 4096 := by
    simpa only [Array.length_toList] using small
  have counted := table_fixed_allocation slot typeHere labelsSmall labelsSmall spec.origin.call travCall
  dsimp only at counted
  have travFrontier : core.scan.input.base.nextVreg = origin.emission.state.base.nextVreg := by
    rw [scanInput]
    exact congrArg LState.nextVreg (outgoing_base_extent outgoing).1
  rw [scanEq,spec.scan_input_frontier termShape] at travFrontier
  have sameInput : input.base.nextVreg = spec.input.base.nextVreg := by omega
  refine ⟨sameInput ▸ capped,?_⟩
  intro bi' j y key available mapped
  have away := outside available mapped
  rw [spec.scan_input_frontier termShape,sameInput] at away
  exact away

/-- **The retained `br_table` emission of a `TableBodySpec` takes the edge of the source index.**
For an `i32` index and at most 4096 successors, the guarded post-body frame executes the resolved
retained emission to its `jt_sequence`, on the `branchIdx` edge `tableTarget bits.toNat ts.length`,
with the register file of the body's end and the guarded frame at the stop world. The emission
defines only its two temporaries, the next two registers after the core input. Source context,
call selection and alias/demand bounds are derived from the real core. -/
theorem TableBodySpec.table_branch_values_last {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brTable x dc tbl)
    (typeX : result.ctx.valueType? x = some (.int 32))
    (small : result.order.successors[label]!.size ≤ 4096)
    {fr : Clif.Frame} {cm : Clif.Mem} {bits : BitVec 32}
    (getX : (restrict fr (availOf f (availIn f result.ctx) spec.core.scan.block b.body.length)).getAs x .i32 =
      .ok bits)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (post : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
      (b.body.length,fr,cm) ρ world) :
    ∃ d ts,result.order.successors[label]!.toList = d :: ts ∧
      spec.origin.emission.state.base.nextVreg = spec.input.base.nextVreg+2 ∧
      (∀ m ∈ spec.origin.emission.code.toList,∀ k ∈ vdefs m,
        spec.input.base.nextVreg ≤ k ∧ k < spec.origin.emission.state.base.nextVreg) ∧
      ∃ index inst ops prefixWorld outs endWorld,
        seqRun isem (spec.origin.emission.code.toList.map
          (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
          some (.stop index inst ops ρ prefixWorld outs endWorld (.goto (tableTarget bits.toNat ts.length))) ∧
        index+1 = spec.origin.emission.code.size ∧
        GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
          (b.body.length,fr,cm) ρ endWorld ∧
        inst.targets = result.order.successors[label]!.toList ∧ inst.isTerminator = true := by
  have specOrigin := stock_lowerBlockCore_scanOrigin spec.coreRun
  have ctxEq := specOrigin.2.1
  have inv := (stock_lower_record_context run scope spec.events).1
  rw [ctxEq] at inv
  have slot := spec.table_slot block termShape
  have typeHere : {Driver.termCtx result.ctx (spec.ranges[bi]!.2-1) spec.data with
      tryRegs := spec.input.tryRegs[spec.ranges[bi]!.2-1]!}.valueType? x = some (.int 32) := typeX
  obtain ⟨emission,afterEdges,retained,branchCall,outgoing,scanInput,scanCtx,branchScan,combined⟩ :=
    table_core_calls termShape spec.coreRun
  have same : emission = spec.origin.emission := Option.some.inj (retained.symm.trans spec.origin.retained)
  rw [same] at outgoing
  obtain ⟨edgeBase,edgeExtent⟩ := outgoing_base_extent outgoing
  have scanExtent : spec.core.scan.input.demand.size = spec.origin.emission.state.demand.size := by
    rw [scanInput]; exact edgeExtent
  have demandSize : spec.origin.emission.state.demand.size = spec.input.demand.size :=
    (Extent.named_demand_size spec.origin.call).trans rfl
  have termRecorded : spec.term ∈ spec.core.scan.output.records := by rw [spec.split.records]; simp
  have bounded : result.final.alias.size ≤ spec.input.base.nextVreg :=
    Nat.le_trans (stock_lower_allocationBounds run).1
      (spec.branch_alias_outside run scope dominated tag termShape typeX small).1
  have extent : ∀ value r,{Driver.termCtx result.ctx (spec.ranges[bi]!.2-1) spec.data with
      tryRegs := spec.input.tryRegs[spec.ranges[bi]!.2-1]!}.valueReg? value = some r →
      value < spec.input.demand.size := by
    intro value r mapped
    rw [← ctxEq] at mapped
    have actual := (Extent.lower_mapped_demand_bounds run scope spec.events termRecorded mapped).1
    rw [spec.split.termInput,scanExtent,demandSize] at actual
    exact actual
  have termDemand := (Control.stock_branch_scan_body_code spec.split spec.origin.branchScan).2
  have heldScan : ValuesHeld (Demanded spec.origin.emission.state) spec.core.scan.ctx
      (restrict fr (availOf f (availIn f result.ctx) spec.core.scan.block b.body.length))
      (fun key => ρ (aliasNum result.final.alias key)) := by
    intro value needed val read
    have av := restrict_regs_isSome (by rw [read]; rfl)
    rw [restrict_regs_of_mem av] at read
    have mono := table_core_emission_demand termShape spec.coreRun spec.origin value
    have demanded : Demanded spec.term.output.state value := by
      unfold Demanded at needed ⊢
      rw [termDemand,spec.split.termInput]
      omega
    exact post.2.2.2 value ⟨demanded,av⟩ val read
  have held : ValuesHeld (Demanded spec.origin.emission.state)
      {Driver.termCtx result.ctx (spec.ranges[bi]!.2-1) spec.data with
        tryRegs := spec.input.tryRegs[spec.ranges[bi]!.2-1]!}
      (restrict fr (availOf f (availIn f result.ctx) spec.core.scan.block b.body.length))
      (fun key => ρ (aliasNum result.final.alias key)) := by
    intro value needed
    have one := heldScan value needed
    rw [ctxEq] at one
    exact one
  obtain ⟨d,ts,labels,frontier,defs,execution⟩ :=
    spec.origin.table_values inv slot typeHere small refines getX bounded extent held
  obtain ⟨index,inst,ops,prefixWorld,outs,endWorld,machine,last,guarded,targets,terminal⟩ :=
    (execution world).guarded stable post
  refine ⟨d,ts,labels,frontier,defs,index,inst,ops,prefixWorld,outs,endWorld,machine,?_,guarded,targets,terminal⟩
  rw [last,List.length_map,Array.length_toList]

/-- The resolved form of a branch emission whose definitions are in its branch interval
defines only registers in that interval: the final aliases are below the initial frontier. -/
private theorem resolved_defs_inside {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {lo hi : Nat} (capped : result.initial.base.nextVreg ≤ lo)
    {code : List MInst} (fresh : ∀ m ∈ code,∀ d ∈ vdefs m,lo ≤ d ∧ d < hi) :
    ∀ m ∈ code.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))),
      ∀ key ∈ vdefs m,lo ≤ key ∧ key < hi := by
  intro m member key defined
  obtain ⟨raw,inside,rfl⟩ := List.mem_map.mp member
  rw [Resolved.renamed_defs] at defined
  obtain ⟨d,rawDefined,rfl⟩ := List.mem_map.mp defined
  have interval := fresh raw inside d rawDefined
  have bounded := (stock_lower_allocationBounds run).1
  have identity : aliasNum result.final.alias d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none (by omega)]
    rfl
  rw [identity]
  exact interval

/-- **The register update at the stop of a `br_table` emission keeps every register outside the
branch interval.** The stop instruction is an instruction of the resolved emission, whose
definitions are in the branch interval. -/
theorem TableBodySpec.table_stop_update_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brTable x dc tbl) (typeX : result.ctx.valueType? x = some (.int 32))
    (small : result.order.successors[label]!.size ≤ 4096)
    (freshDefs : ∀ m ∈ spec.origin.emission.code.toList,∀ d ∈ vdefs m,
      spec.input.base.nextVreg ≤ d ∧ d < spec.origin.emission.state.base.nextVreg)
    {ρ regs : Nat → CV} {world prefixWorld endWorld : Arm.ArmState} {index : Nat} {inst : MInst}
    {ops : Array Operand} {outs : List CV} {control : Ctl}
    (machine : seqRun isem (spec.origin.emission.code.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
      some (.stop index inst ops regs prefixWorld outs endWorld control)) :
    ∀ key,key < spec.input.base.nextVreg ∨ spec.origin.emission.state.base.nextVreg ≤ key →
      vdefUpd ops outs regs key = regs key := by
  have capped := (spec.branch_alias_outside run scope dominated tag termShape typeX small).1
  obtain ⟨found,operands⟩ := seqRun_stop_mem machine
  have member := List.mem_of_getElem? found
  intro key outside
  apply vdefUpd_not_mem
  intro defined
  have inside := resolved_defs_inside run capped freshDefs inst member key
    (by simpa only [vdefs,operands] using defined)
  omega

/-- **The guarded post-frame through the register update at the stop of a `br_table`
emission.** -/
theorem TableBodySpec.guarded_of_table_update {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brTable x dc tbl) (typeX : result.ctx.valueType? x = some (.int 32))
    (small : result.order.successors[label]!.size ≤ 4096)
    {st : State} {point : Nat} {fr : Clif.Frame} {cm : Clif.Mem} {ρ regs : Nat → CV} {world : Arm.ArmState}
    (post : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR st (point,fr,cm) ρ world)
    (frame : ∀ key,key < spec.input.base.nextVreg ∨ spec.origin.emission.state.base.nextVreg ≤ key →
      regs key = ρ key) :
    GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR st (point,fr,cm) regs world := by
  obtain ⟨_,outside⟩ := spec.branch_alias_outside run scope dominated tag termShape typeX small
  have mapEq := (stock_lower_record_context run scope spec.events).2.1
  refine ⟨post.1,post.2.1,post.2.2.1,?_⟩
  intro y needed v read
  obtain ⟨n,mapped,holds⟩ := post.2.2.2 y needed v read
  refine ⟨n,mapped,?_⟩
  change VHolds v (regs (aliasNum result.final.alias n))
  rw [frame _ (outside needed.2 (by rw [← mapEq]; exact mapped))]
  exact holds

/-- **The carried values through the register update at the stop of a `br_table` emission.** A
value held at the body's end, available at the block entry, keeps its register. -/
theorem TableBodySpec.table_carry_of_update {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brTable x dc tbl) (typeX : result.ctx.valueType? x = some (.int 32))
    (small : result.order.successors[label]!.size ≤ 4096)
    {needed : Nat → Prop}
    (available : ∀ y,needed y → y ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {fr : Clif.Frame} {ρ regs : Nat → CV}
    (held : ValuesHeld needed spec.core.scan.ctx fr (fun key => ρ (aliasNum result.final.alias key)))
    (frame : ∀ key,key < spec.input.base.nextVreg ∨ spec.origin.emission.state.base.nextVreg ≤ key →
      regs key = ρ key) :
    ValuesHeld needed spec.core.scan.ctx fr (fun key => regs (aliasNum result.final.alias key)) := by
  obtain ⟨_,outside⟩ := spec.branch_alias_outside run scope dominated tag termShape typeX small
  have mapEq := (stock_lower_record_context run scope spec.events).2.1
  intro y need v read
  obtain ⟨n,mapped,holds⟩ := held y need v read
  refine ⟨n,mapped,?_⟩
  change VHolds v (regs (aliasNum result.final.alias n))
  rw [frame _ (outside (available y need) (by rw [← mapEq]; exact mapped))]
  exact holds

end Backend.Stock.Proof.ConditionalValues
