import FV.Backend.Proof.StockComparisonZeroValues
import FV.Backend.Proof.StockComparisonComputedValues
import FV.Backend.Proof.StockComparisonZeroComputedFacts

/-! Zero comparison branches on a computed operand: source branch values (#140, CB-9).

`comparison_zero_branch_values_last` with a nonconstant first operand (`NonConstantSource`) in
place of a source parameter. The branch values (`Calls.comparison_source_values`) need only the
operand type: the `cbz`/`cbnz` emission demands the operand, so the guarded post-body frame holds
it in a register, whether it is a parameter or a result of the block body. The selection of
ordinary brif needs `cc = ne` or a first operand that is not a `band` result (`NonBandSource`), and
the selection of the zero rule needs `NonConstantSource`. -/

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp Backend.Stock.Proof.ComparisonBranch
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- An operand that is not a `band` result in the original context is not one in the actual
terminator context: the terminator slot has no source instruction. -/
theorem ConditionalBodySpec.nonband_here {f : Clif.Function} {result : Result}
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp) {value : Nat}
    (band : NonBandSource result.ctx value) : NonBandSource spec.core.scan.ctx value := by
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  intro j info defined found ty a b clif
  rw [ctxEq] at defined found
  by_cases same : j = spec.ranges[bi]!.2-1
  · rw [same] at found
    change (result.ctx.insts.set! _ ⟨spec.data,[],[],none⟩)[_]? = some info at found
    rw [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self] at found
    split at found
    · cases found
      cases clif
    · cases found
  · rw [termCtx_insts_ne same] at found
    exact band j info defined found ty a b clif

/-- Original source metadata and the retained core derive the named call packet of a branch on
a direct comparison with `cc = ne` or whose first operand is not a `band` result. -/
theorem ConditionalBodySpec.comparison_zero_computed_calls {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    (origin : result.ctx.defClif? c = some (.icmp cc ty x y))
    (bandX : cc = .ne ∨ NonBandSource result.ctx x) :
    ∃ calls : ConditionalCalls.Calls spec.core.scan.ctx (spec.ranges[bi]!.2-1)
      result.order.successors[label]!.toList
      {spec.input with current := some (spec.ranges[bi]!.2-1),color := none,base.emitted := #[]}
      spec.origin.out spec.origin.emission.state,calls.source = .value c := by
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have originHere := spec.defClif_here block origin
  have bandHere := bandX.imp id spec.nonband_here
  have expected : Coverage.blockData f b.term =
      .ok (.data 152 5 [.data 151 1 [],.value c,.blockCalls [0,1]]) := by
    rw [termShape]
    with_unfolding_all rfl
  have dataEq := Except.ok.inj (spec.prepared.symm.trans expected)
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
  have slot : spec.core.scan.ctx.insts[spec.ranges[bi]!.2-1]? =
      some ⟨.data 152 5 [.data 151 1 [],.value c,.blockCalls [0,1]],[],[],none⟩ := by
    rw [ctxEq]
    change (result.ctx.insts.set! (spec.ranges[bi]!.2-1) ⟨spec.data,[],[],none⟩)[spec.ranges[bi]!.2-1]? = _
    simp only [dataEq,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt bound]
  have named : Stock.runTerm spec.core.scan.ctx "lower_branch"
      [.inst (spec.ranges[bi]!.2-1),.labels result.order.successors[label]!.toList]
      {spec.input with current := some (spec.ranges[bi]!.2-1),color := none,base.emitted := #[]} =
      .ok (some spec.origin.out,spec.origin.emission.state,spec.origin.trace) := by
    simpa only [ctxEq] using spec.origin.call
  exact ComparisonBranch.comparison_named_calls_zero_computed inv slot originHere bandHere named

/-- The actual source-correct wide `eq`/`ne` comparison branch of a nonconstant
operand with a zero constant (`cbz`/`cbnz`) stops at the last instruction
of its real buffer, with the guarded post-frame. The chosen edge is the
source truth of `icmp eq/ne x 0`: for `eq` the emitted `cbz` jumps exactly
when the operand is zero. Source context, call selection, alias/demand
bounds and the complete guarded post-frame are derived internally from the
real core. -/
theorem ConditionalBodySpec.comparison_zero_computed_branch_values_last {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    (origin : result.ctx.defClif? c = some (.icmp cc ty x y)) (wide : Bool)
    (typeX : result.ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (constantX : NonConstantSource result.ctx x) (bandX : cc = .ne ∨ NonBandSource result.ctx x)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : result.ctx.defClif? y = some (.iconst ty' k))
    (equality : cc = .eq ∨ cc = .ne) (zero : k = 0)
    {fr : Clif.Frame} {cm : Clif.Mem} {cty : Clif.Ty} {test : BitVec cty.width}
    (getC : (restrict fr (availOf f (availIn f result.ctx) spec.core.scan.block b.body.length)).getAs c cty = .ok test)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (post : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
      (b.body.length,fr,cm) ρ world) :
    ∃ index inst ops regs prefixWorld endWorld,
      seqRun isem (spec.origin.emission.code.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
        some (.stop index inst ops regs prefixWorld [] endWorld (.goto (if test != 0 then 0 else 1))) ∧
      index+1 = spec.origin.emission.code.size ∧
      GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
        (b.body.length,fr,cm) regs endWorld ∧
      inst.targets = result.order.successors[label]!.toList ∧ inst.isTerminator = true := by
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have originHere := spec.defClif_here block origin
  have constYHere := spec.defClif_here block constY
  have typeXHere : spec.core.scan.ctx.valueType? x = some (.int (if wide then 64 else 32)) := by
    rw [ctxEq]; exact typeX
  have constantXHere := spec.nonconstant_here constantX
  obtain ⟨calls,source⟩ := spec.comparison_zero_computed_calls run scope block termShape origin bandX
  have typedReads : ∀ {value : Nat} {vty : Clif.Ty} {bits : BitVec vty.width},
      (restrict fr (availOf f (availIn f result.ctx) spec.core.scan.block b.body.length)).getAs value vty =
        .ok bits → spec.core.scan.ctx.valueType? value = some (.int vty.width) := by
    intro value vty bits read
    have available := restrict_regs_isSome (by rw [getAs_ok read]; rfl)
    exact stock_lower_available_getAs_type run spec.events available post.2.1 read
  obtain ⟨emission,afterEdges,retained,branchCall,outgoing,scanInput,scanCtx,branchScan,combined⟩ :=
    conditional_core_calls termShape spec.coreRun
  have same : emission = spec.origin.emission := Option.some.inj (retained.symm.trans spec.origin.retained)
  rw [same] at outgoing
  obtain ⟨edgeBase,edgeExtent⟩ := outgoing_base_extent outgoing
  have scanBase : spec.core.scan.input.base = spec.origin.emission.state.base := by rw [scanInput]; exact edgeBase
  have scanExtent : spec.core.scan.input.demand.size = spec.origin.emission.state.demand.size := by rw [scanInput]; exact edgeExtent
  have sizes : spec.origin.emission.state.base.nextVreg = spec.input.base.nextVreg ∧
      spec.origin.emission.state.demand.size = spec.input.demand.size :=
    calls.comparison_zero_computed_bounds inv source originHere wide typeXHere constantXHere constYHere equality zero
  have termRecorded : spec.term ∈ spec.core.scan.output.records := by rw [spec.split.records]; simp
  have bounded : result.final.alias.size ≤ spec.input.base.nextVreg := by
    have actual := stock_lower_blockScanAliasBounds run spec.core.scan spec.events spec.term termRecorded
    have fresh : (scanState spec.term.input spec.term.inst).base.nextVreg = spec.term.input.base.nextVreg := by
      unfold scanState
      dsimp only
      split <;> rfl
    rw [fresh] at actual
    rw [spec.split.termInput,scanBase,sizes.1] at actual
    exact actual
  have extent : ∀ value r,spec.core.scan.ctx.valueReg? value = some r → value < spec.input.demand.size := by
    intro value r mapped
    have actual := (Extent.lower_mapped_demand_bounds run scope spec.events termRecorded mapped).1
    rw [spec.split.termInput,scanExtent,sizes.2] at actual
    exact actual
  have termDemand := (Control.stock_branch_scan_body_code spec.split spec.origin.branchScan).2
  have held : ValuesHeld (Demanded spec.origin.emission.state) spec.core.scan.ctx
      (restrict fr (availOf f (availIn f result.ctx) spec.core.scan.block b.body.length))
      (fun key => ρ (aliasNum result.final.alias key)) := by
    intro value needed val read
    have av := restrict_regs_isSome (by rw [read]; rfl)
    rw [restrict_regs_of_mem av] at read
    have mono := conditional_core_emission_demand termShape spec.coreRun spec.origin value
    have demanded : Demanded spec.term.output.state value := by
      unfold Demanded at needed ⊢
      rw [termDemand,spec.split.termInput]
      omega
    exact post.2.2.2 value ⟨demanded,av⟩ val read
  obtain ⟨yesLabel,noLabel,code,labels,fragment,execution⟩ := calls.comparison_source_values
    inv source post.2.1 getC typedReads originHere wide typeXHere refines bounded extent held
  obtain ⟨other,otherFragment,noDefs⟩ :=
    calls.comparison_zero_computed_no_defs inv source originHere wide typeXHere constantXHere constYHere equality zero
  have buffersEq := congrArg Array.toList (fragment.emitted.symm.trans otherFragment.emitted)
  simp only [Array.toList_append] at buffersEq
  have codeSame : code = other := List.append_cancel_left buffersEq
  rw [← codeSame] at noDefs
  have actualCode : spec.origin.emission.code.toList = code := by
    rw [spec.origin.emitted]
    have buffers := congrArg Array.toList fragment.emitted
    simpa only [Array.toList_append,Array.toList_empty,List.toList_toArray,List.nil_append] using buffers
  obtain ⟨index,inst,ops,regs,prefixWorld,endWorld,machine,last,nf,outside,targets,terminal⟩ := execution world
  have frame : ∀ key,regs key = ρ key := by
    intro key
    apply Sequence.stop_frame isem machine key
    intro selected member defined
    obtain ⟨raw,inside,rfl⟩ := List.mem_map.mp member
    rw [Resolved.renamed_defs,noDefs raw inside,List.map_nil] at defined
    exact List.not_mem_nil defined
  have registerEq : regs = ρ := funext frame
  refine ⟨index,inst,ops,regs,prefixWorld,endWorld,?_,?_,?_,targets.trans labels.symm,terminal⟩
  · simpa only [actualCode] using machine
  · rw [List.length_map,← actualCode,Array.length_toList] at last
    exact last
  · refine ⟨post.1,post.2.1,stable _ _ _ _ nf post.2.2.1,?_⟩
    simpa only [registerEq] using post.2.2.2

/-- An original direct wide `eq`/`ne` comparison of a nonconstant operand with
a zero constant and the guarded post-body frame execute the actual retained
`cbz`/`cbnz`. This is the zero analog of `comparison_branch_values`. -/
theorem ConditionalBodySpec.comparison_zero_computed_branch_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    (origin : result.ctx.defClif? c = some (.icmp cc ty x y)) (wide : Bool)
    (typeX : result.ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (constantX : NonConstantSource result.ctx x) (bandX : cc = .ne ∨ NonBandSource result.ctx x)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : result.ctx.defClif? y = some (.iconst ty' k))
    (equality : cc = .eq ∨ cc = .ne) (zero : k = 0)
    {fr : Clif.Frame} {cm : Clif.Mem} {cty : Clif.Ty} {test : BitVec cty.width}
    (getC : (restrict fr (availOf f (availIn f result.ctx) spec.core.scan.block b.body.length)).getAs c cty = .ok test)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (post : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
      (b.body.length,fr,cm) ρ world) :
    ∃ index inst ops regs prefixWorld endWorld,
      seqRun isem (spec.origin.emission.code.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
        some (.stop index inst ops regs prefixWorld [] endWorld (.goto (if test != 0 then 0 else 1))) ∧
      GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
        (b.body.length,fr,cm) regs endWorld ∧
      inst.targets = result.order.successors[label]!.toList ∧ inst.isTerminator = true := by
  obtain ⟨index,inst,ops,regs,prefixWorld,endWorld,machine,_,guarded,targets,terminal⟩ :=
    spec.comparison_zero_computed_branch_values_last run scope refines stable block termShape origin wide typeX
      constantX bandX constY equality zero getC post
  exact ⟨index,inst,ops,regs,prefixWorld,endWorld,machine,guarded,targets,terminal⟩

/-- The real emission of a wide `eq`/`ne` comparison branch of a nonconstant
operand with a zero constant is exactly one instruction. -/
theorem ConditionalBodySpec.comparison_zero_computed_emission_size {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    (origin : result.ctx.defClif? c = some (.icmp cc ty x y)) (wide : Bool)
    (typeX : result.ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (constantX : NonConstantSource result.ctx x) (bandX : cc = .ne ∨ NonBandSource result.ctx x)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : result.ctx.defClif? y = some (.iconst ty' k))
    (equality : cc = .eq ∨ cc = .ne) (zero : k = 0) :
    spec.origin.emission.code.size = 1 := by
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have originHere := spec.defClif_here block origin
  have constYHere := spec.defClif_here block constY
  have typeXHere : spec.core.scan.ctx.valueType? x = some (.int (if wide then 64 else 32)) := by
    rw [ctxEq]; exact typeX
  have constantXHere := spec.nonconstant_here constantX
  obtain ⟨calls,source⟩ := spec.comparison_zero_computed_calls run scope block termShape origin bandX
  rw [spec.origin.emitted]
  have actual := calls.comparison_zero_computed_emitted_size inv source originHere wide typeXHere
    constantXHere constYHere equality zero
  simpa only [Array.size_empty,Nat.zero_add] using actual

/-- The actual `cbz`/`cbnz` branch on a direct wide `eq`/`ne` comparison of a nonconstant
operand with zero defines no virtual registers. -/
theorem ConditionalBodySpec.comparison_zero_computed_branch_no_defs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    (origin : result.ctx.defClif? c = some (.icmp cc ty x y)) (wide : Bool)
    (typeX : result.ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (constantX : NonConstantSource result.ctx x) (bandX : cc = .ne ∨ NonBandSource result.ctx x)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : result.ctx.defClif? y = some (.iconst ty' k))
    (equality : cc = .eq ∨ cc = .ne) (zero : k = 0) :
    ∀ m ∈ spec.origin.emission.code.toList,vdefs m = [] := by
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have originHere := spec.defClif_here block origin
  have constYHere := spec.defClif_here block constY
  have typeXHere : spec.core.scan.ctx.valueType? x = some (.int (if wide then 64 else 32)) := by
    rw [ctxEq]; exact typeX
  have constantXHere := spec.nonconstant_here constantX
  obtain ⟨calls,source⟩ := spec.comparison_zero_computed_calls run scope block termShape origin bandX
  obtain ⟨code,fragment,noDefs⟩ :=
    calls.comparison_zero_computed_no_defs inv source originHere wide typeXHere constantXHere constYHere equality zero
  have actualCode : spec.origin.emission.code.toList = code := by
    rw [spec.origin.emitted]
    have buffers := congrArg Array.toList fragment.emitted
    simpa only [Array.toList_append,Array.toList_empty,List.toList_toArray,List.nil_append] using buffers
  rw [actualCode]
  exact noDefs

end Backend.Stock.Proof.ConditionalValues
