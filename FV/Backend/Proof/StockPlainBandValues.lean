import FV.Backend.Proof.StockPlainBandSelection
import FV.Backend.Proof.StockPlainConditionValues
import FV.Backend.Proof.StockConditionalGuardedLast
import FV.Backend.Proof.StockComparisonZeroComputedValues

/-! Branches on a `PlainSource'` condition: source branch values (#140, CB-15).

The CB-11 plain branch values (`StockPlainConditionValues`) with `PlainSource'` in place of
`PlainSource`. Those proofs use the `band` exclusion only for the selection of ordinary `brif`
(3231); the call packet, the scalar nonzero values and the `cbnz` emission use only the comparison
exclusion, which `PlainSource'` keeps. The selection is `plain_selected'`. A `PlainSource'`
condition in the original context is one in the actual terminator context (`plain_here'`): the
terminator slot has no source instruction, and value types do not change. -/

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.PlainBranch
set_option autoImplicit false
set_option Elab.async false

/-- `parameter_source_branch_values` for a `PlainSource'` condition: the actual original condition
call cannot take the comparison path, so the scalar nonzero branch contract applies. -/
theorem plain_source_branch_values' {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cty : Clif.Ty} {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {c : Nat} {test : BitVec cty.width} (getC : fr.getAs c cty = .ok test)
    (typed : ctx.valueType? c = some (.int cty.width))
    (plain : PlainSource' ctx c)
    {conditionFuel constructFuel emitFuel : Nat}
    (enoughCondition : 400 ≤ conditionFuel) (enoughConstruct : 100 ≤ constructFuel) (enoughEmit : 30 ≤ emitFuel)
    {before middle constructed next : State} {trace conditionTrace constructTrace final : Array RuleId}
    {raw descriptor out : V} {yes no : Label}
    (conditionRun : ApplyInternal program (Stock.sem ctx) {} conditionFuel 123 650 [.value c]
      (before,trace) raw (middle,conditionTrace))
    (constructRun : ApplyInternal program (Stock.sem ctx) {} constructFuel 46 722
      [raw,.label yes,.label no] (middle,conditionTrace) descriptor (constructed,constructTrace))
    (emitRun : ApplyInternal program (Stock.sem ctx) {} emitFuel 13 242
      [descriptor] (constructed,constructTrace) out (next,final))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ before.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < before.demand.size)
    (held : ValuesHeld (Demanded middle) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ code,Frag before.base next.base code ∧
      ∀ world,BranchExecution F isem yes no (code.map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))))
        (test != 0) before.base next.base ρ world := by
  rcases ScalarSelect.stock_original_select_condition_calls inv enoughCondition conditionRun with
    ⟨helperFuel,helperTrace,enough,nonzero⟩ |
    ⟨cc,ty,a,b,origin,helperFuel,helperTrace,enough,comparison⟩
  · exact nonzero_source_branch_values inv dfg getC typed enough enoughConstruct enoughEmit
      nonzero constructRun emitRun refines bounded extent held
  · exact False.elim (plain.2 cc ty a b origin)

end Backend.Stock.Proof.ConditionalValues

namespace Backend.Stock.Proof.ConditionalCalls
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 ConditionalValues
open Backend.Stock.Proof.PlainBranch
set_option autoImplicit false
set_option Elab.async false

/-- `Calls.parameter_source_values` for a `PlainSource'` condition. -/
theorem Calls.plain_source_values' {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    {cty : Clif.Ty} {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {test : BitVec cty.width} (getC : fr.getAs c cty = .ok test)
    (typed : ctx.valueType? c = some (.int cty.width))
    (plain : PlainSource' ctx c)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ before.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < before.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ yes no code,labels = [yes,no] ∧ Frag before.base next.base code ∧
      ∀ world,BranchExecution F isem yes no (code.map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))))
        (test != 0) before.base next.base ρ world := by
  have constructMono := stock_apply_demand_mono calls.constructRun
  have emitMono := stock_apply_demand_mono calls.emitRun
  have intermediate : ValuesHeld (Demanded calls.middle) ctx fr
      (fun key => ρ (aliasNum aliases key)) := held.mono (by
    intro value needed
    have first := constructMono value
    have second := emitMono value
    unfold Demanded at needed ⊢
    omega)
  have conditionRun := calls.conditionRun
  rw [source] at conditionRun
  obtain ⟨code,fragment,execution⟩ := plain_source_branch_values' inv dfg getC typed plain
    calls.conditionEnough calls.constructEnough calls.emitEnough conditionRun
    calls.constructRun calls.emitRun refines bounded extent intermediate
  exact ⟨calls.yes,calls.no,code,calls.labels_eq,fragment,execution⟩

/-- `Calls.parameter_wide_no_defs` for a `PlainSource'` condition. -/
theorem Calls.plain_wide_no_defs' {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c) (wide : Bool)
    (typed : ctx.valueType? c = some (.int (if wide then 64 else 32)))
    (plain : PlainSource' ctx c) :
    ∃ code,Frag before.base next.base code ∧ ∀ inst ∈ code,vdefs inst = [] := by
  have conditionRun := calls.conditionRun
  rw [source] at conditionRun
  rcases ScalarSelect.stock_original_select_condition_calls inv calls.conditionEnough conditionRun with
    ⟨helperFuel,helperTrace,enough,nonzero⟩ |
    ⟨cc,ty,a,b,origin,helperFuel,helperTrace,enough,comparison⟩
  · exact nonzero_wide_no_defs inv wide typed (by omega) calls.constructEnough calls.emitEnough
      nonzero calls.constructRun calls.emitRun
  · exact False.elim (plain.2 cc ty a b origin)

/-- `Calls.parameter_wide_bounds` for a `PlainSource'` condition. -/
theorem Calls.plain_wide_bounds' {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c) (wide : Bool)
    (typed : ctx.valueType? c = some (.int (if wide then 64 else 32)))
    (plain : PlainSource' ctx c) :
    next.base.nextVreg = before.base.nextVreg ∧ next.demand.size = before.demand.size := by
  have size := (Extent.apply_demand_size calls.emitRun).trans
    ((Extent.apply_demand_size calls.constructRun).trans (Extent.apply_demand_size calls.conditionRun))
  have conditionRun := calls.conditionRun
  rw [source] at conditionRun
  rcases ScalarSelect.stock_original_select_condition_calls inv calls.conditionEnough conditionRun with
    ⟨helperFuel,helperTrace,enough,nonzero⟩ |
    ⟨cc,ty,a,b,origin,helperFuel,helperTrace,enough,comparison⟩
  · exact ⟨nonzero_wide_allocation inv wide typed (by omega) calls.constructEnough calls.emitEnough
      nonzero calls.constructRun calls.emitRun,size⟩
  · exact False.elim (plain.2 cc ty a b origin)

/-- `Calls.parameter_wide_emitted_size` for a `PlainSource'` condition. -/
theorem Calls.plain_wide_emitted_size' {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c) (wide : Bool)
    (typed : ctx.valueType? c = some (.int (if wide then 64 else 32)))
    (plain : PlainSource' ctx c) :
    next.base.emitted.size = before.base.emitted.size+1 := by
  have conditionRun := calls.conditionRun
  rw [source] at conditionRun
  rcases ScalarSelect.stock_original_select_condition_calls inv calls.conditionEnough conditionRun with
    ⟨helperFuel,helperTrace,enough,nonzero⟩ |
    ⟨cc,ty,a,b,origin,helperFuel,helperTrace,enough,comparison⟩
  · exact nonzero_wide_emitted_size inv wide typed (by omega) calls.constructEnough calls.emitEnough
      nonzero calls.constructRun calls.emitRun
  · exact False.elim (plain.2 cc ty a b origin)

/-- `Calls.parameter_wide_source_values` for a `PlainSource'` condition: source truth, real fragment and
no virtual definitions. -/
theorem Calls.plain_wide_source_values' {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    {cty : Clif.Ty} {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {test : BitVec cty.width} (getC : fr.getAs c cty = .ok test)
    (width : cty.width = 32 ∨ cty.width = 64)
    (typed : ctx.valueType? c = some (.int cty.width)) (plain : PlainSource' ctx c)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ before.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < before.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ yes no code,labels = [yes,no] ∧ Frag before.base next.base code ∧
      (∀ inst ∈ code,vdefs inst = []) ∧
      ∀ world,BranchExecution F isem yes no (code.map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))))
        (test != 0) before.base next.base ρ world := by
  obtain ⟨yes,no,code,labelsEq,fragment,execution⟩ := calls.plain_source_values' inv source
    dfg getC typed plain refines bounded extent held
  have noDefs : ∃ other,Frag before.base next.base other ∧ ∀ inst ∈ other,vdefs inst = [] := by
    rcases width with narrow | wide
    · exact calls.plain_wide_no_defs' inv source false (by simpa [narrow] using typed) plain
    · exact calls.plain_wide_no_defs' inv source true (by simpa [wide] using typed) plain
  obtain ⟨other,otherFragment,noDefs⟩ := noDefs
  have buffers := congrArg Array.toList (fragment.emitted.symm.trans otherFragment.emitted)
  simp only [Array.toList_append,List.toList_toArray] at buffers
  have same : code = other := List.append_cancel_left buffers
  rw [← same] at noDefs
  exact ⟨yes,no,code,labelsEq,fragment,noDefs,execution⟩

end Backend.Stock.Proof.ConditionalCalls

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.PlainBranch Backend.Stock.Proof.ComparisonBranch
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- A `PlainSource'` condition in the original context is one in the actual terminator context. -/
theorem ConditionalBodySpec.plain_here' {f : Clif.Function} {result : Result}
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp) {value : Nat}
    (plain : PlainSource' result.ctx value) : PlainSource' spec.core.scan.ctx value := by
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  refine ⟨?_,?_⟩
  · rintro ⟨ty,x,k,ty',imm,t,bit,band,mask,typed,bitEq⟩
    apply plain.1
    refine ⟨ty,x,k,ty',imm,t,bit,spec.defClif_back band,spec.defClif_back mask,?_,bitEq⟩
    rw [ctxEq] at typed
    exact typed
  intro cc ty a b' origin
  apply plain.2 cc ty a b'
  rcases origin with direct | ⟨target,z,extended,comparison⟩
  · exact Or.inl (spec.defClif_back direct)
  · exact Or.inr ⟨target,z,spec.defClif_back extended,spec.defClif_back comparison⟩

/-- Original source metadata and the retained core derive the named call packet of a branch on a
`PlainSource'` condition. -/
theorem ConditionalBodySpec.plain_calls' {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    (plain : PlainSource' result.ctx c) :
    ∃ calls : ConditionalCalls.Calls spec.core.scan.ctx (spec.ranges[bi]!.2-1)
      result.order.successors[label]!.toList
      {spec.input with current := some (spec.ranges[bi]!.2-1),color := none,base.emitted := #[]}
      spec.origin.out spec.origin.emission.state,calls.source = .value c := by
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have plainHere := spec.plain_here' plain
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
  exact PlainBranch.plain_named_calls' inv slot plainHere named

/-- `parameter_branch_values_last` for a `PlainSource'` condition: the actual retained `cbnz` stops at the
last instruction of its real buffer on the edge of the source truth, with the guarded
post-frame. Source context, call selection, alias/demand bounds and the complete guarded
post-frame are derived internally from the real core. -/
theorem ConditionalBodySpec.plain_branch_values_last' {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    (plain : PlainSource' result.ctx c)
    {fr : Clif.Frame} {cm : Clif.Mem} {cty : Clif.Ty} {test : BitVec cty.width}
    (getC : (restrict fr (availOf f (availIn f result.ctx) spec.core.scan.block b.body.length)).getAs c cty = .ok test)
    (width : cty.width = 32 ∨ cty.width = 64) {ρ : Nat → CV} {world : Arm.ArmState}
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
  have plainHere := spec.plain_here' plain
  obtain ⟨calls,source⟩ := spec.plain_calls' run scope block termShape plain
  have available := restrict_regs_isSome (by rw [getAs_ok getC]; rfl)
  have typed := stock_lower_available_getAs_type run spec.events available post.2.1 getC
  obtain ⟨emission,afterEdges,retained,branchCall,outgoing,scanInput,scanCtx,branchScan,combined⟩ :=
    conditional_core_calls termShape spec.coreRun
  have same : emission = spec.origin.emission := Option.some.inj (retained.symm.trans spec.origin.retained)
  rw [same] at outgoing
  obtain ⟨edgeBase,edgeExtent⟩ := outgoing_base_extent outgoing
  have scanBase : spec.core.scan.input.base = spec.origin.emission.state.base := by rw [scanInput]; exact edgeBase
  have scanExtent : spec.core.scan.input.demand.size = spec.origin.emission.state.demand.size := by rw [scanInput]; exact edgeExtent
  have sizes : spec.origin.emission.state.base.nextVreg = spec.input.base.nextVreg ∧
      spec.origin.emission.state.demand.size = spec.input.demand.size := by
    rcases width with narrow | wide
    · exact calls.plain_wide_bounds' inv source false (by simpa [narrow] using typed) plainHere
    · exact calls.plain_wide_bounds' inv source true (by simpa [wide] using typed) plainHere
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
  obtain ⟨yesLabel,noLabel,code,labels,fragment,noDefs,execution⟩ := calls.plain_wide_source_values'
    inv source post.2.1 getC width typed plainHere refines bounded extent held
  have actualCode : spec.origin.emission.code.toList = code := by
    rw [spec.origin.emitted]
    have buffers := congrArg Array.toList fragment.emitted
    simpa only [Array.toList_append,Array.toList_empty,List.toList_toArray,List.nil_append] using buffers
  obtain ⟨index,inst,ops,regs,prefixWorld,endWorld,machine,nf,outside,targets,terminal⟩ := execution world
  have frame : ∀ key,regs key = ρ key := by
    intro key
    apply Sequence.stop_frame isem machine key
    intro selected member defined
    obtain ⟨raw,inside,rfl⟩ := List.mem_map.mp member
    rw [Resolved.renamed_defs,noDefs raw inside,List.map_nil] at defined
    exact List.not_mem_nil defined
  have registerEq : regs = ρ := funext frame
  have count : spec.origin.emission.code.size = 1 := by
    rw [spec.origin.emitted]
    have size : spec.origin.emission.state.base.emitted.size = 1 := by
      rcases width with narrow | wide
      · have actual := calls.plain_wide_emitted_size' inv source false (by simpa [narrow] using typed) plainHere
        simpa only [Array.size_empty,Nat.zero_add] using actual
      · have actual := calls.plain_wide_emitted_size' inv source true (by simpa [wide] using typed) plainHere
        simpa only [Array.size_empty,Nat.zero_add] using actual
    exact size
  have machine' : seqRun isem (spec.origin.emission.code.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
      some (.stop index inst ops regs prefixWorld [] endWorld (.goto (if test != 0 then 0 else 1))) := by
    simpa only [actualCode] using machine
  have bound := (List.getElem?_eq_some_iff.mp (seqRun_stop_mem machine').1).1
  simp only [List.length_map,Array.length_toList] at bound
  refine ⟨index,inst,ops,regs,prefixWorld,endWorld,machine',by omega,?_,targets.trans labels.symm,terminal⟩
  refine ⟨post.1,post.2.1,stable _ _ _ _ nf post.2.2.1,?_⟩
  simpa only [registerEq] using post.2.2.2

/-- The real emission of a branch on a wide `PlainSource'` condition is exactly one instruction. -/
theorem ConditionalBodySpec.plain_emission_size' {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    (plain : PlainSource' result.ctx c)
    (conditionTy : result.ctx.valueType? c = some (.int 32) ∨ result.ctx.valueType? c = some (.int 64)) :
    spec.origin.emission.code.size = 1 := by
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have plainHere := spec.plain_here' plain
  obtain ⟨calls,source⟩ := spec.plain_calls' run scope block termShape plain
  rw [spec.origin.emitted]
  have size : spec.origin.emission.state.base.emitted.size = 1 := by
    rcases conditionTy with narrow | wide
    · have actual := calls.plain_wide_emitted_size' inv source false
        (by rw [ctxEq]; exact narrow) plainHere
      simpa only [Array.size_empty,Nat.zero_add] using actual
    · have actual := calls.plain_wide_emitted_size' inv source true
        (by rw [ctxEq]; exact wide) plainHere
      simpa only [Array.size_empty,Nat.zero_add] using actual
  exact size

/-- The actual `cbnz` branch on a wide `PlainSource'` condition defines no virtual registers. -/
theorem ConditionalBodySpec.plain_branch_no_defs' {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    (plain : PlainSource' result.ctx c)
    (conditionTy : result.ctx.valueType? c = some (.int 32) ∨ result.ctx.valueType? c = some (.int 64)) :
    ∀ m ∈ spec.origin.emission.code.toList,vdefs m = [] := by
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have plainHere := spec.plain_here' plain
  obtain ⟨calls,source⟩ := spec.plain_calls' run scope block termShape plain
  have wideCase : ∀ wide : Bool,spec.core.scan.ctx.valueType? c = some (.int (if wide then 64 else 32)) →
      ∀ m ∈ spec.origin.emission.code.toList,vdefs m = [] := by
    intro wide typed
    obtain ⟨code,fragment,noDefs⟩ := calls.plain_wide_no_defs' inv source wide typed plainHere
    have actualCode : spec.origin.emission.code.toList = code := by
      rw [spec.origin.emitted]
      have buffers := congrArg Array.toList fragment.emitted
      simpa only [Array.toList_append,Array.toList_empty,List.toList_toArray,List.nil_append] using buffers
    intro m member
    rw [actualCode] at member
    exact noDefs m member
  rcases conditionTy with narrow | wide
  · exact wideCase false (by rw [ctxEq]; exact narrow)
  · exact wideCase true (by rw [ctxEq]; exact wide)

end Backend.Stock.Proof.ConditionalValues
