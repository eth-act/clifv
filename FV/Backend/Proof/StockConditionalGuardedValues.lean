import FV.Backend.Proof.StockConditionalBodyCalls
import FV.Backend.Proof.StockConditionalNoDefs
import FV.Backend.Proof.StockConditionalWideAllocation
import FV.Backend.Proof.StockConditionalParameterSelection
import FV.Backend.Proof.StockConditionalBodyRefines
import FV.Backend.Proof.StockConditionalCoreDemand
import FV.Backend.Proof.StockOutgoingFrame
import FV.Backend.Proof.StockAvailableTypes

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Original parameter choice and the guarded post-body frame execute the
actual retained wide branch. Source context, call selection, alias/demand bounds
and the complete guarded post-frame are derived internally from the real core.
The source getter and width identify the current source step and staged class. -/
theorem ConditionalBodySpec.parameter_branch_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    (parameter : result.ctx.defInst? c = none)
    {fr : Clif.Frame} {cm : Clif.Mem} {cty : Clif.Ty} {test : BitVec cty.width}
    (getC : (restrict fr (availOf f (availIn f result.ctx) spec.core.scan.block b.body.length)).getAs c cty = .ok test)
    (width : cty.width = 32 ∨ cty.width = 64) {ρ : Nat → CV} {world : Arm.ArmState}
    (post : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
      (b.body.length,fr,cm) ρ world) :
    ∃ index inst ops regs prefixWorld endWorld,
      seqRun isem (spec.origin.emission.code.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
        some (.stop index inst ops regs prefixWorld [] endWorld (.goto (if test != 0 then 0 else 1))) ∧
      GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
        (b.body.length,fr,cm) regs endWorld ∧
      inst.targets = result.order.successors[label]!.toList ∧ inst.isTerminator = true := by
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have parameterHere : spec.core.scan.ctx.defInst? c = none := by rw [ctxEq]; exact parameter
  obtain ⟨calls,source⟩ := spec.parameter_calls block termShape parameter
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
    · exact calls.parameter_wide_bounds inv source false (by simpa [narrow] using typed) parameterHere
    · exact calls.parameter_wide_bounds inv source true (by simpa [wide] using typed) parameterHere
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
  obtain ⟨yesLabel,noLabel,code,labels,fragment,noDefs,execution⟩ := calls.parameter_wide_source_values
    inv source post.2.1 getC width typed parameterHere refines bounded extent held
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
  refine ⟨index,inst,ops,regs,prefixWorld,endWorld,?_,?_,targets.trans labels.symm,terminal⟩
  · simpa only [actualCode] using machine
  · refine ⟨post.1,post.2.1,stable _ _ _ _ nf post.2.2.1,?_⟩
    simpa only [registerEq] using post.2.2.2

end Backend.Stock.Proof.ConditionalValues
