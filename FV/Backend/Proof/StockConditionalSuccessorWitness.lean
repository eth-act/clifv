module

public import FV.Backend.Proof.StockConditionalSuccessor
public import FV.Backend.Proof.StockConditionalGuardedWitness

@[expose] public section

namespace Backend.Stock.Proof.ConditionalValues.SuccessorWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private abbrev function := ConditionalCalls.sourceFunction
private def initial : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 7 ⟨.i64,1⟩,slots := [],
  body := [],term := .brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩ }
private def after : Clif.Frame := {
  initial with regs := initial.regs.set 31 ⟨.i64,1⟩,term := .ret [31] }
private theorem empty_state {exec : Nat → State → Except String Scan}
    {before : State} {body : BlockScan} (scanned : ScansSpec exec [] before body) : body.state = before := by
  cases scanned
  rfl

/-- A complete entered, returning conditional source inhabits selected copies
with a nonempty argument vector. Actual forward traversal derives demand, real
edgeArgs performs the copy, and the next retained scan gets its guarded frame. -/
theorem selected_successor_witness (X : ExtSem) :
    ∃ result, ∃ (spec : ConditionalBodySpec function result function.blocks[0]! 0 0 7
      ⟨1,[7]⟩ ⟨2,[7]⟩ (csem (fun _ => False) ⟨0,0⟩ X)
      (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      ∃ next targetLabel ρ' index inst ops regs prefixWorld endWorld,
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      Clif.enterFunc function [⟨.i64,1⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨initial,[],Clif.Mem.empty⟩ =
        .returned [⟨.i64,1⟩] Clif.Mem.empty ∧
      Clif.enterBlock initial ⟨1,[7]⟩ = .ok after ∧
      seqRun (csem (fun _ => False) ⟨0,0⟩ X)
        (spec.origin.emission.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        (entrySeed spec.core.scan.ctx initial) Arm.ArmState.default =
          some (.stop index inst ops regs prefixWorld [] endWorld (.goto 0)) ∧
      index+1 = spec.origin.emission.code.size ∧
      next ∈ result.blockScans.toList ∧ next.block = 1 ∧
      result.order.nodes[targetLabel]? = some (.original 1) ∧
      SelectedCopyRoute result 0 0 regs targetLabel ρ' ∧
      SourceDefinedAt function result.ctx 1 0 after ∧
      GuardedScanRel function result next.ctx next.block (fun _ _ _ => True)
        next.output.state (0,after,Clif.Mem.empty) ρ' endWorld := by
  obtain ⟨result,spec,index,inst,ops,regs,prefixWorld,endWorld,run,scope,dominated,
    entered,returned,machine,before,targets,terminal⟩ :=
    GuardedWitness.executable_parameter_branch_witness X 1
  have entered : Clif.enterFunc function [⟨.i64,1⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) := rfl
  have crossed : Clif.enterBlock initial ⟨1,[7]⟩ = .ok after := rfl
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨initial,[],Clif.Mem.empty⟩ =
      .returned [⟨.i64,1⟩] Clif.Mem.empty := rfl
  have ordered : blockOrder function = .ok ⟨#[.original 0,.original 2,.original 1],#[#[2,1],#[],#[]]⟩ := by cbv
  have orderEq := Except.ok.inj ((stock_lower_order run).symm.trans ordered)
  have tag : result.order.nodes[0]? = some (.original 0) := by rw [orderEq]; rfl
  have targetTag : result.order.nodes[2]? = some (.original 1) := by rw [orderEq]; rfl
  obtain ⟨ranges,params,input,data,core,block,prelude,coreRun,assembled,build,sizes,prepared,
    event,atBlock,rawCode,placed⟩ := stock_lower_original_block_scan_assembly run targetTag
  let built := (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)
  have build : Stock.buildCtx function = .ok built := rfl
  have context : result.ctx = built.1 := congrArg Prod.fst (Except.ok.inj (spec.build.symm.trans build))
  have parameter : result.ctx.defInst? 7 = none := by rw [context]; rfl
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have parameterHere : spec.core.scan.ctx.defInst? 7 = none := by rw [ctxEq]; exact parameter
  have typed : spec.core.scan.ctx.valueType? 7 = some (.int 64) := by rw [ctxEq]; change result.ctx.valueType? 7 = _; rw [context]; rfl
  obtain ⟨calls,source⟩ := spec.parameter_calls rfl rfl parameter
  obtain ⟨code,fragment,noDefs⟩ := calls.parameter_wide_no_defs
    (stock_lower_record_context run scope spec.events).1 source true typed parameterHere
  have actualCode : spec.origin.emission.code.toList = code := by
    rw [spec.origin.emitted]
    have buffers := congrArg Array.toList fragment.emitted
    simpa only [Array.toList_append,Array.toList_empty,List.toList_toArray,List.nil_append] using buffers
  have count : spec.origin.emission.code.size = 1 := by
    rw [spec.origin.emitted]
    have actual := calls.parameter_wide_emitted_size
      (stock_lower_record_context run scope spec.events).1 source true typed parameterHere
    simpa only [Array.size_empty,Nat.zero_add] using actual
  have indexBound := (List.getElem?_eq_some_iff.mp (seqRun_stop_mem machine).1).1
  simp only [List.length_map,Array.length_toList] at indexBound
  have last : index+1 = spec.origin.emission.code.size := by omega
  have registerEq : regs = entrySeed spec.core.scan.ctx initial := by
    funext key
    apply Sequence.stop_frame _ machine key
    intro selected member defined
    rw [actualCode] at member
    obtain ⟨raw,inside,rfl⟩ := List.mem_map.mp member
    rw [Resolved.renamed_defs,noDefs raw inside,List.map_nil] at defined
    exact List.not_mem_nil defined
  have allHeld := entrySeed_entered_resolved_values run scope dominated spec.events entered
  have arguments : ValuesHeld (fun x => x ∈ ([7] : List Nat)) result.ctx initial
      (fun key => regs (aliasNum result.final.alias key)) := by
    rw [registerEq]
    intro x member value get
    obtain ⟨key,mapped,held⟩ := allHeld x trivial value get
    refine ⟨key,?_,held⟩
    rw [← (stock_lower_record_context run scope spec.events).2.1 x]
    exact mapped
  have defined := source_defined_enterFunc dominated result.ctx entered
  obtain ⟨tl,targetLabel,ρ',targetIndex,selectedTag,route,nextDefined,guarded⟩ :=
    spec.selected_successor_guarded run scope dominated tag (index := 0) (bc := ⟨1,[7]⟩) rfl
      event (by change core.scan.block = 1; exact atBlock)
      (by simpa only [atBlock] using targetTag) (by decide)
      before defined crossed arguments
  have indexOne : blockIdx? function 1 = some 1 := rfl
  have same : tl = 1 := Option.some.inj (targetIndex.symm.trans indexOne)
  subst tl
  exact ⟨result,spec,core.scan,targetLabel,ρ',index,inst,ops,regs,prefixWorld,endWorld,
    run,scope,dominated,entered,returned,crossed,machine,last,event,atBlock,selectedTag,route,nextDefined,guarded⟩

end Backend.Stock.Proof.ConditionalValues.SuccessorWitness
