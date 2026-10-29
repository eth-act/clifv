module

public import FV.Backend.Proof.StockConditionalCoreOrigin
public import FV.Backend.Proof.StockOriginalBlockOrigin
public import FV.Backend.Proof.StockJumpCode
public import FV.Backend.Proof.StockMaskBlockRefines

@[expose] public section

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm lowerBlockCore

/-- The actual retained conditional core, scalar body and original source
continuation share one scan. First traps and source fuel remain exact. -/
structure ConditionalBodySpec (f : Clif.Function) (result : Result) (b : Clif.Block)
    (label bi c : Nat) (yes no : Clif.BlockCall) (isem : Backend.Proof.Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) where
  ranges : Array (Nat × Nat)
  params : List Nat
  input : State
  data : V
  core : LoweredBlockCore
  raw : VBlock
  preludeCode : Array MInst
  term : ScanRecord
  body : BlockScan
  origin : CoreOrigin
    {Driver.termCtx result.ctx (ranges[bi]!.2-1) data with tryRegs := input.tryRegs[ranges[bi]!.2-1]!}
    f bi (ranges[bi]!.2-1) result.order.successors[label]! input core
  build : Stock.buildCtx f = .ok (result.ctx,ranges,result.initial)
  sizes : sigParamBytes f.sig = .ok params
  coreRun : lowerBlockCore result.ctx result.order f b bi ranges[bi]!.1 ranges[bi]!.2
    data result.order.successors[label]! input = .ok core
  assembled : assembleOriginalBlock result.ctx f b bi label result.order.successors[label]!
    core.outgoing params core.state.uses core.code = .ok raw
  prepared : Coverage.blockData f b.term = .ok data
  events : core.scan ∈ result.blockScans.toList
  atBlock : core.scan.block = bi
  split : SourceBodySplit f core.scan b term body
  bodyCode : core.code = body.code ++ origin.emission.code
  rawCode : raw.insts = preludeCode ++ core.code
  placed : result.code.blocks[label]? = some {raw with
    insts := raw.insts.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))
    params := raw.params.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))
    branchArgs := raw.branchArgs.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))}
  returns : ∀ (fuel : Nat) (s : Clif.State) (vals : List Clif.Val) (cm : Clif.Mem),
    s.frame.body = b.body → s.frame.term = b.term →
    Clif.runLoop env cp fuel s = .returned vals cm → ∀ ρ w,
    GuardedScanRel f result core.scan.ctx core.scan.block MR core.scan.output.state (0,s.frame,s.mem) ρ w →
    ∃ t left ρ' w',left+b.body.length = fuel ∧ Clif.runLoop env cp left t = .returned vals cm ∧
      t.frame.body = [] ∧ LocalBody.SourceFrameEq s t ∧ t.frame.term = .brif c yes no ∧
      seqRun isem (body.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
          some (.fall ρ' w') ∧
      GuardedScanRel f result core.scan.ctx core.scan.block MR term.output.state
        (b.body.length,t.frame,t.mem) ρ' w'
  traps : ∀ (fuel : Nat) (s : Clif.State) (code : Clif.TrapCode),
    s.frame.body = b.body → s.frame.term = b.term →
    Clif.runLoop env cp fuel s = .trapped code → ∀ ρ w,
    GuardedScanRel f result core.scan.ctx core.scan.block MR core.scan.output.state (0,s.frame,s.mem) ρ w →
    TrapRun isem (core.code.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w code ∨
    ∃ t left ρ' w',left+b.body.length = fuel ∧ Clif.runLoop env cp left t = .trapped code ∧
      t.frame.body = [] ∧ LocalBody.SourceFrameEq s t ∧ t.frame.term = .brif c yes no ∧
      seqRun isem (body.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
          some (.fall ρ' w') ∧
      GuardedScanRel f result core.scan.ctx core.scan.block MR term.output.state
        (b.body.length,t.frame,t.mem) ρ' w'

private theorem local_family {b : Clif.Block}
    (family : ∀ stm ∈ b.body,MaskBody.Family stm.inst) : ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst := by
  intro stm member
  rcases family stm member with (scalar | ⟨op,ty,x,y,shape⟩) | ⟨ty,x,shape⟩ | shape
  · exact LocalBody.LocalInst.of_pure (HighMulBody.family_pure scalar)
  all_goals simp [LocalBody.LocalInst,shape]

/-- Original scope and the returned node derive the complete retained
conditional/body contract. Source body semantics and first traps reuse the
existing scalar scan proof; no branch-execution certificate enters the input. -/
theorem stock_lower_conditional_body_spec {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {label bi : Nat} {b : Clif.Block} {c : Nat} {yes no : Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.original bi)) (source : f.blocks[bi]? = some b)
    (termShape : b.term = .brif c yes no)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    (env : Clif.Env) (cp : Clif.Program) :
    Nonempty (ConditionalBodySpec f result b label bi c yes no isem MR env cp) := by
  obtain ⟨ranges,params,input,data,core,raw,preludeCode,coreRun,assembled,build,sizes,prepared,
    events,atBlock,rawCode,placed⟩ := stock_lower_original_block_scan_assembly run tag
  have sourceValue : f.blocks[bi]! = b := by rw [List.getElem!_eq_getElem?_getD,source]; rfl
  rw [sourceValue] at coreRun assembled prepared
  obtain ⟨origin⟩ := conditional_core_origin termShape coreRun
  obtain ⟨term,body,split,normal,trapping⟩ := MaskBody.actual_body_refines_at_block
    run scope dominated family events (b := b) (by rw [atBlock]; exact source) refines driver stable
    (env := env) (cp := cp)
  have scanCode := (Control.stock_branch_scan_body_code split origin.branchScan).1
  have bodyCode : core.code = body.code ++ origin.emission.code := by rw [origin.combined,scanCode]
  have localFamily := local_family (family b (List.mem_of_getElem? source))
  refine ⟨{
    ranges := ranges
    params := params
    input := input
    data := _
    core := core
    raw := raw
    preludeCode := preludeCode
    term := term
    body := body
    origin := origin
    build := build
    sizes := sizes
    coreRun := coreRun
    assembled := assembled
    prepared := prepared
    events := events
    atBlock := atBlock
    split := split
    bodyCode := bodyCode
    rawCode := rawCode
    placed := placed
    returns := ?_
    traps := ?_}⟩
  · intro fuel s vals cm remaining atTerm returned ρ w held
    obtain ⟨t,left,total,continued,empty,steps,frame⟩ := LocalBody.actual_local_source_execution_frame
      run events split localFamily (j := 0) (by omega) (by simpa using remaining) returned
    obtain ⟨ρ',w',executed,post⟩ := normal (0,s.frame,s.mem) (b.body.length,t.frame,t.mem)
      (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range] using steps) ρ w held
    exact ⟨t,left,ρ',w',by simpa using total,continued,empty,frame,
      frame.2.2.2.trans (atTerm.trans termShape),executed,post⟩
  · intro fuel s code remaining atTerm trapped ρ w held
    rcases LocalBody.actual_local_source_trap_or_continue run events split localFamily
      (j := 0) (by omega) (by simpa using remaining) trapped with failed | ⟨t,left,total,continued,empty,steps,frame⟩
    · left
      have failedRun := trapping (0,s.frame,s.mem) code
        (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range] using failed) ρ w held
      obtain ⟨k,i,ops,ρ',w',outs,w'',executed,coded⟩ := failedRun
      refine ⟨k,i,ops,ρ',w',outs,w'',?_,coded⟩
      rw [bodyCode,Array.toList_append,List.map_append]
      exact seqRun_append_stop isem executed
    · right
      obtain ⟨ρ',w',executed,post⟩ := normal (0,s.frame,s.mem) (b.body.length,t.frame,t.mem)
        (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range] using steps) ρ w held
      exact ⟨t,left,ρ',w',by simpa using total,continued,empty,frame,
        frame.2.2.2.trans (atTerm.trans termShape),executed,post⟩

end Backend.Stock.Proof.ConditionalValues
