module

public import FV.Backend.Proof.StockOriginalBlockOrigin
public import FV.Backend.Proof.StockJumpCode
public import FV.Backend.Proof.StockMaskBlockRefines

@[expose] public section

namespace Backend.Stock.Proof.Control
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm lowerBlockCore

/-- The source body, original jump and returned machine block share one actual
compiler core. Return and trap continuations keep their original source fuel. -/
structure JumpBodySpec (f : Clif.Function) (result : Result) (b : Clif.Block)
    (label bi : Nat) (bc : Clif.BlockCall) (isem : Backend.Proof.Sem) (MR : MemRelT)
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
  target : Nat
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
  targets : result.order.successors[label]!.toList = [target]
  bodyCode : core.code = body.code ++ #[.jump target]
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
      t.frame.body = [] ∧ LocalBody.SourceFrameEq s t ∧ t.frame.term = .jump bc ∧
      seqRun isem (core.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
          some (.stop body.code.size (.jump target) #[] ρ' w' [] w' (.goto 0)) ∧
      GuardedScanRel f result core.scan.ctx core.scan.block MR term.output.state
        (b.body.length,t.frame,t.mem) ρ' w'
  traps : ∀ (fuel : Nat) (s : Clif.State) (code : Clif.TrapCode),
    s.frame.body = b.body → s.frame.term = b.term →
    Clif.runLoop env cp fuel s = .trapped code → ∀ ρ w,
    GuardedScanRel f result core.scan.ctx core.scan.block MR core.scan.output.state (0,s.frame,s.mem) ρ w →
    TrapRun isem (core.code.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w code ∨
    ∃ t left ρ' w',left+b.body.length = fuel ∧ Clif.runLoop env cp left t = .trapped code ∧
      t.frame.body = [] ∧ LocalBody.SourceFrameEq s t ∧ t.frame.term = .jump bc ∧
      seqRun isem (core.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
          some (.stop body.code.size (.jump target) #[] ρ' w' [] w' (.goto 0)) ∧
      GuardedScanRel f result core.scan.ctx core.scan.block MR term.output.state
        (b.body.length,t.frame,t.mem) ρ' w'

private theorem local_family {b : Clif.Block}
    (family : ∀ stm ∈ b.body,MaskBody.Family stm.inst) : ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst := by
  intro stm member
  rcases family stm member with (scalar | ⟨op,ty,x,y,shape⟩) | ⟨ty,x,shape⟩ | shape
  · exact LocalBody.LocalInst.of_pure (HighMulBody.family_pure scalar)
  all_goals simp [LocalBody.LocalInst,shape]

/-- Original scope, source syntax and the actual returned node derive the
complete body/jump machine contract. No code/scan certificate enters the input. -/
theorem stock_lower_jump_body_spec {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {label bi : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.original bi)) (source : f.blocks[bi]? = some b)
    (jump : b.term = .jump bc)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    (env : Clif.Env) (cp : Clif.Program) :
    Nonempty (JumpBodySpec f result b label bi bc isem MR env cp) := by
  obtain ⟨ranges,params,input,data,core,raw,preludeCode,coreRun,assembled,build,sizes,prepared,
    events,atBlock,rawCode,placed⟩ := stock_lower_original_block_scan_assembly run tag
  have sourceValue : f.blocks[bi]! = b := by rw [List.getElem!_eq_getElem?_getD,source]; rfl
  rw [sourceValue] at coreRun assembled prepared
  have expected : Coverage.blockData f b.term =
      .ok (.data 152 15 [.data 151 0 [],.blockCalls [0]]) := by
    rw [jump]
    with_unfolding_all rfl
  have dataEq := Except.ok.inj (prepared.symm.trans expected)
  subst data
  obtain ⟨original,st0,oldBuild,ctxSpec,view⟩ := buildCtx_source build
  have range : ranges[bi]! = (blockStart f bi,blockStart f bi+b.body.length+1) := by
    simp only [getElem!_def,ctxSpec.ranges bi b source]
  have placeholder : result.ctx.insts[blockStart f bi+b.body.length]? = some ⟨.op .unit,[],[],none⟩ := by
    rw [view.insts]
    exact ctxSpec.facts.term bi b source
  have bound : ranges[bi]!.2-1 < result.ctx.insts.size := by
    have inside := (Array.getElem?_eq_some_iff.mp placeholder).1
    rw [range]
    dsimp only
    omega
  obtain ⟨target,targets,branch,coreCode⟩ := stock_jump_core_code jump bound coreRun
  obtain ⟨term,body,split,normal,trapping⟩ := MaskBody.actual_body_refines_at_block
    run scope dominated family events (b := b) (by rw [atBlock]; exact source) refines driver stable
    (env := env) (cp := cp)
  have scanCode := (stock_branch_scan_body_code split branch).1
  have bodyCode : core.code = body.code ++ #[.jump target] := by rw [coreCode,scanCode]
  have localFamily := local_family (family b (List.mem_of_getElem? source))
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have finish : ∀ ρ w ρ' w',seqRun isem (body.code.toList.map (·.mapRegs resolve)) ρ w = some (.fall ρ' w') →
      seqRun isem (core.code.toList.map (·.mapRegs resolve)) ρ w =
        some (.stop body.code.size (.jump target) #[] ρ' w' [] w' (.goto 0)) := by
    intro ρ w ρ' w' executed
    have bodyRun : seqRun isem (core.scan.output.code.map (·.mapRegs resolve)).toList ρ w = some (.fall ρ' w') := by
      simpa only [Array.toList_map,scanCode] using executed
    obtain ⟨next,labels,executed⟩ := stock_jump_core_seq jump bound coreRun driver.toDriverSemG resolve bodyRun
    have same : next = target := (List.cons.inj (labels.symm.trans targets)).1
    subst next
    simpa only [Array.toList_map,scanCode] using executed
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
    target := target
    build := build
    sizes := sizes
    coreRun := coreRun
    assembled := assembled
    prepared := prepared
    events := events
    atBlock := atBlock
    split := split
    targets := targets
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
      frame.2.2.2.trans (atTerm.trans jump),finish ρ w ρ' w' executed,post⟩
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
        frame.2.2.2.trans (atTerm.trans jump),finish ρ w ρ' w' executed,post⟩

end Backend.Stock.Proof.Control
