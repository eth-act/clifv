import FV.Backend.Proof.StockJumpBodyRefines
import FV.Backend.Proof.StockMemoryOrdinarySourceContinuation
import FV.Backend.Proof.StockMemoryBodyNotrap

namespace Backend.Stock.Proof.Control
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm lowerBlockCore

/-- A proved ordinary body derives its actual jump contract without restricting successor blocks. -/
theorem stock_lower_ordinary_notrap_jump_body_spec {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {label bi : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.original bi)) (source : f.blocks[bi]? = some b)
    (family : ∀ stm ∈ b.body,OrdinaryBody.OrdinaryInst stm.inst) (jump : b.term = .jump bc)
    {isem : Backend.Proof.Sem} (driver : DriverSem isem) {MR : MemRelT}
    (env : Clif.Env) (cp : Clif.Program)
    (notrap : ∀ stm ∈ b.body,∀ fr cm code,instOutcome env cp fr cm stm.inst ≠ .trap code)
    (bodyRefines : ∀ event,event ∈ result.blockScans.toList → f.blocks[event.block]? = some b →
      ∃ (term : ScanRecord) (body : BlockScan),SourceBodySplit f event b term body ∧
        ∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
          ((List.range b.body.length).map (blockStart f event.block+·)) s s' →
          ∀ ρ w,GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w →
            ∃ ρ' w',seqRun isem (body.code.toList.map (·.mapRegs
              (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
                some (.fall ρ' w') ∧
              GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w') :
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
  obtain ⟨term,body,split,normal⟩ := bodyRefines core.scan events (by rw [atBlock]; exact source)
  have scanCode := (stock_branch_scan_body_code split branch).1
  have bodyCode : core.code = body.code ++ #[.jump target] := by rw [coreCode,scanCode]
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
    obtain ⟨t,left,total,continued,empty,steps,frame⟩ := OrdinaryBody.actual_ordinary_source_execution_frame
      run events split family (j := 0) (by omega) (by simpa using remaining) returned
    obtain ⟨ρ',w',executed,post⟩ := normal (0,s.frame,s.mem) (b.body.length,t.frame,t.mem)
      (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range] using steps) ρ w held
    exact ⟨t,left,ρ',w',by simpa using total,continued,empty,frame,
      frame.2.2.2.trans (atTerm.trans jump),finish ρ w ρ' w' executed,post⟩
  · intro fuel s code remaining atTerm trapped ρ w held
    rcases OrdinaryBody.actual_ordinary_source_trap_or_continue run events split family
      (j := 0) (by omega) (by simpa using remaining) trapped with failed | ⟨t,left,total,continued,empty,steps,frame⟩
    · exact False.elim ((OrdinaryBody.source_body_notrap run events split notrap
        (0,s.frame,s.mem) code)
        (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range] using failed))
    · right
      obtain ⟨ρ',w',executed,post⟩ := normal (0,s.frame,s.mem) (b.body.length,t.frame,t.mem)
        (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range] using steps) ρ w held
      exact ⟨t,left,ρ',w',by simpa using total,continued,empty,frame,
        frame.2.2.2.trans (atTerm.trans jump),finish ρ w ρ' w' executed,post⟩


end Backend.Stock.Proof.Control
