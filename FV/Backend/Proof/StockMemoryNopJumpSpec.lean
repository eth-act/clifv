import FV.Backend.Proof.StockJumpBodyRefines
import FV.Backend.Proof.StockMemoryNopTrapBody

namespace Backend.Stock.Proof.Control
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm lowerBlockCore

/-- Local NOP syntax derives the actual jump contract without restricting other blocks. -/
theorem stock_lower_nop_jump_body_spec {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {label bi : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.original bi)) (source : f.blocks[bi]? = some b)
    (nops : ∀ stm ∈ b.body,stm.inst = .nop) (jump : b.term = .jump bc)
    {isem : Backend.Proof.Sem} (driver : DriverSem isem) {MR : MemRelT}
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
  obtain ⟨term,body,split,normal,trapping⟩ := Backend.Stock.Memory.stock_nop_body_with_traps
    run scope dominated events (b := b) (by rw [atBlock]; exact source) nops
    (isem := isem) (MR := MR) (env := env) (cp := cp)
  have scanCode := (stock_branch_scan_body_code split branch).1
  have bodyCode : core.code = body.code ++ #[.jump target] := by rw [coreCode,scanCode]
  have localFamily : ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst := by
    intro stm member
    simp [LocalBody.LocalInst,nops stm member]
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
