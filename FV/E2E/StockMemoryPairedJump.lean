import FV.Backend.Proof.StockMemoryCfgJumpReturnAt
import FV.E2E.StockMemoryPairedScan
import FV.E2E.PairDriver
import FV.Backend.Proof.VCodeSemISeq

namespace E2E.StockMemory
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock Backend.Stock.Proof Backend.Stock.Proof.Control
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem pair_fall_first {sem : Sem} {ms : List MInst}
    {ρ ρ' : Nat → CV} {q q' : W2}
    (executed : seqRun (pairSem sem) ms ρ q = some (.fall ρ' q')) :
    seqRun sem ms ρ q.1 = some (.fall ρ' q'.1) := by
  exact seqRun_mapW (π := Prod.fst) (P := fun _ => True)
    (fun i _ us w outs next ctl ran => (pairSem_inv ran).1)
    ms (fun _ _ => True.intro) ρ q (.fall ρ' q') executed

private theorem paired_jump_seq (Γ : Rel) (fc : FnCtx) (X : ExtSem)
    (label : Nat) (ρ : Nat → CV) (q : W2) :
    seqRun (pairSem (csem Γ.F fc X)) [.jump label] ρ q =
      some (.stop 0 (.jump label) #[] ρ q [] q (.goto 0)) := by
  simp only [seqRun,show (MInst.jump label).operands = .ok #[] from rfl,
    show vuses (#[] : Array Operand) ρ = [] from rfl,(driverSemG_pair Γ.F fc X).jump]
  rfl

/-- A proved paired body crosses the actual jump with one shared virtual register file. -/
theorem paired_jump_body_returns_at_of_body {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b targetBlock : Clif.Block} {label bi tl : Nat} {bc : Clif.BlockCall}
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    {env : Clif.Env} {cp : Clif.Program}
    (spec : JumpBodySpec f result b label bi bc (csem Γ.F fc X) (RelW Γ f c) env cp)
    (localFamily : ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst)
    (bodyRefines : ∀ a a',SourceSteps (IndexedSourceInst env cp f spec.core.scan.ctx spec.core.scan.block)
      (sourceBodyIndices f spec.core.scan.block b).reverse a a' → ∀ ρ q,
      PairedScanRel f result spec.core.scan.ctx spec.core.scan.block Γ c D spec.body.state a ρ q → ∃ ρ' q',
        seqRun (pairSem (csem Γ.F fc X)) (spec.body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ q =
            some (.fall ρ' q') ∧
        PairedScanRel f result spec.core.scan.ctx spec.core.scan.block Γ c D spec.term.output.state a' ρ' q')
    (tag : result.order.nodes[label]? = some (.original bi))
    (jump : b.term = .jump bc)
    (targetTag : result.order.nodes[spec.target]? = some (.original tl))
    (targetIndex : blockIdx? f bc.block = some tl)
    (target : f.block? bc.block = some targetBlock)
    {next : BlockScanEvent} (nextEvent : next ∈ result.blockScans.toList) (nextBlock : next.block = tl)
    (demand : ∀ (x : Nat),next.output.state.demand[x]! ≤ spec.term.output.state.demand[x]!)
    {vals : List Clif.Val} {outMem : Clif.Mem}
    (continuation : ∀ (fuel : Nat) (s : Clif.State) (ρ : Nat → CV) (q : W2),
      s.frame.func = f → s.callers = [] → s.frame.body = targetBlock.body →
      s.frame.term = targetBlock.term → SourceDefinedAt f result.ctx tl 0 s.frame →
      Clif.runLoop env cp fuel s = .returned vals outMem →
      PairedScanRel f result next.ctx next.block Γ c D next.output.state (0,s.frame,s.mem) ρ q →
      RunOkABIAt f result.code result.edgeArgs (pairSem (csem Γ.F fc X)) (MRP Γ f c D) s.frame.slots
        ⟨spec.target,0,ρ,q⟩ (.returned vals outMem))
    {fuel : Nat} {s : Clif.State} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals outMem)
    {ρ : Nat → CV} {q : W2}
    (held : PairedScanRel f result spec.core.scan.ctx spec.core.scan.block Γ c D spec.core.scan.output.state
      (0,s.frame,s.mem) ρ q) :
    RunOkABIAt f result.code result.edgeArgs (pairSem (csem Γ.F fc X)) (MRP Γ f c D) s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,q⟩ (.returned vals outMem) := by
  have source := spec.split.block
  rw [spec.atBlock] at source
  obtain ⟨t,left,total,continued,empty,steps,frame⟩ := LocalBody.actual_local_source_execution_frame
    run spec.events spec.split localFamily (j := 0) (by omega) (by simpa using remaining) returned
  obtain ⟨ρ',q',bodyRun,postPair⟩ := bodyRefines (0,s.frame,s.mem) (b.body.length,t.frame,t.mem)
    (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range,sourceBodyIndices,List.reverse_reverse] using steps)
    ρ q (by simpa only [spec.split.state] using held)
  obtain ⟨sourceFrame,atJump,firstRun,tDefined⟩ := Inherited.jump_continuation_defined run scope dominated
    (driverSem_csem Γ.F fc X) spec jump (needed := fun _ => False)
    (by intro x impossible; cases impossible) (by simpa only [Nat.add_zero,Nat.sub_zero] using steps)
    frame atTerm (pair_fall_first bodyRun) defined
  have coreCode : spec.core.code.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) =
      spec.body.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ++ [.jump spec.target] := by
    rw [spec.bodyCode,Array.toList_append,List.map_append]
    rfl
  have executed := seqRun_append_fall_stop (pairSem (csem Γ.F fc X)) bodyRun
    (paired_jump_seq Γ fc X spec.target ρ' q')
  have executed : seqRun (pairSem (csem Γ.F fc X)) (spec.core.code.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ q =
        some (.stop spec.body.code.size (.jump spec.target) #[] ρ' q' [] q' (.goto 0)) := by
    rw [coreCode]
    simpa only [List.length_map,Array.length_toList,Nat.zero_add] using executed
  cases left with
  | zero => cases continued
  | succ left =>
    have crossing : ∃ fr',Clif.enterBlock t.frame bc = .ok fr' := by
      cases call : Clif.enterBlock t.frame bc with
      | ok fr' => exact ⟨fr',rfl⟩
      | trap code =>
        rw [Clif.runLoop_succ] at continued
        simp only [Clif.step,empty,atJump,Clif.stepTerm,call,Clif.StepResult.ofRes] at continued
        cases continued
      | stuck message =>
        rw [Clif.runLoop_succ] at continued
        simp only [Clif.step,empty,atJump,Clif.stepTerm,call,Clif.StepResult.ofRes] at continued
        cases continued
    obtain ⟨fr',crossed⟩ := crossing
    have successor : result.order.successors[label]![0]? = some spec.target := by
      have targets : result.order.successors[label]! = #[spec.target] := Array.toList_inj.mp spec.targets
      rw [targets]; rfl
    obtain ⟨ρnext,copied,nextDefined,nextHeld⟩ := direct_successor_guarded_of_demand run scope dominated
      spec.events nextEvent tag source (by simp [jump,dests]) successor targetTag targetIndex target
      spec.atBlock nextBlock postPair.1 (by simpa only [spec.atBlock] using tDefined) crossed
      (jump_successor_values_of_demand run scope dominated spec jump targetTag targetIndex target nextBlock demand postPair.1)
    obtain ⟨otherNext,copiedOther,otherDefined,otherHeld⟩ := direct_successor_guarded_of_demand run scope dominated
      spec.events nextEvent tag source (by simp [jump,dests]) successor targetTag targetIndex target
      spec.atBlock nextBlock postPair.2.1 (by simpa only [spec.atBlock] using tDefined) crossed
      (jump_successor_values_of_demand run scope dominated spec jump targetTag targetIndex target nextBlock demand postPair.2.1)
    have copiedEq : otherNext = ρnext := Option.some.inj (copiedOther.symm.trans copied)
    subst otherNext
    have nextReturned : Clif.runLoop env cp left ⟨fr',[],t.mem⟩ = .returned vals outMem := by
      rw [Clif.runLoop_succ] at continued
      have tc : t.callers = [] := frame.1.trans callers
      simpa only [Clif.step,empty,atJump,Clif.stepTerm,crossed,Clif.StepResult.ofRes,tc] using continued
    have tFunc := postPair.1.1
    obtain ⟨destination,args,regs,found,read,types,set,frEq⟩ := enterBlock_spec crossed
    have destinationEq : destination = targetBlock := by
      rw [tFunc] at found
      exact Option.some.inj (found.symm.trans target)
    have bodyEq : fr'.body = targetBlock.body := by rw [frEq,destinationEq]
    have termEq : fr'.term = targetBlock.term := by rw [frEq,destinationEq]
    have slotsEq : fr'.slots = s.frame.slots := by rw [frEq]; exact frame.2.2.1
    have finished := continuation left ⟨fr',[],t.mem⟩ ρnext q' nextHeld.1 rfl bodyEq termEq
      nextDefined nextReturned ⟨nextHeld,otherHeld,postPair.2.2⟩
    let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
    have segment : SegAt {spec.raw with
        insts := spec.raw.insts.map (·.mapRegs resolve)
        params := spec.raw.params.map resolve
        branchArgs := spec.raw.branchArgs.map resolve}
        spec.preludeCode.size (spec.core.code.toList.map (·.mapRegs resolve)) := by
      intro k hk
      have bound : k < spec.core.code.size := by simpa using hk
      simp only [spec.rawCode,Array.map_append]
      rw [Array.getElem?_append_right (by simpa only [Array.size_map] using Nat.le_add_right spec.preludeCode.size k)]
      simp only [Array.size_map,Nat.add_sub_cancel_left]
      simp [bound]
    have last : spec.preludeCode.size+spec.body.code.size+1 =
        (spec.raw.insts.map (·.mapRegs resolve)).size := by
      simp only [spec.rawCode,spec.bodyCode,Array.size_map,Array.size_append,Array.size_singleton]
      omega
    obtain ⟨ps,cfg⟩ := stock_lower_computed_cfg run scope
    have actualSuccessor : succOf result.code label 0 = some spec.target := by
      cases row : result.order.successors[label]? with
      | none =>
        simp only [getElem!_def,row,Option.getD_none] at successor
        change (#[] : Array Nat)[0]? = some spec.target at successor
        cases successor
      | some values => simpa [succOf,cfg,getElem!_def,row] using successor
    have path := seqRun_goto_starAt spec.placed segment executed last actualSuccessor
      (by simpa only [vdefUpd,writeV,List.foldl_nil,Array.toList_empty,List.filter_nil,List.zip_nil_left] using copied)
    have whole := RunOkABIAt.prefix path finished
    simpa only [slotsEq] using whole


end E2E.StockMemory
