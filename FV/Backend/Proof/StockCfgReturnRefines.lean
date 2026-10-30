import FV.Backend.Proof.StockLocalSourceExecution
import FV.Backend.Proof.StockArithmeticTerminalDefined
import FV.Backend.Proof.StockReturnContract

/-! Original-block return composition without a single-block input restriction.
The previous theorem and its interfaces remain unchanged. -/
namespace Backend.Stock.Proof.CfgReturn
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem return_done_of_runLoop {env : Clif.Env} {cp : Clif.Program}
    {s : Clif.State} {xs : List Nat} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (empty : s.frame.body = []) (callers : s.callers = []) (term : s.frame.term = .ret xs)
    (returned : Clif.runLoop env cp fuel s = .returned vals mem) :
    Clif.stepTerm env cp s (.ret xs) = .done vals mem := by
  cases fuel with
  | zero => cases returned
  | succ fuel =>
    rw [Clif.runLoop_succ,Clif.step_term env cp s empty,term] at returned
    cases step : Clif.stepTerm env cp s (.ret xs) with
    | next t => exact False.elim ((stepTerm_ret callers).1 t step)
    | done vs cm =>
      simp only [step,Clif.Outcome.returned.injEq] at returned
      obtain ⟨rfl,rfl⟩ := returned
      rfl
    | trapped c => simp only [step] at returned; cases returned
    | stuck message => simp only [step] at returned; cases returned

private theorem factor_seg {vb : VBlock} {pre code post : Array MInst}
    (parts : vb.insts = pre ++ code ++ post) : SegAt vb pre.size code.toList := by
  intro k hk
  have bound : k < code.size := by simpa using hk
  rw [parts,Array.append_assoc,Array.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [Array.getElem?_append_left bound]
  simp [bound]

/-- Compose a proved pure body with its actual placed return segment. -/
theorem actual_local_return_refines_at_block {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block}
    (family : ∀ stm ∈ b.body, LocalBody.LocalInst stm.inst)
    {xs : List Nat} (ret : b.term = .ret xs)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {term : ScanRecord} {body : BlockScan} (split : SourceBodySplit f event b term body)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {s : Clif.State}
    (func : s.frame.func = f) (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (terminal : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx event.block 0 s.frame)
    {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel s = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR)
    (bodyRun : ∀ s s', SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block + ·)) s s' →
        ∀ ρ w, GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w → ∃ ρ' w',
          seqRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ w =
            some (.fall ρ' w') ∧
          GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w')
    {label : Nat} {vb : VBlock} {pre post : Array MInst}
    (placed : result.code.blocks[label]? = some vb)
    (code : vb.insts = pre ++ event.output.code.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ++ post) :
    ∀ ρ w, GuardedScanRel f result event.ctx event.block MR event.output.state
      (0,s.frame,s.mem) ρ w →
      RunOkABI f result.code isem MR s.frame.slots ⟨label,pre.size,ρ,w⟩ (.returned vals mem) := by
  have start : s.frame.body = b.body.drop 0 := by simpa using remaining
  obtain ⟨t,left,total,ends,empty,steps,frame⟩ := LocalBody.actual_local_source_execution_frame
    run events split family (j := 0) (by omega) start returned
  have tDefined : SourceDefinedAt f result.ctx event.block b.body.length t.frame := by
    apply ArithmeticBody.arithmetic_steps_defined run scope dominated events split.block
      (env := env) (cp := cp) (s := (0,s.frame,s.mem)) (t := (b.body.length,t.frame,t.mem))
      (j := 0) (n := b.body.length) (by omega) rfl ?_ defined
    simpa only [Nat.add_zero,Nat.sub_zero] using steps
  have tFunc : t.frame.func = f := frame.2.1.trans func
  have tCallers : t.callers = [] := frame.1.trans callers
  have tTerm : t.frame.term = .ret xs := frame.2.2.2.trans (terminal.trans ret)
  have done := return_done_of_runLoop empty tCallers tTerm ends
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have pieces : vb.insts = pre ++ body.code.map (·.mapRegs resolve) ++
      (term.output.emitted.map (·.mapRegs resolve) ++ post) := by
    simp only [code,split.code,Array.map_append,Array.append_assoc,resolve]
  have bodySeg : SegAt vb pre.size (body.code.toList.map (·.mapRegs resolve)) := by
    simpa only [Array.toList_map] using factor_seg pieces
  have termPieces : vb.insts = (pre ++ body.code.map (·.mapRegs resolve)) ++
      term.output.emitted.map (·.mapRegs resolve) ++ post := by
    simpa only [Array.append_assoc] using pieces
  have termSeg : SegAt vb (pre.size+body.code.size)
      (term.output.emitted.toList.map (·.mapRegs resolve)) := by
    simpa only [Array.size_append,Array.size_map,Array.toList_map] using factor_seg termPieces
  have termMember : term ∈ event.output.records := by rw [split.records]; exact List.mem_cons_self
  intro ρ w held
  obtain ⟨ρ',w',executed,postHeld⟩ := bodyRun (0,s.frame,s.mem) (b.body.length,t.frame,t.mem)
    (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range] using steps) ρ w held
  obtain ⟨heldFunc,dfg,memory,values⟩ := postHeld
  obtain ⟨step,rs,ps,extra,recorded,emitted,termCode,rest⟩ :=
    stock_lower_return_record_source_run_auto run scope dominated abi events split.block ret
      termMember split.termInst tFunc tCallers done tDefined values refines stable
  have nonempty : 0 < term.output.emitted.size := by rw [termCode]; exact Nat.zero_lt_succ 0
  have room : pre.size + (body.code.toList.map (·.mapRegs resolve)).length < vb.insts.size := by
    have sizes := congrArg Array.size pieces
    simp only [Array.size_append,Array.size_map] at sizes
    simp only [List.length_map,Array.length_toList]
    omega
  have path := seqRun_fall_star (vc := result.code) (sem := isem) placed bodySeg room executed
  have finished := stock_lower_return_record_runOk run scope dominated abi events split.block ret
    termMember split.termInst tFunc tCallers done tDefined values refines stable placed termSeg w' memory
  have combined := RunOkABI.prefix path (by simpa only [List.length_map,Array.length_toList] using finished)
  simpa only [frame.2.2.1] using combined


end Backend.Stock.Proof.CfgReturn
