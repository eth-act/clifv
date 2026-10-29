module

public import FV.Backend.Proof.StockTerminalDriver
public import FV.Backend.Proof.StockBodyScanOrigin

@[expose] public section

/-! Whole-driver terminal classification. Unsunkness and mandatory emission
are derived from actual source construction, traversal and retained scans. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Coverage Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch collectOutgoing scanBlock

private theorem core_branch {ctx : Ctx} {order : Order} {f : Clif.Function} {b : Clif.Block}
    {bi start stop : Nat} {data : V} {targets : Array Nat} {input : State} {core : LoweredBlockCore}
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core) :
    core.scan.isBranch = blockBranch b.term := by
  unfold lowerBlockCore at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; simp_all [blockBranch]

private theorem event_branch {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block}
    (block : f.blocks[event.block]? = some b) : event.isBranch = blockBranch b.term := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  have eventBlock : event.block = bi := by rw [eventEq]; exact (stock_lowerBlockCore_scanOrigin coreRun).2.2.1
  have original : f.blocks[bi]! = b := by simp only [getElem!_def,← eventBlock,block,Option.getD_some]
  rw [eventEq,core_branch coreRun,original]

/-- Every actual original return/trap scan starts unsunk and retains a mandatory
emitted step. Its record, body split, context slot and branch mode are derived. -/
theorem stock_lower_retTrap_emitted {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b) (rt : retOrTrap b.term = true) :
    ∃ (term : ScanRecord) (body : BlockScan) (step : Step),
      SourceBodySplit f event b term body ∧ term ∈ event.output.records ∧
      term.input.sunk[term.inst]! = false ∧ event.isBranch = false ∧
      term.output.step = some step ∧ step.decision = .emitted := by
  obtain ⟨original,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have same := Option.some.inj (split.block.symm.trans block)
  subst original
  have records : term ∈ event.output.records := by rw [split.records]; exact List.mem_cons_self
  have safe := (stock_lower_records_terminal_unsunk scope run events).2 term records |>.1
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,oldState,oldBuild,spec,view⟩ := buildCtx_source build
  have placeholder : result.ctx.insts[term.inst]? = some ⟨.op .unit,[],[],none⟩ := by
    rw [split.termInst,split.termIndex,view.insts]
    exact spec.facts.term event.block b block
  have unsunk : term.input.sunk[term.inst]! = false := safe term.inst
    (by simp only [getElem!_def,placeholder,Option.getD_some])
  have branch : event.isBranch = false := by
    rw [event_branch run events block]
    cases term : b.term <;> simp [term,retOrTrap,blockBranch] at rt ⊢
  have actual := split.termRun
  rw [split.termInst,branch] at actual
  have terminalUnsunk : term.input.sunk[event.termInst]! = false := by rwa [← split.termInst]
  simp only [scanInstruction,terminalUnsunk,Bool.false_eq_true,ite_false,beq_self_eq_true,
    Bool.and_false,ite_true,Bool.not_true,Bool.false_and] at actual
  cases emitted : emitInstruction event.ctx event.termInst (scanState term.input event.termInst) with
  | error e => simp only [emitted,bind,Except.bind] at actual; cases actual
  | ok emission =>
    simp only [emitted,bind,Except.bind,pure,Except.pure] at actual
    have same : term.output = emission.scan event.block event.termInst (scanState term.input event.termInst) :=
      (Except.ok.inj actual).symm
    refine ⟨term,body,⟨event.block,event.termInst,.emitted,scanState term.input event.termInst,
      emission.state,emission.results,emission.rules,emission.code⟩,split,records,unsunk,branch,?_,rfl⟩
    rw [same]; rfl

/-- Any retained record at the original terminal index is the unique head of
the actual source/body split; its emitted decision requires no caller proof. -/
theorem stock_lower_retTrap_record_emitted {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b) (rt : retOrTrap b.term = true)
    {record : ScanRecord} (records : record ∈ event.output.records) (terminal : record.inst = event.termInst) :
    ∃ step,record.output.step = some step ∧ step.decision = .emitted := by
  obtain ⟨term,body,step,split,member,unsunk,branch,recorded,emitted⟩ := stock_lower_retTrap_emitted run scope events block rt
  rw [split.records] at records
  rcases List.mem_cons.mp records with rfl | rest
  · exact ⟨step,recorded,emitted⟩
  · obtain ⟨j,stm,statement,current⟩ := split.positions record rest
    have bound : j < b.body.length := by
      by_cases bound : j < b.body.length
      · exact bound
      have outside := bound
      exfalso
      have absent : b.body[j]? = none := List.getElem?_eq_none (Nat.le_of_not_lt outside)
      rw [absent] at statement
      cases statement
    rw [terminal,split.termIndex] at current
    omega
end Backend.Stock.Proof
