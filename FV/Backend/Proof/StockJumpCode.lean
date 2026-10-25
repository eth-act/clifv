import FV.Backend.Proof.StockControlShape
import FV.Backend.Proof.StockCoreScanOrigin
import FV.Backend.Proof.StockBodyScanOrigin

namespace Backend.Stock.Proof.Control
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch collectOutgoing scanBlock lowerBlockCore

/-- The real jump branch emitter produces exactly its singleton jump. -/
theorem stock_emit_jump_code {ctx : Ctx} {f : Clif.Function} {bc : Clif.BlockCall}
    {bi ti : Nat} {fields : List V} {targets : Array Nat} {input : State} {output : BranchEmission}
    (slot : ctx.insts[ti]? = some ⟨.data 152 15 fields,[],[],none⟩)
    (run : emitBranch ctx f (.jump bc) bi ti targets input = .ok output) :
    ∃ label,targets.toList = [label] ∧ output.code = #[.jump label] := by
  let before : State := {input with current := some ti,color := none,base.emitted := #[]}
  unfold emitBranch at run
  change (do
    let (v,next,fired) ← Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets.toList] before
    if v.isNone then throw s!"no lowering rule for terminator {repr (Clif.Terminator.jump bc)}"
    let code ← branchCode f (.jump bc) targets next.base.emitted
    pure (⟨next,code,⟨bi,ti,.emitted,before,next,[],fired,code⟩,fired⟩ : BranchEmission)) = .ok output at run
  cases call : Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets.toList] before with
  | error e => simp only [call,bind,Except.bind] at run; cases run
  | ok q =>
    obtain ⟨v,next,fired⟩ := q
    simp only [call,bind,Except.bind] at run
    cases v with
    | none => simp at run
    | some v =>
      simp only [Option.isNone_some,Bool.false_eq_true,ite_false,branchCode,
        bind,Except.bind,pure,Except.pure] at run
      cases run
      obtain ⟨label,labels,state,_,_⟩ := stock_named_jump_shape slot call
      refine ⟨label,labels,?_⟩
      rw [state]
      rfl

/-- Actual original jump block code is the real scan followed by one jump. -/
theorem stock_jump_core_code {ctx : Ctx} {order : Order} {f : Clif.Function}
    {b : Clif.Block} {bi start stop : Nat} {fields : List V} {targets : Array Nat}
    {input : State} {output : LoweredBlockCore} {bc : Clif.BlockCall}
    (term : b.term = .jump bc) (bound : stop-1 < ctx.insts.size)
    (run : lowerBlockCore ctx order f b bi start stop (.data 152 15 fields) targets input = .ok output) :
    ∃ label,targets.toList = [label] ∧ output.scan.isBranch = true ∧
      output.code = output.scan.output.code ++ #[.jump label] := by
  let actualCtx : Ctx := {ctx with
    insts := ctx.insts.set! (stop-1) ⟨.data 152 15 fields,[],[],none⟩
    tryRegs := input.tryRegs[stop-1]!}
  have slot : actualCtx.insts[stop-1]? =
      some ⟨.data 152 15 fields,[],[],none⟩ := by
    simp only [actualCtx,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt bound]
  unfold lowerBlockCore at run
  dsimp only at run
  simp only [term] at run
  cases branchCall : emitBranch actualCtx f (.jump bc) bi (stop-1) targets input with
  | error message =>
    dsimp only [actualCtx] at branchCall
    simp only [branchCall,Functor.map,Except.map,bind,Except.bind] at run
    cases run
  | ok emission =>
    dsimp only [actualCtx] at branchCall
    simp only [branchCall,Functor.map,Except.map,bind,Except.bind,Option.map_some,Option.getD_some] at run
    cases outgoing : collectOutgoing ctx order bi targets emission.state with
    | error message => simp only [outgoing,bind,Except.bind] at run; cases run
    | ok pair =>
      obtain ⟨next,args⟩ := pair
      simp only [outgoing,bind,Except.bind] at run
      cases scanned : scanBlock actualCtx bi (stop-1) true
          (((Array.range (stop-start)).map (start+·)).reverse.toList)
          {next with color := some next.endColor[bi]!} with
      | error message =>
        dsimp only [actualCtx] at scanned
        simp only [scanned,bind,Except.bind] at run
        cases run
      | ok scan =>
        dsimp only [actualCtx] at scanned
        simp only [scanned,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at run
        cases run
        obtain ⟨label,labels,code⟩ := stock_emit_jump_code slot branchCall
        exact ⟨label,labels,rfl,by simp only [code]⟩

/-- Branch terminator scans contribute no body code and preserve outgoing
source demand. The separately emitted branch remains the actual terminator. -/
theorem stock_branch_scan_body_code {f : Clif.Function} {event : BlockScanEvent}
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body) (branch : event.isBranch = true) :
    event.output.code = body.code ∧ term.output.state.demand = term.input.demand := by
  have scanned := split.termRun
  rw [split.termInst] at scanned
  unfold scanInstruction at scanned
  have emptyAndDemand : term.output.emitted = #[] ∧ term.output.state.demand = term.input.demand := by
    split at scanned
    · have same := Except.ok.inj scanned
      exact ⟨(congrArg Scan.emitted same).symm,(congrArg (fun out : Scan => out.state.demand) same).symm⟩
    · simp only [beq_self_eq_true,branch,Bool.true_and,ite_true] at scanned
      have same := Except.ok.inj scanned
      constructor
      · exact (congrArg Scan.emitted same).symm
      · rw [← same]
        change (scanState term.input event.termInst).demand = term.input.demand
        unfold scanState
        dsimp only
        split <;> rfl
  exact ⟨by rw [split.code,emptyAndDemand.1,Array.append_empty],emptyAndDemand.2⟩

end Backend.Stock.Proof.Control
