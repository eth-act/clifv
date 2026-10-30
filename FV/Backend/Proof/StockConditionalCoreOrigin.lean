import FV.Backend.Proof.DriverCheck
import FV.Backend.Proof.IselExtern
import FV.Backend.Proof.RegallocCSem
import FV.Backend.Proof.StockBranchSelection

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch collectOutgoing scanBlock

/-- The conditional terminator retained by an actual core is exactly its named
branch run and emitted buffer, before outgoing demands and the backward scan.
No independently supplied branch-code or call certificate is needed. -/
structure CoreOrigin (ctx : Ctx) (f : Clif.Function) (bi ti : Nat)
    (targets : Array Nat) (input : State) (core : LoweredBlockCore) where
  emission : BranchEmission
  out : V
  trace : List RuleId
  call : Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets.toList]
    {input with current := some ti,color := none,base.emitted := #[]} =
      .ok (some out,emission.state,trace)
  selected : BranchSelection ctx ti targets.toList
    {input with current := some ti,color := none,base.emitted := #[]}
    out emission.state trace
  retained : core.branch = some emission
  emitted : emission.code = emission.state.base.emitted
  combined : core.code = core.scan.output.code ++ emission.code
  branchScan : core.scan.isBranch = true

private theorem emission_origin {ctx : Ctx} {f : Clif.Function} {c : Nat}
    {yes no : Clif.BlockCall} {bi ti : Nat} {targets : Array Nat}
    {input : State} {emission : BranchEmission}
    (run : emitBranch ctx f (.brif c yes no) bi ti targets input = .ok emission) :
    ∃ out trace,Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets.toList]
        {input with current := some ti,color := none,base.emitted := #[]} =
        .ok (some out,emission.state,trace) ∧
      emission.code = emission.state.base.emitted := by
  unfold emitBranch at run
  dsimp only at run
  cases call : Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets.toList]
      {input with current := some ti,color := none,base.emitted := #[]} with
  | error message => simp only [call,bind,Except.bind] at run; cases run
  | ok q =>
    obtain ⟨out,next,trace⟩ := q
    simp only [call,bind,Except.bind] at run
    cases out with
    | none => simp at run
    | some out =>
      simp only [Option.isNone_some,Bool.false_eq_true,ite_false,branchCode,
        pure,Except.pure,bind,Except.bind] at run
      cases run
      exact ⟨out,trace,rfl,rfl⟩

/-- Invert the actual conditional core once, retaining its branch emission,
outgoing argument call and real backward scan boundary for all later consumers. -/
theorem conditional_core_calls {ctx : Ctx} {order : Order} {f : Clif.Function}
    {b : Clif.Block} {bi start stop : Nat} {data : V} {targets : Array Nat}
    {input : State} {core : LoweredBlockCore} {c : Nat} {yes no : Clif.BlockCall}
    (term : b.term = .brif c yes no)
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core) :
    ∃ (emission : BranchEmission) (afterEdges : State),
      core.branch = some emission ∧
      emitBranch {Driver.termCtx ctx (stop-1) data with tryRegs := input.tryRegs[stop-1]!}
        f (.brif c yes no) bi (stop-1) targets input = .ok emission ∧
      collectOutgoing ctx order bi targets emission.state = .ok (afterEdges,core.outgoing) ∧
      core.scan.input = {afterEdges with color := some afterEdges.endColor[bi]!} ∧
      core.scan.ctx = {Driver.termCtx ctx (stop-1) data with tryRegs := input.tryRegs[stop-1]!} ∧
      core.scan.isBranch = true ∧ core.code = core.scan.output.code ++ emission.code := by
  let actualCtx : Ctx := {Driver.termCtx ctx (stop-1) data with tryRegs := input.tryRegs[stop-1]!}
  unfold lowerBlockCore at run
  dsimp only at run
  simp only [term] at run
  cases branchCall : emitBranch actualCtx f (.brif c yes no) bi (stop-1) targets input with
  | error message =>
    dsimp only [actualCtx,Driver.termCtx] at branchCall
    simp only [branchCall,Functor.map,Except.map,bind,Except.bind] at run
    cases run
  | ok emission =>
    dsimp only [actualCtx,Driver.termCtx] at branchCall
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
        dsimp only [actualCtx,Driver.termCtx] at scanned
        simp only [scanned,bind,Except.bind] at run
        cases run
      | ok scan =>
        dsimp only [actualCtx,Driver.termCtx] at scanned
        simp only [scanned,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at run
        cases run
        exact ⟨emission,next,rfl,rfl,outgoing,rfl,rfl,rfl,rfl⟩


/-- The old core-origin interface is retained; its named branch and first-match
selection are derived from the shared actual core-call decomposition. -/
theorem conditional_core_origin {ctx : Ctx} {order : Order} {f : Clif.Function}
    {b : Clif.Block} {bi start stop : Nat} {data : V} {targets : Array Nat}
    {input : State} {core : LoweredBlockCore} {c : Nat} {yes no : Clif.BlockCall}
    (term : b.term = .brif c yes no)
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core) :
    Nonempty (CoreOrigin
      {Driver.termCtx ctx (stop-1) data with tryRegs := input.tryRegs[stop-1]!}
      f bi (stop-1) targets input core) := by
  obtain ⟨emission,afterEdges,retained,branchCall,outgoing,scanInput,scanCtx,branchScan,combined⟩ :=
    conditional_core_calls term run
  obtain ⟨out,trace,call,emitted⟩ := emission_origin branchCall
  obtain ⟨selected⟩ := stock_named_branch_selection call
  exact ⟨⟨emission,out,trace,call,selected,retained,emitted,combined,branchScan⟩⟩

end Backend.Stock.Proof.ConditionalValues
