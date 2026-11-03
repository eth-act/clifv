import FV.Backend.Proof.StockAcquireOutgoingMarkFrame

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] emitBranch collectOutgoing scanBlock

private theorem branch_init_sunk {ctx : Ctx} {f : Clif.Function} {term : Clif.Terminator}
    {bi ti : Nat} {targets : Array Nat} {input : State} {branch : Option BranchEmission}
    (isBranch : Bool)
    (run : (if isBranch then some <$> emitBranch ctx f term bi ti targets input else pure none) = .ok branch) :
    ((branch.map (·.state)).getD input).sunk = input.sunk := by
  cases isBranch with
  | false => cases run; rfl
  | true =>
    cases called : emitBranch ctx f term bi ti targets input with
    | error message => simp only [called,Functor.map,Except.map] at run; cases run
    | ok emitted =>
      simp only [called,Functor.map,Except.map] at run
      cases run
      exact emitBranch_sunk called

/-- Real branch and successor processing preserve sunk marks before the actual body scan. -/
theorem blockCore_scan_input_sunk {ctx : Ctx} {f : Clif.Function} {order : Order} {block : Clif.Block}
    {bi start stop : Nat} {data : V} {targets : Array Nat} {input : State} {output : LoweredBlockCore}
    (run : lowerBlockCore ctx order f block bi start stop data targets input = .ok output) :
    output.scan.input.sunk = input.sunk ∧ output.state.sunk = output.scan.output.state.sunk := by
  let tc : Ctx := {ctx with insts := ctx.insts.set! (stop-1) ⟨data,[],[],none⟩, tryRegs := input.tryRegs[stop-1]!}
  let isBranch : Bool := match block.term with | .ret .. | .trap .. | .returnCall .. => false | _ => true
  unfold lowerBlockCore at run
  dsimp only at run
  cases branchRun : (if isBranch then some <$> emitBranch tc f block.term bi (stop-1) targets input else pure none) with
  | error message => simp only [← tc,← isBranch,branchRun,bind,Except.bind] at run; cases run
  | ok branch =>
    simp only [← tc,← isBranch,branchRun,bind,Except.bind] at run
    cases edges : collectOutgoing ctx order bi targets ((branch.map (·.state)).getD input) with
    | error message => simp only [edges] at run; cases run
    | ok result =>
      obtain ⟨next,outgoing⟩ := result
      simp only [edges] at run
      cases scanned : scanBlock tc bi (stop-1) isBranch
          ((Array.range (stop-start)).map (start+·)).reverse.toList {next with color := some next.endColor[bi]!} with
      | error message => simp only [scanned] at run; cases run
      | ok bodyScan =>
        simp only [scanned,pure,Except.pure] at run
        cases run
        exact ⟨(collectOutgoing_sunk edges).trans (branch_init_sunk isBranch branchRun),rfl⟩

end Backend.Stock.Proof.Acquire810
