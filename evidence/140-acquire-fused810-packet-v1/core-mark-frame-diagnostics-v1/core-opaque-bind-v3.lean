import FV.Backend.Proof.StockAcquireOutgoingMarkFrame

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch collectOutgoing scanBlock

private theorem map_success {α β : Type} {value : Except String α} {mapped : α → β} {output : β}
    (run : mapped <$> value = .ok output) : ∃ input,value = .ok input ∧ mapped input = output := by
  cases value with
  | error message => cases run
  | ok input => cases run; exact ⟨input,rfl,rfl⟩

private theorem branch_init_sunk {ctx : Ctx} {f : Clif.Function} {term : Clif.Terminator}
    {bi ti : Nat} {targets : Array Nat} {input : State} {branch : Option BranchEmission}
    (isBranch : Bool)
    (run : (if isBranch then some <$> emitBranch ctx f term bi ti targets input else pure none) = .ok branch) :
    ((branch.map (·.state)).getD input).sunk = input.sunk := by
  cases isBranch with
  | false => cases run; rfl
  | true =>
    obtain ⟨emitted,called,equal⟩ := map_success run
    rw [← equal]
    exact emitBranch_sunk called


private theorem bind_success {α β : Type} {value : Except String α} {next : α → Except String β} {output : β}
    (run : (value >>= next) = .ok output) : ∃ input,value = .ok input ∧ next input = .ok output := by
  cases value with
  | error message => cases run
  | ok input => exact ⟨input,rfl,run⟩

/-- Real branch and successor processing preserve sunk marks before the actual body scan. -/
theorem blockCore_scan_input_sunk {ctx : Ctx} {f : Clif.Function} {order : Order} {block : Clif.Block}
    {bi start stop : Nat} {data : V} {targets : Array Nat} {input : State} {output : LoweredBlockCore}
    (run : lowerBlockCore ctx order f block bi start stop data targets input = .ok output) :
    output.scan.input.sunk = input.sunk ∧ output.state.sunk = output.scan.output.state.sunk := by
  let tc : Ctx := {ctx with insts := ctx.insts.set! (stop-1) ⟨data,[],[],none⟩, tryRegs := input.tryRegs[stop-1]!}
  let isBranch : Bool := match block.term with | .ret .. | .trap .. | .returnCall .. => false | _ => true
  unfold lowerBlockCore at run
  dsimp only at run
  obtain ⟨branch,branchRun,rest⟩ := bind_success run
  obtain ⟨edgesResult,edges,rest⟩ := bind_success rest
  obtain ⟨next,outgoing⟩ := edgesResult
  obtain ⟨bodyScan,scanned,finished⟩ := bind_success rest
  have equal := Except.ok.inj finished
  have inputState : output.scan.input.sunk = next.sunk :=
    (congrArg (fun core : LoweredBlockCore => core.scan.input.sunk) equal).symm
  have branchSunk : ((branch.map (·.state)).getD input).sunk = input.sunk :=
    branch_init_sunk (ctx := tc) (f := f) (term := block.term) (bi := bi) (ti := stop-1)
      (targets := targets) (input := input) isBranch branchRun
  have edgesSunk := collectOutgoing_sunk edges
  refine ⟨inputState.trans (edgesSunk.trans branchSunk),?_⟩
  rw [← equal]

end Backend.Stock.Proof.Acquire810
