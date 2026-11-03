import FV.Backend.Proof.StockAcquirePreparedRecordOrigin

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch collectOutgoing scanBlock

private theorem bind_success {α β : Type} {value : Except String α} {next : α → Except String β} {output : β}
    (run : (value >>= next) = .ok output) : ∃ input,value = .ok input ∧ next input = .ok output := by
  cases value with
  | error message => cases run
  | ok input => exact ⟨input,rfl,run⟩

private def sourceCoreAfterBranch (ctx tc : Ctx) (order : Order) (bi ti start stop : Nat)
    (isBranch : Bool) (targets : Array Nat) (input : State) (action : Except String (Option BranchEmission)) :
    Except String LoweredBlockCore := do
  let branch ← action
  let (next,outgoing) ← collectOutgoing ctx order bi targets ((branch.map (·.state)).getD input)
  let beforeScan := {next with color := some next.endColor[bi]!}
  let indices := ((Array.range (stop-start)).map (start+·)).reverse.toList
  let bodyScan ← scanBlock tc bi ti isBranch indices beforeScan
  pure ⟨bodyScan.state,bodyScan.code++((branch.map (·.code)).getD #[]),outgoing,branch,
    ⟨tc,bi,ti,isBranch,indices,beforeScan,bodyScan⟩⟩

private theorem sourceCoreAfterBranch_branch {ctx tc : Ctx} {order : Order} {bi ti start stop : Nat}
    {isBranch : Bool} {targets : Array Nat} {input : State} {output : LoweredBlockCore}
    {action : Except String (Option BranchEmission)}
    (run : sourceCoreAfterBranch ctx tc order bi ti start stop isBranch targets input action = .ok output) :
    output.scan.isBranch = isBranch := by
  unfold sourceCoreAfterBranch at run
  obtain ⟨branch,branchRun,rest⟩ := bind_success run
  obtain ⟨edges,edgesRun,rest⟩ := bind_success rest
  obtain ⟨next,outgoing⟩ := edges
  obtain ⟨bodyScan,scanned,finished⟩ := bind_success rest
  exact (congrArg (fun core : LoweredBlockCore => core.scan.isBranch) (Except.ok.inj finished)).symm

/-- Actual core execution retains its original source branch classification. -/
theorem blockCore_source_branch {ctx : Ctx} {order : Order} {f : Clif.Function} {block : Clif.Block}
    {bi start stop : Nat} {data : V} {targets : Array Nat} {input : State} {core : LoweredBlockCore}
    (run : lowerBlockCore ctx order f block bi start stop data targets input = .ok core) :
    core.scan.isBranch = Coverage.blockBranch block.term := by
  let tc : Ctx := {ctx with insts := ctx.insts.set! (stop-1) ⟨data,[],[],none⟩,tryRegs := input.tryRegs[stop-1]!}
  let isBranch : Bool := match block.term with | .ret .. | .trap .. | .returnCall .. => false | _ => true
  have normal : lowerBlockCore ctx order f block bi start stop data targets input =
      if isBranch then sourceCoreAfterBranch ctx tc order bi (stop-1) start stop isBranch targets input
        (some <$> emitBranch tc f block.term bi (stop-1) targets input)
      else sourceCoreAfterBranch ctx tc order bi (stop-1) start stop isBranch targets input (pure none) := by rfl
  rw [normal] at run
  change core.scan.isBranch = isBranch
  split at run
  · exact sourceCoreAfterBranch_branch run
  · exact sourceCoreAfterBranch_branch run

end Backend.Stock.Proof.Acquire810
