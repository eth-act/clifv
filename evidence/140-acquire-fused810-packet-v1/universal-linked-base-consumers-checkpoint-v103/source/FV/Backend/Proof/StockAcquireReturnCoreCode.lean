import FV.Backend.Proof.StockAcquireCoreSourceBranch

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Stock.runTerm emitBranch collectOutgoing scanBlock

private def returnCore (ctx tc : Ctx) (order : Order) (bi ti start stop : Nat)
    (targets : Array Nat) (input : State) : Except String LoweredBlockCore := do
  let (next,outgoing) ← collectOutgoing ctx order bi targets input
  let beforeScan := {next with color := some next.endColor[bi]!}
  let indices := ((Array.range (stop-start)).map (start+·)).reverse.toList
  let bodyScan ← scanBlock tc bi ti false indices beforeScan
  pure ⟨bodyScan.state,bodyScan.code++#[],outgoing,none,
    ⟨tc,bi,ti,false,indices,beforeScan,bodyScan⟩⟩

private theorem returnCore_code {ctx tc : Ctx} {order : Order} {bi ti start stop : Nat}
    {targets : Array Nat} {input : State} {core : LoweredBlockCore}
    (run : returnCore ctx tc order bi ti start stop targets input = .ok core) :
    core.code = core.scan.output.code := by
  unfold returnCore at run
  obtain ⟨pair,edgesRun,rest⟩ := Except.bind_ok run
  obtain ⟨scan,scanned,finished⟩ := Except.bind_ok rest
  cases Except.ok.inj finished
  exact Array.append_empty

/-- The actual return core has no branch suffix; opaque bind inversion retains its full source domain. -/
theorem returned_core_code {ctx : Ctx} {order : Order} {f : Clif.Function} {block : Clif.Block}
    {bi start stop : Nat} {data : V} {targets : Array Nat} {input : State} {core : LoweredBlockCore}
    {values : List Nat} (ret : block.term = .ret values)
    (run : lowerBlockCore ctx order f block bi start stop data targets input = .ok core) :
    core.code = core.scan.output.code := by
  let tc : Ctx := {ctx with insts := ctx.insts.set! (stop-1) ⟨data,[],[],none⟩,tryRegs := input.tryRegs[stop-1]!}
  have normal : lowerBlockCore ctx order f block bi start stop data targets input =
      returnCore ctx tc order bi (stop-1) start stop targets input := by
    unfold lowerBlockCore
    rw [ret]
    rfl
  rw [normal] at run
  exact returnCore_code run

end Backend.Stock.Proof.Acquire810
