import FV.Backend.Proof.StockExplicitCallPhysical
namespace Backend.Stock.Proof.ExplicitCallExecutionDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64 ExplicitCallSemDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

/-- A canonical direct call actually executes with the source's explicit result
count under the original external contract, with result values and returned world. -/
theorem stock_explicit_direct_call_execution {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {env : Clif.Env} {exts : List Clif.ExtFunc} {MR : MemRelT}
    (external : XCallsOk env exts MR X) {ext : Clif.ExtFunc} (member : ext ∈ exts)
    {g : List Clif.Val → Clif.Mem → Clif.Outcome} {sl : List (Clif.SlotId × Nat)}
    {cm cm' : Clif.Mem} {w : Arm.ArmState} {L : List (Nat × Reg)} {base : Nat}
    {ρ : Nat → CV} {vals rvals : List Clif.Val} (fr : Clif.Frame)
    (found : env.extern ext.name = some g)
    (arguments : ArgsAt ext.sig vals (L.map (ρ ·.1)) w) (memory : MR sl cm w)
    (returned : g vals cm = .returned rvals cm') (length : rvals.length = ext.sig.returns.length) :
    ∃ outs w',seqRun (explicitCallSem (csem F ctx X))
        [.call ⟨.sym ext.name,retPairs L,callDefs (outDefs base ext.sig.returns.length)⟩] ρ w =
          some (.fall (writeV ρ ((callDefOps (outDefs base ext.sig.returns.length)).zip outs)) w') ∧
      outs.length = ext.sig.returns.length ∧ AllHold rvals outs ∧
      ResultsHeld base fr (outRegs' base ext.sig.returns.length) rvals
        (writeV ρ ((callDefOps (outDefs base ext.sig.returns.length)).zip outs)) ∧ MR sl cm' w' := by
  obtain ⟨outs,w',call,count,held,related⟩ := stock_explicit_direct_call_return (F := F) (ctx := ctx)
    (us := retPairs L) (ds := callDefs (outDefs base ext.sig.returns.length)) external member found (.inl ⟨rfl,rfl⟩) (by simp [callDefs,outDefs]) arguments memory returned length
  have size : outs.length = ext.sig.returns.length := by simpa [callDefs,outDefs] using count
  have executed := seqRun_call_sym (ρ := ρ) call (by simpa [outDefs] using size)
  have results := CallResultValuesDraft.stock_resultsHeld_call_prefix (fr := fr) (ρ := ρ) (b := base) held.prefixHold
  rw [length] at results
  exact ⟨outs,w',executed,size,held,results,related⟩

/-- Canonical indirect calls execute with explicit results under the ORIGINAL
indirect external contract, preserving returned memory and result holding. -/
theorem stock_explicit_indirect_call_execution {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {env : Clif.Env} {sigs : List Clif.Signature} {MR : MemRelT}
    (external : XCallsIndOk env sigs MR X) {sig : Clif.Signature} (member : sig ∈ sigs)
    {name : String} {g : List Clif.Val → Clif.Mem → Clif.Outcome}
    {sl : List (Clif.SlotId × Nat)} {cm cm' : Clif.Mem} {w : Arm.ArmState}
    {target base : Nat} {L : List (Nat × Reg)} {ρ : Nat → CV} {vals rvals : List Clif.Val} (fr : Clif.Frame)
    (found : env.extern name = some g) (signature : ∀ s,env.sigOf name = some s → sig.abiMatch s = true)
    (address : lo64 (ρ target) = X.sym name 0) (count : vals.length ≤ 8)
    (arguments : AllHold vals (L.map (ρ ·.1))) (memory : MR sl cm w)
    (returned : g vals cm = .returned rvals cm') (length : rvals.length = sig.returns.length)
    (typed : vals.map (·.ty) = Clif.AbiParam.tys sig.params) :
    ∃ outs w',seqRun (explicitCallSem (csem F ctx X))
        [.call ⟨.reg (.vreg target .int),retPairs L,callDefs (outDefs base sig.returns.length)⟩] ρ w =
          some (.fall (writeV ρ ((callDefOps (outDefs base sig.returns.length)).zip outs)) w') ∧
      outs.length = sig.returns.length ∧ AllHold rvals outs ∧
      ResultsHeld base fr (outRegs' base sig.returns.length) rvals
        (writeV ρ ((callDefOps (outDefs base sig.returns.length)).zip outs)) ∧ MR sl cm' w' := by
  obtain ⟨outs,w',call,size,held,related⟩ := stock_explicit_indirect_call_return (F := F) (ctx := ctx)
    (us := retPairs L) (ds := callDefs (outDefs base sig.returns.length)) external member found signature address (by simp [callDefs,outDefs]) count arguments memory returned length typed
  have size : outs.length = sig.returns.length := by simpa [callDefs,outDefs] using size
  have executed := seqRun_call_reg (ρ := ρ) call (by simpa [outDefs] using size)
  have results := CallResultValuesDraft.stock_resultsHeld_call_prefix (fr := fr) (ρ := ρ) (b := base) held.prefixHold
  rw [length] at results
  exact ⟨outs,w',executed,size,held,results,related⟩
end Backend.Stock.Proof.ExplicitCallExecutionDraft
