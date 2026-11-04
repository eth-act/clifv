import FV.E2E.StockCallStoreFaultReady
import FV.E2E.StockCallStoreAccessTail
import FV.Backend.Proof.StockCallStoreAddress
import FV.ArmFault.Step

namespace Backend.Stock.CallStore
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E MemoryFaults Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- The source map condition applies to the actual reached store after arbitrary callee effects. -/
theorem FaultReady.execute {f : Clif.Function} {result : Stock.Result} {env : Clif.Env}
    {cp : Clif.Program} {fr : Clif.Frame} {cm : Clif.Mem} {Γ : Rel} {fc : FnCtx}
    {X : ExtSem} {initial : Arm.ArmState} {trap : Clif.TrapCode}
    (source : FaultReady f result env cp fr cm Γ fc X initial trap)
    {args : List Clif.Val} (types : args.map (·.ty) = f.sig.params.map (·.ty))
    (arguments : ArgsAtEntry Γ.F f.sig args initial) {c : BitVec 64}
    (memory : RelW Γ f c fr.slots cm initial)
    (calls : XCallsOk env (f.externs.map (·.2)) (RelW Γ f c) X)
    (mp : ArmFault.MemMap)
    (faults : ∀ s code a n,Reach env cp ⟨fr,[],cm⟩ s → Clif.MemTrapAt env cp s code a n →
      ∃ j < n,mp (BitVec.ofNat 64 (a+j)) = .none) :
    VAccessTrapFrom fc.slotBase result.code (valueSem Γ.F fc X) ⟨0,0,source.seed,initial⟩ trap
      (sourceAddrPred (fun a n => ∃ j < n,mp (BitVec.ofNat 64 (a+j)) = .none)) := by
  obtain ⟨_,before,preRun,related⟩ := ABIReadOnly.seqRun_fall_realize types arguments (SameWorld.refl Γ.F initial)
    (b := 0) (start := 0) (by simpa only [Nat.zero_add] using source.reads) (fun _ => rfl) source.preRun
  have beforeMemory := mrStable_relW Γ f c fr.slots cm initial before (SameWorld.nf related) memory
  obtain ⟨actual,after,called,arity,held,mem⟩ := calls source.ext source.member source.callee fr.slots cm before
    (some source.ext.name) [source.values source.argument] [source.values source.argument]
    [⟨.i64,source.liveWord⟩] [⟨.i64,source.returnedWord⟩] source.after source.found (Or.inl ⟨rfl,rfl⟩)
    (source.arguments before) beforeMemory source.sourceReturned (by rw [source.returns]; rfl)
  rw [source.returns] at arity
  cases actual with
  | nil => cases arity
  | cons output tail =>
    have empty : tail = [] := by simpa using arity
    subst tail
    have callStep : valueSem Γ.F fc X
        (.call ⟨.sym source.ext.name,retPairs [(source.argument,.x 0)],callDefs [(.x 0,source.called)]⟩)
        ([(source.argument,Reg.x 0)].map (source.values ·.1)) before = some ([output],after,.next) := by
      change (X.call (some source.ext.name) [source.values source.argument] before).map
        (fun pair => (pair.1,pair.2,Ctl.next)) = _
      rw [called]
      rfl
    exact access_tail source.placed source.separate source.code preRun callStep source.flag
      (CallStoreResult.pointer_address source.pointerHeld source.pointerType after)
      ⟨Clif.effAddr source.pointerValue 8,rfl,
        faults source.sourceState trap (Clif.effAddr source.pointerValue 8) 8 source.sourceReached source.sourceTrap⟩

end Backend.Stock.CallStore
