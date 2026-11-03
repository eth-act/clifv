import FV.Backend.Proof.StockAcquireReturnPendingExhaustion
import FV.Backend.Proof.StockBlockCode
import FV.E2E.StockMemoryPairedReturnValue

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- The actual return boundary recovers all bindings and derives its resolved segment and paired ABI outcome.
The whole traversal must still construct the internal frontier and original source return. -/
theorem stock_lower_paired_frontier_return_runOkABI {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {block : Clif.Block} (blockAt : f.blocks[event.block]? = some block)
    {values : List Nat} (ret : block.term = .ret values)
    {record : ScanRecord} (records : record ∈ event.output.records) (terminal : record.inst = event.termInst)
    {env : Clif.Env} {program : Clif.Program} {s : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (callers : s.callers = []) (done : Clif.stepTerm env program s (.ret values) = .done vals cm)
    (defined : SourceDefinedAt f result.ctx event.block block.body.length s.frame)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} (tls : XTls Γ.F X)
    {entry : Clif.Frame × Clif.Mem} {prefixRecords : List ScanRecord} {regs : Nat → CV} {worlds : W2}
    (prior : PairedReadFrontierAt f result event env program (RelW Γ f c) (fun a => Γ.F a ∨ D a)
      entry prefixRecords record.output.state (block.body.length,(s.frame,s.mem)) regs worlds) :
    ∃ (label k : Nat),RunOkABI f result.code (pairSem (valueSem Γ.F fc X)) (MRP Γ f c D)
      s.frame.slots ⟨label,k,regs,worlds⟩ (.returned vals cm) := by
  obtain ⟨finished,left,right,agreement⟩ := stock_lower_paired_return_guarded_recovery
    run scope events blockAt ret records terminal prior
  obtain ⟨label,vb,k,placed,segment⟩ := stock_lower_record_segment run events records
  have pairedAgreement := sameWorld_zof left.2.2.1.1.1 right.2.2.1.1.1 agreement (fun _ member => member)
  exact ⟨label,k,E2E.StockMemory.stock_lower_return_record_paired_runOk_value
    (fc := fc) run scope dominated abi events blockAt ret records terminal
    left.1 callers done defined left.2.2.2 tls placed segment worlds ⟨left.2.2.1,right.2.2.1,pairedAgreement⟩⟩

end Backend.Stock.Proof.Acquire810
