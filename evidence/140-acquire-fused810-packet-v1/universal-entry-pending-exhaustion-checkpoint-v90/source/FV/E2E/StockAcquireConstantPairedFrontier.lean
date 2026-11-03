import FV.E2E.StockAcquireConstantPendingPairedScan
import FV.Backend.Proof.StockAcquireConstantEmptyMarks
import FV.Backend.Proof.StockAcquireEmptyMarksPairedFrontier

namespace E2E.StockAcquirePending
open Backend.DeadCleanup
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- Actual constants discharge the empty-group frontier branch in paired value semantics.
The complete outstanding queue and every required nonsuspended binding remain unchanged. -/
theorem stock_lower_constant_paired_frontier_at {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[event.block]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block + j)
    {info : IInfo} {ty : Clif.Ty} {imm : BitVec ty.width} {x a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.iconst ty imm))
    (results : info.results = [x]) (statementResults : stm.results = [x])
    (mapped : event.ctx.valueReg? x = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (tls : XTls Γ.F X) {env : Clif.Env} {cp : Clif.Program}
    {entry : Clif.Frame × Clif.Mem} {prefixRecords : List ScanRecord} {before after : SourcePoint}
    (sourceStep : IndexedSourceInst env cp f event.ctx event.block record.inst before after)
    {regs : Nat → CV} {worlds : W2}
    (prior : PairedReadFrontierAt f result event env cp (RelW Γ f c) (Zof Γ.F D before.2.2)
      entry prefixRecords record.output.state before regs worlds) :
    ∃ nextRegs nextWorlds,∃ post : PairedReadFrontierAt f result event env cp (RelW Γ f c)
        (Zof Γ.F D before.2.2) entry (prefixRecords++[record]) record.input after nextRegs nextWorlds,
      post.frontier = prior.frontier ∧
      seqRun (pairSem (valueSem Γ.F fc X)) (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        regs worlds = some (.fall nextRegs nextWorlds) := by
  have localTransfer := stock_lower_constant_pending_paired_scan_value (c := c) (D := D) (fc := fc) run scope dominated events records
    block statement current source clif results statementResults mapped recorded emitted tls prior.frontier.history
  obtain ⟨nextRegs,nextWorlds,executed,left,right,agreement⟩ :=
    localTransfer before after sourceStep regs worlds ⟨prior.left,prior.right,prior.agreement⟩
  have memorySame : after.2.2 = before.2.2 := by
    obtain ⟨index,advance,stepped⟩ := sourceStep
    obtain ⟨actual,inst,values,registers,rest,present,original,remaining,outcome,written,updated⟩ := stepped
    have infoEq := Option.some.inj (present.symm.trans source)
    subst actual
    have instEq := Option.some.inj (original.symm.trans clif)
    subst inst
    rw [instOutcome_of_pure (show pureInst (.iconst ty imm) = true from rfl)] at outcome
    exact (evalInst_pure (by rfl) outcome).1
  rw [memorySame] at agreement
  have marks := stock_lower_constant_empty_marks run scope events records source clif results mapped
    recorded emitted (refines_valueSemG (F := Γ.F) (ctx := fc) (X := X) (Rd := fun _ => True)
      (syms := Γ.syms) (exts := []) (sigs := []) (sp0 := 0) (Pc := fun _ _ _ _ => False))
  obtain ⟨post,same,runCode⟩ := stock_lower_empty_marks_paired_frontier_at run events records recorded emitted
    marks sourceStep prior executed left right agreement
  exact ⟨nextRegs,nextWorlds,post,same,runCode⟩

end E2E.StockAcquirePending
