import FV.E2E.StockMemoryPairedSource

namespace E2E.StockMemory
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Original guarded source values on both worlds, with the existing initialized
memory disagreement relation. One virtual file is shared by the pair. -/
def PairedScanRel (f : Clif.Function) (result : Result) (ctx : Ctx) (bi : Nat)
    (Γ : Rel) (c : BitVec 64) (D : BitVec 64 → Prop) (st : State) (s : SourcePoint)
    (ρ : Nat → CV) (q : W2) : Prop :=
  GuardedScanRel f result ctx bi (RelW Γ f c) st s ρ q.1 ∧
  GuardedScanRel f result ctx bi (RelW Γ f c) st s ρ q.2 ∧
  SameWorld (Zof Γ.F D s.2.2) q.1 q.2

/-- Actual load records discharge the existing generic scan-composition
interface at paired worlds. Original RelW premises derive initialized read
permissions; existing guarded lockstep supplies one pairSem execution. -/
theorem stock_lower_load_paired_scan
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j)
    {info : IInfo} {z a x nreg : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.load .load .i32 flags x 0)) (results : info.results = [z])
    (statementResults : stm.results = [z]) (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    (parameter : event.ctx.defInst? x = none) (pointer : event.ctx.valueReg? x = some (.vreg nreg .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n b,Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (tls : XTls Γ.F X) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx bi) (pairSem (csem Γ.F fc X))
      result.final.alias (PairedScanRel f result event.ctx bi Γ c D) record := by
  intro s s' sourceIndex ρ q before
  obtain ⟨held,otherHeld,worlds⟩ := before
  have reads := initIn_zof (Γ := Γ) held.2.2.1 D
  obtain ⟨ρ',t,t',first,second,post,otherPost⟩ := stock_lower_load_scan_pair
    run scope dominated events records block statement current source clif results statementResults mapped
    parameter pointer recorded emitted (mrStable_relW Γ f c)
    (memRefines_csem Γ.F fc X slot symbols) (memRelOk_relW Γ f c)
    (memRefinesR_csemG (ctx := fc) (X := X) (syms := Γ.syms) slot symbols)
    (fun _ _ _ _ h => (csemG_sub h).2.2)
    s s' sourceIndex ρ q.1 q.2 reads held otherHeld
  let code := record.output.emitted.toList.map (·.mapRegs
    (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))
  obtain ⟨t2,equal,paired,related⟩ := pair_fall
    (fun _ _ _ _ h => (csemG_sub h).2.2)
    (guardedStep0 (D := D) (syms := Γ.syms) tls fc s.2.2 code [] []) worlds first second
  have sameWorld : t' = t2 := (SeqEnd.fall.inj equal).2
  subst t2
  have sourceStep := sourceIndex.2.2
  obtain ⟨info',inst,vals,regs,rest,found,original,body,outcome,written,updated⟩ := sourceStep
  cases Option.some.inj (found.symm.trans source)
  cases Option.some.inj (original.symm.trans clif)
  have evaluated : Clif.evalInst s.2.1 s.2.2 (.load .load .i32 flags x 0) = .ok (vals,s'.2.2) := by
    simpa only [instOutcome] using outcome
  have selectedId := stock_lower_load_i32_selected_id run scope events records source clif recorded emitted
  have little := (stock_lower_load_selected_receipts run scope events records source clif recorded emitted selectedId).1
  obtain ⟨pv,raw,pvEq,width,valid,read,valsEq,memEq⟩ := evalInst_load_inv little evaluated
  refine ⟨ρ',(t,t'),paired,post,otherPost,?_⟩
  simpa only [memEq] using related

end E2E.StockMemory
