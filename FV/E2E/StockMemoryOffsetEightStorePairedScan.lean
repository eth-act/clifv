import FV.Backend.Proof.StockMemoryOffsetEightStoreSourceValues
import FV.E2E.StockMemoryPairedScan

namespace E2E.StockMemory.StoreRoots
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
open Backend.Stock.Memory.StoreRoots
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Actual source stores compose under the existing paired scan relation.
The updated source relation handles newly initialized bytes without a new read-permission condition. -/
theorem stock_lower_integer_store_eight_paired_scan (kind : Kind) (ty : Clif.Ty)
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j)
    {info : IInfo} {value pointer valueReg pointerReg : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.store kind.sourceOp ty flags value pointer 8))
    (typed : kind.sourceOp = .store → event.ctx.valueType? value = some (.int kind.width.bits))
    (parameter : event.ctx.defInst? pointer = none)
    (pointerMapped : event.ctx.valueReg? pointer = some (.vreg pointerReg .int))
    (valueMapped : event.ctx.valueReg? value = some (.vreg valueReg .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n b,Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (tls : XTls Γ.F X) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx bi) (pairSem (csem Γ.F fc X))
      result.final.alias (PairedScanRel f result event.ctx bi Γ c D) record := by
  intro s s' sourceIndex ρ q before
  obtain ⟨indexed,advance,sourceStep⟩ := sourceIndex
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨firstHeld,secondHeld,worlds⟩ := before
  obtain ⟨func,dfg,memory,values⟩ := firstHeld
  rw [position] at dfg values
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  let guarded : Backend.Proof.Sem := csemG Γ.F fc X (fun a => ¬ Zof Γ.F D s.2.2 a) Γ.syms [] [] 0
    (fun _ _ _ _ => False)
  have memorySem : StoreRefines Γ.F Γ.slotOff guarded :=
    store_refines_of_memR (memRefinesR_csemG (ctx := fc) (X := X) (syms := Γ.syms) slot symbols)
  obtain ⟨pv,t,pointer,evaluated,first,same,memory',post⟩ := stock_lower_integer_store_eight_source_step_of_store kind
    run scope dominated events records block statement current source clif typed parameter pointerMapped valueMapped
    recorded emitted (mrStable_relW Γ f c) memorySem (memRelOk_relW Γ f c) memory dfg values sourceStep
  have otherValues := secondHeld.2.2.2
  rw [position] at otherValues
  obtain ⟨pv',t',pointer',evaluated',second,same',otherMemory',otherPost⟩ :=
    stock_lower_integer_store_eight_source_step_of_store kind run scope dominated events records block statement current
      source clif typed parameter pointerMapped valueMapped recorded emitted (mrStable_relW Γ f c)
      memorySem (memRelOk_relW Γ f c) secondHeld.2.2.1 dfg otherValues sourceStep
  let code := record.output.emitted.toList.map (·.mapRegs
    (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))
  obtain ⟨t2,equal,paired,related⟩ := pair_fall
    (fun _ _ _ _ h => (csemG_sub h).2.2)
    (guardedStep0 (D := D) (syms := Γ.syms) tls fc s.2.2 code [] []) worlds first second
  have sameWorld : t' = t2 := (SeqEnd.fall.inj equal).2
  subst t2
  have postFunc : s'.2.1.func = f := by
    obtain ⟨info',inst,vals,regs,rest,_,_,_,_,_,updated⟩ := sourceStep
    change s'.2.1 = _ at updated
    rw [updated]
    exact func
  refine ⟨ρ,(t,t'),paired,⟨postFunc,?_,memory',?_⟩,⟨postFunc,?_,otherMemory',?_⟩,?_⟩
  · simpa only [advance,position] using postDFG
  · simpa only [advance,position] using post
  · simpa only [advance,position] using postDFG
  · simpa only [advance,position] using otherPost
  · exact sameWorld_zof memory'.1.1 otherMemory'.1.1 related (zof_sub s.2.2)

end E2E.StockMemory.StoreRoots
