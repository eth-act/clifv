import FV.E2E.StockMemoryPairedBody
import FV.Backend.Proof.StockReturnContract

namespace E2E.StockMemory
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The original actual source return supplies a paired ABI-aware observation.
Existing source demand, pinning and value proofs are reused with guarded return
semantics and the original initialized-memory pairing framework. -/
theorem stock_lower_return_record_paired_runOk {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {xs : List Nat} (ret : b.term = .ret xs)
    {record : ScanRecord} (records : record ∈ event.output.records) (terminal : record.inst = event.termInst)
    {env : Clif.Env} {cp : Clif.Program} {s : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (func : s.frame.func = f) (callers : s.callers = [])
    (done : Clif.stepTerm env cp s (.ret xs) = .done vals cm)
    (defined : SourceDefinedAt f result.ctx event.block b.body.length s.frame)
    {ρ : Nat → CV} (held : ValuesHeld (fun x => Demanded record.output.state x ∧
      x ∈ availOf f (availIn f result.ctx) event.block b.body.length) event.ctx s.frame
      (fun key => ρ (aliasNum result.final.alias key)))
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (tls : XTls Γ.F X)
    {label k : Nat} {vb : VBlock} (placed : result.code.blocks[label]? = some vb)
    (segment : SegAt vb k (record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))))
    (q : W2) (memory : MRP Γ f c D s.frame.slots s.mem q) :
    RunOkABI f result.code (pairSem (csem Γ.F fc X)) (MRP Γ f c D)
      s.frame.slots ⟨label,k,ρ,q⟩ (.returned vals cm) := by
  let guarded := csemG Γ.F fc X (fun b => ¬ Zof Γ.F D s.mem b) Γ.syms [] [] 0 (fun _ _ _ _ => False)
  obtain ⟨step,rs,ps,extra,recorded,emitted,code,root,mapped,pinned,count,read,execution⟩ :=
    stock_lower_return_record_source_run_auto run scope dominated abi events block ret records terminal
      func callers done defined held (isem := guarded) (MR := RelW Γ f c)
      refines_csemG (mrStable_relW Γ f c)
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  let us : List (Reg × Reg) := (rs.zip ps).map (fun q => (resolve q.1,q.2))
  have length : us.length = rs.length := by simp [us,List.length_zip,count]
  have selected : ReturnABI f us := by
    have second : us.map (·.2) = ps := by
      simp only [us,List.map_map,Function.comp_def]
      exact List.map_snd_zip (by omega)
    unfold ReturnABI
    rw [length,second]
    exact pinned
  have requested := stock_lower_return_guarded_operands run scope dominated events block ret records terminal
    recorded emitted held
  have sourceValues := requested_values_hold requested read mapped
  have valueCount : (vals ++ extra).length = rs.length := by
    simpa only [List.length_map] using sourceValues.1
  obtain ⟨left,right,worlds⟩ := memory
  obtain ⟨ops,t,first,values,memory'⟩ := execution q.1 left
  obtain ⟨ops',t',second,otherValues,otherMemory'⟩ := execution q.2 right
  have instruction : ((.rets (rs.zip ps) : MInst).mapRegs resolve) = .rets us := rfl
  rw [instruction] at first second
  let ms := record.output.emitted.toList.map (·.mapRegs resolve)
  obtain ⟨otherPre,otherPost,equal,paired,relatedPre,relatedPost⟩ := pair_stop
    (fun _ _ _ _ h => (csemG_sub h).2.2)
    (guardedStep0 (D := D) (syms := Γ.syms) tls fc s.mem ms [] []) worlds first second
  have preEq : q.2 = otherPre := congrArg (fun e => match e with
    | .fall _ w => w | .stop _ _ _ _ w _ _ _ => w) equal
  have postEq : t' = otherPost := congrArg (fun e => match e with
    | .fall _ w => w | .stop _ _ _ _ _ _ w _ => w) equal
  rw [← preEq,← postEq] at paired
  rw [← postEq] at relatedPost
  have returnCount : us.length = vals.length + (sretRet f).length := by
    have explicit := (getMany_ok ((stepTerm_ret callers).2.2 vals cm done).1).1
    have both := (getMany_ok read).1
    simp only [List.length_append] at both valueCount explicit ⊢
    omega
  exact runOkABI_of_return_stop placed segment paired ⟨selected, returnCount⟩
    (by have := values.1; omega) values.prefix_append ⟨memory',otherMemory',relatedPost⟩
    ((stepTerm_ret callers).2.2 vals cm done).2

end E2E.StockMemory
