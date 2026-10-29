module

public import FV.Backend.Proof.StockTerminalEmission
public import FV.Backend.Proof.StockReturnRecordSource

@[expose] public section

/-! Original whole-driver execution supplies the return's emitted classification.
All prior conditional source interfaces remain available unchanged. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- The actual retained return refines its original source return without a
caller-supplied step or decision, helper execution, or operand certificate.
Only original scope/source conditions and the simulation invariant remain. -/
theorem stock_lower_return_record_source_run_auto {f : Clif.Function} {result : Result}
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
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) :
    ∃ (step : Step) (rs ps : List Reg) (extra : List Clif.Val),
      record.output.step = some step ∧ step.decision = .emitted ∧
      record.output.emitted = #[.rets (rs.zip ps)] ∧ step.rules.getLast? = some rule_lower_2574.id ∧
      (xs ++ sretRet f).mapM event.ctx.valueReg? = some rs ∧
      returnPins f rs.length = some ps ∧ ps.length = rs.length ∧
      s.frame.getMany (xs ++ sretRet f) = .ok (vals ++ extra) ∧
      ∀ world,MR s.frame.slots s.mem world → ∃ ops world',
        seqRun isem (record.output.emitted.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
          some (.stop 0 ((.rets (rs.zip ps) : MInst).mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ops ρ world [] world' .ret) ∧
        AllHold (vals ++ extra) (vuses ops ρ) ∧ MR s.frame.slots s.mem world'  := by
  have rt : retOrTrap b.term = true := by rw [ret]; rfl
  obtain ⟨step,recorded,emitted⟩ := stock_lower_retTrap_record_emitted run scope events block rt records terminal
  obtain ⟨rs,ps,extra,code,root,mapped,pinned,count,read,execution⟩ := stock_lower_return_record_source_run
    run scope dominated abi events block ret records terminal recorded emitted func callers done defined held refines stable
  exact ⟨step,rs,ps,extra,recorded,emitted,code,root,mapped,pinned,count,read,execution⟩
end Backend.Stock.Proof
