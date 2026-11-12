import FV.Backend.Proof.StockTermContract
import FV.Backend.Proof.StockReturnAutomaticSource

/-! Consume actual retained Stock return execution at the VCode simulation
boundary. Segment placement is an internal assembly obligation, not an input
filter. Source arity, pin selection, helper runs and demanded operands are
derived from the original successful source/Stock executions. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem runOkABI_of_return_stop {W : Type} {f : Clif.Function} {vc : VCode}
    {sem : ISem CV W} {MR : MemRelTW W} {slots : List (Clif.SlotId × Nat)}
    {label k offset : Nat} {vb : VBlock} {ms : List MInst} {ρ ρ₁ : Nat → CV}
    {w w₁ w₂ : W} {us : List (Reg × Reg)} {ops : Array Operand} {outs : List CV}
    {vals : List Clif.Val} {cm0 cm : Clif.Mem}
    (block : vc.blocks[label]? = some vb) (segment : SegAt vb k ms)
    (execution : seqRun sem ms ρ w = some (.stop offset (.rets us) ops ρ₁ w₁ outs w₂ .ret))
    (pins : ReturnABIV f vals us) (arity : us.length = (vuses ops ρ₁).length)
    (values : PrefixHold vals (vuses ops ρ₁)) (memory : MR slots cm0 w₂)
    (freed : cm = (cm0.free (slots.map (·.2))).leave) :
    RunOkABI f vc sem MR slots ⟨label,k,ρ,w⟩ (.returned vals cm) := by
  obtain ⟨steps,_,inst,operands,ran,_,_⟩ := seqRun_stop_star block segment execution
  exact ⟨us,vuses ops ρ₁,w₂,cm0,
    ⟨label,k+offset,ρ₁,w₁,vb,ops,outs,steps,block,inst,operands,rfl,ran⟩,
    pins,arity,values,memory,freed⟩

/-- A real original source return and its actual retained record satisfy the
ABI-aware whole-run observation once the resolved record is placed in the
returned VCode. This includes implicit x8 sret returns and memory deallocation. -/
theorem stock_lower_return_record_runOk {f : Clif.Function} {result : Result}
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
    {MR : MemRelT} (stable : MRStable F MR)
    {label k : Nat} {vb : VBlock} (placed : result.code.blocks[label]? = some vb)
    (segment : SegAt vb k (record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))))
    (world : Arm.ArmState) (memory : MR s.frame.slots s.mem world) :
    RunOkABI f result.code isem MR s.frame.slots ⟨label,k,ρ,world⟩ (.returned vals cm) := by
  obtain ⟨step,rs,ps,extra,recorded,emitted,code,_,mapped,pinned,count,read,execution⟩ :=
    stock_lower_return_record_source_run_auto run scope dominated abi events block ret records terminal
      func callers done defined held refines stable
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
  obtain ⟨ops,world',executed,values,mem⟩ := execution world memory
  have instruction : ((.rets (rs.zip ps) : MInst).mapRegs resolve) = .rets us := rfl
  rw [instruction] at executed
  have returnCount : us.length = vals.length + (sretRet f).length := by
    have explicit := (getMany_ok ((stepTerm_ret callers).2.2 vals cm done).1).1
    have both := (getMany_ok read).1
    simp only [List.length_append] at both valueCount explicit ⊢
    omega
  exact runOkABI_of_return_stop placed segment executed ⟨selected, returnCount⟩
    (by have := values.1; omega) values.prefix_append mem
    ((stepTerm_ret callers).2.2 vals cm done).2
end Backend.Stock.Proof
