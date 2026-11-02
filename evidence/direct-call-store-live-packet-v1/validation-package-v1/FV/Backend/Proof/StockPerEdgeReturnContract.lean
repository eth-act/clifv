import FV.Backend.Proof.StockTermContract
import FV.Backend.Proof.StockReturnAutomaticSource
import FV.Backend.Proof.PerEdgeSeq
import FV.Backend.Proof.PerEdgePrepareSound

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

def RunOkABIAt {W : Type} (f : Clif.Function) (vc : VCode) (edges : Array (Array (Array Reg))) (sem : ISem CV W)
    (MR : MemRelTW W) (slots : List (Clif.SlotId × Nat)) (vs : VState CV W) : Clif.Outcome → Prop
  | .returned vals cm => ∃ us outs w cm0, PerEdgePrep.VRetFromAt vc edges sem vs us outs w ∧
      ReturnABI f us ∧ us.length = outs.length ∧ PrefixHold vals outs ∧
      MR slots cm0 w ∧ cm = (cm0.free (slots.map (·.2))).leave
  | .trapped c => PerEdgePrep.VTrapFromAt vc edges sem vs c
  | .stuck _ | .outOfFuel => True

theorem RunOkABIAt.prefix {W : Type} {f : Clif.Function} {vc : VCode} {edges : Array (Array (Array Reg))} {sem : ISem CV W}
    {MR : MemRelTW W} {slots : List (Clif.SlotId × Nat)} {vs vs' : VState CV W} {o : Clif.Outcome}
    (h : Star (VStepAt vc edges sem) (.run vs) (.run vs')) (h' : RunOkABIAt f vc edges sem MR slots vs' o) :
    RunOkABIAt f vc edges sem MR slots vs o := by
  cases o with
  | returned vals cm =>
    obtain ⟨us,outs,w,cm0,ret,rest⟩ := h'
    exact ⟨us,outs,w,cm0,by
      obtain ⟨b,k,ρ,w₁,vb,ops,outputs,steps,tail⟩ := ret
      exact ⟨b,k,ρ,w₁,vb,ops,outputs,h.trans steps,tail⟩,rest⟩
  | trapped c =>
    obtain ⟨b,k,ρ,w,vb,i,ops,outs,w',steps,rest⟩ := h'
    exact ⟨b,k,ρ,w,vb,i,ops,outs,w',h.trans steps,rest⟩
  | _ => trivial

theorem runOkABIAt_of_return_stop {W : Type} {f : Clif.Function} {vc : VCode}
    {edges : Array (Array (Array Reg))} {sem : ISem CV W} {MR : MemRelTW W} {slots : List (Clif.SlotId × Nat)}
    {label k offset : Nat} {vb : VBlock} {ms : List MInst} {ρ ρ₁ : Nat → CV}
    {w w₁ w₂ : W} {us : List (Reg × Reg)} {ops : Array Operand} {outs : List CV}
    {vals : List Clif.Val} {cm0 cm : Clif.Mem}
    (block : vc.blocks[label]? = some vb) (segment : SegAt vb k ms)
    (execution : seqRun sem ms ρ w = some (.stop offset (.rets us) ops ρ₁ w₁ outs w₂ .ret))
    (pins : ReturnABI f us) (arity : us.length = (vuses ops ρ₁).length)
    (values : PrefixHold vals (vuses ops ρ₁)) (memory : MR slots cm0 w₂)
    (freed : cm = (cm0.free (slots.map (·.2))).leave) :
    RunOkABIAt f vc edges sem MR slots ⟨label,k,ρ,w⟩ (.returned vals cm) := by
  obtain ⟨steps,_,inst,operands,ran,_,_⟩ := seqRun_stop_starAt block segment execution
  exact ⟨us,vuses ops ρ₁,w₂,cm0,
    ⟨label,k+offset,ρ₁,w₁,vb,ops,outs,steps,block,inst,operands,rfl,ran⟩,
    pins,arity,values,memory,freed⟩

/-- A real original source return and its actual retained record satisfy the
ABI-aware whole-run observation once the resolved record is placed in the
returned VCode. This includes implicit x8 sret returns and memory deallocation. -/
theorem stock_lower_return_record_runOkAt {f : Clif.Function} {result : Result}
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
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots ⟨label,k,ρ,world⟩ (.returned vals cm) := by
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
  exact runOkABIAt_of_return_stop placed segment executed selected
    (by have := values.1; omega) values.prefix_append mem
    ((stepTerm_ret callers).2.2 vals cm done).2

end Backend.Stock.Proof
