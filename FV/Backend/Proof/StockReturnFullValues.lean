import FV.Backend.Proof.StockPerEdgeReturnContract
import FV.Backend.Proof.StockBlockCode

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Keep the original source values and the implicit ABI values in the same actual return trace. -/
def ReturnValuesAt {W : Type} (f : Clif.Function) (vc : VCode) (edges : Array (Array (Array Reg)))
    (sem : ISem CV W) (MR : MemRelTW W) (s : Clif.State) (vs : VState CV W)
    (xs : List Nat) (vals : List Clif.Val) (cm : Clif.Mem) : Prop :=
  ∃ us outs world extra,
    PerEdgePrep.VRetFromAt vc edges sem vs us outs world ∧
    ReturnABI f us ∧ us.length = outs.length ∧
    s.frame.getMany (xs ++ sretRet f) = .ok (vals ++ extra) ∧
    AllHold (vals ++ extra) outs ∧ MR s.frame.slots s.mem world ∧
    cm = (s.mem.free (s.frame.slots.map (·.2))).leave

theorem ReturnValuesAt.runOkABIAt {W : Type} {f : Clif.Function} {vc : VCode}
    {edges : Array (Array (Array Reg))} {sem : ISem CV W} {MR : MemRelTW W}
    {s : Clif.State} {vs : VState CV W} {xs : List Nat} {vals : List Clif.Val} {cm : Clif.Mem}
    (returned : ReturnValuesAt f vc edges sem MR s vs xs vals cm) :
    RunOkABIAt f vc edges sem MR s.frame.slots vs (.returned vals cm) := by
  obtain ⟨us,outs,world,extra,execution,pins,arity,read,values,memory,freed⟩ := returned
  exact ⟨us,outs,world,s.mem,execution,pins,arity,values.prefix_append,memory,freed⟩

theorem ReturnValuesAt.prefix {W : Type} {f : Clif.Function} {vc : VCode}
    {edges : Array (Array (Array Reg))} {sem : ISem CV W} {MR : MemRelTW W}
    {s : Clif.State} {vs vs' : VState CV W} {xs : List Nat} {vals : List Clif.Val} {cm : Clif.Mem}
    (steps : Star (VStepAt vc edges sem) (.run vs) (.run vs'))
    (returned : ReturnValuesAt f vc edges sem MR s vs' xs vals cm) :
    ReturnValuesAt f vc edges sem MR s vs xs vals cm := by
  obtain ⟨us,outs,world,extra,execution,rest⟩ := returned
  obtain ⟨b,k,ρ,w,vb,ops,outputs,tail,more⟩ := execution
  exact ⟨us,outs,world,extra,⟨b,k,ρ,w,vb,ops,outputs,steps.trans tail,more⟩,rest⟩

theorem stock_lower_return_record_full_values {f : Clif.Function} {result : Result}
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
    ReturnValuesAt f result.code result.edgeArgs isem MR s ⟨label,k,ρ,world⟩ xs vals cm := by
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
  obtain ⟨steps,_,inst,operands,ran,_,_⟩ := seqRun_stop_starAt placed segment executed
  refine ⟨us,vuses ops ρ,world',extra,?_,selected,?_,read,values,mem,?_⟩
  · exact ⟨label,k+0,ρ,world,vb,ops,[],steps,placed,inst,operands,rfl,ran⟩
  · have := values.1
    omega
  · exact ((stepTerm_ret callers).2.2 vals cm done).2

/-- Recover the implicit pointer and its actual x8 pin from the retained source-value relation. -/
theorem ReturnValuesAt.sret_value {W : Type} {f : Clif.Function} {vc : VCode}
    {edges : Array (Array (Array Reg))} {sem : ISem CV W} {MR : MemRelTW W}
    {s : Clif.State} {vs : VState CV W} {xs : List Nat} {vals : List Clif.Val} {cm : Clif.Mem}
    (returned : ReturnValuesAt f vc edges sem MR s vs xs vals cm)
    (sret : (sigRets f.sig).any (·.purpose == .sret) = true) {pointer : Clif.Val}
    (readPointer : s.frame.getMany (xs ++ sretRet f) = .ok [pointer]) :
    ∃ source value world,
      PerEdgePrep.VRetFromAt vc edges sem vs [(source,.x 8)] [value] world ∧
      VHolds pointer value ∧ MR s.frame.slots s.mem world ∧
      cm = (s.mem.free (s.frame.slots.map (·.2))).leave := by
  obtain ⟨us,outs,world,extra,execution,pins,arity,read,values,memory,freed⟩ := returned
  have equal : vals ++ extra = [pointer] := Clif.Res.ok.inj (read.symm.trans readPointer)
  rw [equal] at values
  have outLength : outs.length = 1 := by simpa only [List.length_singleton] using values.1.symm
  obtain ⟨value,rfl⟩ := List.length_eq_one_iff.mp outLength
  have count : us.length = 1 := by simpa only [List.length_singleton] using arity
  obtain ⟨⟨source,pin⟩,rfl⟩ := List.length_eq_one_iff.mp count
  have physical : pin = .x 8 := by
    simpa only [ReturnABI,returnPins,sret,↓reduceIte,List.map_cons,List.map_nil,
      Option.some.injEq,List.cons.injEq,and_true] using pins.symm
  subst pin
  exact ⟨source,value,world,execution,values.2 0 pointer value (by rfl) (by rfl),memory,freed⟩

end Backend.Stock.Proof

