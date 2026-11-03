import FV.Backend.Proof.StockAcquireSourcePrefixReach

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- Original entry and actual source history derive the fault's typing and reachability internally. -/
theorem stock_lower_acquire_entry_prefix_fault {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (R : SourceEndpointReceipt f event record) (pointerReg dest label index : Nat) (block : VBlock),
      result.code.blocks[label]? = some block ∧
      SegAt block index [.loadAcquire (CTy.ofClif R.ty) (.vreg dest .int)
        (.vreg (aliasNum result.final.alias pointerReg) .int) R.flags] ∧
      ∀ (env : Clif.Env) (args : List Clif.Val) (initial : Clif.State)
        (atFault : Clif.Frame × Clif.Mem) (mp : ArmFault.MemMap) (code : Clif.TrapCode),
        SourceEntry f args initial.frame → initial.frame.body = R.block.body →
        MapFaults mp env {funcs := []} initial →
        SourceSteps (SourceInstResult env {funcs := []} event.ctx)
          (List.range' (blockStart f event.block) R.producerIndex) (initial.frame,initial.mem) atFault →
        SourceInstFault env {funcs := []} event.ctx R.producer atFault code →
        ∀ (regs : Nat → CV) (world : Arm.ArmState),
        ValueHeld event.ctx atFault.1 (fun n => regs (aliasNum result.final.alias n)) R.pointer →
        ∃ address bytes,AcquireAt (block.insts[index]!) [regs (aliasNum result.final.alias pointerReg)] world code address bytes ∧
          ∃ j < bytes,mp (address+BitVec.ofNat 64 j) = .none := by
  obtain ⟨R,pointerReg,dest,label,index,block,found,segment,transfer⟩ :=
    stock_lower_acquire_selected_resolved_fault run scope dominated events records recorded emitted selectedId
  refine ⟨R,pointerReg,dest,label,index,block,found,segment,?_⟩
  intro env args initial atFault mp code entered body faults executed failed regs world held
  have initialTyped := stock_lower_entered_frame_typed_frame run dominated events entered
  have function : initial.frame.func = f := by
    obtain ⟨block,regs,entry,argsTypes,paramTypes,bound,frame⟩ := entered
    rw [frame]
  have initialBody : initial.frame.body = R.block.body.drop 0 := by simpa only [List.drop_zero] using body
  have producerBound := (List.getElem?_eq_some_iff.mp R.producerAt).1
  have actualSteps : SourceSteps (SourceInstResult env {funcs := []} event.ctx)
      (List.range' (blockStart f event.block+0) R.producerIndex) (initial.frame,initial.mem) atFault := by
    simpa only [Nat.add_zero] using executed
  have typed := stock_lower_source_body_prefix_frame_typed run scope dominated events R.built R.blockAt
    (start := 0) (count := R.producerIndex) (by omega) initialBody function initialTyped actualSteps
  have reached := source_steps_bare_reach initial.callers executed
  have initialState : (⟨initial.frame,initial.callers,initial.mem⟩ : Clif.State) = initial := by cases initial;rfl
  rw [initialState] at reached
  exact transfer env initial ⟨atFault.1,initial.callers,atFault.2⟩ mp code faults reached failed typed regs world held

end Backend.Stock.Proof.Acquire810
