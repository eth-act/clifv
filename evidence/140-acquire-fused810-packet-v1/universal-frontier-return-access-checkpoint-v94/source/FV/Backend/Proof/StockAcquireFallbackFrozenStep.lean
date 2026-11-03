import FV.Backend.Proof.StockAcquireFallbackExtendFresh

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Actual fallback extension leaves every sink mark unchanged through scan reset and output binding. -/
theorem stock_lower_fallback_extend_sunk_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (signed : Bool) {info : IInfo} {target : Clif.Ty} {x : Nat}
    (installed : event.ctx.insts[record.inst]? = some info)
    (source : info.clif = some (.extend (ScalarCast.extendOp signed) target x))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (ScalarCast.extendRule signed).id) :
    record.output.state.sunk = record.input.sunk := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have last : receipt.fired.getLast? = some (ScalarCast.extendRule signed).id := by rw [← receipt.rules];exact selectedId
  have chosen := fallback_extend_selected_rule signed receipt.selected last
  obtain ⟨sourceType,pointer,typed,accepted,mapped,output,nextEq⟩ := fallback_extend_selected_shape
    (stock_lower_record_context run scope events).1 signed installed source receipt.selected chosen
  obtain ⟨entries,color,sunk⟩ := bindResults_mark_fields receipt.binding
  rw [receipt.state,sunk,nextEq]
  exact scanState_sunk record.input record.inst

/-- The actual encoded fallback callback advances every pending field while the original source fault stays fixed.
Its pipeline observations and prefix machine relation remain internal integration obligations. -/
theorem stock_lower_fallback_extend_frozen_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (signed : Bool) {info : IInfo} {target : Clif.Ty} {x : Nat}
    (installed : event.ctx.insts[record.inst]? = some info)
    (source : info.clif = some (.extend (ScalarCast.extendOp signed) target x))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (ScalarCast.extendRule signed).id)
    {j : Nat} {block : Clif.Block} {statement : Clif.Stmt}
    (blockAt : f.blocks[event.block]? = some block) (statementAt : block.body[j]? = some statement)
    (current : record.inst = blockStart f event.block+j) :
    ∃ (sourceType : CTy) (pointer dest : Nat),event.ctx.valueType? x = some sourceType ∧
      record.output.emitted = #[.extend (.vreg dest .int) (.vreg pointer .int) signed sourceType.bits target.width] ∧
      ∀ (R : RL) (physical world : Arm.ArmState) (values : Loc → CV),StRel R physical values world →
        ∀ (encodingEnv : Backend.Env) (machineDest machinePointer : Reg) (state next : PState) (lines : List Line),
          (MInst.extend machineDest machinePointer signed sourceType.bits target.width).lines R.ctx state = .ok (lines,next) →
          (∀ instruction trap,Line.ins instruction trap ∈ lines → ∃ arm,instruction.armFields encodingEnv = .ok arm) →
          ∀ (env : Clif.Env) (program : Clif.Program) (MR : MemRelT),MRStable R.F MR →
          ∀ (point : SourcePoint) (faultSlot : Nat) (code : Clif.TrapCode) (frontier : ReadEffectFrontier event.ctx env program)
            (regs : Nat → CV),point.1 ≤ j → SourceInstFault env program event.ctx faultSlot point.2 code →
            PendingReadMarks frontier record.output.state → RetiredReadUnmarked frontier record.output.state →
            RetiredUndemanded frontier record.output.state →
            PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history record.output.state point regs world →
            ∃ nextRegs nextWorld,seqRun (csem R.F R.ctx R.X) (record.output.emitted.toList.map
              (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs world =
                some (.fall nextRegs nextWorld) ∧ SourceInstFault env program event.ctx faultSlot point.2 code ∧
              PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history record.input point nextRegs nextWorld ∧
              PendingReadMarks frontier record.input ∧ RetiredReadUnmarked frontier record.input ∧ RetiredUndemanded frontier record.input := by
  obtain ⟨sourceType,pointer,dest,typed,mapped,fresh,chunk,transfer⟩ :=
    stock_lower_fallback_extend_encoded run scope dominated events records signed installed source recorded emitted selectedId
  refine ⟨sourceType,pointer,dest,typed,chunk,?_⟩
  intro R physical world values related encodingEnv machineDest machinePointer state next lines expanded encoded
    env program MR stable point faultSlot code frontier regs order failed pending retiredMarks retiredValues prior
  obtain ⟨nextRegs,nextWorld,executed,same,kept⟩ := transfer R physical world values related encodingEnv
    machineDest machinePointer state next lines expanded encoded regs
  have post := stock_lower_pending_frozen_source_frame run scope dominated events records blockAt statementAt current
    recorded emitted stable order prior
    (stock_lower_fallback_extend_resolved_defs run scope dominated events records signed installed source recorded emitted selectedId)
    executed same
  have sunk := stock_lower_fallback_extend_sunk_frame run scope events records signed installed source recorded emitted selectedId
  refine ⟨nextRegs,nextWorld,executed,failed,post,?_,?_,?_⟩
  · intro captured member
    rw [← sunk]
    exact pending captured member
  · intro captured member
    rw [← sunk]
    exact retiredMarks captured member
  · exact retired_undemanded_of_le retiredValues (stock_lower_record_demand_mono run events records recorded emitted)

end Backend.Stock.Proof.Acquire810
