import FV.Backend.Proof.StockAcquireFallbackExtendEncodedPaired
import FV.Backend.Proof.StockAcquireReadPrefixPaired

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- The actual encoded fallback callback advances every pending field while the original source fault stays fixed.
Its pipeline observations and prefix machine relation remain internal integration obligations. -/
theorem stock_lower_fallback_extend_paired_frozen_step {f : Clif.Function} {result : Result}
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
      ∀ (R : RL) (physicalLeft physicalRight : Arm.ArmState) (worlds : W2) (valuesLeft valuesRight : Loc → CV),
        StRel R physicalLeft valuesLeft worlds.1 → StRel R physicalRight valuesRight worlds.2 →
        ∀ (Z : BitVec 64 → Prop),(∀ a,R.F a → Z a) → SameWorld Z worlds.1 worlds.2 →
        ∀ (encodingEnv : Backend.Env) (machineDest machinePointer : Reg) (state next : PState) (lines : List Line),
          (MInst.extend machineDest machinePointer signed sourceType.bits target.width).lines R.ctx state = .ok (lines,next) →
          (∀ instruction trap,Line.ins instruction trap ∈ lines → ∃ arm,instruction.armFields encodingEnv = .ok arm) →
          ∀ (env : Clif.Env) (program : Clif.Program) (MR : MemRelT),MRStable R.F MR →
          ∀ (point : SourcePoint) (faultSlot : Nat) (code : Clif.TrapCode) (frontier : ReadEffectFrontier event.ctx env program)
            (regs : Nat → CV),point.1 ≤ j → SourceInstFault env program event.ctx faultSlot point.2 code →
            PendingReadMarks frontier record.output.state → RetiredReadUnmarked frontier record.output.state →
            RetiredUndemanded frontier record.output.state →
            PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history record.output.state point regs worlds.1 →
            PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history record.output.state point regs worlds.2 →
            ∃ nextRegs nextWorlds,seqRun (pairSem (csem R.F R.ctx R.X)) (record.output.emitted.toList.map
              (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs worlds =
                some (.fall nextRegs nextWorlds) ∧ SourceInstFault env program event.ctx faultSlot point.2 code ∧
              PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history record.input point nextRegs nextWorlds.1 ∧
              PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history record.input point nextRegs nextWorlds.2 ∧
              SameWorld Z nextWorlds.1 nextWorlds.2 ∧
              PendingReadMarks frontier record.input ∧ RetiredReadUnmarked frontier record.input ∧ RetiredUndemanded frontier record.input := by
  obtain ⟨sourceType,pointer,dest,typed,mapped,fresh,chunk,transfer⟩ :=
    stock_lower_fallback_extend_encoded_paired run scope dominated events records signed installed source recorded emitted selectedId
  refine ⟨sourceType,pointer,dest,typed,chunk,?_⟩
  intro R physicalLeft physicalRight worlds valuesLeft valuesRight left right Z includes agreement
    encodingEnv machineDest machinePointer state next lines expanded encoded
    env program MR stable point faultSlot code frontier regs order failed pending retiredMarks retiredValues priorLeft priorRight
  obtain ⟨nextRegs,nextWorlds,executed,leftFrame,rightFrame,related,kept⟩ :=
    transfer R physicalLeft physicalRight worlds valuesLeft valuesRight left right Z includes agreement
      encodingEnv machineDest machinePointer state next lines expanded encoded regs
  obtain ⟨leftRun,rightRun⟩ := E2E.StockAcquirePair.seqRun_paired_fall_projections executed
  have definitions := stock_lower_fallback_extend_resolved_defs run scope dominated events records
    signed installed source recorded emitted selectedId
  have postLeft := stock_lower_pending_frozen_source_frame run scope dominated events records blockAt statementAt current
    recorded emitted stable order priorLeft definitions leftRun leftFrame
  have postRight := stock_lower_pending_frozen_source_frame run scope dominated events records blockAt statementAt current
    recorded emitted stable order priorRight definitions rightRun rightFrame
  have sunk := stock_lower_fallback_extend_sunk_frame run scope events records signed installed source recorded emitted selectedId
  refine ⟨nextRegs,nextWorlds,executed,failed,postLeft,postRight,related,?_,?_,?_⟩
  · intro captured member
    rw [← sunk]
    exact pending captured member
  · intro captured member
    rw [← sunk]
    exact retiredMarks captured member
  · exact retired_undemanded_of_le retiredValues (stock_lower_record_demand_mono run events records recorded emitted)

end Backend.Stock.Proof.Acquire810
