import FV.Backend.Proof.StockAcquireTwoLoadVirtualPrefix

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- The unchanged admitted two-load function supplies the actual schedule and entry event internally.
The first source result and second source fault remain explicit execution premises. -/
-- witness: native_decide
theorem original_two_load_virtual_prefix :
    ∃ (result : Result) (event : BlockScanEvent),Stock.lower function = .ok result ∧
      LowerScope function ∧ Dominated function ∧ event ∈ result.blockScans.toList ∧
      ∀ {args : List Clif.Val} {cm : Clif.Mem} {frame : Clif.Frame} (entered : SourceEntry function args frame)
    {env : Clif.Env} {program : Clif.Program} {atFault : Clif.Frame × Clif.Mem} {code : Clif.TrapCode}
    (source : SourceInstResult env program event.ctx 0 (frame,cm) atFault)
    (failed : SourceInstFault env program event.ctx 1 atFault code)
    {isem : Backend.Proof.Sem} (driver : DriverSem isem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    (memoryOk : MemRelOk F sb syms function MR)
    {world : Arm.ArmState} (memory : MR frame.slots cm world) (arguments : ArgsAtEntry F function.sig args world),
    ∃ (consumer : ScanRecord) (block : VBlock) (prefixCode suffix : List MInst)
      (regs : Nat → CV) (nextWorld : Arm.ArmState) (frontier : ReadEffectFrontier event.ctx env program),
      consumer ∈ event.output.records ∧ consumer.inst = 3 ∧ result.code.blocks[0]? = some block ∧
      block.insts.toList = prefixCode++consumer.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))++suffix ∧
      seqRun isem prefixCode (entrySeed event.ctx frame) world = some (.fall regs nextWorld) ∧
      SameWorld F nextWorld world ∧ SourceInstFault env program event.ctx 1 atFault code ∧
      SourceReadCaptures event.ctx env program (event.output.records.reverse.take 1) (frame,cm) atFault frontier.history ∧
      PendingReadMarks frontier consumer.output.state ∧ RetiredReadUnmarked frontier consumer.output.state ∧
      RetiredUndemanded frontier consumer.output.state ∧
      PendingGuardedScanRel function result event.ctx 0 env program MR frontier.history consumer.output.state (1,atFault) regs nextWorld := by
  obtain ⟨result,event,run,scope,dominated,abi,size,events,schedule⟩ := original_two_load_schedule
  refine ⟨result,event,run,scope,dominated,events,?_⟩
  intro args cm frame entered env program atFault code source failed isem driver F sb syms memorySem MR stable memoryOk world memory arguments
  exact two_load_actual_virtual_prefix run scope dominated size events schedule entered source failed driver memorySem stable memoryOk memory arguments

end Backend.Stock.Proof.AcquireTwoLoadPrefix
