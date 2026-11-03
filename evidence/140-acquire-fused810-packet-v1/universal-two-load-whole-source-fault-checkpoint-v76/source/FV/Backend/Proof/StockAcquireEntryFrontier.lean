import FV.Backend.Proof.StockAcquireFaultPendingEmpty
import FV.Backend.Proof.StockEntryPrelude

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The initial execution frontier records no earlier source reads. Static inherited marks stay unchanged. -/
def ReadEffectFrontier.empty (ctx : Ctx) (env : Clif.Env) (program : Clif.Program) : ReadEffectFrontier ctx env program :=
  ⟨[],[],[],rfl⟩

/-- Original source entry and the actual ABI prelude construct the initial pending relation and source history.
No caller supplies a virtual register file, scan schedule, or initial frontier certificate. -/
theorem stock_lower_entry_pending_frontier {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {args : List Clif.Val} {cm : Clif.Mem} {frame : Clif.Frame}
    (entered : SourceEntry f args frame)
    {isem : Backend.Proof.Sem} (driver : DriverSem isem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {world : Arm.ArmState} (memory : MR frame.slots cm world) (arguments : ArgsAtEntry F f.sig args world) :
    ∃ (event : BlockScanEvent) (block : VBlock) (prelude after : Array MInst) (regs : Nat → CV) (nextWorld : Arm.ArmState),
      event ∈ result.blockScans.toList ∧ event.block = 0 ∧ result.code.blocks[0]? = some block ∧
      block.insts = prelude++event.output.code.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))++after ∧
      seqRun isem prelude.toList (entrySeed event.ctx frame) world = some (.fall regs nextWorld) ∧
      SameWorld F nextWorld world ∧
      ∀ (env : Clif.Env) (program : Clif.Program),
        SourceReadCaptures event.ctx env program [] (frame,cm) (frame,cm) (ReadEffectFrontier.empty event.ctx env program).history ∧
        PendingReadMarks (ReadEffectFrontier.empty event.ctx env program) event.output.state ∧
        RetiredReadUnmarked (ReadEffectFrontier.empty event.ctx env program) event.output.state ∧
        RetiredUndemanded (ReadEffectFrontier.empty event.ctx env program) event.output.state ∧
        PendingGuardedScanRel f result event.ctx event.block env program MR
          (ReadEffectFrontier.empty event.ctx env program).history event.output.state (0,frame,cm) regs nextWorld := by
  obtain ⟨event,block,prelude,body,regs,nextWorld,events,entryBlock,located,code,executed,afterMemory,values,same,after,pieces⟩ :=
    stock_lower_entry_prelude_refines_frame run scope dominated entered driver memorySem stable memory arguments
  refine ⟨event,block,prelude,after,regs,nextWorld,events,entryBlock,located,?_,executed,same,?_⟩
  · rw [code,pieces,Array.append_assoc]
  · intro env program
    have guarded := stock_lower_entered_values_guarded_frame run scope dominated events entered values event.output.state nextWorld afterMemory
    refine ⟨.nil (frame,cm),?_,?_,?_,?_⟩
    · intro captured member
      cases member
    · intro captured member
      cases member
    · intro captured member
      cases member
    · exact pending_guarded_nil.mpr guarded

end Backend.Stock.Proof.Acquire810
