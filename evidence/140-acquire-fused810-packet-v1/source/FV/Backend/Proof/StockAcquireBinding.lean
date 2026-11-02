import FV.Backend.Proof.StockAcquireValue
import FV.Backend.Proof.StockResults

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The real binder records the fused result without a copy or a memory effect. -/
theorem acquire_result_binding (ctx : Ctx) (st : State) (z key d nr : Nat)
    (mapped : ctx.valueReg? z = some (.vreg key .int)) (flags : Clif.MemFlags) :
    bindResults ctx [(z,[.vreg d .int])]
      {st with base := (st.base.fresh .int).2.emit (.loadAcquire (.int 8) (.vreg d .int) (.vreg nr .int) flags)} =
      .ok ({st with base := (st.base.fresh .int).2.emit (.loadAcquire (.int 8) (.vreg d .int) (.vreg nr .int) flags), alias := aliasStep st.alias (key,d)},#[]) := by
  simpa using bindResults_virtual ctx
    {st with base := (st.base.fresh .int).2.emit (.loadAcquire (.int 8) (.vreg d .int) (.vreg nr .int) flags)}
    [(z,key,d)] (by intro pair member; cases List.mem_singleton.mp member; exact mapped)

/-- One fused acquire executes the original atomic read and widened result.
The source memory and every unrelated virtual register stay unchanged. -/
theorem acquire_byte_pair_run {F : BitVec 64 → Prop} {sb : Nat}
    {syms : String → Option Nat} {isem : Backend.Proof.Sem} {MR : MemRelT}
    {f : Clif.Function} (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {cm cm' : Clif.Mem} {p z d nr : Nat} {pointer small : Clif.Val}
    {flags : Clif.MemFlags} (little : flags.endianness ≠ some .big)
    (pointerSource : fr.regs p = some pointer) (pointerType : pointer.ty = .i64)
    {regs : Nat → CV} (pointerHeld : VHolds pointer (regs nr))
    (source : Clif.evalInst fr cm (.atomicLoad .i8 flags p) = .ok ([small],cm'))
    {world : Arm.ArmState} (memory : MR fr.slots cm world) :
    ∃ (raw : BitVec 8) (nextRegs : Nat → CV) (nextWorld : Arm.ArmState),
      small = ⟨.i8,raw⟩ ∧ cm' = cm ∧
      Clif.evalInst (withValue fr z small) cm' (.extend .uextend .i64 z) =
        .ok ([⟨.i64,raw.setWidth 64⟩],cm) ∧
      seqRun isem [.loadAcquire (.int 8) (.vreg d .int) (.vreg nr .int) flags] regs world =
        some (.fall nextRegs nextWorld) ∧
      nextRegs d = ofX (raw.setWidth 64) ∧ (∀ key,key ≠ d → nextRegs key = regs key) ∧
      MR fr.slots cm nextWorld := by
  obtain ⟨raw,next,smallEq,sameMemory,extended,executed,kept⟩ :=
    acquire_byte_widened_value stable memorySem memoryOk little pointerSource pointerType pointerHeld source memory
  let operands : Array Operand := #[⟨nr,.int,.use,.early,.reg⟩,⟨d,.int,.def,.late,.reg⟩]
  let finalRegs := vdefUpd operands [ofX (raw.setWidth 64)] regs
  refine ⟨raw,finalRegs,next,smallEq,sameMemory,extended,?_,?_,?_,kept⟩
  · exact seqRun_isem_one (operands_loadAcquire (.int 8) d nr flags) executed rfl
  · simp [finalRegs,operands,vdefUpd,writeV,Operand.isDef,Operand.isEarly,Operand.isLate,upd]
  · intro key different
    exact vdefUpd_other (by simpa [operands,Operand.isDef] using different)

end Backend.Stock.Proof.Acquire810
