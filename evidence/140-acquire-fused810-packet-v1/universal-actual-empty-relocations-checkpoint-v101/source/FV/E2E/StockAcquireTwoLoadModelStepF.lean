import FV.E2E.StockAcquirePhysicalNoHooks
import FV.E2E.StockAcquireModelStepF
import FV.E2E.StockAcquireTwoLoadBoundedW

namespace E2E.StockAcquirePending
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Actual lowering, either preparation mode, allocation, and emission derive the complete no-hook fact. -/
-- witness: native_decide
theorem two_load_compiled_no_hooks (L : LinkSys) {k : Nat} {result : Stock.Result} {cleanup : Bool}
    (hc : CompiledStockArithmeticStage AcquireTwoLoadPrefix.function cleanup k result
      (L.A AcquireTwoLoadPrefix.function).vcp (L.A AcquireTwoLoadPrefix.function).rf
      (L.A AcquireTwoLoadPrefix.function).af (L.A AcquireTwoLoadPrefix.function).fa
      (L.A AcquireTwoLoadPrefix.function).fb) :
    ∀ (j : Nat) (inst : Insn) (trap : Option Clif.TrapCode),
      (L.A AcquireTwoLoadPrefix.function).fa.lines.toList[j]? = some (.ins inst trap) →
      inst.hooked = false := by
  obtain ⟨actual,event,lowered,scope,dominated,abi,size,events,schedule⟩ :=
    AcquireTwoLoadPrefix.original_two_load_schedule
  have equal := Except.ok.inj (lowered.symm.trans hc.lower)
  subst actual
  have allocated := two_load_allocated_no_hooks hc.lower scope dominated size events schedule hc.prepare hc.alloc
  have lines := emitFunc_no_hooks hc.emit allocated
  intro j inst trap located
  have clean := lines _ (List.mem_of_getElem? located)
  cases eq : inst.hooked <;> simp_all [Line.noHookB]

/-- Actual compiled code discharges the no-hook condition of the model-to-stepF adapter. -/
-- witness: native_decide
theorem two_load_goodAtW_stepF_eq_mach (L : LinkSys) {κ : Nat → Clif.Function → Nat}
    {k M : Nat} {result : Stock.Result} {cleanup : Bool}
    (hc : CompiledStockArithmeticStage AcquireTwoLoadPrefix.function cleanup k result
      (L.A AcquireTwoLoadPrefix.function).vcp (L.A AcquireTwoLoadPrefix.function).rf
      (L.A AcquireTwoLoadPrefix.function).af (L.A AcquireTwoLoadPrefix.function).fa
      (L.A AcquireTwoLoadPrefix.function).fb)
    {F G : BitVec 64 → Prop} {ra : BitVec 64} {initial world state : Arm.ArmState}
    (entry : L.MachEntry κ M AcquireTwoLoadPrefix.function F G ra initial world)
    (good : L.GoodAtW M AcquireTwoLoadPrefix.function initial state)
    {mp : ArmFault.MemMap} {codeImage : BitVec 64 → Prop}
    (kept : ∀ a, (mp a).allows .W = false → L.Img a)
    (readable : ∀ a, codeImage a → (mp a).allows .R = true)
    (tableImage : ∀ j tag bytes,
      (L.A AcquireTwoLoadPrefix.function).fa.lines.toList[j]? = some (.word tag bytes) →
      ∀ i < 4, codeImage ((L.A AcquireTwoLoadPrefix.function).base +
        BitVec.ofNat 64 (lineOffset (L.A AcquireTwoLoadPrefix.function).fa.lines.toList j) +
        BitVec.ofNat 64 i)) :
    ArmFault.stepF mp state = L.mach M AcquireTwoLoadPrefix.function state := by
  exact goodAtW_stepF_eq_mach L good hc.layout (by have := entry.abi.fits; omega)
    kept readable tableImage (two_load_compiled_no_hooks L hc)

end E2E.StockAcquirePending
