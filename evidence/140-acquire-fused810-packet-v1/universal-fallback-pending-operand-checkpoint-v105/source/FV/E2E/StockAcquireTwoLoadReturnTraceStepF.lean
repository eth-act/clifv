import FV.E2E.StockAcquireTwoLoadReturnedStepF

namespace E2E.LinkSys
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The full return field transfers unchanged, including a paired enlarged world and shared reference state. -/
-- witness: native_decide
theorem two_load_return_trace_stepF (L : LinkSys) {κ : Nat → Clif.Function → Nat}
    {k M n : Nat} {result : Stock.Result} {cleanup : Bool}
    (hc : CompiledStockArithmeticStage AcquireTwoLoadPrefix.function cleanup k result
      (L.A AcquireTwoLoadPrefix.function).vcp (L.A AcquireTwoLoadPrefix.function).rf
      (L.A AcquireTwoLoadPrefix.function).af (L.A AcquireTwoLoadPrefix.function).fa
      (L.A AcquireTwoLoadPrefix.function).fb)
    {F targetF G : BitVec 64 → Prop} {ra : BitVec 64} {initial world reference : Arm.ArmState}
    {us : List (Reg × Reg)} {outs : List CV}
    (entry : L.MachEntry κ M AcquireTwoLoadPrefix.function F G ra initial world)
    (returned : ActRet ra targetF G us outs reference initial
      (runX (L.mach M AcquireTwoLoadPrefix.function) n initial))
    (post : PostTrace (L.A AcquireTwoLoadPrefix.function).fa (L.A AcquireTwoLoadPrefix.function).af
      (L.A AcquireTwoLoadPrefix.function).base (L.mach M AcquireTwoLoadPrefix.function) initial n)
    (trace : ∀ j < n, actGoodXW (L.A AcquireTwoLoadPrefix.function).vcp
      (L.A AcquireTwoLoadPrefix.function).rf (L.A AcquireTwoLoadPrefix.function).af
      (L.A AcquireTwoLoadPrefix.function).fa (L.A AcquireTwoLoadPrefix.function).fb
      (L.A AcquireTwoLoadPrefix.function).base initial L.Xb (L.hooks M)
      (κ M AcquireTwoLoadPrefix.function) G (GotV (L.A AcquireTwoLoadPrefix.function).vcp)
      (runX (L.mach M AcquireTwoLoadPrefix.function) j initial))
    {mp : ArmFault.MemMap} {codeImage : BitVec 64 → Prop}
    (kept : ∀ a, (mp a).allows .W = false → L.Img a)
    (readable : ∀ a, codeImage a → (mp a).allows .R = true)
    (codeAddresses : ∀ a, CodeAddr (Arm.set_program Arm.ArmState.default
      ((L.A AcquireTwoLoadPrefix.function).fb.program (L.A AcquireTwoLoadPrefix.function).base)) a →
      codeImage a) :
    ActRet ra targetF G us outs reference initial (ArmFault.runF mp n initial) ∧
      PostTrace (L.A AcquireTwoLoadPrefix.function).fa (L.A AcquireTwoLoadPrefix.function).af
        (L.A AcquireTwoLoadPrefix.function).base (ArmFault.stepF mp) initial n ∧
      L.RunGoodLBW n M AcquireTwoLoadPrefix.function initial := by
  have prefixes : ∀ j ≤ n, ArmFault.runF mp j initial =
      runX (L.mach M AcquireTwoLoadPrefix.function) j initial := by
    intro j bound
    exact StockAcquirePending.two_load_runF_eq_traceW L hc entry
      (fun i inside => trace i (by omega)) kept readable
      (StockAcquirePending.layout_table_image_of_codeAddr hc.layout codeAddresses)
  refine ⟨by rwa [prefixes n (Nat.le_refl _)], ?_, L.two_load_runGoodB_of_traceW hc entry trace⟩
  intro i positive before called
  have eqi : runX (ArmFault.stepF mp) i initial =
      runX (L.mach M AcquireTwoLoadPrefix.function) i initial :=
    (runF_eq_runX_stepF mp i initial).symm.trans (prefixes i (by omega))
  rw [eqi] at called ⊢
  exact post i positive before called

end E2E.LinkSys
