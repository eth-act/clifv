import FV.E2E.StockAcquireTwoLoadModelStepF
import FV.E2E.StockAcquireFaultPrefixRun

namespace E2E.StockAcquirePending
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The complete original W trace supplies each model step without a new error-free hypothesis. -/
theorem runF_eq_no_call_traceW (L : LinkSys) {M n : Nat} {g : Clif.Function}
    {G : BitVec 64 → Prop} {K : Nat} {gv : Nat → String → Prop} {initial : Arm.ArmState}
    (layout : (L.A g).fa.layout = .ok (L.A g).fb)
    (fits : 4 * (L.A g).fb.words.size ≤ 2 ^ 64)
    (noCall : ∀ info, ¬ (L.A g).vcp.CallSite info)
    (image : ∀ a, L.Img a → G a)
    (imageMem : ∀ a, L.Img a → initial.mem a = L.imgMem a)
    (trace : ∀ j < n, actGoodXW (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb
      (L.A g).base initial L.Xb (L.hooks M) K G gv (runX (L.mach M g) j initial))
    {mp : ArmFault.MemMap} {codeImage : BitVec 64 → Prop}
    (kept : ∀ a, (mp a).allows .W = false → L.Img a)
    (readable : ∀ a, codeImage a → (mp a).allows .R = true)
    (tableImage : ∀ j tag bytes, (L.A g).fa.lines.toList[j]? = some (.word tag bytes) →
      ∀ i < 4, codeImage ((L.A g).base + BitVec.ofNat 64 (lineOffset (L.A g).fa.lines.toList j) +
        BitVec.ofNat 64 i))
    (unhooked : ∀ (j : Nat) (inst : Insn) (trap : Option Clif.TrapCode), (L.A g).fa.lines.toList[j]? = some (.ins inst trap) → inst.hooked = false) :
    ArmFault.runF mp n initial = runX (L.mach M g) n initial := by
  apply runF_eq_model_prefix
  intro j before
  have good := trace j before
  have linkedGood : L.GoodAtW M g initial (runX (L.mach M g) j initial) :=
    ⟨L.Xb, K, G, gv, rfl, good, image, imageMem, (L.no_call_at_goodW layout fits noCall good).2⟩
  exact goodAtW_stepF_eq_mach L linkedGood layout fits kept readable tableImage unhooked

/-- The compiled two-load artifact derives no-call and all physical no-hook facts in both modes. -/
-- witness: native_decide
theorem two_load_runF_eq_traceW (L : LinkSys) {κ : Nat → Clif.Function → Nat}
    {k M n : Nat} {result : Stock.Result} {cleanup : Bool}
    (hc : CompiledStockArithmeticStage AcquireTwoLoadPrefix.function cleanup k result
      (L.A AcquireTwoLoadPrefix.function).vcp (L.A AcquireTwoLoadPrefix.function).rf
      (L.A AcquireTwoLoadPrefix.function).af (L.A AcquireTwoLoadPrefix.function).fa
      (L.A AcquireTwoLoadPrefix.function).fb)
    {F G : BitVec 64 → Prop} {ra : BitVec 64} {initial world : Arm.ArmState}
    (entry : L.MachEntry κ M AcquireTwoLoadPrefix.function F G ra initial world)
    (trace : ∀ j < n, actGoodXW (L.A AcquireTwoLoadPrefix.function).vcp
      (L.A AcquireTwoLoadPrefix.function).rf (L.A AcquireTwoLoadPrefix.function).af
      (L.A AcquireTwoLoadPrefix.function).fa (L.A AcquireTwoLoadPrefix.function).fb
      (L.A AcquireTwoLoadPrefix.function).base initial L.Xb (L.hooks M)
      (κ M AcquireTwoLoadPrefix.function) G (GotV (L.A AcquireTwoLoadPrefix.function).vcp)
      (runX (L.mach M AcquireTwoLoadPrefix.function) j initial))
    {mp : ArmFault.MemMap} {codeImage : BitVec 64 → Prop}
    (kept : ∀ a, (mp a).allows .W = false → L.Img a)
    (readable : ∀ a, codeImage a → (mp a).allows .R = true)
    (tableImage : ∀ j tag bytes,
      (L.A AcquireTwoLoadPrefix.function).fa.lines.toList[j]? = some (.word tag bytes) →
      ∀ i < 4, codeImage ((L.A AcquireTwoLoadPrefix.function).base +
        BitVec.ofNat 64 (lineOffset (L.A AcquireTwoLoadPrefix.function).fa.lines.toList j) +
        BitVec.ofNat 64 i)) :
    ArmFault.runF mp n initial = runX (L.mach M AcquireTwoLoadPrefix.function) n initial := by
  obtain ⟨actual,event,lowered,scope,dominated,abi,size,events,schedule⟩ :=
    AcquireTwoLoadPrefix.original_two_load_schedule
  have equal := Except.ok.inj (lowered.symm.trans hc.lower)
  subst actual
  have noCall := AcquireTwoLoadPrefix.two_load_prepared_no_call_sites hc.lower scope dominated size events schedule hc.prepare
  exact runF_eq_no_call_traceW L hc.layout (by have := entry.abi.fits; omega) noCall
    entry.imgG entry.imgS trace kept readable tableImage (two_load_compiled_no_hooks L hc)

end E2E.StockAcquirePending
