import FV.E2E.StockAcquireTwoLoadStepFPrefix

namespace E2E.LinkSys
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Original source trapping derives a real stepF fault prefix under the internal kept/code-image obligations. -/
-- witness: native_decide
theorem two_load_fault_stepF_of_images (L : LinkSys) {κ : Nat → Clif.Function → Nat}
    {p : Clif.Program} {M k : Nat} {result : Stock.Result} {cleanup : Bool}
    (hc : CompiledStockArithmeticStage AcquireTwoLoadPrefix.function cleanup k result
      (L.A AcquireTwoLoadPrefix.function).vcp (L.A AcquireTwoLoadPrefix.function).rf
      (L.A AcquireTwoLoadPrefix.function).af (L.A AcquireTwoLoadPrefix.function).fa (L.A AcquireTwoLoadPrefix.function).fb)
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {F G : BitVec 64 → Prop} {c : BitVec 64}
    (covered : FormsCovered ⟨(L.A AcquireTwoLoadPrefix.function).fa.k,(L.A AcquireTwoLoadPrefix.function).af.slotBase⟩
      (L.A AcquireTwoLoadPrefix.function).vcp)
    (symbols : ∀ name address,syms name = some address → L.Xb.sym name 0 = BitVec.ofNat 64 address)
    (slot : (L.A AcquireTwoLoadPrefix.function).af.slotBase = slotOff)
    {world : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (sourceEntry : ClifEntry AcquireTwoLoadPrefix.function args cs)
    (related : RelW ⟨F,syms,slotOff,(RAFrame.compute (L.A AcquireTwoLoadPrefix.function).vcp
      (L.A AcquireTwoLoadPrefix.function).rf).intBase⟩ AcquireTwoLoadPrefix.function c cs.frame.slots cs.mem world)
    (arguments : ArgsAtEntry F AcquireTwoLoadPrefix.function.sig args world)
    (mp : ArmFault.MemMap) (faults : MapFaults mp env p cs) (fuel : Nat) (code : Clif.TrapCode)
    (trapped : Clif.runLoop env p fuel cs = .trapped code)
    {ra : BitVec 64} {initial : Arm.ArmState}
    (machineEntry : L.MachEntry κ M AcquireTwoLoadPrefix.function F G ra initial world)
    (entry : ActEntry (L.A AcquireTwoLoadPrefix.function).vcp (L.A AcquireTwoLoadPrefix.function).rf
      (L.A AcquireTwoLoadPrefix.function).af (L.A AcquireTwoLoadPrefix.function).fa (L.A AcquireTwoLoadPrefix.function).fb
      (κ M AcquireTwoLoadPrefix.function) F G L.Xb (L.hooks M) (L.A AcquireTwoLoadPrefix.function).base ra initial world)
    {codeImage : BitVec 64 → Prop}
    (kept : ∀ a, (mp a).allows .W = false → L.Img a)
    (readable : ∀ a, codeImage a → (mp a).allows .R = true)
    (tableImage : ∀ j tag bytes,
      (L.A AcquireTwoLoadPrefix.function).fa.lines.toList[j]? = some (.word tag bytes) →
      ∀ i < 4, codeImage ((L.A AcquireTwoLoadPrefix.function).base +
        BitVec.ofNat 64 (lineOffset (L.A AcquireTwoLoadPrefix.function).fa.lines.toList j) +
        BitVec.ofNat 64 i)) :
    ∃ n,TrapAtF mp (L.A AcquireTwoLoadPrefix.function).fb (L.A AcquireTwoLoadPrefix.function).base code
      (ArmFault.runF mp n initial) ∧
      L.RunGoodLBW n M AcquireTwoLoadPrefix.function initial ∧
      ArmFault.runF mp (n+1) initial = Arm.write_err ArmFault.memFault (ArmFault.runF mp n initial) := by
  obtain ⟨n,fault,trace⟩ := backend_correct_worldX_stock_two_load_acquire_faultW hc covered symbols slot
    sourceEntry related arguments mp faults fuel code trapped (L.hooks M) G
    (L.A AcquireTwoLoadPrefix.function).base ra initial entry
  have prefixEq := StockAcquirePending.two_load_runF_eq_traceW L hc machineEntry trace kept readable tableImage
  refine ⟨n, by rwa [prefixEq], L.two_load_runGoodB_of_traceW hc machineEntry trace, ?_⟩
  rw [ArmFault.runF_succ', prefixEq]
  exact ArmFault.stepF_fault fault.2

end E2E.LinkSys
