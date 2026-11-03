import FV.E2E.StockAcquireNoCallBoundedW
import FV.Backend.Proof.StockAcquireTwoLoadCodeNoCall
import FV.Backend.Proof.StockAcquireTwoLoadPublicMachineW

namespace E2E.LinkSys
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Actual lowering and preparation derive no-call; the original linked entry supplies fit and image facts. -/
-- witness: native_decide
theorem two_load_runGoodB_of_traceW (L : LinkSys) {κ : Nat → Clif.Function → Nat}
    {M n k : Nat} {result : Stock.Result} {cleanup : Bool}
    (hc : CompiledStockArithmeticStage AcquireTwoLoadPrefix.function cleanup k result
      (L.A AcquireTwoLoadPrefix.function).vcp (L.A AcquireTwoLoadPrefix.function).rf
      (L.A AcquireTwoLoadPrefix.function).af (L.A AcquireTwoLoadPrefix.function).fa (L.A AcquireTwoLoadPrefix.function).fb)
    {F G : BitVec 64 → Prop} {ra : BitVec 64} {initial world : Arm.ArmState}
    (entry : L.MachEntry κ M AcquireTwoLoadPrefix.function F G ra initial world)
    (trace : ∀ j < n,actGoodXW (L.A AcquireTwoLoadPrefix.function).vcp
      (L.A AcquireTwoLoadPrefix.function).rf (L.A AcquireTwoLoadPrefix.function).af
      (L.A AcquireTwoLoadPrefix.function).fa (L.A AcquireTwoLoadPrefix.function).fb
      (L.A AcquireTwoLoadPrefix.function).base initial L.Xb (L.hooks M) (κ M AcquireTwoLoadPrefix.function) G
      (GotV (L.A AcquireTwoLoadPrefix.function).vcp) (runX (L.mach M AcquireTwoLoadPrefix.function) j initial)) :
    L.RunGoodLBW n M AcquireTwoLoadPrefix.function initial := by
  obtain ⟨actual,event,lowered,scope,dominated,abi,size,events,schedule⟩ := AcquireTwoLoadPrefix.original_two_load_schedule
  have equal := Except.ok.inj (lowered.symm.trans hc.lower)
  subst actual
  have noCall := AcquireTwoLoadPrefix.two_load_prepared_no_call_sites hc.lower scope dominated size events schedule hc.prepare
  exact L.runGoodB_of_no_call_traceW hc.layout (by have := entry.abi.fits;omega) noCall entry.imgG entry.imgS trace

/-- The original public source trap supplies the complete bounded linked W prefix in both preparation modes.
No caller supplies a no-call, scan, source-history, or execution certificate. -/
-- witness: native_decide
theorem two_load_public_fault_runGoodBW (L : LinkSys) {κ : Nat → Clif.Function → Nat}
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
      (κ M AcquireTwoLoadPrefix.function) F G L.Xb (L.hooks M) (L.A AcquireTwoLoadPrefix.function).base ra initial world) :
    ∃ n,TrapAtF mp (L.A AcquireTwoLoadPrefix.function).fb (L.A AcquireTwoLoadPrefix.function).base code
      (runX (L.mach M AcquireTwoLoadPrefix.function) n initial) ∧
      L.RunGoodLBW n M AcquireTwoLoadPrefix.function initial := by
  obtain ⟨n,fault,trace⟩ := backend_correct_worldX_stock_two_load_acquire_faultW hc covered symbols slot
    sourceEntry related arguments mp faults fuel code trapped (L.hooks M) G
    (L.A AcquireTwoLoadPrefix.function).base ra initial entry
  exact ⟨n,fault,L.two_load_runGoodB_of_traceW hc machineEntry trace⟩

end E2E.LinkSys
