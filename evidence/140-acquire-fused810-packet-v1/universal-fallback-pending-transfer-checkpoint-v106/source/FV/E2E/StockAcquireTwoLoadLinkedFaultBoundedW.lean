import FV.E2E.StockAcquireLinkedNoCallBoundedW
import FV.E2E.StockAcquireTwoLoadLinkedEntry
import FV.Backend.Proof.StockAcquireTwoLoadPublicMachineW

namespace E2E.LinkSys
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The original public source trap supplies the complete bounded linked W prefix in both preparation modes.
No caller supplies a no-call, scan, source-history, or execution certificate. -/
-- witness: native_decide
theorem two_load_linked_public_fault_runGoodBW (L : LinkSys) {κ : Nat → Clif.Function → Nat}
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
    (basePc : ∀ d s, L.BaseDest d → Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
      Arm.r .PC (L.Hb.call d s) = Arm.r .PC s+4)
    (baseExt : ∀ d uses w outs w', L.BaseDest d → L.Xb.call d uses w = some (outs,w') →
      Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    ∃ n,TrapAtF mp (L.A AcquireTwoLoadPrefix.function).fb (L.A AcquireTwoLoadPrefix.function).base code
      (runX (L.mach M AcquireTwoLoadPrefix.function) n initial) ∧
      L.RunGoodLBW n M AcquireTwoLoadPrefix.function initial := by
  obtain ⟨entry,stepEq⟩ := StockAcquirePending.two_load_linked_actEntry L hc basePc baseExt machineEntry
  obtain ⟨n,fault,trace⟩ := backend_correct_worldX_stock_two_load_acquire_faultW
    (X := L.X κ M AcquireTwoLoadPrefix.function F) hc covered symbols slot
    sourceEntry related arguments mp faults fuel code trapped (L.hooks M) G
    (L.A AcquireTwoLoadPrefix.function).base ra initial entry
  rw [stepEq] at fault trace
  obtain ⟨actual,event,lowered,scope,dominated,abi,size,events,schedule⟩ :=
    AcquireTwoLoadPrefix.original_two_load_schedule
  have equal := Except.ok.inj (lowered.symm.trans hc.lower)
  subst actual
  have noCall := AcquireTwoLoadPrefix.two_load_prepared_no_call_sites
    hc.lower scope dominated size events schedule hc.prepare
  exact ⟨n,fault,L.runGoodB_of_no_call_traceW_machine hc.layout
    (by have := machineEntry.abi.fits;omega) noCall machineEntry.imgG machineEntry.imgS stepEq trace⟩

end E2E.LinkSys
