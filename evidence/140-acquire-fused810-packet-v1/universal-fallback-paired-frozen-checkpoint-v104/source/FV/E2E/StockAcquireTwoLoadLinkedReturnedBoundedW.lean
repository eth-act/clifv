import FV.E2E.StockAcquireLinkedNoCallBoundedW
import FV.E2E.StockAcquireTwoLoadLinkedEntry
import FV.Backend.Proof.StockAcquireTwoLoadPublicReturnedW

namespace E2E.LinkSys
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The original returned source run supplies bounded linked W facts with both final values and free/leave memory.
The caller supplies no scan, history, no-call, or trace certificate. -/
-- witness: native_decide
theorem two_load_linked_public_return_runGoodBW (L : LinkSys) {κ : Nat → Clif.Function → Nat}
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
    (fuel : Nat) {vals : List Clif.Val} {final : Clif.Mem}
    (returned : Clif.runLoop env p fuel cs = .returned vals final)
    {ra : BitVec 64} {initial : Arm.ArmState}
    (machineEntry : L.MachEntry κ M AcquireTwoLoadPrefix.function F G ra initial world)
    (basePc : ∀ d s, L.BaseDest d → Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
      Arm.r .PC (L.Hb.call d s) = Arm.r .PC s+4)
    (baseExt : ∀ d uses w outs w', L.BaseDest d → L.Xb.call d uses w = some (outs,w') →
      Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    ∃ (us : List (Reg × Reg)) (outs : List CV) (reference : Arm.ArmState) (n : Nat),
      ReturnABI AcquireTwoLoadPrefix.function us ∧ us.length = outs.length ∧ PrefixHold vals outs ∧
      MemRel F syms final reference ∧ result.code.RetsSite us ∧
      ActRet ra F G us outs reference initial (runX (L.mach M AcquireTwoLoadPrefix.function) n initial) ∧
      PostTrace (L.A AcquireTwoLoadPrefix.function).fa (L.A AcquireTwoLoadPrefix.function).af
        (L.A AcquireTwoLoadPrefix.function).base (L.mach M AcquireTwoLoadPrefix.function) initial n ∧
      L.RunGoodLBW n M AcquireTwoLoadPrefix.function initial := by
  obtain ⟨entry,stepEq⟩ := StockAcquirePending.two_load_linked_actEntry L hc basePc baseExt machineEntry
  obtain ⟨us,outs,reference,pins,arity,values,memory,site,machine⟩ :=
    backend_correct_worldX_stock_two_load_acquire_returnW (X := L.X κ M AcquireTwoLoadPrefix.function F) hc covered symbols slot
      sourceEntry related arguments fuel returned
  obtain ⟨n,ret,post,trace⟩ := machine (L.hooks M) G (L.A AcquireTwoLoadPrefix.function).base ra initial entry
  rw [stepEq] at ret post trace
  obtain ⟨actual,event,lowered,scope,dominated,abi,size,events,schedule⟩ :=
    AcquireTwoLoadPrefix.original_two_load_schedule
  have equal := Except.ok.inj (lowered.symm.trans hc.lower)
  subst actual
  have noCall := AcquireTwoLoadPrefix.two_load_prepared_no_call_sites
    hc.lower scope dominated size events schedule hc.prepare
  exact ⟨us,outs,reference,n,pins,arity,values,memory,site,ret,post,
    L.runGoodB_of_no_call_traceW_machine hc.layout
      (by have := machineEntry.abi.fits;omega) noCall machineEntry.imgG machineEntry.imgS stepEq trace⟩

end E2E.LinkSys
