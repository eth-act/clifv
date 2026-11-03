import FV.E2E.StockAcquireTwoLoadBoundedW
import FV.Backend.Proof.StockAcquireTwoLoadPublicReturnedW

namespace E2E.LinkSys
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The original returned source run supplies bounded linked W facts with both final values and free/leave memory.
The caller supplies no scan, history, no-call, or trace certificate. -/
-- witness: native_decide
theorem two_load_public_return_runGoodBW (L : LinkSys) {κ : Nat → Clif.Function → Nat}
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
    (entry : ActEntry (L.A AcquireTwoLoadPrefix.function).vcp (L.A AcquireTwoLoadPrefix.function).rf
      (L.A AcquireTwoLoadPrefix.function).af (L.A AcquireTwoLoadPrefix.function).fa (L.A AcquireTwoLoadPrefix.function).fb
      (κ M AcquireTwoLoadPrefix.function) F G L.Xb (L.hooks M) (L.A AcquireTwoLoadPrefix.function).base ra initial world) :
    ∃ (us : List (Reg × Reg)) (outs : List CV) (reference : Arm.ArmState) (n : Nat),
      ReturnABI AcquireTwoLoadPrefix.function us ∧ us.length = outs.length ∧ PrefixHold vals outs ∧
      MemRel F syms final reference ∧ result.code.RetsSite us ∧
      ActRet ra F G us outs reference initial (runX (L.mach M AcquireTwoLoadPrefix.function) n initial) ∧
      PostTrace (L.A AcquireTwoLoadPrefix.function).fa (L.A AcquireTwoLoadPrefix.function).af
        (L.A AcquireTwoLoadPrefix.function).base (L.mach M AcquireTwoLoadPrefix.function) initial n ∧
      L.RunGoodLBW n M AcquireTwoLoadPrefix.function initial := by
  obtain ⟨us,outs,reference,pins,arity,values,memory,site,machine⟩ :=
    backend_correct_worldX_stock_two_load_acquire_returnW hc covered symbols slot
      sourceEntry related arguments fuel returned
  obtain ⟨n,ret,post,trace⟩ := machine (L.hooks M) G (L.A AcquireTwoLoadPrefix.function).base ra initial entry
  exact ⟨us,outs,reference,n,pins,arity,values,memory,site,ret,post,
    L.two_load_runGoodB_of_traceW hc machineEntry trace⟩

end E2E.LinkSys
