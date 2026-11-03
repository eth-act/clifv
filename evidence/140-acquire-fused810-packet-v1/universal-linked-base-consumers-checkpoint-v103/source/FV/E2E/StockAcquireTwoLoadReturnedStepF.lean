import FV.E2E.StockAcquireTwoLoadFaultCodeImage
import FV.E2E.StockAcquireTwoLoadReturnedBoundedW
import FV.Backend.Proof.StockAcquireTwoLoadPublicReturnedW

namespace E2E.LinkSys
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

theorem runF_eq_runX_stepF (mp : ArmFault.MemMap) (n : Nat) (initial : Arm.ArmState) :
    ArmFault.runF mp n initial = runX (ArmFault.stepF mp) n initial := by
  induction n generalizing initial with
  | zero => rfl
  | succ n ih => exact ih _

/-- The original returned source run supplies stepF execution and bounded linked W facts with both final values and free/leave memory.
The caller supplies no scan, history, no-call, or trace certificate. -/
-- witness: native_decide
theorem two_load_return_stepF_of_code_image (L : LinkSys) {κ : Nat → Clif.Function → Nat}
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
      (κ M AcquireTwoLoadPrefix.function) F G L.Xb (L.hooks M) (L.A AcquireTwoLoadPrefix.function).base ra initial world)
    {mp : ArmFault.MemMap} {codeImage : BitVec 64 → Prop}
    (kept : ∀ a, (mp a).allows .W = false → L.Img a)
    (readable : ∀ a, codeImage a → (mp a).allows .R = true)
    (codeAddresses : ∀ a, CodeAddr (Arm.set_program Arm.ArmState.default
      ((L.A AcquireTwoLoadPrefix.function).fb.program (L.A AcquireTwoLoadPrefix.function).base)) a →
      codeImage a) :
    ∃ (us : List (Reg × Reg)) (outs : List CV) (reference : Arm.ArmState) (n : Nat),
      ReturnABI AcquireTwoLoadPrefix.function us ∧ us.length = outs.length ∧ PrefixHold vals outs ∧
      MemRel F syms final reference ∧ result.code.RetsSite us ∧
      ActRet ra F G us outs reference initial (ArmFault.runF mp n initial) ∧
      PostTrace (L.A AcquireTwoLoadPrefix.function).fa (L.A AcquireTwoLoadPrefix.function).af
        (L.A AcquireTwoLoadPrefix.function).base (ArmFault.stepF mp) initial n ∧
      L.RunGoodLBW n M AcquireTwoLoadPrefix.function initial := by
  obtain ⟨us,outs,reference,pins,arity,values,memory,site,machine⟩ :=
    backend_correct_worldX_stock_two_load_acquire_returnW hc covered symbols slot
      sourceEntry related arguments fuel returned
  obtain ⟨n,ret,post,trace⟩ := machine (L.hooks M) G (L.A AcquireTwoLoadPrefix.function).base ra initial entry
  have prefixes : ∀ j ≤ n, ArmFault.runF mp j initial =
      runX (L.mach M AcquireTwoLoadPrefix.function) j initial := by
    intro j bound
    exact StockAcquirePending.two_load_runF_eq_traceW L hc machineEntry
      (fun i inside => trace i (by omega)) kept readable
      (StockAcquirePending.layout_table_image_of_codeAddr hc.layout codeAddresses)
  have actualPost : PostTrace (L.A AcquireTwoLoadPrefix.function).fa
      (L.A AcquireTwoLoadPrefix.function).af (L.A AcquireTwoLoadPrefix.function).base
      (ArmFault.stepF mp) initial n := by
    intro i positive before called
    have eqi : runX (ArmFault.stepF mp) i initial =
        runX (L.mach M AcquireTwoLoadPrefix.function) i initial :=
      (runF_eq_runX_stepF mp i initial).symm.trans (prefixes i (by omega))
    rw [eqi] at called ⊢
    exact post i positive before called
  refine ⟨us,outs,reference,n,pins,arity,values,memory,site,?_,actualPost,
    L.two_load_runGoodB_of_traceW hc machineEntry trace⟩
  rwa [prefixes n (Nat.le_refl _)]

end E2E.LinkSys
