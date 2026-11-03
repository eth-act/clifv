import FV.E2E.StockAcquireTwoLoadFaultStepF
import FV.E2E.StockAcquireLayoutImage

namespace E2E.LinkSys
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Original source trapping derives a real stepF fault prefix from the original code-address image field and internal kept/readable obligations. -/
-- witness: native_decide
theorem two_load_fault_stepF_of_code_image (L : LinkSys) {κ : Nat → Clif.Function → Nat}
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
    (codeAddresses : ∀ a, CodeAddr (Arm.set_program Arm.ArmState.default
      ((L.A AcquireTwoLoadPrefix.function).fb.program (L.A AcquireTwoLoadPrefix.function).base)) a →
      codeImage a) :
    ∃ n,TrapAtF mp (L.A AcquireTwoLoadPrefix.function).fb (L.A AcquireTwoLoadPrefix.function).base code
      (ArmFault.runF mp n initial) ∧
      L.RunGoodLBW n M AcquireTwoLoadPrefix.function initial ∧
      ArmFault.runF mp (n+1) initial = Arm.write_err ArmFault.memFault (ArmFault.runF mp n initial) := by
  exact L.two_load_fault_stepF_of_images hc covered symbols slot sourceEntry related arguments mp
    faults fuel code trapped machineEntry entry kept readable
    (StockAcquirePending.layout_table_image_of_codeAddr hc.layout codeAddresses)

end E2E.LinkSys
