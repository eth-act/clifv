import FV.Backend.Proof.StockAcquireTwoLoadEntryNormal
import FV.Backend.Proof.StockAcquireTwoLoadWholeBoundary
import FV.Backend.Proof.StockAcquireMachineCoveredW
import FV.Backend.Proof.StockAcquireStage
import FV.E2E.LinkWorld
import FV.E2E.StockArithmeticSemantics

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- Original ClifEntry, RelW and ActEntry derive both physical first-fault branches in both preparation modes.
The caller supplies no indexed source, scan schedule, frame typing, or pending-frontier certificate. -/
-- witness: native_decide
theorem backend_correct_worldX_stock_two_load_acquire_faultW {p : Clif.Program} {k : Nat} {result : Stock.Result} {vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {cleanup : Bool}
    (hc : CompiledStockArithmeticStage AcquireTwoLoadPrefix.function cleanup k result vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k,af.slotBase⟩ vcp)
    (hsym : ∀ name address,syms name = some address → X.sym name 0 = BitVec.ofNat 64 address)
    (hslot : af.slotBase = slotOff)
    {world : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry AcquireTwoLoadPrefix.function args cs)
    (hrel : RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ AcquireTwoLoadPrefix.function c cs.frame.slots cs.mem world)
    (hargs : ArgsAtEntry F AcquireTwoLoadPrefix.function.sig args world)
    (mp : ArmFault.MemMap) (faults : MapFaults mp env p cs) (fuel : Nat) (code : Clif.TrapCode)
    (trapped : Clif.runLoop env p fuel cs = .trapped code)
    (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (initial : Arm.ArmState)
    (he : ActEntry vcp rf af fa fb K F G X H base ra initial world) :
    ∃ n,TrapAtF mp fb base code (runX (ArmStepX X H fa) n initial) ∧
      ∀ j < n,actGoodXW vcp rf af fa fb base initial X H K G (GotV vcp) (runX (ArmStepX X H fa) j initial) := by
  obtain ⟨actual,event,lowered,scope,dominated,abi,size,events,schedule⟩ := AcquireTwoLoadPrefix.original_two_load_schedule
  have resultEq := Except.ok.inj (lowered.symm.trans hc.lower)
  subst actual
  obtain ⟨firstPointer,secondPointer,argumentList,frame,callers⟩ := AcquireTwoLoadPrefix.original_entry_normal_form hcs
  have same : (⟨AcquireTwoLoadPrefix.entry firstPointer secondPointer,[],cs.mem⟩ : Clif.State) = cs := by cases cs;simp_all
  have sourceTrap : Clif.runLoop env p fuel ⟨AcquireTwoLoadPrefix.entry firstPointer secondPointer,[],cs.mem⟩ = .trapped code := by rw [same];exact trapped
  have sourceFaults : MapFaults mp env p ⟨AcquireTwoLoadPrefix.entry firstPointer secondPointer,[],cs.mem⟩ := by rw [same];exact faults
  have slots : cs.frame.slots = [] := by rw [frame];rfl
  let Γ : Rel := ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩
  have raw := AcquireTwoLoadPrefix.two_load_whole_source_fault_boundary hc.lower scope dominated size events schedule sourceTrap
    (driverSem_valueSem F ⟨fa.k,af.slotBase⟩ X) (memRefines_valueSem F ⟨fa.k,af.slotBase⟩ X hslot hsym)
    (mrStable_relW Γ AcquireTwoLoadPrefix.function c) (memRelOk_relW Γ AcquireTwoLoadPrefix.function c)
    (by simpa only [slots] using hrel) (by simpa only [argumentList] using hargs) [] mp sourceFaults
  have prepared := Acquire810.acquireTrap_gotV_value (Acquire810.acquireTrap_stage hc.prepOk raw)
  have machine := Acquire810.regLevel_acquire_fault_covered_worldX_valueW hc.check hc.alloc hc.emit hc.layout
    hcov he.abi he.stack he.gfree (by rw [he.hF];exact he.calls) (by rw [he.hF];exact he.tries)
    (by rw [he.hF];exact he.tls) (by rw [he.hF];exact he.body)
    (entrySeed event.ctx (AcquireTwoLoadPrefix.entry firstPointer secondPointer)) mp
  rw [he.hF] at machine
  exact machine code _ (fun address bytes allowed => allowed) prepared

end E2E
