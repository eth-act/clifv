import FV.E2E.StockCallStoreFaultMachine
import FV.E2E.StockCallStorePreparedShapes

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof MemoryFaults Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- The original caller derives both artifact checks internally in either cleanup mode. -/
-- witness: native_decide (fixed original compiler and prepared artifacts only)
theorem original_call_store_machine_fault_or_callee
    {p : Clif.Program} {k : Nat} {result : Stock.Result} {vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p CallStoreFixture.caller) {cleanup : Bool}
    (hc : CompiledStockArithmeticStage CallStoreFixture.caller cleanup k result vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k,af.slotBase⟩ vcp)
    (hX : XCallsOk env (CallStoreFixture.caller.externs.map (·.2))
      (RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ CallStoreFixture.caller c) X)
    (hsym : ∀ n b,syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry CallStoreFixture.caller args cs)
    (hrel : RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ CallStoreFixture.caller c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F CallStoreFixture.caller.sig args w₀)
    (mp : ArmFault.MemMap) (faults : MapFaults mp env p cs) {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env p fuel cs = .trapped code) :
    CallStoreCalleeTrap env p cs.frame cs.mem code ∨
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n,TrapAtF mp fb base code (runX (ArmStepX X H fa) n s) ∧
          ∀ j < n,actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
            (runX (ArmStepX X H fa) j s) := by
  have checked : Stock.CallStore.check CallStoreFixture.caller result.code = true := by
    obtain ⟨actual,lowered,admitted⟩ := CallStoreCompiledWitness.checked_caller cleanup
    have same := Except.ok.inj (lowered.symm.trans hc.lower)
    subst actual
    exact admitted
  obtain ⟨prepared,preparedRun,preparedCheck,shapes⟩ :=
    CallStoreCompiledWitness.prepared_access_shapes hc.lower cleanup
  rw [hc.prepare] at preparedRun
  cases Except.ok.inj preparedRun
  exact backend_store_fault_or_callee_stock_call_store hsub checked hc hcov hX hsym hslot
    hcs hrel hargs shapes mp faults trapped

end E2E
