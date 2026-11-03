import FV.E2E.StockCallStoreFirstTrap
import FV.E2E.StockCallStoreAccessShape

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof MemoryFaults Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- Existing class checks derive every prepared access condition internally. -/
theorem backend_first_trap_stock_call_store_checked
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {result : Stock.Result} {vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (checked : Stock.CallStore.check f result.code = true) {cleanup : Bool}
    (hc : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k,af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXT : XTrapsOk env (f.externs.map (·.2)) (indSigs f)
      (RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b,syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (mp : ArmFault.MemMap) (faults : MapFaults mp env p cs) {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env p fuel cs = .trapped code)
    (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState)
    (entry : ActEntry vcp rf af fa fb K F G X H base ra s w₀) :
    (∃ n,CallTrapAt vcp F K G s fa base X (GotV vcp)
      (TrapCallSem env (f.externs.map (·.2)) (indSigs f)
        (RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c) X code)
      (runX (ArmStepX X H fa) n s) ∧
      ∀ j < n,actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
        (runX (ArmStepX X H fa) j s)) ∨
    (∃ n,TrapAtF mp fb base code (runX (ArmStepX X H fa) n s) ∧
      ∀ j < n,actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
        (runX (ArmStepX X H fa) j s)) := by
  obtain ⟨actual,lowered,equal,scope,dominated,abi,⟨layout⟩,_⟩ := Stock.CallStore.check_sound checked
  have sameResult : actual = result := Except.ok.inj (lowered.symm.trans hc.lower)
  subst actual
  exact backend_first_trap_stock_call_store hsub checked hc hcov hX hXT hsym hslot hcs hrel hargs
    (layout.prepared_access_shapes hc.prepare) mp faults trapped H G base ra s entry

end E2E
