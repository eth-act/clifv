import FV.Backend.Proof.StockAcquireTwoLoadOriginalVirtualReturned
import FV.Backend.Proof.StockMemoryAccessStage
import FV.E2E.StockArithmeticSemantics
import FV.E2E.DeadCleanupRegLevelW
import FV.E2E.LinkWorld

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- Original public source returns reach the actual prepared machine return with every original W field.
The source free/leave memory and both complete final bindings remain exact. -/
-- witness: native_decide
theorem backend_correct_worldX_stock_two_load_acquire_returnW {p : Clif.Program} {k : Nat} {result : Stock.Result} {vcp : VCode}
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
    (fuel : Nat) {vals : List Clif.Val} {final : Clif.Mem}
    (returned : Clif.runLoop env p fuel cs = .returned vals final) :
    ∃ (us : List (Reg × Reg)) (outs : List CV) (reference : Arm.ArmState),
      ReturnABI AcquireTwoLoadPrefix.function us ∧ us.length = outs.length ∧ PrefixHold vals outs ∧ MemRel F syms final reference ∧
      result.code.RetsSite us ∧
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (initial : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra initial world →
        ∃ n,ActRet ra F G us outs reference initial (runX (ArmStepX X H fa) n initial) ∧
          PostTrace fa af base (ArmStepX X H fa) initial n ∧
          ∀ j < n,actGoodXW vcp rf af fa fb base initial X H K G (GotV vcp) (runX (ArmStepX X H fa) j initial) := by
  let Γ : Rel := ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩
  obtain ⟨regs,source⟩ := AcquireTwoLoadPrefix.original_returned_runOkABI hc.lower hcs env p fuel returned
    (refines_valueSem F ⟨fa.k,af.slotBase⟩ X) (driverSem_valueSem F ⟨fa.k,af.slotBase⟩ X)
    (mrStable_relW Γ AcquireTwoLoadPrefix.function c) (memRefines_valueSem F ⟨fa.k,af.slotBase⟩ X hslot hsym)
    (memRelOk_relW Γ AcquireTwoLoadPrefix.function c) hrel hargs
  obtain ⟨us,outs,reference,cm0,reached,pins,arity,values,memory,freed⟩ := source
  have prepared := MemoryFaults.returns_stage hc.prepOk reached
  have site : result.code.RetsSite us := by
    obtain ⟨b,j,ρ,w,vb,ops,outputs,path,found,located,rest⟩ := reached
    exact ⟨b,vb,j,found,located⟩
  have finalMemory : MemRel F syms final reference := by
    rw [freed]
    exact memRel_leave (memRel_free memory.1.1 _)
  refine ⟨us,outs,reference,pins,arity,values,finalMemory,site,?_⟩
  intro H G base ra initial he
  have machine := regLevelCorrect_worldX_valueW hc.check hc.alloc hc.emit hc.layout
    (X := X) (H := H) (K := K) (G := G) (gv := GotV vcp)
    hcov he.abi he.stack he.gfree (by rw [he.hF];exact he.calls) (by rw [he.hF];exact he.tries)
    (by rw [he.hF];exact he.tls) (by rw [he.hF];exact he.body) regs
  rw [he.hF] at machine
  obtain ⟨n,⟨ret0,ret1,ret2,ret3,ret4,ret5,trace⟩,good⟩ := machine.1 us outs reference (vReturns_gotV_value prepared)
  exact ⟨n,⟨ret0,ret1,ret2,ret3,ret4,ret5⟩,trace,good⟩

end E2E
