import FV.E2E.StockResultCallDomain
import FV.E2E.StockArithmeticStageContract
import FV.E2E.StockArithmeticStage
import FV.E2E.DeadCleanupRegLevelX
import FV.E2E.DeadCleanupGot

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- The existing raw and cleanup stage transport preserves the original complete call semantics. -/
theorem stock_result_call_machine_return {f : Clif.Function} {k : Nat} {result : Stock.Result}
    {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {cleanup : Bool}
    (hc : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb)
    {X : ExtSem} {K : Nat} {F Z : BitVec 64 → Prop}
    (covers : ∀ a,F a → Z a) (covered : FormsCovered ⟨fa.k,af.slotBase⟩ vcp)
    {initial final reference : Arm.ArmState} (worlds : SameWorld Z final reference)
    {ρ : Nat → CV} {us : List (Reg × Reg)} {outs : List CV}
    (returned : VReturns result.code (valueSem F ⟨fa.k,af.slotBase⟩ X) ρ initial us outs final)
    (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState)
    (entry : ActEntry vcp rf af fa fb K F G X H base ra s initial) :
    ∃ n,ActRet ra Z G us outs reference s (runX (ArmStepX X H fa) n s) ∧
      PostTrace fa af base (ArmStepX X H fa) s n ∧
      ∀ i < n,actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
        (runX (ArmStepX X H fa) i s) := by
  have staged := StockArithmeticStage_returns hc.prepOk returned
  have machine := regLevelCorrect_worldX_value hc.check hc.alloc hc.emit hc.layout
    (X := X) (H := H) (K := K) (G := G) (gv := GotV vcp)
    covered entry.abi entry.stack entry.gfree (by rw [entry.hF]; exact entry.calls)
    (by rw [entry.hF]; exact entry.tries) (by rw [entry.hF]; exact entry.tls)
    (by rw [entry.hF]; exact entry.body) ρ
  rw [entry.hF] at machine
  obtain ⟨n,⟨ret,regs,world,frame,kept,program,trace⟩,good⟩ :=
    machine.1 us outs final (vReturns_gotV_value staged)
  refine ⟨n,⟨ret,regs,?_,?_,kept,program⟩,trace,good⟩
  · intro a outside
    exact (world a (fun hf => outside (covers a hf))).trans (worlds.2.1 a outside)
  · intro field unmasked fp sp
    exact (frame field unmasked fp sp).trans (worlds.1 field unmasked)


end E2E
