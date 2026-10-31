import FV.E2E.StockMemoryStoreValue
import FV.E2E.StockArithmeticStage
import FV.E2E.DeadCleanupRegLevelX
import FV.E2E.DeadCleanupGot

namespace E2E.StockMemory.StoreRoots
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- Actual effect-only Stock returns use the existing checked allocation,
cleanup/preparation, encoding and machine consumer with exact value semantics. -/
theorem machine_return {f : Clif.Function} {args : List Clif.Val}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {k : Nat}
    {cleanup : Bool} (effects : effectsOnly vc = true)
    (prep : prepCheck (Stock.Arithmetic.stage cleanup vc) vcp = true)
    (check : checkAlloc vcp rf = .ok ()) (alloc : lowerRFunc vcp rf = .ok af)
    (emit : emitFunc k af = .ok fa) (layout : fa.layout = .ok fb)
    {X : ExtSem} {K : Nat} {F Z : BitVec 64 → Prop}
    (frame : ∀ a, F a → Z a) (covered : FormsCovered ⟨fa.k,af.slotBase⟩ vcp)
    {w final reference : Arm.ArmState} (arguments : ArgsAtEntry F f.sig args w)
    (worlds : SameWorld Z final reference)
    {ρ : Nat → CV} {us : List (Reg × Reg)} {outs : List CV}
    (returned : VReturns vc (csem F ⟨fa.k,af.slotBase⟩ X) ρ w us outs final)
    (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState)
    (entry : ActEntry vcp rf af fa fb K F G X H base ra s w) :
    ∃ n, ActRet ra Z G us outs reference s (runX (ArmStepX X H fa) n s) ∧
      PostTrace fa af base (ArmStepX X H fa) s n ∧
      ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
        (runX (ArmStepX X H fa) i s) := by
  have valueRun := return_value effects returned
  let t := final
  have finalWorld := worlds
  have prepared := StockArithmeticStage_returns prep valueRun
  have machine := regLevelCorrect_worldX_value check alloc emit layout
    (X := X) (H := H) (K := K) (G := G) (gv := GotV vcp)
    covered entry.abi entry.stack entry.gfree (by rw [entry.hF]; exact entry.calls)
    (by rw [entry.hF]; exact entry.tries) (by rw [entry.hF]; exact entry.tls)
    (by rw [entry.hF]; exact entry.body) ρ
  rw [entry.hF] at machine
  obtain ⟨n,⟨h1,h2,h3,h4,h5,h6,h7⟩,h8⟩ :=
    machine.1 us outs t (vReturns_gotV_value prepared)
  refine ⟨n,⟨h1,h2,?_,?_,h5,h6⟩,h7,h8⟩
  · intro a outside
    rw [h3 a (fun hf => outside (frame a hf))]
    exact finalWorld.2.1 a outside
  · intro field unmasked fp sp
    rw [h4 field unmasked fp sp]
    exact finalWorld.1 field unmasked


end E2E.StockMemory.StoreRoots
