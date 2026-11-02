import FV.Backend.Proof.StockFenceMachineW
import FV.Backend.Proof.StockFenceOriginal

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.MemoryFaults Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- Original-source legalization preserves every memory and division outcome.
No ordinary-load/store exclusion is required. Old NoMemTrap variants remain unchanged. -/
theorem backend_correct_worldX_stock_fence_originalW {p : Clif.Program} {k : Nat} {result : Stock.Result} {vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {cleanup : Bool}
    (hc : CompiledStockArithmeticStage (Opt.Legalize128.legalize FenceFixture.function) cleanup k result vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry FenceFixture.function args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ FenceFixture.function c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F FenceFixture.function.sig args w₀)
    (mp : ArmFault.MemMap) (faults : MapFaults mp env p cs)
    (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        ReturnABI FenceFixture.function us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ result.code.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodXW vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        (∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s) ∧
          (∀ i < n, actGoodXW vcp rf af fa fb base s X H K G (GotV vcp)
            (runX (ArmStepX X H fa) i s)) ∧
          ∀ m, Arm.r .ERR (runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None) ∨
        (∃ n,TrapAtF mp fb base c' (runX (ArmStepX X H fa) n s) ∧
          ∀ i < n,actGoodXW vcp rf af fa fb base s X H K G (GotV vcp)
            (runX (ArmStepX X H fa) i s))) := by
  have compiled : CompiledStockArithmeticStage FenceFixture.function cleanup k result vcp rf af fa fb := by
    simpa only [FenceFixture.mixed_legalize_identity] using hc
  exact backend_correct_worldX_stock_fenceW compiled hcov hsym hslot hcs hrel hargs mp faults fuel

end E2E
