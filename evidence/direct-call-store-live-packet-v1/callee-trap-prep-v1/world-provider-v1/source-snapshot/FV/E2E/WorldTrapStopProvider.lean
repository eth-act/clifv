import FV.E2E.StockCallStoreCalleeTrap

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- An internal world theorem supplied by checked artifact constructors. -/
structure WorldTrapStopProvider (p : Clif.Program) (f : Clif.Function)
    (vcp : VCode) (rf : RFunc) (af : AFunc) (fa : FnAsm) (fb : FnBin) : Prop where
  run :
    ∀ {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXT : XTrapsOk env (f.externs.map (·.2)) (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicitC env p cs) {fuel : Nat} {tc : Clif.TrapCode}
    (hrun : Clif.runLoop env p fuel cs = .trapped tc),
    ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
      ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
      ∃ n, (∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
          (runX (ArmStepX X H fa) i s)) ∧
        spv (runX (ArmStepX X H fa) n s) = spv s - BitVec.ofNat 64 (frameDrop af) ∧
        (runX (ArmStepX X H fa) n s).program = fb.program base ∧
        ((TrapAt fb base tc (runX (ArmStepX X H fa) n s) ∧
            ∀ m, Arm.r .ERR (runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None) ∨
          CallTrapAt vcp F K G s fa base X (GotV vcp)
            (TrapCallSem env (f.externs.map (·.2)) (indSigs f)
              (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X tc)
            (runX (ArmStepX X H fa) n s))

/-- The old cleanup theorem supplies the same internal provider. -/
theorem worldTrapStopProvider_cleanup {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (lowerU : lowerCheckU f vc = true) (empty : p.funcs = [])
    (noTry : ∀ B ∈ f.blocks,B.term.isTry = false) :
    WorldTrapStopProvider p f vcp rf af fa fb where
  run := backend_correct_world_cleanup_trapstop hsub hc lowerU empty noTry

/-- The real Stock class derives its provider without a legacy-output condition. -/
theorem worldTrapStopProvider_callStore {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {result : Stock.Result} {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (checked : Stock.CallStore.check f result.code = true) {cleanup : Bool}
    (hc : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb) :
    WorldTrapStopProvider p f vcp rf af fa fb where
  run := by
    intro X syms slotOff env K F c covered calls indirect traps symbols slot world args source
      entered related arguments explicit fuel code trapped H G base ra s entry
    obtain ⟨n,stopped,trace,stack,program⟩ := backend_callee_trap_stop_stock_call_store
      hsub checked hc covered calls indirect traps symbols slot entered related arguments
      explicit trapped H G base ra s entry
    exact ⟨n,trace,stack,program,.inr stopped⟩

end E2E
