import FV.E2E.StockAcquireNoCallBoundedW
import FV.E2E.StockAcquireLinkedBaseEntry

namespace E2E.LinkSys
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A bounded no-call trace needs no global callee induction or source-class restriction. -/
theorem runGoodB_of_no_call_traceW_machine (L : LinkSys) {M n : Nat} {g : Clif.Function}
    {G : BitVec 64 → Prop} {K : Nat} {gv : Nat → String → Prop} {s : Arm.ArmState} {X : ExtSem}
    (layout : (L.A g).fa.layout = .ok (L.A g).fb)
    (fits : 4 * (L.A g).fb.words.size ≤ 2 ^ 64)
    (noCall : ∀ info, ¬ (L.A g).vcp.CallSite info)
    (image : ∀ a,L.Img a → G a)
    (imageMem : ∀ a,L.Img a → s.mem a = L.imgMem a)
    (stepEq : ArmStepX X (L.hooks M) (L.A g).fa = L.mach M g)
    (trace : ∀ k < n,actGoodXW (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb
      (L.A g).base s X (L.hooks M) K G gv (runX (L.mach M g) k s)) :
    L.RunGoodLBW n M g s := by
  intro M' g' c' t reached errorFree
  rcases reached with ⟨k,before,noReturn,rfl,rfl,rfl,rfl⟩ |
    ⟨M0,k,h,depth,before,noReturn,called,errorFree',nested⟩
  · have good := trace k before
    exact ⟨X,K,G,gv,stepEq,good,image,imageMem,(L.no_call_at_goodW layout fits noCall good).2⟩
  · subst M
    exact ((L.no_call_at_goodW layout fits noCall (trace k before)).1 h called).elim


end E2E.LinkSys
