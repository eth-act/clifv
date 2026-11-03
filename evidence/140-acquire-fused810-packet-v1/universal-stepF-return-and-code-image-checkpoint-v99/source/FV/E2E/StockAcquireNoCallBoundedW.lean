import FV.E2E.LinkGoodBoundedW

namespace E2E.LinkSys
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A good state cannot call when its actual prepared function has no call site. -/
theorem no_call_at_goodW (L : LinkSys) {g : Clif.Function}
    {G : BitVec 64 → Prop} {K : Nat} {gv : Nat → String → Prop}
    {X : ExtSem} {H : ArmHooks} {s t : Arm.ArmState}
    (layout : (L.A g).fa.layout = .ok (L.A g).fb)
    (fits : 4 * (L.A g).fb.words.size ≤ 2 ^ 64)
    (noCall : ∀ info, ¬ (L.A g).vcp.CallSite info)
    (good : actGoodXW (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb
      (L.A g).base s X H K G gv t) :
    (∀ h, ¬ L.CallsAtL g t h) ∧ L.BlrAt g t := by
  obtain ⟨x,line,tail⟩ := good.1.line
  obtain ⟨j,tt,located,pc⟩ := line
  obtain ⟨lm,labels⟩ := FnAsm.layout_labelOffsets layout
  have located' : (L.A g).fa.lines.toList[j]? = some (.ins x tt) := located
  have atProg : insnAt (L.A g).fa (progBase t) (Arm.r .PC t) = some x := by
    rw [pc]
    exact insnAt_ofLine layout labels fits good.1.prog located'
  have atBase : insnAt (L.A g).fa (L.A g).base (Arm.r .PC t) = some x := by
    rw [pc]
    apply insnAt_line _ located'
    rw [layout_sum layout]
    exact fits
  have notCall : ((∃ name,x = .bl name) ∨ ∃ reg,x = .blr reg) → False := by
    intro kind
    obtain ⟨ctx,i,ctl,⟨info,site,shape⟩,rest⟩ := good.1.call x ⟨j,tt,located,pc⟩ kind
    exact noCall info site
  constructor
  · intro h called
    rcases called with ⟨name,foundAt,found⟩ | ⟨⟨reg,foundAt⟩,found⟩
    · rw [atProg] at foundAt
      cases foundAt
      exact notCall (.inl ⟨name,rfl⟩)
    · rw [atProg] at foundAt
      cases foundAt
      exact notCall (.inr ⟨reg,rfl⟩)
  · intro reg h foundAt found
    rw [atBase] at foundAt
    cases foundAt
    exact (notCall (.inr ⟨reg,rfl⟩)).elim

/-- A bounded no-call trace needs no global callee induction or source-class restriction. -/
theorem runGoodB_of_no_call_traceW (L : LinkSys) {M n : Nat} {g : Clif.Function}
    {G : BitVec 64 → Prop} {K : Nat} {gv : Nat → String → Prop} {s : Arm.ArmState}
    (layout : (L.A g).fa.layout = .ok (L.A g).fb)
    (fits : 4 * (L.A g).fb.words.size ≤ 2 ^ 64)
    (noCall : ∀ info, ¬ (L.A g).vcp.CallSite info)
    (image : ∀ a,L.Img a → G a)
    (imageMem : ∀ a,L.Img a → s.mem a = L.imgMem a)
    (trace : ∀ k < n,actGoodXW (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb
      (L.A g).base s L.Xb (L.hooks M) K G gv (runX (L.mach M g) k s)) :
    L.RunGoodLBW n M g s := by
  intro M' g' c' t reached errorFree
  rcases reached with ⟨k,before,noReturn,rfl,rfl,rfl,rfl⟩ |
    ⟨M0,k,h,depth,before,noReturn,called,errorFree',nested⟩
  · have good := trace k before
    exact ⟨L.Xb,K,G,gv,rfl,good,image,imageMem,(L.no_call_at_goodW layout fits noCall good).2⟩
  · subst M
    exact ((L.no_call_at_goodW layout fits noCall (trace k before)).1 h called).elim

end E2E.LinkSys
