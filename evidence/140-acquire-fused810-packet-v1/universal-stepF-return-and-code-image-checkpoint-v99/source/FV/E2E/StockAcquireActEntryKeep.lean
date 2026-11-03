import FV.E2E.StockAcquireKeptWorld

namespace E2E.StockAcquirePending
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual absence of calls and TLS preserves the original activation contract under the kept-world extension.
The original hook pc and external-return fields remain unchanged. -/
theorem actEntry_keep_of_no_calls_no_tls {vc : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {K : Nat} {F G S : BitVec 64 → Prop} {X : ExtSem} {H : ArmHooks}
    {base ra : BitVec 64} {initial world : Arm.ArmState}
    (entry : ActEntry vc rf af fa fb K F G X H base ra initial world)
    (noCall : ∀ info,¬ vc.CallSite info) (noTls : vc.hasTls = false)
    (stackAvoids : ∀ a,S a → ¬ StackBelow (frameDrop af+K) (spv initial) a) :
    ActEntry vc rf af fa fb K (fun a => F a ∨ S a) (fun a => G a ∨ S a) X H base ra initial world := by
  refine ⟨entry.abi,entry.stack,?_,?_,?_,?_,?_,bodyEntryW_keep entry.body⟩
  · intro a marked
    exact marked.elim (entry.gfree a) (stackAvoids a)
  · rw [← entry.hF]
    funext a
    apply propext
    exact or_assoc.symm
  · exact ⟨fun ctx info site => (noCall info site).elim,entry.calls.pc,entry.calls.ext⟩
  · intro hasTls ctx info ti site
    exact (noCall info site.callSite).elim
  · intro present
    rw [noTls] at present
    cases present

/-- The kept-image update preserves the actual linked hooks at every depth. -/
theorem hooks_keep_image (L : LinkSys) (F S : BitVec 64 → Prop) (memory : Arm.Memory) :
    ∀ M,({L with F := F,Img := fun a => L.Img a ∨ S a,imgMem := memory} : LinkSys).hooks M = L.hooks M
  | 0 => rfl
  | M+1 => by
    simp only [LinkSys.hooks]
    rw [hooks_keep_image L F S memory M]

/-- The kept-image update preserves the actual model machine. -/
theorem mach_keep_image (L : LinkSys) (F S : BitVec 64 → Prop) (memory : Arm.Memory) (M : Nat) (f : Clif.Function) :
    ({L with F := F,Img := fun a => L.Img a ∨ S a,imgMem := memory} : LinkSys).mach M f = L.mach M f := by
  unfold LinkSys.mach
  rw [hooks_keep_image]

end E2E.StockAcquirePending
