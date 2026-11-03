import FV.E2E.ABIReadOnlyMachine
import FV.E2E.StockMemoryMachineReturnValueW

namespace E2E.ABIReadOnly
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- The existing read-only virtual realization retains the full checked W prefix. -/
theorem machine_returnW {f : Clif.Function} {args : List Clif.Val}
    (types : args.map (·.ty) = f.sig.params.map (·.ty))
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {k : Nat}
    {cleanup : Bool} (readOnly : Backend.ABIReadOnly.check f.sig vc = true)
    (prep : prepCheck (Stock.Arithmetic.stage cleanup vc) vcp = true)
    (check : checkAlloc vcp rf = .ok ()) (alloc : lowerRFunc vcp rf = .ok af)
    (emit : emitFunc k af = .ok fa) (layout : fa.layout = .ok fb)
    {X : ExtSem} {K : Nat} {F Z : BitVec 64 → Prop}
    (frame : ∀ a, F a → Z a) (covered : FormsCovered ⟨fa.k,af.slotBase⟩ vcp)
    {w reference : Arm.ArmState} (arguments : ArgsAtEntry F f.sig args w)
    (worlds : SameWorld Z w reference)
    {ρ : Nat → CV} {us : List (Reg × Reg)} {outs : List CV}
    (returned : VReturns vc (sem F ⟨fa.k,af.slotBase⟩ X) ρ w us outs w)
    (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState)
    (entry : ActEntry vcp rf af fa fb K F G X H base ra s w) :
    ∃ n, ActRet ra Z G us outs reference s (runX (ArmStepX X H fa) n s) ∧
      PostTrace fa af base (ArmStepX X H fa) s n ∧
      ∀ i < n, actGoodXW vcp rf af fa fb base s X H K G (GotV vcp)
        (runX (ArmStepX X H fa) i s) := by
  obtain ⟨t,valueRun,related⟩ := return_realize types readOnly arguments returned
  exact StockMemory.machine_return_valueW (f := f) prep check alloc emit layout frame covered
    arguments ((SameWorld.mono frame related).trans worlds) valueRun H G base ra s entry

end E2E.ABIReadOnly
