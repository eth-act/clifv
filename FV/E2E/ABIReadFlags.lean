module

public import FV.E2E.ABIReadBoundary

@[expose] public section

/-! Preserved flag-boundary variants using shared execution/ABI composition. -/
namespace E2E.MixedFlagBoundary
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

private noncomputable def boundaryModel : ABIReadBoundary.Model where
  instruction := Backend.ABIReadFlags.instruction
  eval := sem
  frame := checked_step_frame
  transport := checked_step_transport
  realize := Realize.step_realize

theorem star_transport {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {vc : VCode} (checked : check sig vc = true)
    {F Z : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {initial initial' : Arm.ArmState}
    (registers : ∀ r v, (.reg r,v) ∈ (locsOf sig).zip args →
      regVal initial' r = regVal initial r)
    (stack : ∀ (off : Nat) (v : Clif.Val), (.stack off,v) ∈ (locsOf sig).zip args →
      ∀ j < v.ty.bytes,
      initial'.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j) =
      initial.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j))
    {c c' d : VConf CV Arm.ArmState} (related : Related Z initial initial' c d)
    (path : Star (VStep vc (sem F ctx X)) c c') :
    ∃ d', Star (VStep vc (sem F ctx X)) d d' ∧ Related Z initial initial' c' d' := by
  exact ABIReadBoundary.star_transport (model := boundaryModel) types checked registers stack related path

theorem return_transport {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {vc : VCode} (checked : check sig vc = true)
    {F Z : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {initial initial' : Arm.ArmState} (worlds : SameWorld Z initial initial')
    (registers : ∀ r v, (.reg r,v) ∈ (locsOf sig).zip args →
      regVal initial' r = regVal initial r)
    (stack : ∀ (off : Nat) (v : Clif.Val), (.stack off,v) ∈ (locsOf sig).zip args →
      ∀ j < v.ty.bytes,
      initial'.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j) =
      initial.mem (Arm.r (.GPR 29#5) initial + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j))
    {ρ : Nat → CV} {us : List (Reg × Reg)} {outs : List CV} {world : Arm.ArmState}
    (returned : VReturns vc (sem F ctx X) ρ initial us outs world) :
    ∃ world', VReturns vc (sem F ctx X) ρ initial' us outs world' ∧ SameWorld Z world world' := by
  exact ABIReadBoundary.return_transport (model := boundaryModel) types checked worlds registers stack returned

namespace Realize
theorem star_realize {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {vc : VCode} (checked : check sig vc = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {initial : Arm.ArmState}
    (arguments : ArgsAtEntry F sig args initial)
    {c c' d : VConf CV Arm.ArmState} (related : Related F initial c d)
    (path : Star (VStep vc (sem F ctx X)) c c') :
    ∃ d', Star (VStep vc (valueSem F ctx X)) d d' ∧ Related F initial c' d' := by
  exact ABIReadBoundary.Realize.star_realize (model := boundaryModel) types checked arguments related path

theorem return_realize {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {vc : VCode} (checked : check sig vc = true)
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {initial : Arm.ArmState}
    (arguments : ArgsAtEntry F sig args initial)
    {ρ : Nat → CV} {us : List (Reg × Reg)} {outs : List CV} {world : Arm.ArmState}
    (returned : VReturns vc (sem F ctx X) ρ initial us outs world) :
    ∃ t, VReturns vc (valueSem F ctx X) ρ initial us outs t ∧ SameWorld F t world := by
  exact ABIReadBoundary.Realize.return_realize (model := boundaryModel) types checked arguments returned

end Realize

theorem machine_return {f : Clif.Function} {args : List Clif.Val}
    (types : args.map (·.ty) = f.sig.params.map (·.ty))
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {k : Nat}
    {cleanup : Bool} (readOnly : check f.sig vc = true)
    (prep : prepCheck (Stock.Arithmetic.stage cleanup vc) vcp = true)
    (check : checkAlloc vcp rf = .ok ()) (alloc : lowerRFunc vcp rf = .ok af)
    (emit : emitFunc k af = .ok fa) (layout : fa.layout = .ok fb)
    {X : ExtSem} {K : Nat} {F Z : BitVec 64 → Prop}
    (frame : ∀ a, F a → Z a) (covered : FormsCovered ⟨fa.k,af.slotBase⟩ vcp)
    {w final reference : Arm.ArmState} (arguments : ArgsAtEntry F f.sig args w)
    (worlds : SameWorld Z final reference)
    {ρ : Nat → CV} {us : List (Reg × Reg)} {outs : List CV}
    (returned : VReturns vc (sem F ⟨fa.k,af.slotBase⟩ X) ρ w us outs final)
    (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState)
    (entry : ActEntry vcp rf af fa fb K F G X H base ra s w) :
    ∃ n, ActRet ra Z G us outs reference s (runX (ArmStepX X H fa) n s) ∧
      PostTrace fa af base (ArmStepX X H fa) s n ∧
      ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
        (runX (ArmStepX X H fa) i s) := by
  exact ABIReadBoundary.machine_return (model := boundaryModel) types readOnly prep check alloc emit layout
    frame covered arguments worlds returned H G base ra s entry

end E2E.MixedFlagBoundary
