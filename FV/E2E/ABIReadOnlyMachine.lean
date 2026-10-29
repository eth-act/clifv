module

public import FV.E2E.ABIReadOnlyRealize
public import FV.E2E.StockArithmeticStage
public import FV.E2E.LinkWorld
public import FV.E2E.DeadCleanupRegLevelX
public import FV.E2E.DeadCleanupGot

@[expose] public section

namespace E2E.ABIReadOnly
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- The existing checked preparation/allocation machine consumer realizes the
read-only run in either cleanup mode, including a wider non-interference world.
Initial virtual values stay proof-internal in the complete source consumer. -/
theorem machine_return {f : Clif.Function} {args : List Clif.Val}
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
      ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
        (runX (ArmStepX X H fa) i s) := by
  obtain ⟨t,valueRun,related⟩ := return_realize types readOnly arguments returned
  have finalWorld := (SameWorld.mono frame related).trans worlds
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

/-- The original ABI agreement transfers the original argument premise. -/
theorem arguments_transport {sig : Clif.Signature} {args : List Clif.Val}
    {F Z : BitVec 64 → Prop} {w w' : Arm.ArmState} (arguments : ArgsAtEntry F sig args w)
    (worlds : SameWorld Z w w')
    (registers : ∀ r v, (.reg r,v) ∈ (locsOf sig).zip args → regVal w' r = regVal w r)
    (stack : ∀ (off : Nat) (v : Clif.Val), (.stack off,v) ∈ (locsOf sig).zip args → ∀ j < v.ty.bytes,
      w'.mem (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j) =
      w.mem (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j)) :
    ArgsAtEntry F sig args w' := by
  intro loc v member
  have arg := arguments loc v member
  cases loc with
  | reg pin =>
    change VHolds v (regVal w' pin)
    rw [registers pin v member]
    exact arg
  | stack off =>
    have fp : Arm.r (.GPR 29#5) w' = Arm.r (.GPR 29#5) w :=
      (worlds.1 (.GPR 29#5) (by simp [Masked])).symm
    change Avoids F v.ty.bytes _ ∧ _
    rw [fp]
    refine ⟨arg.1,?_⟩
    rw [read_mem_bytes_congr v.ty.bytes _ (stack off v member)]
    exact arg.2

end E2E.ABIReadOnly
