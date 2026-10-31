import FV.E2E.StockArithmeticStageContract
import FV.E2E.ABIReadOnlyMachine
import FV.E2E.ABIReadScalar
import FV.Backend.Proof.StockScalarContract

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- Complete source-to-machine non-interference for actual Stock scalar bodies.
The runtime ABI-read check derives the read boundary; no legacy lowering verdict,
second chosen virtual file or extra source-value assumption is needed. -/
theorem backend_correct_world_niX_stock_scalar {p : Clif.Program} {f : Clif.Function} {k : Nat} {result : Stock.Result} {vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (domain : Stock.Scalar.Domain f) {cleanup : Bool}
    (readOnly : E2E.ScalarBoundary.check f.sig result.code = true)
    (hc : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (fuel : Nat) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ result.code.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
        (∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
            ActEntry vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n ∧
              ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
                (runX (ArmStepX X H fa) i s)) := by
  intro vals cm returned
  have state : (⟨cs.frame,[],cs.mem⟩ : Clif.State) = cs := by
    have callers := hcs.callers
    cases cs
    cases callers
    rfl
  obtain ⟨ρ,source⟩ := domain.returns hc.lower hcs.stockSourceEntry
    (by rwa [state]) (ScalarBoundary.refines F ⟨fa.k,af.slotBase⟩ X)
    (ScalarBoundary.driver F ⟨fa.k,af.slotBase⟩ X)
    (ScalarBoundary.memory F ⟨fa.k,af.slotBase⟩ X hslot hsym)
    (mrStable_relW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c) hrel hargs
  obtain ⟨us,outs,w,cm0,reached,pins,arity,values,memory,freed⟩ := source
  have site : result.code.RetsSite us := by
    obtain ⟨b,k,ρ,w₁,vb,ops,outs',_,hvb,hk,_⟩ := reached
    exact ⟨b,vb,k,hvb,hk⟩
  have mem : MemRel F syms cm w := by
    rw [freed]
    exact memRel_leave (memRel_free memory.1.1 _)
  refine ⟨us,outs,w,pins.retPins domain.ordinary,arity,values,mem,site,?_,?_⟩
  · intro H G base ra s he
    exact ScalarBoundary.machine_return (f := f) hcs.sig readOnly hc.prepOk hc.check hc.alloc hc.emit hc.layout
      (fun _ h => h) hcov hargs (SameWorld.refl F w) reached H G base ra s he
  · intro D w₀' hrel' hsw hreg hstk H G base ra s he
    have arguments := ABIReadOnly.arguments_transport hargs hsw hreg hstk
    obtain ⟨otherWorld,other,relatedWorlds⟩ :=
      ScalarBoundary.return_transport hcs.sig readOnly hsw hreg hstk reached
    exact ScalarBoundary.machine_return (f := f) hcs.sig readOnly hc.prepOk hc.check hc.alloc hc.emit hc.layout
      (fun _ h => Or.inl h) hcov arguments relatedWorlds.symm other H G base ra s he

end E2E
