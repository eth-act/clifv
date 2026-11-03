import FV.E2E.CompiledSemanticReturnPins
import FV.E2E.CompiledSemanticReturnTraceW
import FV.E2E.StockMemorySretCopyNIW
import FV.E2E.StockMemoryABIWorldXW
import FV.E2E.StockVoidCallNIW
import FV.E2E.StockResultCallNIW
import FV.E2E.StockLiveCallNIW
import FV.E2E.WorldReturnTraceCallStore

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

theorem backend_correct_world_niX_semantic_return_pinsW {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {mode : ReturnPinMode}
    (hsub : InSubset p f) (hc : CompiledSemanticReturnPins f k vc vcp rf af fa fb mode)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        ReturnPinMode.Valid mode f us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodXW vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
          (CallLg env (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
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
              ∀ i < n, actGoodXW vcp rf af fa fb base s X H K G (GotV vcp)
                (runX (ArmStepX X H fa) i s)) := by
  cases hc with
  | compatible old =>
    intro vals cm returned
    obtain ⟨us,outs,w,pins,arity,values,memory,site,run,paired⟩ :=
      backend_correct_world_niX_semanticW hsub old hcov hX hXI hsym hslot hcs hrel hargs htr fuel vals cm returned
    exact ⟨us,outs,w,pins,arity,values,memory,site,run,paired⟩
  | memorySretCopy family equal effects h =>
    subst vc
    classical
    by_cases tls : XTls F X
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,run,paired⟩ :=
        backend_correct_world_niX_stock_sret_copy_memoryW family effects h hcov hsym hslot tls hcs hrel hargs
          fuel vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,run,fun _ _ => paired⟩
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,run⟩ :=
        (backend_correct_worldX_stock_memory_abiW family.domainABI h hcov hsym hslot hcs hrel hargs fuel).1 vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,run,fun _ positive => False.elim (tls positive)⟩
  | voidCall source equal h =>
    subst vc
    exact backend_correct_world_niX_stock_void_callW hsub source h hcov hX hXI hsym hslot hcs hrel hargs htr fuel
  | resultCall source equal h =>
    subst vc
    exact backend_correct_world_niX_stock_result_callW hsub source h hcov hX hXI hsym hslot hcs hrel hargs htr fuel


  | liveCall source equal h =>
    subst vc
    exact backend_correct_world_niX_stock_live_callW hsub source h hcov hX hXI hsym hslot hcs hrel hargs htr fuel


  | callStore source equal h =>
    subst vc
    exact (worldReturnTraceProvider_callStore hsub source h).run hcov hX hXI hsym hslot hcs hrel hargs htr fuel


theorem worldReturnTraceProvider_artifact {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {mode : ReturnPinMode}
    (hsub : InSubset p f) (hc : CompiledSemanticReturnPins f k vc vcp rf af fa fb mode) :
    WorldReturnTraceProvider p f vc vcp rf af fa fb (mode.Valid f) where
  run := backend_correct_world_niX_semantic_return_pinsW hsub hc

end E2E
