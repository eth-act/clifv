import FV.E2E.SemanticNIBoundary
import FV.E2E.StockMemoryABIWorldX
import FV.E2E.StockMemorySretCopyNI
import FV.Backend.Proof.StockMemorySretCopyCheck
import FV.Backend.Proof.StockMemorySretCopyDomain
import FV.Backend.SemanticABICheck
import FV.E2E.StockVoidCallNI

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Add ABI-aware memory artifacts while retaining every previous semantic artifact. -/
inductive CompiledSemanticABI (f : Clif.Function) (k : Nat) (vc vcp : VCode)
    (rf : RFunc) (af : AFunc) (fa : FnAsm) (fb : FnBin) : Prop where
  | compatible : CompiledSemanticNI f k vc vcp rf af fa fb →
      CompiledSemanticABI f k vc vcp rf af fa fb
  | memorySretCopy {cleanup : Bool} {result : Stock.Result} :
      Stock.Memory.SretCopy.CfgClass f → result.code = vc → Stock.MemoryStoreCfg.effectsOnly vc = true →
      CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb →
      CompiledSemanticABI f k vc vcp rf af fa fb

  | voidCall {cleanup : Bool} {result : Stock.Result} :
      Stock.VoidCall.NI.check f result.code = true → result.code = vc →
      CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb →
      CompiledSemanticABI f k vc vcp rf af fa fb

namespace CompiledSemanticABI
variable {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin}

/-- All artifact conditions follow from executable checks and the actual pipeline observations. -/
theorem of_checks {cleanup : Bool} (lower : SemanticABI.check f vc = true)
    (prepared : Backend.prepare (Stock.Arithmetic.stage cleanup vc) = .ok vcp)
    (prepOk : prepCheck (Stock.Arithmetic.stage cleanup vc) vcp = true)
    (check : Backend.checkAlloc vcp rf = .ok ()) (alloc : lowerRFunc vcp rf = .ok af)
    (emit : emitFunc k af = .ok fa) (layout : fa.layout = .ok fb) :
    CompiledSemanticABI f k vc vcp rf af fa fb := by
  rcases Bool.or_eq_true_iff.mp lower with old | memory
  · exact .compatible (CompiledSemanticNI.of_checks old prepared prepOk check alloc emit layout)
  · obtain ⟨result,family,run,equal,effects⟩ := Stock.MemorySretCopy.check_sound memory
    exact .memorySretCopy family equal effects
      ⟨run,by rwa [equal],by rwa [equal],check,alloc,emit,layout⟩

theorem of_checks_calls {cleanup : Bool} (lower : SemanticABI.checkCalls f vc = true)
    (prepared : Backend.prepare (Stock.Arithmetic.stage cleanup vc) = .ok vcp)
    (prepOk : prepCheck (Stock.Arithmetic.stage cleanup vc) vcp = true)
    (check : Backend.checkAlloc vcp rf = .ok ()) (alloc : lowerRFunc vcp rf = .ok af)
    (emit : emitFunc k af = .ok fa) (layout : fa.layout = .ok fb) :
    CompiledSemanticABI f k vc vcp rf af fa fb := by
  rcases Bool.or_eq_true_iff.mp lower with old | caller
  · exact of_checks old prepared prepOk check alloc emit layout
  · obtain ⟨result,run,equal,_,_,_,_,_⟩ := Stock.VoidCall.check_sound (Bool.and_eq_true_iff.mp caller).1
    exact .voidCall (by rwa [equal]) equal
      ⟨run,by rwa [equal],by rwa [equal],check,alloc,emit,layout⟩

theorem check (hc : CompiledSemanticABI f k vc vcp rf af fa fb) : Backend.checkAlloc vcp rf = .ok () := by
  cases hc with
  | compatible h => exact h.check
  | memorySretCopy _ _ _ h => exact h.check
  | voidCall _ _ h => exact h.check

theorem alloc (hc : CompiledSemanticABI f k vc vcp rf af fa fb) : lowerRFunc vcp rf = .ok af := by
  cases hc with
  | compatible h => exact h.alloc
  | memorySretCopy _ _ _ h => exact h.alloc
  | voidCall _ _ h => exact h.alloc

theorem emit (hc : CompiledSemanticABI f k vc vcp rf af fa fb) : emitFunc k af = .ok fa := by
  cases hc with
  | compatible h => exact h.emit
  | memorySretCopy _ _ _ h => exact h.emit
  | voidCall _ _ h => exact h.emit

theorem layout (hc : CompiledSemanticABI f k vc vcp rf af fa fb) : fa.layout = .ok fb := by
  cases hc with
  | compatible h => exact h.layout
  | memorySretCopy _ _ _ h => exact h.layout
  | voidCall _ _ h => exact h.layout

end CompiledSemanticABI

theorem backend_correct_world_niX_semantic_abi {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledSemanticABI f k vc vcp rf af fa fb)
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
        (us.map (·.2) = (List.range us.length).map Reg.x ∨ ReturnABI f us) ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
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
              ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
                (runX (ArmStepX X H fa) i s)) := by
  cases hc with
  | compatible old =>
    intro vals cm returned
    obtain ⟨us,outs,w,pins,arity,values,memory,site,run,paired⟩ :=
      backend_correct_world_niX_semantic hsub old hcov hX hXI hsym hslot hcs hrel hargs htr fuel vals cm returned
    exact ⟨us,outs,w,.inl pins,arity,values,memory,site,run,paired⟩
  | memorySretCopy family equal effects h =>
    subst vc
    classical
    by_cases tls : XTls F X
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,run,paired⟩ :=
        backend_correct_world_niX_stock_sret_copy_memory family effects h hcov hsym hslot tls hcs hrel hargs
          fuel vals cm returned
      exact ⟨us,outs,w,.inr pins,arity,values,memory,site,run,fun _ _ => paired⟩
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,run⟩ :=
        (backend_correct_worldX_stock_memory_abi family.domainABI h hcov hsym hslot hcs hrel hargs fuel).1 vals cm returned
      exact ⟨us,outs,w,.inr pins,arity,values,memory,site,run,fun _ positive => False.elim (tls positive)⟩
  | voidCall source equal h =>
    subst vc
    intro vals cm returned
    obtain ⟨us,outs,w,pins,arity,values,memory,site,run,paired⟩ :=
      backend_correct_world_niX_stock_void_call hsub source h hcov hX hXI hsym hslot hcs hrel hargs htr
        fuel vals cm returned
    exact ⟨us,outs,w,.inr pins,arity,values,memory,site,run,paired⟩

end E2E
