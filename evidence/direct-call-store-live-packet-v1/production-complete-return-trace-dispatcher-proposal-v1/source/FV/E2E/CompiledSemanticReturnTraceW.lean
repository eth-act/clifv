import FV.E2E.CompiledSemanticNI
import FV.E2E.CompiledProductionReturnTraceW
import FV.E2E.StockArithmeticNIW
import FV.E2E.StockMixedNIW
import FV.E2E.StockLogicalNIW
import FV.E2E.StockScalarNIW
import FV.E2E.StockDivNIW
import FV.E2E.StockCfgNIW
import FV.E2E.StockMemoryNIW
import FV.E2E.StockMemoryCfgNIW
import FV.E2E.StockMemoryIntegerNIW
import FV.E2E.StockMemoryExtLoadNIW
import FV.E2E.StockMemoryStoreNIW
import FV.E2E.StockMemoryStoreCfgNIW
import FV.E2E.StockMemoryLoadStoreNIW
import FV.E2E.StockMemoryCapturedCopyNIW
import FV.E2E.StockMemoryWorldXW
import FV.E2E.StockMemoryCfgWorldXW

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

theorem backend_correct_world_niX_semanticW {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledSemanticNI f k vc vcp rf af fa fb)
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
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
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
  | compatible h =>
    exact (worldReturnTraceProvider_production hsub h).run hcov hX hXI hsym hslot hcs hrel hargs htr fuel
  | arithmetic domain equal reads h =>
    subst vc
    intro vals cm returned
    obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
      backend_correct_world_niX_stock_arithmeticW domain reads h hcov hsym hslot hcs hrel hargs
        fuel vals cm returned
    exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩
  | mixed domain equal reads h =>
    subst vc
    intro vals cm returned
    obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
      backend_correct_world_niX_stock_mixedW domain reads h hcov hsym hslot hcs hrel hargs
        fuel vals cm returned
    exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩

  | logical domain equal reads h =>
    subst vc
    intro vals cm returned
    obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
      backend_correct_world_niX_stock_logicalW domain reads h hcov hsym hslot hcs hrel hargs
        fuel vals cm returned
    exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩

  | scalar domain equal reads h =>
    subst vc
    intro vals cm returned
    obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
      backend_correct_world_niX_stock_scalarW domain reads h hcov hsym hslot hcs hrel hargs
        fuel vals cm returned
    exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩
  | scalarDiv domain equal reads h =>
    subst vc
    intro vals cm returned
    obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
      backend_correct_world_niX_stock_divW domain reads h hcov hsym hslot hcs hrel hargs
        fuel vals cm returned
    exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩
  | cfg domain equal reads h =>
    subst vc
    intro vals cm returned
    obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
      backend_correct_world_niX_stock_cfgW domain reads h hcov hsym hslot hcs hrel hargs
        fuel vals cm returned
    exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩

  | memory family equal effects h =>
    subst vc
    classical
    by_cases tls : XTls F X
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
        backend_correct_world_niX_stock_memoryW family effects h hcov hsym hslot tls hcs hrel hargs
          fuel vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base⟩ :=
        (backend_correct_worldX_stock_memoryW family.domain h hcov hsym hslot hcs hrel hargs fuel).1 vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ positive => False.elim (tls positive)⟩

  | memoryCfg family equal effects h =>
    subst vc
    classical
    by_cases tls : XTls F X
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
        backend_correct_world_niX_stock_memory_cfgW family effects h hcov hsym hslot tls hcs hrel hargs
          fuel vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base⟩ :=
        (backend_correct_worldX_stock_memory_cfgW family effects h hcov hsym hslot hcs hrel hargs fuel).1 vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ positive => False.elim (tls positive)⟩

  | @memoryUnsigned width cleanup result family equal effects h =>
    subst vc
    classical
    by_cases tls : XTls F X
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
        backend_correct_world_niX_stock_integer_memoryW family effects h hcov hsym hslot tls hcs hrel hargs
          fuel vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base⟩ :=
        (backend_correct_worldX_stock_memoryW (Stock.Memory.IntegerRoots.SingleClass.domain width family) h hcov hsym hslot hcs hrel hargs fuel).1 vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ positive => False.elim (tls positive)⟩
  | @memoryExtending kind ty cleanup result family equal effects h =>
    subst vc
    classical
    by_cases tls : XTls F X
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
        backend_correct_world_niX_stock_extending_memoryW family effects h hcov hsym hslot tls hcs hrel hargs
          fuel vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base⟩ :=
        (backend_correct_worldX_stock_memoryW (Stock.Memory.ExtendedRoots.SingleClass.domain kind ty family) h hcov hsym hslot hcs hrel hargs fuel).1 vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ positive => False.elim (tls positive)⟩

  | @memoryStore kind ty cleanup result family equal effects h =>
    subst vc
    classical
    by_cases tls : XTls F X
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
        backend_correct_world_niX_stock_store_memoryW family effects h hcov hsym hslot tls hcs hrel hargs
          fuel vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base⟩ :=
        (backend_correct_worldX_stock_memoryW (Stock.Memory.StoreRoots.SingleClass.domain kind ty family) h hcov hsym hslot hcs hrel hargs fuel).1 vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ positive => False.elim (tls positive)⟩
  | @memoryStoreCfg kind ty cleanup result family equal effects h =>
    subst vc
    classical
    by_cases tls : XTls F X
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
        backend_correct_world_niX_stock_store_cfg_memoryW family effects h hcov hsym hslot tls hcs hrel hargs
          fuel vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base⟩ :=
        (backend_correct_worldX_stock_memoryW (Stock.Memory.StoreRoots.CfgClass.domain kind ty family) h hcov hsym hslot hcs hrel hargs fuel).1 vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ positive => False.elim (tls positive)⟩

  | @memoryLoadStore width kind ty cleanup result family equal effects h =>
    subst vc
    classical
    by_cases tls : XTls F X
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
        backend_correct_world_niX_stock_load_store_memoryW family effects h hcov hsym hslot tls hcs hrel hargs
          fuel vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base⟩ :=
        (backend_correct_worldX_stock_memoryW (Stock.Memory.LoadStore.SingleClass.domain width kind ty family) h hcov hsym hslot hcs hrel hargs fuel).1 vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ positive => False.elim (tls positive)⟩

  | @memoryCapturedCopy cleanup result family equal effects h =>
    subst vc
    classical
    by_cases tls : XTls F X
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base,paired⟩ :=
        backend_correct_world_niX_stock_captured_copy_memoryW family effects h hcov hsym hslot tls hcs hrel hargs
          fuel vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ _ => paired⟩
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,base⟩ :=
        (backend_correct_worldX_stock_memoryW family.domain h hcov hsym hslot hcs hrel hargs fuel).1 vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,base,fun _ positive => False.elim (tls positive)⟩



theorem worldReturnTraceProvider_semantic {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledSemanticNI f k vc vcp rf af fa fb) :
    WorldReturnTraceProvider p f vc vcp rf af fa fb
      (fun us => us.map (·.2) = (List.range us.length).map Reg.x) where
  run := backend_correct_world_niX_semanticW hsub hc

end E2E
