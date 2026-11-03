import FV.E2E.StockLiveCallNI
import FV.E2E.StockMemoryMachineReturnValueW
import FV.E2E.WorldReturnTraceCore

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

theorem backend_correct_world_niX_stock_live_callW {p : Clif.Program} {f : Clif.Function} {k : Nat} {result : Stock.Result} {vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (checked : Stock.LiveCall.check f result.code = true) {cleanup : Bool}
    (hc : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb)
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
        ReturnABI f us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ result.code.RetsSite us ∧
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
  intro vals cm returned
  obtain ⟨actual,lowered,equal,scope,dominated,abi,⟨layout⟩,_⟩ := Stock.LiveCall.check_sound checked
  have sameResult : actual = result := Except.ok.inj (lowered.symm.trans hc.lower)
  subst actual
  have state : (⟨cs.frame,[],cs.mem⟩ : Clif.State) = cs := by
    have callers := hcs.callers
    cases cs
    cases callers
    rfl
  obtain ⟨path,values⟩ := layout.ready (fc := ⟨fa.k,af.slotBase⟩) hc.lower scope dominated
    hsub hcs.stockSourceEntry (by rwa [state]) hslot hsym hrel hargs
  subst vals
  obtain ⟨before,output,after,final,preRun,related,beforeMemory,called,held,mem,finalWorld,reached⟩ :=
    path.execute hcs.sig hargs hrel hX
  have sumHeld := path.sum_holds held
  have site : result.code.RetsSite (retPairs [(path.sum,.x 0)]) := by
    obtain ⟨b,j,ρ,w₁,vb,ops,vs,_,atBlock,atInst,_⟩ := reached
    exact ⟨b,vb,j,atBlock,atInst⟩
  have finalRelated := mrStable_relW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c
    cs.frame.slots path.after after final finalWorld.nf mem
  have finalMemory : MemRel F syms cm final := by
    rw [path.freed]
    exact memRel_leave (memRel_free finalRelated.1.1 _)
  refine ⟨retPairs [(path.sum,.x 0)],[path.sumValue output],final,path.retABI,rfl,?_,finalMemory,site,?_,?_⟩
  · refine ⟨Nat.le_refl _,?_⟩
    intro j value actual found atOutput
    cases j with
    | zero =>
      have sourceEq : (⟨.i64,path.returnedWord+path.liveWord⟩ : Clif.Val) = value := Option.some.inj found
      have outputEq : path.sumValue output = actual := Option.some.inj atOutput
      subst value
      subst actual
      exact sumHeld
    | succ j => simp at found
  · intro H G base ra s entry
    exact StockMemory.machine_return_valueW (f := f) hc.prepOk hc.check hc.alloc hc.emit hc.layout (fun _ h => h) hcov hargs (SameWorld.refl F final)
      reached H G base ra s entry
  · intro ni tls D other otherMemory worlds registers stack H G base ra s entry
    obtain ⟨otherFinal,finalWorlds,_,otherRun⟩ := path.execute_other hcs.sig hargs related beforeMemory
      called finalWorld hX ni (fun _ h => Or.inl h) otherMemory worlds registers stack
    have otherArguments := ABIReadOnly.arguments_transport hargs worlds registers stack
    exact StockMemory.machine_return_valueW (f := f) hc.prepOk hc.check hc.alloc hc.emit hc.layout (fun _ h => Or.inl h) hcov otherArguments finalWorlds
      otherRun H G base ra s entry


theorem worldReturnTraceProvider_liveCall {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {result : Stock.Result} {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (checked : Stock.LiveCall.check f result.code = true) {cleanup : Bool}
    (hc : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb) :
    WorldReturnTraceProvider p f result.code vcp rf af fa fb (ReturnABI f) where
  run := backend_correct_world_niX_stock_live_callW hsub checked hc

end E2E
