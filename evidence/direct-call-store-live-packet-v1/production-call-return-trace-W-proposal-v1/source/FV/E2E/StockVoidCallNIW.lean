import FV.E2E.StockVoidCallNI
import FV.E2E.DeadCleanupRegLevelW
import FV.E2E.WorldReturnTraceCore

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- The internal void-call view changes no instruction footprint. -/
theorem actGoodXW_of_voidCalls {vc : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {base : BitVec 64} {s u : Arm.ArmState} {X : ExtSem} {H : ArmHooks} {K : Nat}
    {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (good : actGoodXW vc rf af fa fb base s X.voidCalls H K G gv u) :
    actGoodXW vc rf af fa fb base s X H K G gv u := by
  exact ⟨actGoodX_of_voidCalls good.1,good.2⟩

theorem stock_void_call_machine_returnW {f : Clif.Function} {k : Nat} {result : Stock.Result}
    {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {cleanup : Bool}
    (hc : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb)
    (noTry : result.code.hasTryCall = false)
    {X : ExtSem} {K : Nat} {F Z : BitVec 64 → Prop}
    (covers : ∀ a,F a → Z a) (covered : FormsCovered ⟨fa.k,af.slotBase⟩ vcp)
    {initial final reference : Arm.ArmState} (worlds : SameWorld Z final reference)
    {ρ : Nat → CV} {us : List (Reg × Reg)} {outs : List CV}
    (returned : VReturns result.code (valueSem F ⟨fa.k,af.slotBase⟩ X.voidCalls) ρ initial us outs final)
    (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState)
    (entry : ActEntry vcp rf af fa fb K F G X H base ra s initial) :
    ∃ n,ActRet ra Z G us outs reference s (runX (ArmStepX X H fa) n s) ∧
      PostTrace fa af base (ArmStepX X H fa) s n ∧
      ∀ i < n,actGoodXW vcp rf af fa fb base s X H K G (GotV vcp)
        (runX (ArmStepX X H fa) i s) := by
  have preparedNoTry : vcp.hasTryCall = false := noTryCall_of_prepCheck hc.prepOk (by
    cases cleanup with
    | false => exact noTry
    | true => exact Backend.DeadCleanup.prune_noTryCall noTry)
  have internal := entry.voidCalls preparedNoTry
  have staged := StockArithmeticStage_returns hc.prepOk returned
  have machine := regLevelCorrect_worldX_valueW hc.check hc.alloc hc.emit hc.layout
    (X := X.voidCalls) (H := H) (K := K) (G := G) (gv := GotV vcp)
    covered internal.abi internal.stack internal.gfree (by rw [internal.hF]; exact internal.calls)
    (by rw [internal.hF]; exact internal.tries) (by rw [internal.hF]; exact internal.tls)
    (by rw [internal.hF]; exact internal.body) ρ
  rw [internal.hF] at machine
  obtain ⟨n,⟨ret,regs,world,frame,kept,program,trace⟩,good⟩ :=
    machine.1 us outs final (vReturns_gotV_value staged)
  refine ⟨n,⟨ret,regs,?_,?_,kept,program⟩,trace,fun i before => actGoodXW_of_voidCalls (good i before)⟩
  · intro a outside
    exact (world a (fun hf => outside (covers a hf))).trans (worlds.2.1 a outside)
  · intro field unmasked fp sp
    exact (frame field unmasked fp sp).trans (worlds.1 field unmasked)


theorem backend_correct_world_niX_stock_void_callW {p : Clif.Program} {f : Clif.Function} {k : Nat} {result : Stock.Result} {vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (checked : Stock.VoidCall.NI.check f result.code = true) {cleanup : Bool}
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
  have checks := Bool.and_eq_true_iff.mp checked
  obtain ⟨actual,lowered,equal,scope,dominated,abi,⟨layout⟩,_⟩ := Stock.VoidCall.check_sound checks.1
  have sameResult : actual = result := Except.ok.inj (lowered.symm.trans hc.lower)
  subst actual
  have state : (⟨cs.frame,[],cs.mem⟩ : Clif.State) = cs := by
    have callers := hcs.callers
    cases cs
    cases callers
    rfl
  obtain ⟨empty,⟨path⟩⟩ := layout.source_run (fc := ⟨fa.k,af.slotBase⟩) hc.lower scope dominated hsub hcs.stockSourceEntry
    (by rwa [state]) hslot hsym checks.2 hrel hargs
  subst vals
  obtain ⟨before,out,preRun,related,beforeMemory,called,mem,reached⟩ := path.execute hcs.sig hargs hrel hX
  have noTry := Stock.VoidCall.NI.noTryCall_of_codeCheck checks.2
  have site : result.code.RetsSite [] := by
    obtain ⟨b,j,ρ,w₁,vb,ops,vs,_,atBlock,atInst,_⟩ := reached
    exact ⟨b,vb,j,atBlock,atInst⟩
  have finalMemory : MemRel F syms cm out := by
    rw [path.freed]
    exact memRel_leave (memRel_free mem.1.1 _)
  refine ⟨[],[],out,path.retABI,rfl,?_,finalMemory,site,?_,?_⟩
  · simp [PrefixHold]
  · intro H G base ra s entry
    exact stock_void_call_machine_returnW hc noTry (fun _ h => h) hcov (SameWorld.refl F out)
      reached H G base ra s entry
  · intro ni tls D other otherMemory worlds registers stack H G base ra s entry
    obtain ⟨final,finalWorlds,_,otherRun⟩ := path.execute_other hcs.sig hargs related beforeMemory called hX ni
      (fun _ h => Or.inl h) otherMemory worlds registers stack
    exact stock_void_call_machine_returnW hc noTry (fun _ h => Or.inl h) hcov finalWorlds
      otherRun H G base ra s entry


theorem worldReturnTraceProvider_voidCall {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {result : Stock.Result} {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (checked : Stock.VoidCall.NI.check f result.code = true) {cleanup : Bool}
    (hc : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb) :
    WorldReturnTraceProvider p f result.code vcp rf af fa fb (ReturnABI f) where
  run := backend_correct_world_niX_stock_void_callW hsub checked hc

end E2E
