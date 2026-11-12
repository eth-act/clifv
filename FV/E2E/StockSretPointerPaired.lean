import FV.E2E.StockSretPointerWorld
import FV.E2E.StockMemorySretCopyNI

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000

/-- Complete source-to-machine paired correctness for the original
captured sret copy CFG. Source writes determine both updated memory relations; the
old source, ABI, linked-world and activation premises are preserved. -/
theorem backend_correct_world_niX_stock_sret_original_pointer {p : Clif.Program} {f : Clif.Function} {k : Nat} {result : Stock.Result} {vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (family : Stock.Memory.SretCopy.CfgClass f)
    (sret : (sigRets f.sig).any (·.purpose == .sret) = true) {cleanup : Bool}
    (readOnly : StockMemoryStoreCfg.effectsOnly result.code = true)
    (hc : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hTls : XTls F X)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (fuel : Nat) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (pointer : Clif.Val) (reg : Reg) (value : CV) (w : Arm.ArmState),
        sretArg f args = [pointer] ∧ VHolds pointer value ∧
        ReturnABI f [(reg,Reg.x 8)] ∧ [(reg,Reg.x 8)].length = [value].length ∧
        PrefixHold vals [value] ∧ MemRel F syms cm w ∧ result.code.RetsSite [(reg,Reg.x 8)] ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G [(reg,Reg.x 8)] [value] w s (runX (ArmStepX X H fa) n s) ∧
            VHolds pointer (regVal (runX (ArmStepX X H fa) n s) (.x 8)) ∧
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
            ∃ n, ActRet ra (fun a => F a ∨ D a) G [(reg,Reg.x 8)] [value] w s (runX (ArmStepX X H fa) n s) ∧
              VHolds pointer (regVal (runX (ArmStepX X H fa) n s) (.x 8)) ∧
              PostTrace fa af base (ArmStepX X H fa) s n ∧
              ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
                (runX (ArmStepX X H fa) i s)) := by
  intro vals cm returned
  have state : (⟨cs.frame,[],cs.mem⟩ : Clif.State) = cs := by
    have callers := hcs.callers
    cases cs
    cases callers
    rfl
  obtain ⟨entry,middle,target,i0,i8,j0,j8,base,destination,low,high,lf0,lf8,sf0,sf8,
    blocks,jump0,jump1,ret,entryMiddle,entryTarget,middleTarget,entryNops,targetNops,
    loadLow,loadHigh,storeLow,storeHigh,lowEarlier,highEarlier,shape,
    baseParameter,destinationParameter,ln0,ln8,sn0,sn8⟩ := family.shape
  have sourceReturn : Clif.runLoop env p fuel ⟨cs.frame,[],cs.mem⟩ = .returned vals cm := by rwa [state]
  have source := StockMemory.SretCopy.sret_copy_paired_return_function_canonical hc.lower family.scope family.dominated family.abi
    blocks jump0 jump1 ret rfl rfl entryMiddle entryTarget middleTarget entryNops targetNops
    loadLow loadHigh storeLow storeHigh lowEarlier highEarlier shape baseParameter destinationParameter
    ln0 ln8 sn0 sn8 hcs.stockSourceEntry family.registers sourceReturn
    (fc := ⟨fa.k,af.slotBase⟩) hslot hsym hTls (D := fun _ => False)
    ⟨hrel,hrel,SameWorld.refl _ w₀⟩ hargs hargs (fun _ _ _ => rfl)
  obtain ⟨us,outs,q,cm0,reached,pins,arity,values,memory,freed⟩ := source
  have first := (vRetFrom_pair reached).1
  have compatible := LinearCfg.legacy_compatible hc.lower family.scope blocks jump0 jump1 ret
    rfl rfl entryMiddle entryTarget middleTarget
  obtain ⟨pointer,reg,value,world,cmOriginal,original,reachedOriginal,held,memoryOriginal,freedOriginal⟩ :=
    family.x8_return_arguments sret hc.lower hcs.stockSourceEntry sourceReturn
      (refines_valueSem F ⟨fa.k,af.slotBase⟩ X)
      (driverSem_valueSem F ⟨fa.k,af.slotBase⟩ X)
      (memRefines_valueSem F ⟨fa.k,af.slotBase⟩ X hslot hsym)
      (mrStable_relW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c)
      (memRelOk_relW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c) hrel hargs
  have legacy : VRetFrom result.code (valueSem F ⟨fa.k,af.slotBase⟩ X)
      ⟨0,0,entrySeed result.ctx cs.frame,w₀⟩ [(reg,Reg.x 8)] [value] world := by
    obtain ⟨b,k,ρ,w,vb,ops,outputs,path,tail⟩ := reachedOriginal
    exact ⟨b,k,ρ,w,vb,ops,outputs,compatible.star path,tail⟩
  obtain ⟨selectedPins,selectedOuts,selectedWorld⟩ := vRetFrom_det (StockMemoryStoreCfg.return_value readOnly first) legacy
  subst us
  subst outs
  have site : result.code.RetsSite [(reg,Reg.x 8)] := by
    obtain ⟨b,k,ρ,w₁,vb,ops,outs',_,hvb,hk,_⟩ := first
    exact ⟨b,vb,k,hvb,hk⟩
  have mem : MemRel F syms cm q.1 := by
    rw [freed]
    exact memRel_leave (memRel_free memory.1.1.1 _)
  refine ⟨pointer,reg,value,q.1,original,held,pins.abi,arity,values,mem,site,?_,?_⟩
  · intro H G base ra s he
    obtain ⟨n,actual,trace,good⟩ := StockMemoryStoreCfg.machine_return readOnly hc.prepOk hc.check hc.alloc hc.emit hc.layout
      (fun _ h => h) hcov hargs (SameWorld.refl F q.1) first H G base ra s he
    refine ⟨n,actual,?_,trace,good⟩
    rw [actual.regs 0 reg (.x 8) value (by rfl) (by rfl)]
    exact held
  · intro D w₀' hrel' hsw hreg hstk H G base ra s he
    have arguments := ABIReadOnly.arguments_transport hargs hsw hreg hstk
    have pairedMemory : MRP ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c D
        cs.frame.slots cs.mem (w₀,w₀') :=
      ⟨hrel,hrel',sameWorld_zof hrel.1.1 hrel'.1.1 hsw (fun _ h => h)⟩
    have paired := StockMemory.SretCopy.sret_copy_paired_return_function_canonical hc.lower family.scope family.dominated family.abi
      blocks jump0 jump1 ret rfl rfl entryMiddle entryTarget middleTarget entryNops targetNops
      loadLow loadHigh storeLow storeHigh lowEarlier highEarlier shape baseParameter destinationParameter
      ln0 ln8 sn0 sn8 hcs.stockSourceEntry family.registers sourceReturn
      (fc := ⟨fa.k,af.slotBase⟩) hslot hsym hTls pairedMemory hargs arguments hreg
    obtain ⟨us',outs',q',cm0',reached',pins',arity',values',memory',freed'⟩ := paired
    obtain ⟨reference,other⟩ := vRetFrom_pair reached'
    obtain ⟨samePins,sameOuts,sameWorld⟩ := vRetFrom_det first reference
    rw [← samePins,← sameOuts] at other
    have related : SameWorld (fun a => F a ∨ D a) q'.2 q.1 := by
      rw [sameWorld]
      exact (SameWorld.mono (zof_sub cm0') memory'.2.2).symm
    obtain ⟨n,actual,trace,good⟩ := StockMemoryStoreCfg.machine_return readOnly hc.prepOk hc.check hc.alloc hc.emit hc.layout
      (fun _ h => Or.inl h) hcov arguments related other H G base ra s he
    refine ⟨n,actual,?_,trace,good⟩
    rw [actual.regs 0 reg (.x 8) value (by rfl) (by rfl)]
    exact held

end E2E


namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

def SretOriginalPointerPaired (f : Clif.Function) (k : Nat) (result : Stock.Result)
    (vcp : VCode) (rf : RFunc) (af : AFunc) (fa : FnAsm) (fb : FnBin) : Prop :=
  ∀ {p : Clif.Program}
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hTls : XTls F X)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (fuel : Nat),
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (pointer : Clif.Val) (reg : Reg) (value : CV) (w : Arm.ArmState),
        sretArg f args = [pointer] ∧ VHolds pointer value ∧
        ReturnABI f [(reg,Reg.x 8)] ∧ [(reg,Reg.x 8)].length = [value].length ∧
        PrefixHold vals [value] ∧ MemRel F syms cm w ∧ result.code.RetsSite [(reg,Reg.x 8)] ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G [(reg,Reg.x 8)] [value] w s (runX (ArmStepX X H fa) n s) ∧
            VHolds pointer (regVal (runX (ArmStepX X H fa) n s) (.x 8)) ∧
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
            ∃ n, ActRet ra (fun a => F a ∨ D a) G [(reg,Reg.x 8)] [value] w s (runX (ArmStepX X H fa) n s) ∧
              VHolds pointer (regVal (runX (ArmStepX X H fa) n s) (.x 8)) ∧
              PostTrace fa af base (ArmStepX X H fa) s n ∧
              ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
                (runX (ArmStepX X H fa) i s))

theorem sret_original_pointer_paired_of_stage
    {f : Clif.Function} {k : Nat} {result : Stock.Result} {vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (family : Stock.Memory.SretCopy.CfgClass f)
    (sret : (sigRets f.sig).any (·.purpose == .sret) = true) {cleanup : Bool}
    (effects : StockMemoryStoreCfg.effectsOnly result.code = true)
    (stage : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb) :
    SretOriginalPointerPaired f k result vcp rf af fa fb := by
  intro p X syms slotOff env K F c hcov hsym hslot hTls w args cs hcs hrel hargs fuel
  exact backend_correct_world_niX_stock_sret_original_pointer family sret effects stage
    hcov hsym hslot hTls hcs hrel hargs fuel
end E2E

