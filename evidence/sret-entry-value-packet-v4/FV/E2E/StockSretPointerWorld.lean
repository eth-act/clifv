import FV.Backend.Proof.StockMemorySretCopyEntryValue
import FV.E2E.StockMemoryABIWorldX
import FV.Backend.Proof.StockLinearCfgCompatibility

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- The actual physical return preserves the original source pointer through both cleanup modes. -/
theorem backend_correct_worldX_stock_sret_original_pointer
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {result : Stock.Result} {vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (family : Stock.Memory.SretCopy.CfgClass f)
    (sret : (sigRets f.sig).any (·.purpose == .sret) = true) {cleanup : Bool}
    (hc : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k,af.slotBase⟩ vcp)
    (hsym : ∀ name base,syms name = some base → X.sym name 0 = BitVec.ofNat 64 base)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (fuel : Nat) :
    ∀ vals cm,Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (pointer : Clif.Val) (reg : Reg) (value : CV) (world : Arm.ArmState),
        sretArg f args = [pointer] ∧ VHolds pointer value ∧ MemRel F syms cm world ∧
        result.code.RetsSite [(reg,.x 8)] ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (initial : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra initial w₀ →
          ∃ n,ActRet ra F G [(reg,.x 8)] [value] world initial (runX (ArmStepX X H fa) n initial) ∧
            VHolds pointer (regVal (runX (ArmStepX X H fa) n initial) (.x 8)) ∧
            PostTrace fa af base (ArmStepX X H fa) initial n ∧
            ∀ i < n,actGoodX vcp rf af fa fb base initial X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i initial) := by
  have state : (⟨cs.frame,[],cs.mem⟩ : Clif.State) = cs := by
    have callers := hcs.callers
    cases cs
    cases callers
    rfl
  obtain ⟨entry,middle,target,i0,i8,j0,j8,base,destination,low,high,lf0,lf8,sf0,sf8,
    blocks,jump0,jump1,ret,entryMiddle,entryTarget,middleTarget,entryNops,targetNops,
    loadLow,loadHigh,storeLow,storeHigh,lowEarlier,highEarlier,shape,
    baseParameter,destinationParameter,ln0,ln8,sn0,sn8⟩ := family.shape
  have compatible := LinearCfg.legacy_compatible hc.lower family.scope blocks jump0 jump1 ret
    rfl rfl entryMiddle entryTarget middleTarget
  intro vals cm returned
  obtain ⟨pointer,reg,value,world,cm0,original,reached,held,memory,freed⟩ :=
    family.x8_return_arguments sret hc.lower hcs.stockSourceEntry (by rwa [state])
      (refines_valueSem F ⟨fa.k,af.slotBase⟩ X)
      (driverSem_valueSem F ⟨fa.k,af.slotBase⟩ X)
      (memRefines_valueSem F ⟨fa.k,af.slotBase⟩ X hslot hsym)
      (mrStable_relW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c)
      (memRelOk_relW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c) hrel hargs
  have legacy : VRetFrom result.code (valueSem F ⟨fa.k,af.slotBase⟩ X)
      ⟨0,0,entrySeed result.ctx cs.frame,w₀⟩ [(reg,.x 8)] [value] world := by
    obtain ⟨b,k,ρ,w,vb,ops,outputs,path,tail⟩ := reached
    exact ⟨b,k,ρ,w,vb,ops,outputs,compatible.star path,tail⟩
  have staged := StockArithmeticStage_returns hc.prepOk legacy
  have site : result.code.RetsSite [(reg,.x 8)] := by
    obtain ⟨b,k,ρ,w,vb,ops,outputs,path,placed,instruction,tail⟩ := reached
    exact ⟨b,vb,k,placed,instruction⟩
  have related : MemRel F syms cm world := by
    rw [freed]
    exact memRel_leave (memRel_free memory.1.1 _)
  refine ⟨pointer,reg,value,world,original,held,related,site,?_⟩
  intro H G base ra initial entered
  have machine := regLevelCorrect_worldX_value hc.check hc.alloc hc.emit hc.layout
    (X := X) (H := H) (K := K) (G := G) (gv := GotV vcp)
    hcov entered.abi entered.stack entered.gfree (by rw [entered.hF]; exact entered.calls)
    (by rw [entered.hF]; exact entered.tries) (by rw [entered.hF]; exact entered.tls)
    (by rw [entered.hF]; exact entered.body) (entrySeed result.ctx cs.frame)
  rw [entered.hF] at machine
  obtain ⟨n,⟨h1,h2,h3,h4,h5,h6,h7⟩,h8⟩ :=
    machine.1 [(reg,.x 8)] [value] world (vReturns_gotV_value staged)
  have actual : ActRet ra F G [(reg,.x 8)] [value] world initial (runX (ArmStepX X H fa) n initial) :=
    ⟨h1,h2,h3,h4,h5,h6⟩
  refine ⟨n,actual,?_,h7,h8⟩
  rw [actual.regs 0 reg (.x 8) value (by rfl) (by rfl)]
  exact held
end E2E

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

def SretOriginalPointerWorld (f : Clif.Function) (k : Nat) (result : Stock.Result)
    (vcp : VCode) (rf : RFunc) (af : AFunc) (fa : FnAsm) (fb : FnBin) : Prop :=
  ∀ {p : Clif.Program}
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k,af.slotBase⟩ vcp)
    (hsym : ∀ name base,syms name = some base → X.sym name 0 = BitVec.ofNat 64 base)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (fuel : Nat),
    ∀ vals cm,Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (pointer : Clif.Val) (reg : Reg) (value : CV) (world : Arm.ArmState),
        sretArg f args = [pointer] ∧ VHolds pointer value ∧ MemRel F syms cm world ∧
        result.code.RetsSite [(reg,.x 8)] ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (initial : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra initial w₀ →
          ∃ n,ActRet ra F G [(reg,.x 8)] [value] world initial (runX (ArmStepX X H fa) n initial) ∧
            VHolds pointer (regVal (runX (ArmStepX X H fa) n initial) (.x 8)) ∧
            PostTrace fa af base (ArmStepX X H fa) initial n ∧
            ∀ i < n,actGoodX vcp rf af fa fb base initial X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i initial)

theorem sret_original_pointer_world_of_stage
    {f : Clif.Function} {k : Nat} {result : Stock.Result} {vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (family : Stock.Memory.SretCopy.CfgClass f)
    (sret : (sigRets f.sig).any (·.purpose == .sret) = true) {cleanup : Bool}
    (stage : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb) :
    SretOriginalPointerWorld f k result vcp rf af fa fb := by
  intro p X syms slotOff env K F c hcov hsym hslot w args cs hcs hrel hargs fuel
  exact backend_correct_worldX_stock_sret_original_pointer family sret stage hcov hsym hslot hcs hrel hargs fuel
end E2E

