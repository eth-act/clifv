import FV.E2E.StockArithmeticStageContract
import FV.E2E.StockMemoryMachine
import FV.Backend.Proof.StockMemoryExtLoadClass
import FV.E2E.StockMemoryExtLoadPairedFunction
import FV.E2E.ABIReadOnlyMachine

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000

/-- Complete source-to-machine paired correctness for the first original
load/return class. Initialized original bytes determine both load outputs; the
old source, ABI, linked-world and activation premises are preserved. -/
theorem backend_correct_world_niX_stock_extending_memory {kind : Stock.Memory.ExtendedRoots.Kind} {ty : Clif.Ty} {p : Clif.Program} {f : Clif.Function} {k : Nat} {result : Stock.Result} {vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (family : Stock.Memory.ExtendedRoots.SingleClass kind ty f) {cleanup : Bool}
    (readOnly : StockMemory.effectsOnly result.code = true)
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
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
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
  obtain ⟨b,x,z,flags,blocks,body,ret,parameter,notrap⟩ := family.shape
  have sourceReturn : Clif.runLoop env p fuel ⟨cs.frame,[],cs.mem⟩ = .returned vals cm := by rwa [state]
  have source := StockMemory.ExtendedRoots.single_extending_load_return_paired_function_seeded kind ty hc.lower family.scope family.dominated family.abi
    blocks body ret parameter hcs.stockSourceEntry sourceReturn family.registers (fc := ⟨fa.k,af.slotBase⟩) hslot hsym hTls
    (D := fun _ => False) ⟨hrel,hrel,SameWorld.refl _ w₀⟩ hargs hargs (fun _ _ _ => rfl)
  obtain ⟨us,outs,q,cm0,reached,pins,arity,values,memory,freed⟩ := source
  have first := (vRetFrom_pair reached).1
  have site : result.code.RetsSite us := by
    obtain ⟨b,k,ρ,w₁,vb,ops,outs',_,hvb,hk,_⟩ := first
    exact ⟨b,vb,k,hvb,hk⟩
  have mem : MemRel F syms cm q.1 := by
    rw [freed]
    exact memRel_leave (memRel_free memory.1.1.1 _)
  refine ⟨us,outs,q.1,pins.ordinary family.ordinary,arity,values,mem,site,?_,?_⟩
  · intro H G base ra s he
    exact StockMemory.machine_return readOnly hc.prepOk hc.check hc.alloc hc.emit hc.layout
      (fun _ h => h) hcov hargs (SameWorld.refl F q.1) first H G base ra s he
  · intro D w₀' hrel' hsw hreg hstk H G base ra s he
    have arguments := ABIReadOnly.arguments_transport hargs hsw hreg hstk
    have pairedMemory : MRP ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c D
        cs.frame.slots cs.mem (w₀,w₀') :=
      ⟨hrel,hrel',sameWorld_zof hrel.1.1 hrel'.1.1 hsw (fun _ h => h)⟩
    have paired := StockMemory.ExtendedRoots.single_extending_load_return_paired_function_seeded kind ty hc.lower family.scope family.dominated family.abi
      blocks body ret parameter hcs.stockSourceEntry sourceReturn family.registers (fc := ⟨fa.k,af.slotBase⟩) hslot hsym hTls
      pairedMemory hargs arguments hreg
    obtain ⟨us',outs',q',cm0',reached',pins',arity',values',memory',freed'⟩ := paired
    obtain ⟨reference,other⟩ := vRetFrom_pair reached'
    obtain ⟨samePins,sameOuts,sameWorld⟩ := vRetFrom_det first reference
    rw [← samePins,← sameOuts] at other
    have related : SameWorld (fun a => F a ∨ D a) q'.2 q.1 := by
      rw [sameWorld]
      exact (SameWorld.mono (zof_sub cm0') memory'.2.2).symm
    exact StockMemory.machine_return readOnly hc.prepOk hc.check hc.alloc hc.emit hc.layout
      (fun _ h => Or.inl h) hcov arguments related other H G base ra s he

end E2E
