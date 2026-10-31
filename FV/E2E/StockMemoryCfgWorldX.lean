import FV.E2E.StockMemoryCfgNI
import FV.E2E.StockMemoryCfgTls
import FV.Backend.Proof.StockMemoryCfgNotrap

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- The captured class satisfies the unchanged return-and-trap machine contract.
The actual effect check removes any additional TLS-flags assumption. -/
theorem backend_correct_worldX_stock_memory_cfg {p : Clif.Program} {f : Clif.Function} {k : Nat} {result : Stock.Result} {vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (family : Stock.MemoryCfg.TwoBlockClass f) {cleanup : Bool}
    (effects : StockMemoryCfg.effectsOnly result.code = true)
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
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ result.code.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s) ∧
          (∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
            (runX (ArmStepX X H fa) i s)) ∧
          ∀ m, Arm.r .ERR (runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None) := by
  have state : (⟨cs.frame,[],cs.mem⟩ : Clif.State) = cs := by
    have callers := hcs.callers
    cases cs
    cases callers
    rfl
  refine ⟨fun vals cm returned => ?_,fun code trapped H G base ra s he => ?_⟩
  · have sourceReturn : Clif.runLoop env p fuel ⟨cs.frame,[],cs.mem⟩ = .returned vals cm := by
      rwa [state]
    have source := StockMemoryCfg.paired_returns family hc.lower hcs.stockSourceEntry sourceReturn
      (fc := ⟨fa.k,af.slotBase⟩) (X := StockMemoryCfg.fixedTlsFlags X) hslot hsym
      (StockMemoryCfg.fixedTlsFlags_ok F X) (D := fun _ => False)
      ⟨hrel,hrel,SameWorld.refl _ w₀⟩ hargs hargs (fun _ _ _ => rfl)
    obtain ⟨us,outs,q,cm0,reached,pins,arity,values,memory,freed⟩ := source
    have first := StockMemoryCfg.return_original_tls effects (vRetFrom_pair reached).1
    have site : result.code.RetsSite us := by
      obtain ⟨b,k,ρ,w₁,vb,ops,outs',_,block,inst,_⟩ := first
      exact ⟨b,vb,k,block,inst⟩
    have mem : MemRel F syms cm q.1 := by
      rw [freed]
      exact memRel_leave (memRel_free memory.1.1.1 _)
    refine ⟨us,outs,q.1,pins.ordinary family.ordinary,arity,values,mem,site,?_⟩
    intro H G base ra s he
    exact StockMemoryCfg.machine_return effects hc.prepOk hc.check hc.alloc hc.emit hc.layout
      (fun _ h => h) hcov hargs (SameWorld.refl F q.1) first H G base ra s he
  · exact False.elim ((family.source_notrap hcs.stockSourceEntry fuel code) (by rwa [state]))

end E2E
