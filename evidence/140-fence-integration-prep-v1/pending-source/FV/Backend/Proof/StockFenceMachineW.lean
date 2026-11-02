import FV.Backend.Proof.StockFenceMixedDomain
import FV.Backend.Proof.StockFencePreparedShapes
import FV.Backend.Proof.StockMemoryAccessMachineCheckW
import FV.Backend.Proof.StockMemoryAccessStage
import FV.E2E.LinkWorld
import FV.E2E.StockArithmeticSemantics
import FV.E2E.DeadCleanupRegLevelW

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.MemoryFaults Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- The complete mixed function preserves returns and both first-trap outcomes in both cleanup modes.
All source arguments, memory and divisors remain unrestricted. -/
theorem backend_correct_worldX_stock_fenceW {p : Clif.Program} {k : Nat} {result : Stock.Result} {vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {cleanup : Bool}
    (hc : CompiledStockArithmeticStage FenceFixture.function cleanup k result vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry FenceFixture.function args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ FenceFixture.function c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F FenceFixture.function.sig args w₀)
    (mp : ArmFault.MemMap) (faults : MapFaults mp env p cs)
    (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        ReturnABI FenceFixture.function us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ result.code.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodXW vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        (∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s) ∧
          (∀ i < n, actGoodXW vcp rf af fa fb base s X H K G (GotV vcp)
            (runX (ArmStepX X H fa) i s)) ∧
          ∀ m, Arm.r .ERR (runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None) ∨
        (∃ n,TrapAtF mp fb base c' (runX (ArmStepX X H fa) n s) ∧
          ∀ i < n,actGoodXW vcp rf af fa fb base s X H K G (GotV vcp)
            (runX (ArmStepX X H fa) i s))) := by
  have domain := FenceFixture.mixed_domain_with_access_traps
  have state : (⟨cs.frame,[],cs.mem⟩ : Clif.State) = cs := by
    have callers := hcs.callers
    cases cs
    cases callers
    rfl
  refine ⟨fun vals cm returned => ?_, fun code trapped H G base ra s he => ?_⟩
  · obtain ⟨ρ,source⟩ := domain.returns hc.lower hcs.stockSourceEntry
      (by rwa [state]) (refines_valueSem F ⟨fa.k,af.slotBase⟩ X)
      (driverSem_valueSem F ⟨fa.k,af.slotBase⟩ X)
      (memRefines_valueSem F ⟨fa.k,af.slotBase⟩ X hslot hsym)
      (mrStable_relW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ FenceFixture.function c)
      (memRelOk_relW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ FenceFixture.function c) hrel hargs
    obtain ⟨us,outs,w,cm0,reached,pins,arity,values,memory,freed⟩ := source
    have reached' := returns_stage hc.prepOk reached
    have site : result.code.RetsSite us := by
      obtain ⟨b,k,ρ,w₁,vb,ops,outs',_,hvb,hk,_⟩ := reached
      exact ⟨b,vb,k,hvb,hk⟩
    have mem : MemRel F syms cm w := by
      rw [freed]
      exact memRel_leave (memRel_free memory.1.1 _)
    refine ⟨us,outs,w,pins,arity,values,mem,site,?_⟩
    intro H G base ra s he
    have machine := regLevelCorrect_worldX_valueW hc.check hc.alloc hc.emit hc.layout
      (X := X) (H := H) (K := K) (G := G) (gv := GotV vcp)
      hcov he.abi he.stack he.gfree (by rw [he.hF]; exact he.calls)
      (by rw [he.hF]; exact he.tries) (by rw [he.hF]; exact he.tls)
      (by rw [he.hF]; exact he.body) ρ
    rw [he.hF] at machine
    obtain ⟨n,⟨h1,h2,h3,h4,h5,h6,h7⟩,h8⟩ :=
      machine.1 us outs w (vReturns_gotV_value reached')
    exact ⟨n,⟨h1,h2,h3,h4,h5,h6⟩,h7,h8⟩
  · obtain ⟨ρ,source⟩ := domain.traps hc.lower hcs.stockSourceEntry
      (by rwa [state]) (refines_valueSem F ⟨fa.k,af.slotBase⟩ X)
      (driverSem_valueSem F ⟨fa.k,af.slotBase⟩ X)
      (memRefines_valueSem F ⟨fa.k,af.slotBase⟩ X hslot hsym)
      (mrStable_relW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ FenceFixture.function c)
      (memRelOk_relW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ FenceFixture.function c) hrel hargs
      (fun a n => ∃ j < n,mp (BitVec.ofNat 64 (a+j)) = .none)
      (fun current a n reached actual => faults current code a n (by rwa [state] at reached) actual)
    rcases source with explicit | access
    · have staged := runOk_stage (f := FenceFixture.function)
        (MR := RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ FenceFixture.function c)
        (slots := cs.frame.slots) hc.prepOk (outcome := .trapped code) explicit
      have machine := regLevelCorrect_worldX_valueW hc.check hc.alloc hc.emit hc.layout
        (X := X) (H := H) (K := K) (G := G) (gv := GotV vcp)
        hcov he.abi he.stack he.gfree (by rw [he.hF]; exact he.calls)
        (by rw [he.hF]; exact he.tries) (by rw [he.hF]; exact he.tls)
        (by rw [he.hF]; exact he.body) ρ
      rw [he.hF] at machine
      exact .inl (machine.2 code (vTraps_gotV_value staged))
    · rw [← hslot] at access
      have staged := accessTrap_stage hc.prepOk access
      have actual := accessTrap_gotV_value staged
      obtain ⟨prepared,preparedRun,preparedCheck,shapes⟩ :=
        FenceFixture.mixed_prepared_access_shapes hc.lower cleanup
      change Backend.prepare (Stock.Arithmetic.stage cleanup result.code) = .ok prepared at preparedRun
      rw [hc.prepare] at preparedRun
      cases Except.ok.inj preparedRun
      have machine := regLevel_access_fault_worldX_valueW hc.check hc.alloc hc.emit hc.layout
        (X := X) (H := H) (K := K) (G := G) (gv := GotV vcp)
        hcov he.abi he.stack he.gfree (by rw [he.hF]; exact he.calls)
        (by rw [he.hF]; exact he.tries) (by rw [he.hF]; exact he.tls)
        (by rw [he.hF]; exact he.body) ρ
        (fun b block j inst found located uses world code address bytes access =>
          shapes b block j inst found located af.slotBase uses world code address bytes access) mp
      rw [he.hF] at machine
      exact .inr (machine code _ (fun _ _ held => sourceAddrPred_unmapped held) actual)

end E2E
