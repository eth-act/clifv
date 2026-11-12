import FV.Backend.Proof.StockAcquireSourceDomain
import FV.Backend.Proof.StockAcquirePreparedShapes
import FV.Backend.Proof.StockAcquireMachineCheck
import FV.Backend.Proof.StockAcquireStage
import FV.Backend.Proof.StockMemoryAccessStage
import FV.E2E.LinkWorld
import FV.E2E.StockArithmeticSemantics
import FV.E2E.DeadCleanupRegLevelX

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- Complete original-input returns and acquire access faults in both cleanup modes. -/
theorem backend_correct_worldX_stock_acquire810 {p : Clif.Program} {k : Nat} {result : Stock.Result} {vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {cleanup : Bool}
    (hc : CompiledStockArithmeticStage Acquire810.function cleanup k result vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry Acquire810.function args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ Acquire810.function c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F Acquire810.function.sig args w₀)
    (mp : ArmFault.MemMap) (faults : MapFaults mp env p cs)
    (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        ReturnABI Acquire810.function us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ result.code.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
    (∀ code,Clif.runLoop env p fuel cs = .trapped code →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n,TrapAtF mp fb base code (runX (ArmStepX X H fa) n s) ∧
          ∀ i < n,actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
            (runX (ArmStepX X H fa) i s)) := by
  refine ⟨fun vals cm returned => ?_,fun code trapped H G base ra s he => ?_⟩
  · obtain ⟨ρ,source⟩ := Acquire810.original_returns hc.lower hcs env p fuel returned
      (refines_valueSem F ⟨fa.k,af.slotBase⟩ X)
      (driverSem_valueSem F ⟨fa.k,af.slotBase⟩ X)
      (mrStable_relW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ Acquire810.function c)
      (memRefines_valueSem F ⟨fa.k,af.slotBase⟩ X hslot hsym)
      (memRelOk_relW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ Acquire810.function c) hrel hargs
    obtain ⟨us,outs,w,cm0,reached,pins,arity,values,memory,freed⟩ := source
    have reached' := MemoryFaults.returns_stage hc.prepOk reached
    have site : result.code.RetsSite us := by
      obtain ⟨b,k,ρ,w₁,vb,ops,outs',_,hvb,hk,_⟩ := reached
      exact ⟨b,vb,k,hvb,hk⟩
    have mem : MemRel F syms cm w := by
      rw [freed]
      exact memRel_leave (memRel_free memory.1.1 _)
    refine ⟨us,outs,w,pins.abi,arity,values,mem,site,?_⟩
    intro H G base ra s he
    have machine := regLevelCorrect_worldX_value hc.check hc.alloc hc.emit hc.layout
      (X := X) (H := H) (K := K) (G := G) (gv := GotV vcp)
      hcov he.abi he.stack he.gfree (by rw [he.hF]; exact he.calls)
      (by rw [he.hF]; exact he.tries) (by rw [he.hF]; exact he.tls)
      (by rw [he.hF]; exact he.body) ρ
    rw [he.hF] at machine
    obtain ⟨n,⟨h1,h2,h3,h4,h5,h6,h7⟩,h8⟩ :=
      machine.1 us outs w (vReturns_gotV_value reached')
    exact ⟨n,⟨h1,h2,h3,h4,h5,h6⟩,h7,h8⟩
  · obtain ⟨ρ,source⟩ := Acquire810.original_traps hc.lower hcs env p fuel code trapped
      (driverSem_valueSem F ⟨fa.k,af.slotBase⟩ X) mp faults hargs
    have staged := Acquire810.acquireTrap_stage hc.prepOk source.boundary
    have actual := Acquire810.acquireTrap_gotV_value staged
    obtain ⟨prepared,preparedRun,preparedCheck,shapes⟩ := Acquire810.prepared_acquire_shapes hc.lower cleanup
    change Backend.prepare (Stock.Arithmetic.stage cleanup result.code) = .ok prepared at preparedRun
    rw [hc.prepare] at preparedRun
    cases Except.ok.inj preparedRun
    have machine := Acquire810.regLevel_acquire_fault_boundary_worldX_value hc.check hc.alloc hc.emit hc.layout
      (X := X) (H := H) (K := K) (G := G) (gv := GotV vcp)
      hcov he.abi he.stack he.gfree (by rw [he.hF]; exact he.calls)
      (by rw [he.hF]; exact he.tries) (by rw [he.hF]; exact he.tls)
      (by rw [he.hF]; exact he.body) ρ shapes mp
    rw [he.hF] at machine
    exact machine code _ (fun _ _ held => held) actual

end E2E
