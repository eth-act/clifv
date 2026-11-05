import FV.E2E.WorldMemTrap
import FV.E2E.RegLevelMemTrapWorldW

/-!
# The per-function world theorem with memory traps and the writes (A3, #412, slice F8b)

`backend_correct_worldX_cleanup_memtrapW`: `backend_correct_worldX_cleanup_memtrap` with
`actGoodXW`: every state of the activation's run before the trap state has, besides the per-state
facts `GoodX`, the writes fact `RL.WritesAt` (its writes avoid the kept addresses `G`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- `regLevel_memtrap_value` with the writes. -/
theorem regLevel_memtrap_valueW {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ()) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : CalleeOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → CalleeTryOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K X H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀)
    (ρ₀ : Nat → CV) (mp : ArmFault.MemMap) :
    (∀ c, VTraps vcp (valueSemV gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ c →
      ∃ n, TrapAtM mp fa fb base c (E2E.runX (ArmStepX X H fa) n s) ∧
        ∀ i < n, actGoodXW vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) ∧
    (∀ c (A : BitVec 64 → Nat → Prop), (∀ x n, A x n → Unmapped mp x n) →
      VMemTraps vcp (valueSemV gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ c A →
      ∃ n, TrapAtM mp fa fb base c (E2E.runX (ArmStepX X H fa) n s) ∧
        ∀ i < n, actGoodXW vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) := by
  obtain ⟨cc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  obtain ⟨_, h⟩ := regLevel_memtrap_world_valueW hat (entryOk_of_le hle) halloc hemit hlayout hcov
    hent hres hG hC hCT hTls hbe (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState) mp
  exact h

/-- **The per-function world theorem with memory traps and the writes**
(`backend_correct_worldX_cleanup_memtrap` with `actGoodXW`: every state before the trap state with
`GoodX` and the writes `RL.WritesAt`). -/
theorem backend_correct_worldX_cleanup_memtrapW {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
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
    (htr : TrapsExplicitM env p cs) {mp : ArmFault.MemMap} (hmf : MapFaults mp env p cs)
    (fuel : Nat) :
    ∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAtM mp fa fb base c' (runX (ArmStepX X H fa) n s) ∧
          ∀ i < n, actGoodXW vcp rf af fa fb base s X H K G (GotV vcp) (runX (ArmStepX X H fa) i s) := by
  intro c' hrun H G base ra s he
  have hM6 := regLevel_memtrap_valueW hc.check hc.alloc hc.emit hc.layout (X := X) (H := H)
    (K := K) (G := G) (gv := GotV vcp) hcov he.abi he.stack he.gfree (by rw [he.hF]; exact he.calls)
    (by rw [he.hF]; exact he.tries) (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body)
    (fun _ => 0) mp
  rw [he.hF] at hM6
  have hpr : ∀ i us w outs w' ctl, pureForm i = true →
      valueSem F ⟨fa.k, af.slotBase⟩ X i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next :=
    fun _ _ _ _ _ _ hp he => valueSem_pure hp he
  rcases iselSim_relW_cleanup_memtrap_stage hsub hc hX hXI hsym hslot (fun _ => 0) hcs hrel hargs
    htr
    hmf fuel c' hrun with ht | ht
  · have hP : PrepareCorrect (valueSem F ⟨fa.k, af.slotBase⟩ X) (skipStage f vc) vcp := by
      intro a w
      obtain ⟨hr, ht⟩ := prune_correct (vc := skipStage f vc) hpr (valueSem_cmpOverwrite _ _ _) a w
      obtain ⟨pr, pt⟩ := prepareCorrect_of_check (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X)
        hc.prepOk a w
      exact ⟨fun _ _ _ he => pr _ _ _ (hr _ _ _ he), fun _ he => pt _ (ht _ he)⟩
    exact hM6.1 c' (vTraps_gotV_value ((hP (fun _ => 0) w₀).2 c' ht))
  · exact hM6.2 c' _ (fun _ _ h => unmapped_of_addrPred h)
      (vMemTraps_gotV_value (memTraps_prep (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X) hc.prepOk
        (memTraps_prune hpr (valueSem_cmpOverwrite _ _ _) ht)))

end E2E
