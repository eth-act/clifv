import FV.E2E.DeadCleanupWorldX
import FV.E2E.DeadCleanupPairR
import FV.E2E.DeadCleanupContractsR

/-!
# The per-state world theorems of the cleanup stage at the register-guarded semantics
(#753, stage R2)

`DeadCleanupWorldX` at `regG P (valueSem …)` for `ActEntryR P` (given `RegLevelR`):
`backend_correct_worldX_cleanupR`, `backend_correct_world_niX_cleanupR`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

set_option autoImplicit false

section


theorem backend_correct_worldX_cleanupR (hM6 : RegLevelR) {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    {P : BitVec 64 → Clif.Signature → Prop}
    (hPg : RegCompatGot P (f.externs.map (·.2)) (fun n => X.sym n 0))
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hPi : RegCompatInd P env (indSigs f) syms)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s) ∧
          (∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
            (runX (ArmStepX X H fa) i s)) ∧
          ∀ m, Arm.r .ERR (runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None) := by
  have hPrep : PrepareCorrect (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) (skipStage f vc) vcp := by
    intro a w
    obtain ⟨hr, ht⟩ := prune_correct (vc := skipStage f vc)
      (fun _ _ _ _ _ _ hp he => valueSem_pure hp (regG_sub he)) (valueSem_cmpOverwrite _ _ _).regG a w
    obtain ⟨pr, pt⟩ := prepareCorrect_of_check ((driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X).regG)
      hc.prepOk a w
    exact ⟨fun _ _ _ he => pr _ _ _ (hr _ _ _ he), fun _ he => pt _ (ht _ he)⟩
  have hI := iselSim_relW_cleanup_stageR (hPg := hPg) (hPi := hPi) hsub hc hX hXI hsym hslot (fun _ => 0) hcs hrel hargs htr
    fuel
  have hP := hPrep
    (fun _ => 0) w₀
  have hRL : ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
      ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ → _ := fun H G base ra s he => by
    have h := hM6.worldX_value hc.check hc.alloc hc.emit hc.layout (X := X) (H := H)
      (K := K) (G := G) (gv := GotV vcp) (P := P) hcov he.abi he.stack he.gfree (by rw [he.hF]; exact he.calls)
      (by rw [he.hF]; exact he.tries) (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body)
      (fun _ => 0)
    rw [he.hF] at h
    exact h
  refine ⟨fun vals cm hrun => ?_, fun c' hrun H G base ra s he => ?_⟩
  · obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
    have hrs : vc.RetsSite us := by
      obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
      exact retsSite_of_skipStage ⟨b, vb, k, hvb, hk⟩
    refine ⟨us, outs, w, hus, hlen, hhold, hmemR, hrs, fun H G base ra s he => ?_⟩
    obtain ⟨n, ⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ :=
      (hRL H G base ra s he).1 us outs w (vReturns_gotV_valueR (hP.1 _ _ _ hv))
    exact ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7, h8⟩
  · exact (hRL H G base ra s he).2 c' (vTraps_gotV_valueR (hP.2 c' (hI.2 c' hrun)))

/-- **`backend_correct_world_ni` with the per-state facts of the run** (both the ordinary and the
non-interference activations). -/
theorem backend_correct_world_niX_cleanupR (hM6 : RegLevelR) {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    {P : BitVec 64 → Clif.Signature → Prop}
    (hPg : RegCompatGot P (f.externs.map (·.2)) (fun n => X.sym n 0))
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hPi : RegCompatInd P env (indSigs f) syms)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
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
            ActEntryR P vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n ∧
              ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
                (runX (ArmStepX X H fa) i s)) := by
  intro vals cm hrun
  have hPrep : PrepareCorrect (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) (skipStage f vc) vcp := by
    intro a w
    obtain ⟨hr, ht⟩ := prune_correct (vc := skipStage f vc)
      (fun _ _ _ _ _ _ hp he => valueSem_pure hp (regG_sub he)) (valueSem_cmpOverwrite _ _ _).regG a w
    obtain ⟨pr, pt⟩ := prepareCorrect_of_check ((driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X).regG)
      hc.prepOk a w
    exact ⟨fun _ _ _ he => pr _ _ _ (hr _ _ _ he), fun _ he => pt _ (ht _ he)⟩
  have hI := iselSim_relW_cleanup_stageR (hPg := hPg) (hPi := hPi) hsub hc hX hXI hsym hslot (fun _ => 0) hcs hrel hargs htr
    fuel
  have hRL : ∀ (w₀ : Arm.ArmState) (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
      (s : Arm.ArmState), ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ → _ :=
    fun w₀ H G base ra s he => by
      have h := hM6.worldX_value hc.check hc.alloc hc.emit hc.layout (X := X) (H := H)
        (K := K) (G := G) (gv := GotV vcp) (P := P) hcov he.abi he.stack he.gfree (by rw [he.hF]; exact he.calls)
        (by rw [he.hF]; exact he.tries) (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body)
        (fun _ => 0)
      rw [he.hF] at h
      exact h
  obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
  have hrs : vc.RetsSite us := by
    obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
    exact retsSite_of_skipStage ⟨b, vb, k, hvb, hk⟩
  refine ⟨us, outs, w, hus, hlen, hhold, hmemR, hrs, fun H G base ra s he => ?_,
    fun hNI hTls D w₀' hrel' hsw hreg hstk H G base ra s he => ?_⟩
  · have hP := hPrep
      (fun _ => 0) w₀
    obtain ⟨n, ⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ := (hRL w₀ H G base ra s he).1 us outs w
      (vReturns_gotV_valueR (hP.1 _ _ _ hv))
    exact ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7, h8⟩
  · obtain ⟨us', outs', w1, w2, hv1, hv2, hsw12⟩ := vcode_ni_value_stageR (hPg := hPg) (hPi := hPi) hsub hc hX hXI hsym hslot
      hNI hTls
      (fun _ => 0) hcs hrel hrel' hargs hsw hreg hstk htr fuel vals cm hrun
    obtain ⟨rfl, rfl, rfl⟩ := vRetFrom_det (vs := ⟨0, 0, fun _ => 0, w₀⟩) hv1 hv
    have hP := hPrep
      (fun _ => 0) w₀'
    obtain ⟨n, ⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ := (hRL w₀' H G base ra s he).1 us' outs' w2
      (vReturns_gotV_valueR (hP.1 _ _ _ hv2))
    refine ⟨n, ⟨h1, h2, fun a ha => ?_, fun g hg h29 h31 => ?_, h5, h6⟩, h7, h8⟩
    · rw [h3 a (fun hf => ha (.inl hf))]
      exact (hsw12.2.1 a ha).symm
    · rw [h4 g hg h29 h31]
      exact (hsw12.1 g hg).symm

end

end E2E
