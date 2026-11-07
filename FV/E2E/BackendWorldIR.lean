import FV.E2E.BackendWorldI
import FV.E2E.RegLevelCorrectPRSR

/-!
# The counted per-function theorem with the located reads (SEM1 #537, step 3p)

`backend_correct_worldPRIR`: `backend_correct_worldPRI` (same proof, on
`regLevelCorrect_worldPRSR`) that also gives `RL.ReadsIn` (`actReadsIn`) at every state of the
activation's run before its return.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **`backend_correct_worldPRI` with the located reads**: also `actReadsIn` at every state of the
activation's run before its return. -/
theorem backend_correct_worldPRIR {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
          (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
          ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX (XI.at 0) H fa) n s) ∧
            PostTrace fa af base (ArmStepX (XI.at 0) H fa) s n ∧
            ∀ i < n, actReadsIn vcp rf af fa fb base s (XI.at 0) H K G (GotV vcp)
              (runX (ArmStepX (XI.at 0) H fa) i s)) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
        (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
        ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX (XI.at 0) H fa) n s)) := by
  have hI := iselSim_relWI hsub hc hone htc hX hsym hslot (fun _ => 0) hcs hrel hargs htr fuel
  have hP := prep_soundW (DriverSemG.csemI fun m =>
    (driverSem_csem F ⟨fa.k, af.slotBase⟩ (XI.at m)).toDriverSemG) hc.prepOk (fun _ => 0) (w₀, 0)
  have hM6 : ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat)
      (cc : BitVec 64) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
      ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ → _ :=
    fun H G base ra Kp cc P R s he => by
      have h := regLevelCorrect_worldPRSR hc.check hc.alloc hc.emit hc.layout (XI := XI) (H := H)
        (K := K) (G := G) (gv := GotV vcp) hcov he.abi he.stack he.gfree he.proph he.regp
        (by rw [he.hF]; exact he.calls) (by rw [he.hF]; exact he.tries)
        (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body) (fun _ => 0)
      rw [he.hF] at h
      exact h
  refine ⟨fun vals cm hrun => ?_, fun c' hrun H G base ra Kp cc P R s he => ?_⟩
  · obtain ⟨us, outs, ⟨w, nc⟩, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
    have hrs : vc.RetsSite us := by
      obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
      exact ⟨b, vb, k, hvb, hk⟩
    refine ⟨us, outs, w, hus, hlen, hhold, hmemR, hrs, fun H G base ra Kp cc P R s he => ?_⟩
    obtain ⟨n, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      (hM6 H G base ra Kp cc P R s he).1 us outs w nc (vRetFrom_gotVI (hP.1 _ _ _ hv))
    exact ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7, h8⟩
  · exact (hM6 H G base ra Kp cc P R s he).2 c' (vTrapFrom_gotVI (hP.2 c' (hI.2 c' hrun)))

end E2E
