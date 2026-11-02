import FV.E2E.PairDriver
import FV.E2E.RegLevelCorrectX

/-! # The per-function theorems with the per-state facts of the run (L3 (c))

`backend_correct_worldX` and `backend_correct_world_niX` are `backend_correct_world` and
`backend_correct_world_ni` composed with `regLevelCorrect_worldX` instead of
`regLevelCorrect_world`: every activation's run additionally has `actGoodX` (`RL.GoodX` of the
activation) at every state before its return, and a trapping run at every state before the trap
state, after which the machine errs for ever. -/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **`backend_correct_world` with the per-state facts of the run.** -/
theorem backend_correct_worldX {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
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
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
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
  have hI := iselSim_relW hsub hc hX hXI hsym hslot (fun _ => 0) hcs hrel hargs htr fuel
  have hP := prepareCorrect_of_check (driverSem_csem F ⟨fa.k, af.slotBase⟩ X) hc.prepOk
    (fun _ => 0) w₀
  have hM6 : ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
      ActEntry vcp rf af fa fb K F G X H base ra s w₀ → _ := fun H G base ra s he => by
    have h := regLevelCorrect_worldX hc.check hc.alloc hc.emit hc.layout (X := X) (H := H)
      (K := K) (G := G) (gv := GotV vcp) hcov he.abi he.stack he.gfree (by rw [he.hF]; exact he.calls)
      (by rw [he.hF]; exact he.tries) (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body)
      (fun _ => 0)
    rw [he.hF] at h
    exact h
  refine ⟨fun vals cm hrun => ?_, fun c' hrun H G base ra s he => ?_⟩
  · obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
    have hrs : vc.RetsSite us := by
      obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
      exact ⟨b, vb, k, hvb, hk⟩
    refine ⟨us, outs, w, hus, hlen, hhold, hmemR, hrs, fun H G base ra s he => ?_⟩
    obtain ⟨n, ⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ :=
      (hM6 H G base ra s he).1 us outs w (vReturns_gotV (hP.1 _ _ _ hv))
    exact ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7, h8⟩
  · exact (hM6 H G base ra s he).2 c' (vTraps_gotV (hP.2 c' (hI.2 c' hrun)))

/-- **`backend_correct_world_ni` with the per-state facts of the run** (both the ordinary and the
non-interference activations). -/
theorem backend_correct_world_niX {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
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
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
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
            ActEntry vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n ∧
              ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
                (runX (ArmStepX X H fa) i s)) := by
  intro vals cm hrun
  have hI := iselSim_relW hsub hc hX hXI hsym hslot (fun _ => 0) hcs hrel hargs htr fuel
  have hM6 : ∀ (w₀ : Arm.ArmState) (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
      (s : Arm.ArmState), ActEntry vcp rf af fa fb K F G X H base ra s w₀ → _ :=
    fun w₀ H G base ra s he => by
      have h := regLevelCorrect_worldX hc.check hc.alloc hc.emit hc.layout (X := X) (H := H)
        (K := K) (G := G) (gv := GotV vcp) hcov he.abi he.stack he.gfree (by rw [he.hF]; exact he.calls)
        (by rw [he.hF]; exact he.tries) (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body)
        (fun _ => 0)
      rw [he.hF] at h
      exact h
  obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
  have hrs : vc.RetsSite us := by
    obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
    exact ⟨b, vb, k, hvb, hk⟩
  refine ⟨us, outs, w, hus, hlen, hhold, hmemR, hrs, fun H G base ra s he => ?_,
    fun hNI hTls D w₀' hrel' hsw hreg hstk H G base ra s he => ?_⟩
  · have hP := prepareCorrect_of_check (driverSem_csem F ⟨fa.k, af.slotBase⟩ X) hc.prepOk
      (fun _ => 0) w₀
    obtain ⟨n, ⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ := (hM6 w₀ H G base ra s he).1 us outs w
      (vReturns_gotV (hP.1 _ _ _ hv))
    exact ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7, h8⟩
  · obtain ⟨us', outs', w1, w2, hv1, hv2, hsw12⟩ := vcode_ni hsub hc hX hXI hsym hslot hNI hTls
      (fun _ => 0) hcs hrel hrel' hargs hsw hreg hstk htr fuel vals cm hrun
    obtain ⟨rfl, rfl, rfl⟩ := vRetFrom_det (vs := ⟨0, 0, fun _ => 0, w₀⟩) hv1 hv
    have hP := prepareCorrect_of_check (driverSem_csem F ⟨fa.k, af.slotBase⟩ X) hc.prepOk
      (fun _ => 0) w₀'
    obtain ⟨n, ⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ := (hM6 w₀' H G base ra s he).1 us' outs' w2
      (vReturns_gotV (hP.1 _ _ _ hv2))
    refine ⟨n, ⟨h1, h2, fun a ha => ?_, fun g hg h29 h31 => ?_, h5, h6⟩, h7, h8⟩
    · rw [h3 a (fun hf => ha (.inl hf))]
      exact (hsw12.2.1 a ha).symm
    · rw [h4 g hg h29 h31]
      exact (hsw12.1 g hg).symm

end E2E
