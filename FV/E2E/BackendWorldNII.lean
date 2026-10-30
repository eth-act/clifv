import FV.E2E.PairDriverICleanup
import FV.E2E.BackendWorldCleanupI

/-!
# The counted per-function theorem with non-interference (SEM1, `docs/plans/uninit.md` §5.9)

`backend_correct_world_ni` / `backend_correct_world_ni_value` / `backend_correct_world_ni_pipeline`
for the counted VCode run: the return clause of `backend_correct_worldPRI` (resp. `…_cleanupPRI`),
and the non-interference clause: the one counted VCode outcome of `w₀` is realised also by every
`ActEntryPR` activation entered with a body-entry world `w₀'` related to the same CLIF entry and
agreeing with `w₀` outside `F ∪ D`, when the external semantics keeps the agreement (`XNI` of call
number `n` at the CLIF states reached after `n` calls, for the environment restricted to their
invocation; `XTls`).

* `backend_correct_world_niPRI` (legacy), `backend_correct_world_ni_cleanupPRI` (cleanup),
  **`backend_correct_world_ni_pipelinePRI`** (`CompiledEither`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **The counted per-function theorem with non-interference, legacy path.** -/
theorem backend_correct_world_niPRI {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
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
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
          (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
          ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX (XI.at 0) H fa) n s) ∧
            PostTrace fa af base (ArmStepX (XI.at 0) H fa) s n) ∧
        ((∀ s n, ReachN env p cs s n → XNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLg (env.only (Clif.Invoked env p s)) (f.externs.map (·.2)) (indSigs f))
            (XI.at n)) → XTls F (XI.at 0) →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
            (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
            ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s
                (runX (ArmStepX (XI.at 0) H fa) n s) ∧
              PostTrace fa af base (ArmStepX (XI.at 0) H fa) s n) := by
  intro vals cm hrun
  have hI := iselSim_relWI hsub hc hone htc hX hsym hslot (fun _ => 0) hcs hrel hargs htr fuel
  have hP : ∀ w : Arm.ArmState, _ := fun w => prep_soundW (DriverSemG.csemI fun m =>
    (driverSem_csem F ⟨fa.k, af.slotBase⟩ (XI.at m)).toDriverSemG) hc.prepOk (fun _ => 0) (w, 0)
  have hM6 : ∀ (w₀ : Arm.ArmState) (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
      (Kp : Nat) (cc : BitVec 64) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
      (s : Arm.ArmState), ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ → _ :=
    fun w₀ H G base ra Kp cc P R s he => by
      have h := regLevelCorrect_worldPRS hc.check hc.alloc hc.emit hc.layout (XI := XI) (H := H)
        (K := K) (G := G) (gv := GotV vcp) hcov he.abi he.stack he.gfree he.proph he.regp
        (by rw [he.hF]; exact he.calls) (by rw [he.hF]; exact he.tries)
        (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body) (fun _ => 0)
      rw [he.hF] at h
      exact h
  obtain ⟨us, outs, ⟨w, nc⟩, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
  have hrs : vc.RetsSite us := by
    obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
    exact ⟨b, vb, k, hvb, hk⟩
  refine ⟨us, outs, w, hus, hlen, hhold, hmemR, hrs, fun H G base ra Kp cc P R s he => ?_,
    fun hNI hTls D w₀' hrel' hsw hreg hstk H G base ra Kp cc P R s he => ?_⟩
  · obtain ⟨n, h1, h2, h3, h4, h5, h6, h7⟩ :=
      (hM6 w₀ H G base ra Kp cc P R s he).1 us outs w nc (vRetFrom_gotVI ((hP w₀).1 _ _ _ hv))
    exact ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩
  · obtain ⟨us', outs', w1, w2, nc', hv1, hv2, hsw12⟩ := vcode_niI hsub hc hone htc hX hsym hslot
      hNI hTls (fun _ => 0) hcs hrel hrel' hargs hsw hreg hstk htr fuel vals cm hrun
    obtain ⟨rfl, rfl, he12⟩ := vRetFrom_det (vs := ⟨0, 0, fun _ => 0, (w₀, 0)⟩) hv1 hv
    cases he12
    obtain ⟨n, h1, h2, h3, h4, h5, h6, h7⟩ := (hM6 w₀' H G base ra Kp cc P R s he).1 us' outs'
      w2 nc (vRetFrom_gotVI ((hP w₀').1 _ _ _ hv2))
    refine ⟨n, ⟨h1, h2, fun a ha => ?_, fun g hg h29 h31 => ?_, h5, h6⟩, h7⟩
    · rw [h3 a (fun hf => ha (.inl hf))]
      exact (hsw12.2.1 a ha).symm
    · rw [h4 g hg h29 h31]
      exact (hsw12.1 g hg).symm

/-- **The counted per-function theorem with non-interference, cleanup path.** -/
theorem backend_correct_world_ni_cleanupPRI {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
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
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
          (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
          ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX (XI.at 0) H fa) n s) ∧
            PostTrace fa af base (ArmStepX (XI.at 0) H fa) s n) ∧
        ((∀ s n, ReachN env p cs s n → XNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLg (env.only (Clif.Invoked env p s)) (f.externs.map (·.2)) (indSigs f))
            (XI.at n)) → XTls F (XI.at 0) →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
            (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
            ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s
                (runX (ArmStepX (XI.at 0) H fa) n s) ∧
              PostTrace fa af base (ArmStepX (XI.at 0) H fa) s n) := by
  intro vals cm hrun
  have hI := iselSim_relWI_cleanup hsub hc hone htc hX hsym hslot (fun _ => 0) hcs hrel hargs
    htr fuel
  have hPr : ∀ w : Arm.ArmState, _ := fun w =>
    prune_correctW (vc := vc) (sem := valueSemI F ⟨fa.k, af.slotBase⟩ XI)
      (fun _ _ _ _ _ _ hi hs => counted_pure (fun _ _ _ _ _ _ _ hp he => valueSem_pure hp he) hi hs)
      (cmpOverwrite_counted fun n => valueSem_cmpOverwrite _ _ _) (fun _ => 0) (w, 0)
  have hP : ∀ w : Arm.ArmState, _ := fun w => prep_soundW (DriverSemG.counted fun m =>
    (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ (XI.at m)).toDriverSemG) hc.prepOk (fun _ => 0)
    (w, 0)
  have hM6 : ∀ (w₀ : Arm.ArmState) (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
      (Kp : Nat) (cc : BitVec 64) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
      (s : Arm.ArmState), ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ → _ :=
    fun w₀ H G base ra Kp cc P R s he => by
      have h := regLevelCorrect_world_value_worldPRS hc.check hc.alloc hc.emit hc.layout
        (XI := XI) (H := H) (K := K) (G := G) (gv := GotV vcp) hcov he.abi he.stack he.gfree
        he.proph he.regp (by rw [he.hF]; exact he.calls) (by rw [he.hF]; exact he.tries)
        (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body) (fun _ => 0)
      rw [he.hF] at h
      exact h
  obtain ⟨us, outs, ⟨w, nc⟩, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
  have hrs : vc.RetsSite us := by
    obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
    exact ⟨b, vb, k, hvb, hk⟩
  refine ⟨us, outs, w, hus, hlen, hhold, hmemR, hrs, fun H G base ra Kp cc P R s he => ?_,
    fun hNI hTls D w₀' hrel' hsw hreg hstk H G base ra Kp cc P R s he => ?_⟩
  · obtain ⟨n, h1, h2, h3, h4, h5, h6, h7⟩ :=
      (hM6 w₀ H G base ra Kp cc P R s he).1 us outs w nc
        (vRetFrom_gotV_valueI ((hP w₀).1 _ _ _ ((hPr w₀).1 _ _ _ hv)))
    exact ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩
  · obtain ⟨us', outs', w1, w2, nc', hv1, hv2, hsw12⟩ := vcode_niI_value hsub hc hone htc hX hsym
      hslot hNI hTls (fun _ => 0) hcs hrel hrel' hargs hsw hreg hstk htr fuel vals cm hrun
    obtain ⟨rfl, rfl, he12⟩ := vRetFrom_det (vs := ⟨0, 0, fun _ => 0, (w₀, 0)⟩) hv1 hv
    cases he12
    obtain ⟨n, h1, h2, h3, h4, h5, h6, h7⟩ := (hM6 w₀' H G base ra Kp cc P R s he).1 us' outs'
      w2 nc (vRetFrom_gotV_valueI ((hP w₀').1 _ _ _ ((hPr w₀').1 _ _ _ hv2)))
    refine ⟨n, ⟨h1, h2, fun a ha => ?_, fun g hg h29 h31 => ?_, h5, h6⟩, h7⟩
    · rw [h3 a (fun hf => ha (.inl hf))]
      exact (hsw12.2.1 a ha).symm
    · rw [h4 g hg h29 h31]
      exact (hsw12.1 g hg).symm

/-- **The counted per-function theorem with non-interference, for either artifact.** -/
theorem backend_correct_world_ni_pipelinePRI {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledEither f k vc vcp rf af fa fb)
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
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
          (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
          ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX (XI.at 0) H fa) n s) ∧
            PostTrace fa af base (ArmStepX (XI.at 0) H fa) s n) ∧
        ((∀ s n, ReachN env p cs s n → XNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLg (env.only (Clif.Invoked env p s)) (f.externs.map (·.2)) (indSigs f))
            (XI.at n)) → XTls F (XI.at 0) →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
            (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
            ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s
                (runX (ArmStepX (XI.at 0) H fa) n s) ∧
              PostTrace fa af base (ArmStepX (XI.at 0) H fa) s n) := by
  cases hc with
  | legacy hc =>
    exact backend_correct_world_niPRI hsub hc hone htc hcov hX hsym hslot hcs hrel hargs htr fuel
  | cleanup hc =>
    exact backend_correct_world_ni_cleanupPRI hsub hc hone htc hcov hX hsym hslot hcs hrel hargs
      htr fuel

end E2E
