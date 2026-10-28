import FV.E2E.ExtSemGuardRY
import FV.E2E.RegLevelCorrectPRSNXT
import FV.E2E.TrapWorldW

/-!
# The pipeline's trap clause with the call count and the per-state trace (SEM1 #537)

`BackendWorldPRGYNX.lean`'s trap clauses give only the trap site. Here a trapping CLIF run gives
the machine's trap index `n` with: the trap site, no error and the activation's program before
`n`, `actGoodX` at every step before `n`, every state after the trap site's step erring, and a
trapping state of the CLIF run reached after `callsBefore … n` calls (`iselSim_relWINT`,
`prep_soundWT`, `regLevelCorrect_worldPRSNXT`; cleanup path: `prune_correctWT`,
`regLevelCorrect_world_value_worldPRSNXT`).

`backend_correct_worldPRINXT`, `backend_correct_world_cleanupPRINXT`,
`backend_correct_world_pipelinePRINXT`, `backend_correct_world_pipelinePRICNXT`,
**`backend_correct_world_pipelinePRGYNXT`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **`backend_correct_worldPRINX`'s trap clause with the call count and the trace.** -/
theorem backend_correct_worldPRINXT {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
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
    ∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
        (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
        ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX (XI.at 0) H fa) n s) ∧
          (∀ i < n, Arm.r .ERR (runX (ArmStepX (XI.at 0) H fa) i s) = .None ∧
            (runX (ArmStepX (XI.at 0) H fa) i s).program = fb.program base) ∧
          (∀ i < n, ∃ m, actGoodX vcp rf af fa fb base s (XI.at m) H K G (GotV vcp)
            (runX (ArmStepX (XI.at 0) H fa) i s)) ∧
          (∀ m, Arm.r .ERR (runX (ArmStepX (XI.at 0) H fa) (n + m + 1) s) ≠ .None) ∧
          ∃ u, ReachN env p cs u (callsBefore (ArmStepX (XI.at 0) H fa) fa base s n) ∧
            Clif.step env p u = .trapped c' := by
  intro c' hrun H G base ra Kp cc P R s he
  obtain ⟨nc, hv, u, hu, hd⟩ :=
    iselSim_relWINT hsub hc hone htc hX hsym hslot (fun _ => 0) hcs hrel hargs htr fuel c' hrun
  have hP := prep_soundWT (DriverSemG.csemI fun m =>
    (driverSem_csem F ⟨fa.k, af.slotBase⟩ (XI.at m)).toDriverSemG) hc.prepOk (fun _ => 0) (w₀, 0)
    (fun w => w.2 = nc)
  have h := regLevelCorrect_worldPRSNXT hc.check hc.alloc hc.emit hc.layout (XI := XI) (H := H)
    (K := K) (G := G) (gv := GotV vcp) hcov he.abi he.stack he.gfree he.proph he.regp
    (by rw [he.hF]; exact he.calls) (by rw [he.hF]; exact he.tries)
    (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body) (fun _ => 0)
  rw [he.hF] at h
  obtain ⟨n, hcb, htrap, hge, hgx, hst⟩ := h c' nc (vTrapFromW_gotVI (hP c' hv))
  exact ⟨n, htrap, hge, hgx, hst, u, by rw [hcb]; exact hu, hd⟩

/-- **`backend_correct_world_cleanupPRINX`'s trap clause with the call count and the trace.** -/
theorem backend_correct_world_cleanupPRINXT {p : Clif.Program} {f : Clif.Function} {k : Nat}
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
    ∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
        (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
        ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX (XI.at 0) H fa) n s) ∧
          (∀ i < n, Arm.r .ERR (runX (ArmStepX (XI.at 0) H fa) i s) = .None ∧
            (runX (ArmStepX (XI.at 0) H fa) i s).program = fb.program base) ∧
          (∀ i < n, ∃ m, actGoodX vcp rf af fa fb base s (XI.at m) H K G (GotV vcp)
            (runX (ArmStepX (XI.at 0) H fa) i s)) ∧
          (∀ m, Arm.r .ERR (runX (ArmStepX (XI.at 0) H fa) (n + m + 1) s) ≠ .None) ∧
          ∃ u, ReachN env p cs u (callsBefore (ArmStepX (XI.at 0) H fa) fa base s n) ∧
            Clif.step env p u = .trapped c' := by
  intro c' hrun H G base ra Kp cc P R s he
  obtain ⟨nc, hv, u, hu, hd⟩ :=
    iselSim_relWI_cleanupNT_stage hsub hc hone htc hX hsym hslot (fun _ => 0) hcs hrel hargs htr
      fuel c'
      hrun
  have hPr := prune_correctWT (vc := skipStage f vc) (sem := valueSemI F ⟨fa.k, af.slotBase⟩ XI)
    (fun _ _ _ _ _ _ hi hs => counted_pure (fun _ _ _ _ _ _ _ hp he => valueSem_pure hp he) hi hs)
    (cmpOverwrite_counted fun n => valueSem_cmpOverwrite _ _ _) (fun _ => 0) (w₀, 0)
    (fun w => w.2 = nc)
  have hP := prep_soundWT (DriverSemG.counted fun m =>
    (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ (XI.at m)).toDriverSemG) hc.prepOk (fun _ => 0)
    (w₀, 0) (fun w => w.2 = nc)
  have h := regLevelCorrect_world_value_worldPRSNXT hc.check hc.alloc hc.emit hc.layout
    (XI := XI) (H := H) (K := K) (G := G) (gv := GotV vcp) hcov he.abi he.stack he.gfree
    he.proph he.regp (by rw [he.hF]; exact he.calls) (by rw [he.hF]; exact he.tries)
    (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body) (fun _ => 0)
  rw [he.hF] at h
  obtain ⟨n, hcb, htrap, hge, hgx, hst⟩ := h c' nc (vTrapFromW_gotV_valueI (hP c' (hPr c' hv)))
  exact ⟨n, htrap, hge, hgx, hst, u, by rw [hcb]; exact hu, hd⟩

/-- **`backend_correct_world_pipelinePRINX`'s trap clause with the call count and the trace.** -/
theorem backend_correct_world_pipelinePRINXT {p : Clif.Program} {f : Clif.Function} {k : Nat}
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
    ∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
        (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
        ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX (XI.at 0) H fa) n s) ∧
          (∀ i < n, Arm.r .ERR (runX (ArmStepX (XI.at 0) H fa) i s) = .None ∧
            (runX (ArmStepX (XI.at 0) H fa) i s).program = fb.program base) ∧
          (∀ i < n, ∃ m, actGoodX vcp rf af fa fb base s (XI.at m) H K G (GotV vcp)
            (runX (ArmStepX (XI.at 0) H fa) i s)) ∧
          (∀ m, Arm.r .ERR (runX (ArmStepX (XI.at 0) H fa) (n + m + 1) s) ≠ .None) ∧
          ∃ u, ReachN env p cs u (callsBefore (ArmStepX (XI.at 0) H fa) fa base s n) ∧
            Clif.step env p u = .trapped c' := by
  cases hc with
  | legacy hc =>
    exact backend_correct_worldPRINXT hsub hc hone htc hcov hX hsym hslot hcs hrel hargs htr fuel
  | cleanup hc =>
    exact backend_correct_world_cleanupPRINXT hsub hc hone htc hcov hX hsym hslot hcs hrel hargs
      htr fuel

/-- **`backend_correct_world_pipelinePRICNX`'s trap clause with the call count and the trace.** -/
theorem backend_correct_world_pipelinePRICNXT {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledEither f k vc vcp rf af fa fb)
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
    ∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
        (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
        ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX (XI.at 0) H fa) n s) ∧
          (∀ i < n, Arm.r .ERR (runX (ArmStepX (XI.at 0) H fa) i s) = .None ∧
            (runX (ArmStepX (XI.at 0) H fa) i s).program = fb.program base) ∧
          (∀ i < n, ∃ m, actGoodX vcp rf af fa fb base s (XI.at m) H K G (GotV vcp)
            (runX (ArmStepX (XI.at 0) H fa) i s)) ∧
          (∀ m, Arm.r .ERR (runX (ArmStepX (XI.at 0) H fa) (n + m + 1) s) ≠ .None) ∧
          ∃ u, ReachN env p cs u (callsBefore (ArmStepX (XI.at 0) H fa) fa base s n) ∧
            Clif.step env p u = .trapped c' :=
  backend_correct_world_pipelinePRINXT hsub hc (instCallsOne_all f) (tryCallsOne_all f)
    hcov hX hsym hslot hcs hrel hargs htr fuel

/-- **`backend_correct_world_pipelinePRGYNX`'s trap clause with the call count and the trace**
(module doc). -/
theorem backend_correct_world_pipelinePRGYNXT {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledEither f k vc vcp rf af fa fb)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hnrc : NoRetCall env p cs) (hR : InvokedRetOk env p cs (f.externs.map (·.2)) (indSigs f))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    let XG := XI.guardRI (CallPostNXR env p cs (f.externs.map (·.2)) (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) XI.sym)
    ∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
        (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
        ActEntryPR vcp rf af fa fb K F G XG H base ra Kp cc P R s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX (XG.at 0) H fa) n s) ∧
          (∀ i < n, Arm.r .ERR (runX (ArmStepX (XG.at 0) H fa) i s) = .None ∧
            (runX (ArmStepX (XG.at 0) H fa) i s).program = fb.program base) ∧
          (∀ i < n, ∃ m, actGoodX vcp rf af fa fb base s (XG.at m) H K G (GotV vcp)
            (runX (ArmStepX (XG.at 0) H fa) i s)) ∧
          (∀ m, Arm.r .ERR (runX (ArmStepX (XG.at 0) H fa) (n + m + 1) s) ≠ .None) ∧
          ∃ u, ReachN env p cs u (callsBefore (ArmStepX (XG.at 0) H fa) fa base s n) ∧
            Clif.step env p u = .trapped c' :=
  backend_correct_world_pipelinePRICNXT hsub hc hcov (hX_guardRXRI XI hnrc hR) hsym hslot hcs hrel
    hargs htr fuel

end E2E
