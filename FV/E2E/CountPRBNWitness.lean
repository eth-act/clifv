import FV.E2E.LinkArmProgramInit
import FV.E2E.RegLevelCorrectPRSWitness
import FV.E2E.IselSimIWitness
import FV.E2E.BackendWorldPRBWitness
import FV.E2E.LinkArmThmPRBRZeroWitness

/-!
# Witnesses for the call count at the return and `CountPRB` (SEM1 #537, #680 (3):
`RegLevelCorrectPRSN`, `IselSimIN`, `BackendWorldPRGYN`, `LinkArmCountPRBSucc`)

* `RegLevelCorrectPRSWitness.worldPRSN_const`: `regLevelCorrect_worldPRSN` applies to a compiled
  function with a call (the call count at the return);
* `LinkWitness.a2_iselSimIN`, `a2_worldPRIN`: `iselSim_relWIN`, `backend_correct_worldPRIN` apply to
  `LinkWitness`'s compiled `a2`;
* `DeadCleanupWitness.prgyN_applies`, `prgyN_pipeline_applies`: both `*_PRGYN` theorems apply;
* on the slotted system `Lsl`: **`countPRB_one_Lsl`**, `countPRB_succ_Lsl`, **`thmPRBRL_allC_Lsl`**
  (`ThmPRBRL` at every depth from `DetPRB` and `DetTabPRB` alone), `actRet_unique_Lsl`.
-/

namespace Backend.Proof.RegLevelCorrectPRSWitness

open Backend Backend.Proof E2E Backend.Proof.Driver

open RegLevelCorrectUWitness RegLevelCorrectIWitness in
/-- **`regLevelCorrect_worldPRSN` applies to a compiled function with a call**: the return has as many machine calls before it as the VCode return's counter. -/
theorem worldPRSN_const {X : ExtSem} {H : ArmHooks} {K : Nat} {fb : FnBin}
    (hlayout : fa.layout = .ok fb) (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vc)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af s) K X H vc.CallSite)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) {w₀ : Arm.ArmState}
    (hbe : BodyEntryW (frameW K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af s)
      vc.EntryArg af s w₀) (ρ₀ : Nat → CV) (us : List (Reg × Reg)) (vals : List CV)
    (w : Arm.ArmState) (nc : Nat)
    (hret : VRetFrom vc (csemVI (fun _ _ => False) (frameWG K (RAFrame.compute vc rf).intBase
        (RAFrame.compute vc rf).size af (fun _ => False) s) ⟨fa.k, af.slotBase⟩ (ExtSemI.const X))
        ⟨0, 0, ρ₀, (w₀, 0)⟩ us vals (w, nc)) :
    ∃ n, callsBefore (ArmStepX X H fa) fa base s n = nc ∧ ArmRet ra s (E2E.runX (ArmStepX X H fa) n s) := by
  obtain ⟨hca, halloc, hemit, -⟩ := premises K X
  have hnt : vc.hasTryCall = false := by decide +kernel
  have hnl : vc.hasTls = false := by decide +kernel
  have e := frameWG_false K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af s
  obtain ⟨n, hcb, h, -⟩ := (regLevelCorrect_worldPRSN (XI := ExtSemI.const X) (G := fun _ => False)
    (gv := fun _ _ => False) hca halloc hemit hlayout hcov hent hres (fun _ h => h.elim)
    (prophOk_prophOf K (spv w₀) _ fa base s) (prophRegOkM_prophStOf (spv w₀) _ fa base s)
    (fun _ => by rw [e]; exact ((hC s).g _ s _ _).p _) (fun h => absurd h (by rw [hnt]; decide))
    (fun h => absurd h (by rw [hnl]; decide)) (by rw [e]; exact hbe) ρ₀).1 us vals w nc hret
  exact ⟨n, hcb, h⟩

end Backend.Proof.RegLevelCorrectPRSWitness

namespace E2E.LinkWitness

open Backend Backend.Proof Backend.Proof.Driver

/-- **`iselSim_relWIN` applies** to the program's compiled function `a2` (the entry premises
remain). -/
theorem a2_iselSimIN {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val}
    {cs : Clif.State} {w₀ : Arm.ArmState} (ρ₀ : Nat → CV) (hce : ClifEntry fA2 args cs)
    (hrel : RelW ⟨F, fun _ => none, (A fA2).af.slotBase,
      (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase⟩ fA2 c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F fA2.sig args w₀)
    (htr : TrapsExplicit Clif.Rust.env (L F).P.bare cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop Clif.Rust.env (L F).P.bare fuel cs = .returned vals cm →
      ∃ us outs w, VRetFrom (A fA2).vc (csemI F ⟨(A fA2).fa.k, (A fA2).af.slotBase⟩
          (ExtSemI.const Xb)) ⟨0, 0, ρ₀, (w₀, 0)⟩ us outs w ∧
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F (fun _ => none) cm w.1 ∧
        ∃ u, ReachN Clif.Rust.env (L F).P.bare cs u w.2 ∧
          Clif.step Clif.Rust.env (L F).P.bare u = .done vals cm) ∧
    (∀ c', Clif.runLoop Clif.Rust.env (L F).P.bare fuel cs = .trapped c' →
      VTrapFrom (A fA2).vc (csemI F ⟨(A fA2).fa.k, (A fA2).af.slotBase⟩ (ExtSemI.const Xb))
        ⟨0, 0, ρ₀, (w₀, 0)⟩ c') := by
  have hL := L_ok (fun _ => True) (fun _ _ => trivial)
  have hA2 : fA2 ∈ P.funcs := by simp [P]
  exact iselSim_relWIN (hL.subset fA2 hA2) a2_compiled a2_callsOne.1 a2_callsOne.2
    (fun _ n _ => a2_xcalls _ _ _ n) (fun n b h => by cases h) rfl ρ₀ hce hrel hargs htr fuel

/-- **`backend_correct_worldPRIN` applies** to the program's compiled function `a2` (the entry
premises remain): one counted VCode outcome per returning CLIF run, realised by every
`ActEntryPR` activation. -/
theorem a2_worldPRIN {F : BitVec 64 → Prop} {c : BitVec 64} {K : Nat} {args : List Clif.Val}
    {cs : Clif.State} {w₀ : Arm.ArmState} (hce : ClifEntry fA2 args cs)
    (hrel : RelW ⟨F, fun _ => none, (A fA2).af.slotBase,
      (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase⟩ fA2 c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F fA2.sig args w₀)
    (htr : TrapsExplicit Clif.Rust.env (L F).P.bare cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop Clif.Rust.env (L F).P.bare fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F (fun _ => none) cm w ∧ (A fA2).vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
          (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
          ActEntryPR (A fA2).vcp (A fA2).rf (A fA2).af (A fA2).fa (A fA2).fb K F G
            (ExtSemI.const Xb) H base ra Kp cc P R s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX ((ExtSemI.const Xb).at 0) H (A fA2).fa) n s) ∧
            PostTrace (A fA2).fa (A fA2).af base (ArmStepX ((ExtSemI.const Xb).at 0) H (A fA2).fa) s n ∧
            ∃ u, ReachN Clif.Rust.env (L F).P.bare cs u
                (callsBefore (ArmStepX ((ExtSemI.const Xb).at 0) H (A fA2).fa) (A fA2).fa base s n) ∧
              Clif.step Clif.Rust.env (L F).P.bare u = .done vals cm) ∧
    (∀ c', Clif.runLoop Clif.Rust.env (L F).P.bare fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
        (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
        ActEntryPR (A fA2).vcp (A fA2).rf (A fA2).af (A fA2).fa (A fA2).fb K F G
          (ExtSemI.const Xb) H base ra Kp cc P R s w₀ →
        ∃ n, TrapAt (A fA2).fb base c' (runX (ArmStepX ((ExtSemI.const Xb).at 0) H (A fA2).fa) n s)) := by
  have hL := L_ok (fun _ => True) (fun _ _ => trivial)
  have hA2 : fA2 ∈ P.funcs := by simp [P]
  exact backend_correct_worldPRIN (hL.subset fA2 hA2) a2_compiled a2_callsOne.1 a2_callsOne.2
    (hL.covered fA2 hA2) (fun _ n _ => a2_xcalls _ _ _ n) (fun n b h => by cases h) rfl hce hrel
    hargs htr fuel

end E2E.LinkWitness

namespace E2E.DeadCleanupWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **`backend_correct_world_cleanupPRGYN` applies** to the closed cleanup compilation of `source`. -/
theorem prgyN_applies :
    ∃ vc vcp af fa fb, CompiledCleanup source 0 vc vcp (spillAlloc vcp) af fa fb ∧
      ∀ (XI : ExtSemI) (K : Nat) (F : BitVec 64 → Prop) (c : BitVec 64)
        (w₀ : Arm.ArmState) (args : List Clif.Val) (cs : Clif.State),
        ClifEntry source args cs →
        RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
          source c cs.frame.slots cs.mem w₀ →
        ArgsAtEntry F source.sig args w₀ →
        TrapsExplicit Clif.Env.empty ({ funcs := [] } : Clif.Program) cs → ∀ fuel,
        let XG := XI.guardRI (CallPostNXR Clif.Env.empty { funcs := [] } cs
          (source.externs.map (·.2)) (indSigs source)
          (RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
            source c) XI.sym)
        (∀ vals cm, Clif.runLoop Clif.Env.empty { funcs := [] } fuel cs = .returned vals cm →
          ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
            RetPins vals us ∧ us.length = outs.length ∧
            PrefixHold vals outs ∧ MemRel F (fun _ => none) cm w ∧ vc.RetsSite us ∧
            ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat)
              (cc : BitVec 64) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
              (s : Arm.ArmState),
              ActEntryPR vcp (spillAlloc vcp) af fa fb K F G XG H base ra Kp cc P R s w₀ →
              ∃ n, ActRet ra F G us outs w s (runX (ArmStepX (XG.at 0) H fa) n s) ∧
                PostTrace fa af base (ArmStepX (XG.at 0) H fa) s n ∧
                ∃ u, ReachN Clif.Env.empty { funcs := [] } cs u
                    (callsBefore (ArmStepX (XG.at 0) H fa) fa base s n) ∧
                  Clif.step Clif.Env.empty { funcs := [] } u = .done vals cm) ∧
        (∀ c', Clif.runLoop Clif.Env.empty { funcs := [] } fuel cs = .trapped c' →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat)
            (cc : BitVec 64) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
            (s : Arm.ArmState),
            ActEntryPR vcp (spillAlloc vcp) af fa fb K F G XG H base ra Kp cc P R s w₀ →
            ∃ n, TrapAt fb base c' (runX (ArmStepX (XG.at 0) H fa) n s)) := by
  obtain ⟨hsub, vc, vcp, af, fa, fb, hc, hcov, -⟩ := compiled_covered_exists
  refine ⟨vc, vcp, af, fa, fb, hc, fun XI K F c w₀ args cs hce hrel hargs htr fuel => ?_⟩
  have hnrc : NoRetCall Clif.Env.empty { funcs := [] } cs :=
    noRetCall_of_linv (P := ({ funcs := [] } : Clif.Program).only source)
      (fun g hg => (List.mem_singleton.mp hg) ▸ source_linkFree)
      (fun _ h => nomatch h) (linv_entry hce)
  have hR : InvokedRetOk Clif.Env.empty { funcs := [] } cs (source.externs.map (·.2))
      (indSigs source) := fun _ _ _ _ _ _ _ _ hg _ => by simp [Clif.Env.empty] at hg
  exact backend_correct_world_cleanupPRGYN (K := K) hsub hc (hcov _) hnrc hR
    (fun n b h => by cases h) rfl hce hrel hargs htr fuel

/-- **`backend_correct_world_pipelinePRGYN` applies** (same instance, `CompiledEither.cleanup`). -/
theorem prgyN_pipeline_applies : type_of% prgyN_applies := by
  obtain ⟨hsub, vc, vcp, af, fa, fb, hc, hcov, -⟩ := compiled_covered_exists
  refine ⟨vc, vcp, af, fa, fb, hc, fun XI K F c w₀ args cs hce hrel hargs htr fuel => ?_⟩
  have hnrc : NoRetCall Clif.Env.empty { funcs := [] } cs :=
    noRetCall_of_linv (P := ({ funcs := [] } : Clif.Program).only source)
      (fun g hg => (List.mem_singleton.mp hg) ▸ source_linkFree)
      (fun _ h => nomatch h) (linv_entry hce)
  have hR : InvokedRetOk Clif.Env.empty { funcs := [] } cs (source.externs.map (·.2))
      (indSigs source) := fun _ _ _ _ _ _ _ _ hg _ => by simp [Clif.Env.empty] at hg
  exact backend_correct_world_pipelinePRGYN (K := K) hsub (.cleanup hc) (hcov _) hnrc hR
    (fun n b h => by cases h) rfl hce hrel hargs htr fuel

end E2E.DeadCleanupWitness

namespace E2E.LinkSlotSysWitness

open Backend Backend.Proof Backend.Proof.Driver

/-- **`CountPRB` at depth `1` on the slotted system** (`countPRB_succ`; the depth-`0` statement
`thmPRBRL_zero_Lsl`, `RetOkPRB` by `retOkPRB_Lsl`; `DetPRB 0` and `DetTabPRB 1` remain). -/
theorem countPRB_one_Lsl (hdet : Lsl.DetPRB (fun M _ => Lsl.K M) 0)
    (hdt : Lsl.DetTabPRB (fun M _ => Lsl.K M) 1) : Lsl.CountPRB (fun M _ => Lsl.K M) 1 :=
  Lsl.countPRB_succ Lsl_ok (Lsl.budget_K Lsl_ok) needSlots thmPRBRL_zero_Lsl hdet hdt
    (retOkPRB_Lsl 1)

theorem countPRB_succ_Lsl {M' : Nat} (ih : Lsl.ThmPRBRL (fun M _ => Lsl.K M) M')
    (hdet : Lsl.DetPRB (fun M _ => Lsl.K M) M') (hdt : Lsl.DetTabPRB (fun M _ => Lsl.K M) (M' + 1))
    (hret : Lsl.RetOkPRB (fun M _ => Lsl.K M) (M' + 1)) :
    Lsl.CountPRB (fun M _ => Lsl.K M) (M' + 1) :=
  Lsl.countPRB_succ Lsl_ok (Lsl.budget_K Lsl_ok) needSlots ih hdet hdt hret

/-- **`ThmPRBRL` at every depth on the slotted system** from `DetPRB` and `DetTabPRB` alone
(`thmPRBRL_allC`, the scope conditions `baseRetOk_Lsl`, `retCount_Lsl`). -/
theorem thmPRBRL_allC_Lsl (hdet : ∀ M, Lsl.DetPRB (fun M _ => Lsl.K M) M)
    (hdt : ∀ M, Lsl.DetTabPRB (fun M _ => Lsl.K M) M) (M : Nat) :
    Lsl.ThmPRBRL (fun M _ => Lsl.K M) M :=
  Lsl.thmPRBRL_allC Lsl_ok (Lsl.budget_K Lsl_ok) baseRetOk_Lsl retCount_Lsl hdet hdt M

theorem actRet_unique_Lsl {M : Nat} {g : Clif.Function} (hg : g ∈ Lsl.P.funcs)
    {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (hME : Lsl.MachEntry (fun M _ => Lsl.K M) M g F G ra s w₀) (hra : RaOk (Lsl.A g) (ra - 4))
    {us us' : List (Reg × Reg)} {outs outs' : List CV} {wf wf' : Arm.ArmState} {n n' : Nat}
    (h : ActRet ra F G us outs wf s (runX (Lsl.mach M g) n s))
    (ht : PostTrace (Lsl.A g).fa (Lsl.A g).af (Lsl.A g).base (Lsl.mach M g) s n)
    (h' : ActRet ra F G us' outs' wf' s (runX (Lsl.mach M g) n' s))
    (ht' : PostTrace (Lsl.A g).fa (Lsl.A g).af (Lsl.A g).base (Lsl.mach M g) s n') : n = n' :=
  Lsl.actRet_unique Lsl_ok hg hME hra h ht h' ht'

end E2E.LinkSlotSysWitness

namespace E2E.LinkSlotSysWitness

open Backend Backend.Proof Backend.Proof.Driver

/-- **`backend_correct_program_core_init` on the slotted system** (`Ok`, budget, `BaseRetOk`,
`RetCount` discharged; `DetPRB`, `DetTabPRB`, the entry and `TableOf` remain). -/
theorem backend_correct_program_core_init_Lsl :
    type_of% (@backend_correct_program_core_init Lsl Lsl_ok _ (fun M _ => Lsl.K M)
      (Lsl.budget_K Lsl_ok) baseRetOk_Lsl retCount_Lsl) :=
  @backend_correct_program_core_init Lsl Lsl_ok _ (fun M _ => Lsl.K M) (Lsl.budget_K Lsl_ok)
    baseRetOk_Lsl retCount_Lsl

/-- **`backend_correct_program_init` on the slotted system's base `L0`** (`Lsl = L0.std`). -/
theorem backend_correct_program_init_L0 :
    type_of% (@backend_correct_program_init L0 L0_ok (fun M _ => Lsl.K M)
      (L0.budget_K L0_ok) baseRetOk_Lsl retCount_Lsl) :=
  @backend_correct_program_init L0 L0_ok (fun M _ => Lsl.K M) (L0.budget_K L0_ok)
    baseRetOk_Lsl retCount_Lsl

end E2E.LinkSlotSysWitness
