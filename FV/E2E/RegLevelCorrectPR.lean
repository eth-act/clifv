import FV.E2E.RegLevelCorrectP

/-!
# The register-level theorem with the register prophecy (SEM1 #537, step 2r)

`docs/plans/uninit.md` §5.8: call number `n`'s contract may also assume that the masked
registers (but the pc) of the call state are those of the register prophecy `R n` (the state at
the run's `n`-th call, `prophStOf`):

* `ProphRegOkM c Mm fa base s R`: at the run's call states with `sp = c`, the masked registers
  but the pc are `R`'s of the call index;
* `OnCallPR K c P R … n u`: `OnCallP … n u`, and at a call state with `sp = c` the masked
  registers of `R n`; `onCallPR_of` (on a run with both prophecies every `OnCall … n` state);
* `regLevelCorrect_worldPR`: `regLevelCorrect_worldP` with the contracts of index `n` needed only
  at `OnCallPR … n` states.
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.Driver

/-- **A register prophecy of the run**: at the call states with `sp = c` the masked registers but
the pc are those of `R` at the call index. -/
def ProphRegOkM (c : BitVec 64) (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm)
    (base : BitVec 64) (s : Arm.ArmState) (R : Nat → Arm.ArmState) : Prop :=
  ∀ i, CallPc fa base (Arm.r .PC (runX Mm i s)) → spv (runX Mm i s) = c →
    ∀ f, Masked f → f ≠ .PC → Arm.r f (runX Mm i s) = Arm.r f (R (callsBefore Mm fa base s i))

/-- **A state of the run at call `n` with both prophecies** (when it is a call state with
`sp = c`). -/
def OnCallPR (K : Nat) (c : BitVec 64) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
    (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm) (base : BitVec 64) (s : Arm.ArmState)
    (n : Nat) (u : Arm.ArmState) : Prop :=
  OnCallP K c P Mm fa base s n u ∧
    (CallPc fa base (Arm.r .PC u) → spv u = c → ∀ f, Masked f → f ≠ .PC → Arm.r f u = Arm.r f (R n))

theorem onCallPR_of {K : Nat} {c : BitVec 64} {P : Nat → BitVec 64 → BitVec 8}
    {R : Nat → Arm.ArmState} {Mm : Arm.ArmState → Arm.ArmState} {fa : FnAsm} {base : BitVec 64}
    {s : Arm.ArmState} (hP : ProphOk K c Mm fa base s P) (hR : ProphRegOkM c Mm fa base s R)
    {n : Nat} {u : Arm.ArmState} (h : OnCall Mm fa base s n u) :
    OnCallPR K c P R Mm fa base s n u := by
  refine ⟨onCallP_of_prophOk hP h, fun hc hsp f hf hpc => ?_⟩
  obtain ⟨i, rfl, rfl⟩ := h
  exact hR i hc hsp f hf hpc

/-- **`regLevelCorrect_worldP` with the register prophecy**: for prophecies `P` (bytes) and `R`
(masked registers) of the machine run, the contracts of index `n` are needed only at the run's
call-`n` states, and may assume that the `Kp` bytes below `c` hold `P n` and the masked registers
but the pc are `R n`'s there. -/
theorem regLevelCorrect_worldPR {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ()) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {XI : ExtSemI} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    {Kp : Nat} {c : BitVec 64} {P : Nat → BitVec 64 → BitVec 8}
    (hproph : ProphOk Kp c (ArmStepX (XI.at 0) H fa) fa base s P) {R : Nat → Arm.ArmState}
    (hregp : ProphRegOkM c (ArmStepX (XI.at 0) H fa) fa base s R)
    (hC : ∀ n, CalleeOkGP (OnCallPR Kp c P R (ArmStepX (XI.at 0) H fa) fa base s n)
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) (XI.at n) H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → ∀ n,
      CalleeTryOkGP (OnCallPR Kp c P R (ArmStepX (XI.at 0) H fa) fa base s n)
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) (XI.at n) H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → ∀ n,
      TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K (XI.at n) H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀) (ρ₀ : Nat → CV) :
    (∀ us vals w nc, VRetFrom vcp (csemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩
        us vals (w, nc) →
      ∃ n, ArmRet ra s (E2E.runX (ArmStepX (XI.at 0) H fa) n s) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX (ArmStepX (XI.at 0) H fa) n s) p = x) ∧
        (∀ a, ¬ (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) a →
          (E2E.runX (ArmStepX (XI.at 0) H fa) n s).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX (ArmStepX (XI.at 0) H fa) n s) = Arm.r f w) ∧
        (∀ a, G a → (E2E.runX (ArmStepX (XI.at 0) H fa) n s).mem a = s.mem a) ∧
        (E2E.runX (ArmStepX (XI.at 0) H fa) n s).program = s.program ∧
        ∀ i, 0 < i → i < n → PostCall fa base (Arm.r .PC (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) →
          spv (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = spv s - BitVec.ofNat 64 (frameDrop af)) ∧
    (∀ c, VTrapFrom vcp (csemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX (XI.at 0) H fa) n s)) :=
  regLevelCorrect_worldC hcheck halloc hemit hlayout hcov hent hres hG
    (fun n => (hC n).mono fun _ h => onCallPR_of hproph hregp h)
    (fun h n => (hCT h n).mono fun _ h => onCallPR_of hproph hregp h) hTls hbe ρ₀

end Backend.Proof
