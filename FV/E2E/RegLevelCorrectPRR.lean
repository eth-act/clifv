import FV.E2E.RegLevelCorrectPR
import FV.E2E.RegLevelCorrectCR

/-!
# `regLevelCorrect_worldPR` with the located reads (SEM1 #537, step 3p)
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.Driver

/-- **`regLevelCorrect_worldPR` with the located reads** (`actReadsIn` at every state of the run
before the return). `regLevelCorrect_worldP` with the register prophecy: for prophecies `P` (bytes) and `R`
(masked registers) of the machine run, the contracts of index `n` are needed only at the run's
call-`n` states, and may assume that the `Kp` bytes below `c` hold `P n` and the masked registers
but the pc are `R n`'s there. -/
theorem regLevelCorrect_worldPRR {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
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
        (∀ i, 0 < i → i < n → PostCall fa base (Arm.r .PC (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) →
          spv (E2E.runX (ArmStepX (XI.at 0) H fa) i s) = spv s - BitVec.ofNat 64 (frameDrop af)) ∧
        ∀ i < n, actReadsIn vcp rf af fa fb base s (XI.at 0) H K G gv (E2E.runX (ArmStepX (XI.at 0) H fa) i s)) ∧
    (∀ c, VTrapFrom vcp (csemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ c →
      ∃ n, TrapAt fb base c (E2E.runX (ArmStepX (XI.at 0) H fa) n s)) :=
  regLevelCorrect_worldCR hcheck halloc hemit hlayout hcov hent hres hG
    (fun n => (hC n).mono fun _ h => onCallPR_of hproph hregp h)
    (fun h n => (hCT h n).mono fun _ h => onCallPR_of hproph hregp h) hTls hbe ρ₀

end Backend.Proof
