import FV.E2E.RegLevelCorrectC

/-!
# The register-level theorem with the refined (prophecy) call contract (SEM1 #537, step 2l)

`docs/plans/uninit.md` §5.5 "Refined call contract": call number `n`'s contract is needed only
at the activation's own `n`-th call state, and there the callee region below the body's `sp`
holds the prophecy `P n` (`ProphOk`). So the contract of index `n` may assume those bytes:

* `OnCallP K c P Mm fa base s n u`: `OnCall … n u`, and if `u` is a call state with `sp = c`,
  its `K` bytes below `c` are `P n`;
* `onCallP_of_prophOk`: on a run with the prophecy `P`, every `OnCall … n` state is `OnCallP`;
* `CalleeOkGP.mono`, `CalleeTryOkGP.mono`: the contracts at fewer states;
* `regLevelCorrect_worldP`: `regLevelCorrect_worldC` (same conclusion) with the contracts of
  index `n` required only at `OnCallP … P n` states, for a prophecy `P` of the machine run.
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.Driver

/-- **A state of the run at call `n` whose callee region holds `P n` when it is a call state.** -/
def OnCallP (K : Nat) (c : BitVec 64) (P : Nat → BitVec 64 → BitVec 8)
    (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm) (base : BitVec 64) (s : Arm.ArmState)
    (n : Nat) (u : Arm.ArmState) : Prop :=
  OnCall Mm fa base s n u ∧
    (CallPc fa base (Arm.r .PC u) → spv u = c → ∀ a, StackBelow K c a → u.mem a = P n a)

/-- On a run with the prophecy `P`, the call-`n` states see `P n` below `c`. -/
theorem onCallP_of_prophOk {K : Nat} {c : BitVec 64} {P : Nat → BitVec 64 → BitVec 8}
    {Mm : Arm.ArmState → Arm.ArmState} {fa : FnAsm} {base : BitVec 64} {s : Arm.ArmState}
    (hP : ProphOk K c Mm fa base s P) {n : Nat} {u : Arm.ArmState} (h : OnCall Mm fa base s n u) :
    OnCallP K c P Mm fa base s n u := by
  refine ⟨h, fun hc hsp a ha => ?_⟩
  obtain ⟨i, rfl, rfl⟩ := h
  exact hP i hc hsp a ha

theorem CalleeOkGP.mono {P P' : Arm.ArmState → Prop} {F : BitVec 64 → Prop} {K : Nat}
    {G : BitVec 64 → Prop} {s0 : Arm.ArmState} {Pc : BitVec 64 → MInst → Prop} {X : ExtSem}
    {H : ArmHooks} {S : CallInfo → Prop} {gv : Nat → String → Prop}
    (h : CalleeOkGP P' F K G s0 Pc X H S gv) (hPP : ∀ u, P u → P' u) :
    CalleeOkGP P F K G s0 Pc X H S gv :=
  ⟨fun ctx info hs s hp => h.os ctx info hs s (hPP s hp), h.pc, h.ext⟩

theorem CalleeTryOkGP.mono {P P' : Arm.ArmState → Prop} {F : BitVec 64 → Prop} {K : Nat}
    {G : BitVec 64 → Prop} {s0 : Arm.ArmState} {Pc : BitVec 64 → MInst → Prop} {X : ExtSem}
    {H : ArmHooks} {S : CallInfo → TryInfo → Prop} {gv : Nat → String → Prop}
    (h : CalleeTryOkGP P' F K G s0 Pc X H S gv) (hPP : ∀ u, P u → P' u) :
    CalleeTryOkGP P F K G s0 Pc X H S gv :=
  fun ctx info ti hS c wh ops regs i' s w outs w' s' hp =>
    h ctx info ti hS c wh ops regs i' s w outs w' s' (hPP s hp)

/-- **`regLevelCorrect_worldC` with the refined call contract**: for a prophecy `P` of the
machine run (`ProphOk Kp c`), the contracts of index `n` are needed only at the run's call-`n`
states, and may assume that the `Kp` bytes below `c` hold `P n` there. -/
theorem regLevelCorrect_worldP {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ()) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {XI : ExtSemI} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    {Kp : Nat} {c : BitVec 64} {P : Nat → BitVec 64 → BitVec 8}
    (hproph : ProphOk Kp c (ArmStepX (XI.at 0) H fa) fa base s P)
    (hC : ∀ n, CalleeOkGP (OnCallP Kp c P (ArmStepX (XI.at 0) H fa) fa base s n)
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) (XI.at n) H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → ∀ n,
      CalleeTryOkGP (OnCallP Kp c P (ArmStepX (XI.at 0) H fa) fa base s n)
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
    (fun n => (hC n).mono fun _ h => onCallP_of_prophOk hproph h)
    (fun h n => (hCT h n).mono fun _ h => onCallP_of_prophOk hproph h) hTls hbe ρ₀

end Backend.Proof
