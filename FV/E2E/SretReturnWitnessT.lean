import FV.E2E.SretReturnT
import FV.E2E.SretReturnWitness
import FV.E2E.TypedRulesProg

/-!
# Non-vacuity of `backend_correct_finalT_abi` / `backend_correct_finalT_sret` (S7)

`sw` (`SretReturnWitness`) through the typed chain (`InSubset.toT`, `Compiled.toT`, the proven
typed rule families `typedRules_program`): with the witness callees (`NonVacuity`), a return of
a run of `sw` leaves the pointer `p` in x8 (until #587: x0).
-/

namespace E2E.SretReturnWitness

open Backend Backend.Proof Backend.Proof.Driver

/-- **`backend_correct_finalT_sret` applies to `sw`** (its compilation of `compiled_exists`). -/
theorem sw_returns_sretT :
    ∃ vc vcp af fa fb, CompiledT sw 0 vc vcp (spillAlloc vcp) af fa fb ∧
      ∀ {syms : String → Option Nat} {K : Nat} {env : Clif.Env} (_ : 32 ≤ K) (g h tp : BitVec 64)
        {base ra : BitVec 64} {s w₀ : Arm.ArmState} {p v : Clif.Val} {cs : Clif.State},
        AbiEntry fb base ra s → StackAvail K af s → BodyEntry af s w₀ →
        ArgsIn sw.sig [p, v] s → ClifEntry sw [p, v] cs →
        Rel.holds ⟨frameW K (RAFrame.compute vcp (spillAlloc vcp)).intBase
          (RAFrame.compute vcp (spillAlloc vcp)).size af s, syms, af.slotBase,
          (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩ sw cs.frame.slots cs.mem w₀ →
        TrapsExplicit env { funcs := [] } cs → ∀ fuel vals cm,
        Clif.runLoop env { funcs := [] } fuel cs = .returned vals cm →
        ∃ n, ArmRet ra s (runX (ArmStepX (witnessX (witnessSym syms) tp)
            (witnessHooks g h (witnessSym syms) tp) fa) n s) ∧
          XHolds p (xreg 8 (runX (ArmStepX (witnessX (witnessSym syms) tp)
            (witnessHooks g h (witnessSym syms) tp) fa) n s)) ∧
          MemAgree cm (runX (ArmStepX (witnessX (witnessSym syms) tp)
            (witnessHooks g h (witnessSym syms) tp) fa) n s) := by
  obtain ⟨hsub, hS, hi, hnr, -, vc, vcp, af, fa, fb, hc, hcov⟩ := compiled_exists
  refine ⟨vc, vcp, af, fa, fb, hc.toT, ?_⟩
  intro syms K env hK g h tp base ra s w₀ p v cs hent hres hbe hargs hcs hrel htr fuel vals cm hrun
  obtain ⟨hC, hTls, hX, hXI, hsym⟩ :=
    final_contracts_witness (f := sw) (vcp := vcp) (rf := spillAlloc vcp) (af := af)
      (slotOff := af.slotBase) (syms := syms) (env := env) hK g h tp
      (by simp [sw]) (by simp [indSigs, sw]) (by simp [sw]) (by simp [indSigs, sw])
  exact backend_correct_finalT_sret hsub.toT hc.toT hS typedRules_program hi
    (fun q hq => by simp [sw] at hq; subst hq; rfl) hnr hcov hC
    (fun ⟨B, hB, ht⟩ => absurd ht (by simp [sw] at hB; subst hB; decide)) (fun _ => hTls)
    hX hXI hsym rfl hent hres hbe hargs hcs hrel htr fuel hrun (v := p) rfl

end E2E.SretReturnWitness
