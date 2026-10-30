import FV.E2E.SretReturnOpt
import FV.E2E.SretReturnWitness
import FV.Opt.OptimizeX

/-!
# Non-vacuity of `backend_correct_opt_proven_abi` (S7)

`sw` (`SretReturnWitness`) optimised by the executable compiler's mid-end configuration
(`Opt.exeConfig`: the Cranelift rules, the proven rule set) and compiled: every premise of
`backend_correct_opt_proven_abi` but the run's own is discharged (witness callees,
`NonVacuity`), so a return of a run of `sw` on `[p, v]` leaves `p` in x8 after the (no) CLIF
results.
-/

namespace E2E.SretReturnWitness

open Backend Backend.Proof Backend.Proof.Driver

/-- `sw` after the mid-end. -/
def swo : Clif.Function := Opt.optimize sw Opt.exeConfig

/-- Closed compilation of `swo` (as `checks`), and `swo` binds its `sret` value once. -/
def checksOpt : Bool :=
  sretStableB swo &&
  match lowerFunction swo with
  | .error _ => false
  | .ok vc =>
    lowerCheck swo vc &&
    match Backend.prepare vc with
    | .error _ => false
    | .ok vcp =>
      prepCheck vc vcp && (checkAlloc vcp (spillAlloc vcp)).isOk &&
      match lowerRFunc vcp (spillAlloc vcp) with
      | .error _ => false
      | .ok af => match emitFunc 0 af with
        | .error _ => false
        | .ok fa => formsCoveredB ⟨fa.k, af.slotBase⟩ vcp && fa.layout.isOk

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The closed test receipt (not used by any compiler correctness theorem). -/
theorem checksOpt_true : checksOpt = true := by native_decide

/-- **`swo` meets the compile-time premises of `backend_correct_opt_proven_abi`.** -/
theorem compiled_opt_exists :
    sretStableB swo = true ∧
    ∃ vc vcp af fa fb, Compiled swo 0 vc vcp (spillAlloc vcp) af fa fb ∧
      FormsCovered ⟨fa.k, af.slotBase⟩ vcp := by
  have h := checksOpt_true
  simp only [checksOpt, Bool.and_eq_true] at h
  obtain ⟨hs, h⟩ := h
  refine ⟨hs, ?_⟩
  cases hl : lowerFunction swo with
  | error e => rw [hl] at h; cases h
  | ok vc =>
    rw [hl] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hlo, h⟩ := h
    cases hp : Backend.prepare vc with
    | error e => rw [hp] at h; cases h
    | ok vcp =>
      rw [hp] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hpr, hck⟩, h⟩ := h
      have hc : checkAlloc vcp (spillAlloc vcp) = .ok () := by
        cases he : checkAlloc vcp (spillAlloc vcp) with
        | error e => rw [he] at hck; cases hck
        | ok u => cases u; rfl
      cases ha : lowerRFunc vcp (spillAlloc vcp) with
      | error e => rw [ha] at h; cases h
      | ok af =>
        rw [ha] at h
        simp only at h
        cases he : emitFunc 0 af with
        | error e => rw [he] at h; cases h
        | ok fa =>
          rw [he] at h
          simp only [Bool.and_eq_true] at h
          obtain ⟨hcov, hlay⟩ := h
          cases hb : fa.layout with
          | error e => rw [hb] at hlay; cases hlay
          | ok fb =>
            exact ⟨vc, vcp, af, fa, fb, ⟨hl, hlo, hp, hpr, hc, ha, he, hb⟩,
              (formsCoveredB_iff _ _).1 hcov⟩

/-- **`backend_correct_opt_proven_abi` applies to `sw`**: for the compilation of its optimised
form, with the witness callees, the Arm run refines the CLIF run of `sw` on `[p, v]` with the
`sret` pointer `p` as the ABI return value after the CLIF ones. -/
theorem sw_opt_abi :
    ∃ vc vcp af fa fb, Compiled swo 0 vc vcp (spillAlloc vcp) af fa fb ∧
      ∀ {syms : String → Option Nat} {K : Nat} {env : Clif.Env} (_ : 32 ≤ K) (g h tp : BitVec 64),
        Opt.EnvKeepsSymbols env →
        ∀ {base ra : BitVec 64} {s w₀ : Arm.ArmState} {p v : Clif.Val} {cs : Clif.State},
        AbiEntry fb base ra s → StackAvail K af s → BodyEntry af s w₀ →
        ArgsIn sw.sig [p, v] s → ClifEntry sw [p, v] cs →
        Rel.holds ⟨frameW K (RAFrame.compute vcp (spillAlloc vcp)).intBase
          (RAFrame.compute vcp (spillAlloc vcp)).size af s, syms, af.slotBase,
          (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩ sw cs.frame.slots cs.mem w₀ →
        TrapsExplicit env (Opt.optimizeProgram { funcs := [] } Opt.exeConfig)
          (optEntry Opt.exeConfig sw cs) → ∀ fuel,
        ArmRefinesAbi fb base ra (ArmStepX (witnessX (witnessSym syms) tp)
            (witnessHooks g h (witnessSym syms) tp) fa) s [p]
          (Clif.runLoop env { funcs := [] } fuel cs) := by
  obtain ⟨hsub, -, -, -, -, -⟩ := compiled_exists
  obtain ⟨hS, vc, vcp, af, fa, fb, hc, hcov⟩ := compiled_opt_exists
  refine ⟨vc, vcp, af, fa, fb, hc, ?_⟩
  intro syms K env hK g h tp hE base ra s w₀ p v cs hent hres hbe hargs hcs hrel htr fuel
  obtain ⟨hC, hTls, hX, -, hsym⟩ :=
    final_contracts_witness (f := sw) (vcp := vcp) (rf := spillAlloc vcp) (af := af)
      (slotOff := af.slotBase) (syms := syms) (env := env) hK g h tp
      (by simp [sw]) (by simp [indSigs, sw]) (by simp [sw]) (by simp [indSigs, sw])
  have hA := backend_correct_opt_proven_abi Opt.exeConfig rfl rfl hsub
    (by simp [sw]) (by simp [sw]; decide) hc hS hcov hC (fun _ => hTls) hX hsym rfl hE
    hent hres hbe hargs hcs hrel htr fuel
  rwa [sretArg_sw] at hA

end E2E.SretReturnWitness
