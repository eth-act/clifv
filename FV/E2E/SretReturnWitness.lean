import FV.E2E.SretReturn
import FV.E2E.NonVacuity
import FV.Backend.SpillAlloc
import FV.Backend.Proof.RegallocCover

/-!
# Non-vacuity of `backend_correct_final_abi` / `backend_correct_final_sret` (S7)

`sw` is the shape cg_clif emits for a function returning a struct by pointer:
`function %sret_witness(i64 sret, i64) { block0(v0: i64, v1: i64): store v1, v0; return }`.
`compiled_exists`: it is in scope (`InSubset`), `sretStableB`, compiled (with the spill
allocation, through emission and layout) with its prepared code's forms covered, and its ABI
return value is the `sret` argument (`sretArg sw [p, v] = [p]`). `sw_returns_sret`: with the
witness callees (`NonVacuity`), every premise of `backend_correct_final_sret` but the run's own is
discharged: a return of a run of `sw` leaves the pointer `p` in x8 (Cranelift's AArch64 ABI).
-/

namespace E2E.SretReturnWitness

open Backend Backend.Proof Backend.Proof.Driver

/-- `function %sret_witness(i64 sret, i64) system_v { block0(v0: i64, v1: i64):
store.i64 v1, v0; return }` -/
def sw : Clif.Function :=
  { name := "sret_witness",
    sig := { params := [{ ty := .i64, purpose := .sret }, { ty := .i64 }] },
    blocks := [{
      id := 0, params := [(0, .i64), (1, .i64)],
      body := [{ inst := .store .store .i64 ({} : Clif.MemFlags) 1 0 0 }], term := .ret [] }] }

/-- Closed compilation of `sw` through lowering, preparation, the spill allocation, emission and
layout, with the prepared forms covered. -/
def checks : Bool :=
  Backend.verifiable sw && sretStableB sw &&
  match lowerFunction sw with
  | .error _ => false
  | .ok vc =>
    lowerCheck sw vc &&
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
theorem checks_true : checks = true := by native_decide

theorem sretArg_sw (p v : Clif.Val) : sretArg sw [p, v] = [p] := rfl

/-- **`sw` meets the compile-time premises of `backend_correct_final_sret`** (`i = 0`). -/
theorem compiled_exists :
    InSubset ({ funcs := [] } : Clif.Program) sw ∧ sretStableB sw = true ∧
    sw.sig.params.findIdx? (·.purpose == .sret) = some 0 ∧ sw.sig.returns = [] ∧
    (∀ p v, sretArg sw [p, v] = [p]) ∧
    ∃ vc vcp af fa fb, Compiled sw 0 vc vcp (spillAlloc vcp) af fa fb ∧
      FormsCovered ⟨fa.k, af.slotBase⟩ vcp := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true] at h
  obtain ⟨⟨hv, hs⟩, h⟩ := h
  refine ⟨InSubset.of_verifiable hv (fun _ => rfl), hs, by decide, rfl, sretArg_sw, ?_⟩
  cases hl : lowerFunction sw with
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

/-- **`backend_correct_final_sret` applies to `sw`**: for its compilation, with the witness
callees (`NonVacuity`: every contract premise discharged; `sw` makes no calls), a CLIF return of
a run of `sw` on `[p, v]` is matched by an Arm return with the struct pointer `p` in x8. -/
theorem sw_returns_sret :
    ∃ vc vcp af fa fb, Compiled sw 0 vc vcp (spillAlloc vcp) af fa fb ∧
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
  refine ⟨vc, vcp, af, fa, fb, hc, ?_⟩
  intro syms K env hK g h tp base ra s w₀ p v cs hent hres hbe hargs hcs hrel htr fuel vals cm hrun
  obtain ⟨hC, hTls, hX, hXI, hsym⟩ :=
    final_contracts_witness (f := sw) (vcp := vcp) (rf := spillAlloc vcp) (af := af)
      (slotOff := af.slotBase) (syms := syms) (env := env) hK g h tp
      (by simp [sw]) (by simp [indSigs, sw]) (by simp [sw]) (by simp [indSigs, sw])
  exact backend_correct_final_sret hsub hc hS hi hnr hcov hC
    (fun ⟨B, hB, ht⟩ => absurd ht (by simp [sw] at hB; subst hB; decide)) (fun _ => hTls)
    hX hXI hsym rfl hent hres hbe hargs hcs hrel htr fuel hrun (v := p) rfl

end E2E.SretReturnWitness
