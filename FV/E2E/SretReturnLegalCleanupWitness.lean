import FV.E2E.SretReturnLegalCleanup
import FV.E2E.SretReturnLegalWitness

/-!
# Non-vacuity of `backend_correct_legal_cleanup_abi` (S7)

`swl` (`SretReturnLegalWitness`: the legalisation of `swi(i64 sret, i128)`) compiled through
the dead-cleanup pipeline (`checksLC_true`, `native_decide`); with the witness callees every
function-level premise of `backend_correct_legal_cleanup_abi` is discharged.
-/

namespace E2E.SretReturnWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- `swl` compiled through the dead-cleanup pipeline, with the prepared forms covered. -/
def checksLC : Bool :=
  match lowerFunction swl with
  | .error _ => false
  | .ok vc =>
    lowerCheck swl vc &&
    match Backend.prepare (cleanupStage swl vc) with
    | .error _ => false
    | .ok vcp =>
      prepCheck (cleanupStage swl vc) vcp && (checkAlloc vcp (spillAlloc vcp)).isOk &&
      match lowerRFunc vcp (spillAlloc vcp) with
      | .error _ => false
      | .ok af => match emitFunc 0 af with
        | .error _ => false
        | .ok fa => formsCoveredB ⟨fa.k, af.slotBase⟩ vcp && fa.layout.isOk

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The closed test receipt (not used by any compiler correctness theorem). -/
theorem checksLC_true : checksLC = true := by native_decide

theorem compiled_legal_cleanup_exists :
    ∃ vc vcp af fa fb, CompiledCleanup swl 0 vc vcp (spillAlloc vcp) af fa fb ∧
      FormsCovered ⟨fa.k, af.slotBase⟩ vcp := by
  have h := checksLC_true
  simp only [checksLC] at h
  cases hl : lowerFunction swl with
  | error e => rw [hl] at h; cases h
  | ok vc =>
    rw [hl] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hlo, h⟩ := h
    cases hp : Backend.prepare (cleanupStage swl vc) with
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

/-- **`backend_correct_legal_cleanup_abi` applies to `swi`/`swl`** (dead-cleanup compilation). -/
theorem swl_legal_cleanup_abi :
    ∃ vc vcp af fa fb, CompiledCleanup swl 0 vc vcp (spillAlloc vcp) af fa fb ∧
      ∀ {syms : String → Option Nat} {K : Nat} (_ : 32 ≤ K) (g h tp : BitVec 64)
        {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {p lo hi : Clif.Val}
        {cs cs' : Clif.State},
        AbiEntry fb base ra s → StackAvail K af s → BodyEntry af s w₀ →
        Opt.Legal.ExpRel ((Opt.Legal.groups swi.sig.params).getD []) args [p, lo, hi] →
        ArgsIn swl.sig [p, lo, hi] s → ClifEntry swi args cs → ClifEntry swl [p, lo, hi] cs' →
        cs'.frame.slots = cs.frame.slots → cs'.mem = cs.mem →
        Rel.holds ⟨frameW K (RAFrame.compute vcp (spillAlloc vcp)).intBase
          (RAFrame.compute vcp (spillAlloc vcp)).size af s, syms, af.slotBase,
          (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩ swl cs'.frame.slots cs'.mem w₀ →
        TrapsExplicit Clif.Rust.env { funcs := [] } cs →
        TrapsExplicit Clif.Rust.env { funcs := [] } cs' → ∀ fuel,
        ArmRefinesLegalAbi ((Opt.Legal.groups swi.sig.returns).getD []) [p] fb base ra
          (ArmStepX (witnessX (witnessSym syms) tp) (witnessHooks g h (witnessSym syms) tp) fa) s
          (Clif.runLoop Clif.Rust.env { funcs := [] } fuel cs) := by
  obtain ⟨hchk, hsub, hS, hex, hind, hnt, hsa, -⟩ := compiled_legal_exists
  obtain ⟨vc, vcp, af, fa, fb, hc, hcov⟩ := compiled_legal_cleanup_exists
  refine ⟨vc, vcp, af, fa, fb, hc, ?_⟩
  intro syms K hK g h tp base ra s w₀ args p lo hi cs cs' hent hres hbe hexp hargs hcs hcs' hsl
    hmem hrel htrS htr fuel
  obtain ⟨hC, hTls, hX, hXI, hsym⟩ :=
    final_contracts_witness (f := swl) (vcp := vcp) (rf := spillAlloc vcp) (af := af)
      (slotOff := af.slotBase) (syms := syms) (env := Clif.Rust.env) hK g h tp
      (by simp [hex]) (by simp [hind]) (by simp [hex]) (by simp [hind])
  have hA := backend_correct_legal_cleanup_abi (p := { funcs := [] }) hchk hsub hc hS
    (fun fn e he => by simp [Clif.Function.extern?, swi] at he)
    (fun fn e he => by simp [Clif.Function.extern?, hex] at he)
    (fun ⟨B, hB, st, hst, sig, callee, args, hi⟩ => by
      simp [swi] at hB; subst hB; simp at hst)
    hcov hC (fun ⟨B, hB, ht⟩ => by rw [hnt B hB] at ht; cases ht)
    (fun _ => hTls) hX hXI hsym rfl hent hres hbe hexp hargs hcs hcs' hsl hmem hrel htrS htr fuel
  rwa [hsa] at hA

end E2E.SretReturnWitness
