import FV.E2E.SretReturnLegal
import FV.E2E.NonVacuity
import FV.Opt.Legalize128Pass

/-!
# Non-vacuity of `backend_correct_legal_abi` (S7)

`swi(i64 sret, i128)` (returns nothing; the shape of a struct-returning function with an `i128`
argument) is legalised by the compiler's pass (`Opt.Legalize128.function128Cert`) into `swl`,
which the validator accepts (`Opt.Legal.check`), the backend compiles (spill allocation,
emission, layout) and whose `sret` value is bound once (`sretStableB`): the receipt
`checksL_true` (`native_decide`). With the witness callees (`NonVacuity`) every function-level
premise of `backend_correct_legal_abi` is discharged; the entry premises remain. The ABI return
value of `swl`'s run on the split arguments `[p, lo, hi]` is the pointer `p`.
-/

namespace E2E.SretReturnWitness

open Backend Backend.Proof Backend.Proof.Driver

/-- `function %sret_i128(i64 sret, i128) system_v { block0(v0: i64, v1: i128): return }` -/
def swi : Clif.Function :=
  { name := "sret_i128",
    sig := { params := [{ ty := .i64, purpose := .sret }, { ty := .i128 }] },
    blocks := [{ id := 0, params := [(0, .i64), (1, .i128)], body := [], term := .ret [] }] }

/-- The legalisation of `swi` and its certificate (the compiler's pass). -/
def legalSwi : Clif.Function × Opt.Legalize128.Cert :=
  match Opt.Legalize128.function128Cert swi with
  | Except.ok r => r
  | Except.error _ => (swi, {})
def swl : Clif.Function := legalSwi.1
def certL : Opt.Legalize128.Cert := legalSwi.2

/-- The closed receipt: validator, scope, `sretStableB`, no externs/indirect calls/`try_call`,
the ABI return value at index 0, and the compilation of `swl`. -/
def checksL : Bool :=
  Opt.Legal.check swi swl certL && Backend.verifiable swl && sretStableB swl &&
  swl.externs.isEmpty && (indSigs swl).isEmpty && swl.blocks.all (fun B => !B.term.isTry) &&
  swl.sig.params.findIdx? (·.purpose == .sret) == some 0 &&
  (sigRets swl.sig != swl.sig.returns) &&
  match lowerFunction swl with
  | .error _ => false
  | .ok vc =>
    lowerCheck swl vc &&
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
theorem checksL_true : checksL = true := by native_decide

/-- **`swl` meets the compile-time premises of `backend_correct_legal_abi`.** -/
theorem compiled_legal_exists :
    Opt.Legal.check swi swl certL = true ∧ InSubset ({ funcs := [] } : Clif.Program) swl ∧
    sretStableB swl = true ∧ swl.externs = [] ∧ indSigs swl = [] ∧
    (∀ B ∈ swl.blocks, B.term.isTry = false) ∧ (∀ p lo hi, sretArg swl [p, lo, hi] = [p]) ∧
    ∃ vc vcp af fa fb, Compiled swl 0 vc vcp (spillAlloc vcp) af fa fb ∧
      FormsCovered ⟨fa.k, af.slotBase⟩ vcp := by
  have h := checksL_true
  simp only [checksL, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true, Bool.not_eq_true',
    beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hchk, hv⟩, hs⟩, hex⟩, hind⟩, hnt⟩, hidx⟩, hrets⟩, h⟩ := h
  refine ⟨hchk, InSubset.of_verifiable hv (fun _ => rfl), hs, hex, hind, hnt,
    fun p lo hi => by simp [sretArg, hidx, hrets], ?_⟩
  cases hl : lowerFunction swl with
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

/-- **`backend_correct_legal_abi` applies to `swi`/`swl`**: for `swl`'s compilation, with the
witness callees, the Arm code refines the run of the `i128` source `swi`, and a return leaves
the `sret` pointer `p` after the expanded (no) results. -/
theorem swl_legal_abi :
    ∃ vc vcp af fa fb, Compiled swl 0 vc vcp (spillAlloc vcp) af fa fb ∧
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
  obtain ⟨hchk, hsub, hS, hex, hind, hnt, hsa, vc, vcp, af, fa, fb, hc, hcov⟩ :=
    compiled_legal_exists
  refine ⟨vc, vcp, af, fa, fb, hc, ?_⟩
  intro syms K hK g h tp base ra s w₀ args p lo hi cs cs' hent hres hbe hexp hargs hcs hcs' hsl
    hmem hrel htrS htr fuel
  obtain ⟨hC, hTls, hX, hXI, hsym⟩ :=
    final_contracts_witness (f := swl) (vcp := vcp) (rf := spillAlloc vcp) (af := af)
      (slotOff := af.slotBase) (syms := syms) (env := Clif.Rust.env) hK g h tp
      (by simp [hex]) (by simp [hind]) (by simp [hex]) (by simp [hind])
  have hA := backend_correct_legal_abi (p := { funcs := [] }) hchk hsub hc hS
    (fun fn e he => by simp [Clif.Function.extern?, swi] at he)
    (fun fn e he => by simp [Clif.Function.extern?, hex] at he)
    (fun ⟨B, hB, st, hst, sig, callee, args, hi⟩ => by
      simp [swi] at hB; subst hB; simp at hst)
    hcov hC (fun ⟨B, hB, ht⟩ => by rw [hnt B hB] at ht; cases ht)
    (fun _ => hTls) hX hXI hsym rfl hent hres hbe hexp hargs hcs hcs' hsl hmem hrel htrS htr fuel
  rwa [hsa] at hA

end E2E.SretReturnWitness
