import FV.E2E.AllocTotal
import FV.Backend.Proof.RelaxReady

/-!
# Emission and layout without `he`/`hla` premises (V6)

`emitFunc` relaxes out-of-range conditional branches (`relaxLine`, `relaxOf`), so branch range
is no longer a reason for `layout` to fail: `emitFunc_layout_total`
(`FV/Backend/Proof/RelaxLayout.lean`) proves layout succeeds for every emitted function whose
lines pass `FnAsm.layoutReadyB` (labels defined once, every instruction encodable apart from its
label operand, the jump-table/atomic-loop-local PC-relative forms in reach, size < 128 MiB).

`backend_correct_final_total_relaxed` is V5's `backend_correct_final_total` with the premises
`emitFunc k af = .ok fa` and `fa.layout = .ok fb` replaced by
* `hpre`: `emitPre` succeeds (instruction expansion, `MInst.lines`; not branch-related), and
* `hready`: the emitted function passes `layoutReadyB`,
and `fa`, `fb` existential. What is left of emission/layout is exactly these two premises
(`docs/TO-PROVE.md` V6, "Remaining").
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

set_option linter.unusedVariables false in -- the conclusion's premises are named for readability
/-- **The backend's end-to-end theorem, total up to emission's own checks** (V6 on V5's
`backend_correct_final_total`): for every in-scope function and every answer `ra` of the untrusted
allocator, allocation and lowering succeed, and if `emitPre` succeeds and the emitted code passes
`layoutReadyB`, emission and layout succeed and the machine code refines the CLIF run under
`backend_correct_final`'s contract, link-time and run premises. Compared with
`backend_correct_final_total`, the premises `emitFunc k af = .ok fa` and `fa.layout = .ok fb` are
gone (branch range is discharged by relaxation). -/
theorem backend_correct_final_total_relaxed {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} (hsub : InSubset p f) (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (har : Spill.arityOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (ra : Except String RFunc) :
    ∃ af, lowerAlloc vcp ra = .ok af ∧
      ((∃ pre, emitPre k af = .ok pre) → (∀ fa, emitFunc k af = .ok fa → fa.layoutReadyB = true) →
      ∃ fa fb, emitFunc k af = .ok fa ∧ fa.layout = .ok fb ∧
      ∀ {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
        {K : Nat},
      ∀
        (hC : ∀ s, CalleeOk
          (frameW K (RAFrame.compute vcp (allocResult vcp ra)).intBase
            (RAFrame.compute vcp (allocResult vcp ra)).size af s) K X H vcp.CallSite)
        (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
          (frameW K (RAFrame.compute vcp (allocResult vcp ra)).intBase
            (RAFrame.compute vcp (allocResult vcp ra)).size af s) X H vcp.TrySite)
        (hTls : hasTls f = true → ∀ s, TlsOk
          (frameW K (RAFrame.compute vcp (allocResult vcp ra)).intBase
            (RAFrame.compute vcp (allocResult vcp ra)).size af s) K X H)
        (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
          Rel.holds ⟨frameW K (RAFrame.compute vcp (allocResult vcp ra)).intBase
            (RAFrame.compute vcp (allocResult vcp ra)).size af s, syms,
            slotOff, (RAFrame.compute vcp (allocResult vcp ra)).intBase⟩ f sl cm w) X)
        (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
          Rel.holds ⟨frameW K (RAFrame.compute vcp (allocResult vcp ra)).intBase
            (RAFrame.compute vcp (allocResult vcp ra)).size af s, syms,
            slotOff, (RAFrame.compute vcp (allocResult vcp ra)).intBase⟩ f sl cm w) X)
        (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
        (hslot : af.slotBase = slotOff)
        {base ra' : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
        (hent : AbiEntry fb base ra' s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
        (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
        (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp (allocResult vcp ra)).intBase
            (RAFrame.compute vcp (allocResult vcp ra)).size af s,
          syms, slotOff, (RAFrame.compute vcp (allocResult vcp ra)).intBase⟩ f cs.frame.slots cs.mem
          w₀)
        (htr : TrapsExplicit env p cs) (fuel : Nat),
      ArmRefines fb base ra' (ArmStepX X H fa) s (Clif.runLoop env p fuel cs)) := by
  obtain ⟨af, ha, hcor⟩ := backend_correct_final_total (k := k) hsub hd hs har hl hp ra
  refine ⟨af, ha, fun ⟨pre, hpre⟩ hready => ?_⟩
  obtain ⟨fa, he⟩ := emitFunc_of_emitPre hpre
  obtain ⟨fb, hla⟩ := emitFunc_layout_ready he (hready fa he)
  exact ⟨fa, fb, he, hla, hcor he hla⟩

/-- The emitted code of `lowerWitness` (spill allocation) passes `layoutReadyB`. -/
def lowerWitnessReadyB : Bool :=
  match lowerFunction lowerWitness with
  | .error _ => false
  | .ok vc => match Backend.prepare vc with
    | .error _ => false
    | .ok vcp => match lowerRFunc vcp (allocResult vcp (.error "regalloc2 absent")) with
      | .error _ => false
      | .ok af => match emitFunc 0 af with
        | .error _ => false
        | .ok fa => fa.layoutReadyB

/-- **Non-vacuity of `backend_correct_final_total_relaxed`**: on `lowerWitness` (whose input
conditions `backend_correct_final_total_witness` discharges), `lowerAlloc` succeeds, `emitPre`
succeeds and the emitted code passes `layoutReadyB`. -/
theorem backend_correct_final_total_relaxed_witness :
    ∃ vc vcp af, lowerFunction lowerWitness = .ok vc ∧ Backend.prepare vc = .ok vcp ∧
      lowerAlloc vcp (.error "regalloc2 absent") = .ok af ∧
      (∃ pre, emitPre 0 af = .ok pre) ∧ ∀ fa, emitFunc 0 af = .ok fa → fa.layoutReadyB = true := by
  obtain ⟨-, -, vc, vcp, af, hl, hp, -, hr⟩ := lowerWitness_spill_facts
  have h : lowerWitnessReadyB = true := by native_decide
  simp only [lowerWitnessReadyB, hl, hp, hr] at h
  refine ⟨vc, vcp, af, hl, hp, (lowerAlloc_eq_lowerRFunc _ _).trans hr, ?_, fun fa he => ?_⟩
  · cases hpe : emitPre 0 af with
    | ok pre => exact ⟨pre, rfl⟩
    | error e =>
      have : emitFunc 0 af = .error e := by simp [emitFunc, hpe, bind, Except.bind]
      simp [this] at h
  · simpa [he] using h

end E2E
