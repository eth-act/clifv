import FV.E2E.SpillKillFree
import FV.Backend.Proof.RelaxReady

/-!
# Emission and layout without `he`/`hla` premises (V6)

`emitFunc` relaxes out-of-range conditional branches (`relaxLine`, `relaxOf`), so branch range
is no longer a reason for `layout` to fail: `emitFunc_layout_total`
(`FV/Backend/Proof/RelaxLayout.lean`) proves layout succeeds for every emitted function whose
lines pass `FnAsm.layoutReadyB` (labels defined once, every instruction encodable apart from its
label operand, the jump-table/atomic-loop-local PC-relative forms in reach, size < 128 MiB).

`backend_correct_final_relaxed` is `backend_correct_final_alloc_proven` with the premises
`he : emitFunc k af = .ok fa` and `hla : fa.layout = .ok fb` replaced by
* `hpre`: `emitPre` succeeds (instruction expansion, `MInst.lines`; not branch-related), and
* `hready`: the emitted function passes `layoutReadyB`,
and `fa`, `fb` existential. What is left of emission/layout is exactly these two premises
(`docs/TO-PROVE.md` V6, "Remaining").
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **The backend's end-to-end theorem without emission/layout-success premises** (V6). -/
theorem backend_correct_final_relaxed {p : Clif.Program}
    {f : Clif.Function} {k : Nat} {vc vcp : VCode} {ra : Except String RFunc} {rf : RFunc}
    {af : AFunc} (hsub : InSubset p f) (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (har : Spill.arityOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hrf : rf = allocResult vcp ra) (ha : lowerRFunc vcp rf = .ok af)
    (hpre : ∃ pre, emitPre k af = .ok pre)
    (hready : ∀ fa, emitFunc k af = .ok fa → fa.layoutReadyB = true)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff) :
    ∃ fa fb, emitFunc k af = .ok fa ∧ fa.layout = .ok fb ∧
      ∀ {base ra' : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State},
        AbiEntry fb base ra' s → StackAvail K af s → BodyEntry af s w₀ → ArgsIn f.sig args s →
        ClifEntry f args cs →
        Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
          syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀ →
        TrapsExplicit env p cs → ∀ fuel,
          ArmRefines fb base ra' (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) := by
  obtain ⟨pre, hpre⟩ := hpre
  obtain ⟨fa, he⟩ := emitFunc_of_emitPre hpre
  obtain ⟨fb, hla⟩ := emitFunc_layout_ready he (hready fa he)
  exact ⟨fa, fb, he, hla, fun hent hres hbe hargs hcs hrel htr fuel =>
    backend_correct_final_alloc_proven hsub hd hs har hl hp hrf ha he hla hC hCT hTls hX hXI hsym
      hslot hent hres hbe hargs hcs hrel htr fuel⟩

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

/-- **Non-vacuity of `backend_correct_final_relaxed`**: on `lowerWitness` (whose other premises
`backend_correct_final_alloc_proven_witness` discharges), `emitPre` succeeds and the emitted code
passes `layoutReadyB`. -/
theorem backend_correct_final_relaxed_witness :
    ∃ vc vcp af, lowerFunction lowerWitness = .ok vc ∧ Backend.prepare vc = .ok vcp ∧
      lowerRFunc vcp (allocResult vcp (.error "regalloc2 absent")) = .ok af ∧
      (∃ pre, emitPre 0 af = .ok pre) ∧ ∀ fa, emitFunc 0 af = .ok fa → fa.layoutReadyB = true := by
  obtain ⟨-, -, vc, vcp, af, hl, hp, -, hr⟩ := lowerWitness_spill_facts
  have h : lowerWitnessReadyB = true := by native_decide
  simp only [lowerWitnessReadyB, hl, hp, hr] at h
  refine ⟨vc, vcp, af, hl, hp, hr, ?_, fun fa he => ?_⟩
  · cases hpe : emitPre 0 af with
    | ok pre => exact ⟨pre, rfl⟩
    | error e =>
      have : emitFunc 0 af = .error e := by simp [emitFunc, hpe, bind, Except.bind]
      simp [this] at h
  · simpa [he] using h

end E2E
