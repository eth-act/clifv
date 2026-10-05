import FV.E2E.FinalDirect

/-!
# The final theorem without the register-allocation checker premise (V4)

`backend_correct_final_of_lower` still assumed `checkAlloc vcp rf = .ok ()` for the allocation
`rf` regalloc2 computed. The backend now lowers `allocResult vcp ra` (`FV/Backend/SpillAlloc.lean`;
`lowerAlloc_eq` relates it to the compiler's `lowerAlloc`): regalloc2's answer `ra` if
`checkAlloc` accepts it, else the spill allocation `spillAlloc vcp`. So the checker's verdict on
regalloc2's output is no longer a premise: whatever regalloc2 returns (or if it fails or is
absent), the allocation that is lowered is accepted, provided the spill allocation is
(`SpillAccepted`).

`SpillAccepted` is stated as an explicit hypothesis (like `LogicImmComplete` was): it says the
checker accepts the spill allocation of every function the pipeline produces from in-scope
input. It does not depend on the program; `lean-e2e-check` decides its conclusion on every
in-scope function of the corpus and the runtests ("spill fallback" line). What a proof needs
is listed in `docs/TO-PROVE.md` (V4).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Cov

/-- **The spill allocation is accepted** (V4, open; an explicit hypothesis, not an axiom):
`checkAlloc` accepts `spillAlloc vcp` for every prepared VCode `vcp` that `lowerFunction` and
`prepare` produce from a function with the input conditions `Dominated` and `LowerScope`. -/
def SpillAccepted : Prop :=
  ∀ (f : Clif.Function) (vc vcp : VCode), Dominated f → LowerScope f →
    lowerFunction f = .ok vc → Backend.prepare vc = .ok vcp →
      checkAlloc vcp (spillAlloc vcp) = .ok ()

/-- The allocation the backend lowers is accepted by `checkAlloc`, whatever regalloc2 answered:
its own answer only when `checkAlloc` accepts it, else the spill allocation. -/
theorem checkAlloc_allocResult (hsa : SpillAccepted) {f : Clif.Function} {vc vcp : VCode}
    (hd : Dominated f) (hs : LowerScope f) (hl : lowerFunction f = .ok vc)
    (hp : Backend.prepare vc = .ok vcp) (ra : Except String RFunc) :
    checkAlloc vcp (allocResult vcp ra) = .ok () := by
  unfold allocResult
  cases ra with
  | error _ => exact hsa f vc vcp hd hs hl hp
  | ok rf =>
    simp only
    by_cases hc : (checkAlloc vcp rf).isOk = true
    · rw [ite_eq_left_iff.mpr (fun h => absurd hc h)]
      cases h : checkAlloc vcp rf with
      | ok u => rfl
      | error e => rw [h] at hc; cases hc
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hc)]; exact hsa f vc vcp hd hs hl hp

/-- **The backend's end-to-end theorem for the fallback-composed allocation** (V4):
`backend_correct_final_of_lower` with `rf := allocResult vcp ra` for any answer `ra` of the
untrusted allocator, and no premise about `checkAlloc`. The input conditions are
`dominatedB`/`lowerScopeB`, the pipeline's results those of `lowerFunction`, `prepare`,
`lowerRFunc`, `emitFunc` and the layout; `SpillAccepted` is the open V4 hypothesis. -/
theorem backend_correct_final_alloc (hsa : SpillAccepted) {p : Clif.Program}
    {f : Clif.Function} {k : Nat} {vc vcp : VCode} {ra : Except String RFunc} {rf : RFunc}
    {af : AFunc} {fa : FnAsm}
    {fb : FnBin} (hsub : InSubset p f) (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hrf : rf = allocResult vcp ra) (ha : lowerRFunc vcp rf = .ok af)
    (he : emitFunc k af = .ok fa) (hla : fa.layout = .ok fb)
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
    (hslot : af.slotBase = slotOff)
    {base ra' : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra' s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra' (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) :=
  backend_correct_final_of_lower hsub hd hs hl hp
    (hrf ▸ checkAlloc_allocResult hsa (dominated_of hd) (lowerScope_of hs) hl hp ra) ha he hla
    hC hCT hTls hX hXI hsym hslot hent hres hbe hargs hcs hrel htr fuel

/-! ## Non-vacuity

`lowerWitness` (a loop with block parameters, `LowerDirect.lean`) meets the input conditions, and
with no answer from regalloc2 (`ra := .error _`: the oracle is absent) the pipeline runs through
the spill allocation: `allocResult` is `spillAlloc`, `checkAlloc` accepts it (the conclusion of
`SpillAccepted` on this function) and `lowerRFunc` lowers it. -/

theorem lowerWitness_spills :
    (match lowerFunction lowerWitness with
      | .ok vc => match Backend.prepare vc with
        | .ok vcp => (checkAlloc vcp (spillAlloc vcp)).isOk &&
            (lowerRFunc vcp (allocResult vcp (.error "regalloc2 absent"))).isOk
        | .error _ => false
      | .error _ => false) = true := by
  native_decide

/-- **Non-vacuity of `backend_correct_final_alloc`**: on `lowerWitness`, with regalloc2 absent,
the pipeline's premises hold together (the lowering, `prepare`, and `lowerRFunc` of
`allocResult`), and the conclusion of `SpillAccepted` holds for it. -/
theorem backend_correct_final_alloc_witness :
    Dominated lowerWitness ∧ LowerScope lowerWitness ∧
      ∃ vc vcp af, lowerFunction lowerWitness = .ok vc ∧ Backend.prepare vc = .ok vcp ∧
        checkAlloc vcp (spillAlloc vcp) = .ok () ∧
        lowerRFunc vcp (allocResult vcp (.error "regalloc2 absent")) = .ok af := by
  obtain ⟨hd, hs, -, -⟩ := lowerWitness_checks
  have h := lowerWitness_spills
  refine ⟨dominated_of hd, lowerScope_of hs, ?_⟩
  cases hl : lowerFunction lowerWitness with
  | error e => rw [hl] at h; cases h
  | ok vc =>
    rw [hl] at h
    simp only at h
    cases hp : Backend.prepare vc with
    | error e => rw [hp] at h; cases h
    | ok vcp =>
      rw [hp] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      cases hc : checkAlloc vcp (spillAlloc vcp) with
      | error e => rw [hc] at h1; cases h1
      | ok u =>
        cases hr : lowerRFunc vcp (allocResult vcp (.error "regalloc2 absent")) with
        | error e => rw [hr] at h2; cases h2
        | ok af => exact ⟨vc, vcp, af, rfl, hp, hc, hr⟩

end E2E
