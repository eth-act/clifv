module

public import FV.E2E.SpillKillFree
public import FV.E2E.SpillCheckAlloc
public import FV.E2E.LSCheckAlloc
public import FV.Backend.Proof.LSSpillPlan

@[expose] public section

/-!
# Completeness of the Lean allocator (V4b-4, #276)

The Lean allocator `leanAlloc` (`FV/Backend/LinearScan.lean`) returns the build of the first plan
that passes the validator `planOk` (the linear scan with 0, 2, 4 registers per class withheld,
else the all-spill plan, which always passes: `LS.leanAlloc_planOk`). Every validated plan builds
an `AllocChecked` allocation (`LS.planOk_allocChecked`), so on every in-scope function:

* `leanAlloc_accepted`: `leanAlloc` succeeds and its allocation is `AllocChecked` (no hypothesis);
* `leanCheckAlloc`: `checkAlloc` itself accepts it, given definite assignment of the pipeline's
  output (`SpillDefinedHyp`, the premise `spillCheckAlloc` needs for the spill allocation, since
  `checkAlloc` starts from an entry state without vregs);
* `backend_correct_final_leanAlloc`: the backend's end-to-end theorem for the Lean allocation
  itself, with no allocation premise;
* `lowerAllocReady_leanAlloc`: when the Lean allocation is accepted by `checkAlloc`, lowers and
  emits (`emitReady`), the backend's Lean path (`allocateLean`: `lowerAllocReady vcp
  (leanAlloc vcp)`) lowers it and not the spill fallback.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **The Lean allocator's allocation is accepted** (`AllocChecked`) on every in-scope function. -/
theorem leanAlloc_accepted {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode}
    (hsub : InSubset p f) (har : Spill.ArityOk f) (hd : Dominated f) (hs : LowerScope f)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp) :
    ∃ rf, leanAlloc vcp = .ok rf ∧ AllocChecked vcp rf := by
  have hloc := spillLocalAll p f vc vcp hsub har hd hs hl hp
  have hcfg := Spill.cfg_ok_of_prepare hp (prepDomain_of_lower hs hl hs.nonempty)
  obtain ⟨pl, rf, hok, hb, hla⟩ := LS.leanAlloc_planOk hcfg hloc
  obtain ⟨D, hav⟩ := spillAvailable_of_killFree spillKillFree p f vc vcp hsub har hd hs hl hp
  obtain ⟨rf', hb', hac⟩ := LS.planOk_allocChecked hok hloc hav
  rw [hb] at hb'
  cases hb'
  exact ⟨rf, hla, hac⟩

/-- **`checkAlloc` accepts the Lean allocator's allocation** of every in-scope function whose
prepared VCode has availability sets holding nothing on entry. -/
theorem leanCheckAlloc_sets {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode}
    (hsub : InSubset p f) (har : Spill.ArityOk f) (hd : Dominated f) (hs : LowerScope f)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hDs : ∃ D, Spill.SpillAvail vcp D ∧ ∀ v, D 0 v = false) :
    ∃ rf, leanAlloc vcp = .ok rf ∧ checkAlloc vcp rf = .ok () := by
  obtain ⟨D, hav, hD0⟩ := hDs
  have hloc := spillLocalAll p f vc vcp hsub har hd hs hl hp
  have hdom := prepDomain_of_lower hs hl hs.nonempty
  obtain ⟨pl, rf, hok, hb, hla⟩ := LS.leanAlloc_planOk (Spill.cfg_ok_of_prepare hp hdom) hloc
  obtain ⟨rf', hb', hc⟩ := planOk_checkAlloc hok hloc hav hD0
    (fun _ _ hcfg => prepare_reach hp hdom hcfg)
  rw [hb] at hb'
  cases hb'
  exact ⟨rf, hla, hc⟩

/-- **`checkAlloc` accepts the Lean allocator's allocation** of every in-scope function, given
definite assignment of the pipeline's output (`SpillDefinedHyp`). -/
theorem leanCheckAlloc (hD : SpillDefinedHyp) {p : Clif.Program} {f : Clif.Function}
    {vc vcp : VCode} (hsub : InSubset p f) (har : Spill.ArityOk f) (hd : Dominated f)
    (hs : LowerScope f) (hen : Spill.entryParamsB f = true) (hl : lowerFunction f = .ok vc)
    (hp : Backend.prepare vc = .ok vcp) :
    ∃ rf, leanAlloc vcp = .ok rf ∧ checkAlloc vcp rf = .ok () :=
  leanCheckAlloc_sets hsub har hd hs hl hp (hD p f vc vcp hsub har hd hs hen hl hp)

/-- The backend's Lean path lowers the Lean allocation itself when `checkAlloc` accepts it and it
lowers and emits. -/
theorem lowerAllocReady_leanAlloc {vcp : VCode} {rf : RFunc} {af : AFunc}
    (hla : leanAlloc vcp = .ok rf) (hc : checkAlloc vcp rf = .ok ())
    (ha : lowerRFunc vcp rf = .ok af) (hr : emitReady af = true) :
    allocResult vcp (leanAlloc vcp) = rf ∧ lowerAllocReady vcp (leanAlloc vcp) = .ok af := by
  have hok : (checkAlloc vcp rf).isOk = true := by rw [hc]; rfl
  refine ⟨?_, ?_⟩
  · simp only [allocResult, hla, hok, ↓reduceIte, ha]
  · simp only [lowerAllocReady, lowerAlloc, hla, hok, ↓reduceIte, ha, hr]

/-- **The backend's end-to-end theorem for the Lean allocation** (V4b): the allocation the Lean
allocator computes for an in-scope function is lowered correctly; no allocation premise. -/
theorem backend_correct_final_leanAlloc {p : Clif.Program}
    {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm}
    {fb : FnBin} (hsub : InSubset p f) (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (har : Spill.arityOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hrf : leanAlloc vcp = .ok rf) (ha : lowerRFunc vcp rf = .ok af)
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
    ArmRefines fb base ra' (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) := by
  obtain ⟨rf', hrf', hac⟩ := leanAlloc_accepted hsub (Spill.arityOk_of har) (dominated_of hd)
    (lowerScope_of hs) hl hp
  rw [hrf] at hrf'
  cases hrf'
  exact backend_correct_final_of_lower_ex hsub hd hs hl hp hac ha he hla hC hCT hTls hX hXI hsym
    hslot hent hres hbe hargs hcs hrel htr fuel

/-! ## Non-vacuity -/

/-- On `lowerWitness` (a loop with block parameters) the Lean allocator succeeds, `checkAlloc`
accepts its allocation, which lowers, emits (`emitReady`) and differs from the spill allocation;
the backend's Lean path lowers it. -/
theorem lowerWitness_lean :
    (match lowerFunction lowerWitness with
      | .ok vc => match Backend.prepare vc with
        | .ok vcp => match leanAlloc vcp with
          | .ok rf => (checkAlloc vcp rf).isOk && rf.blocks != (spillAlloc vcp).blocks &&
              match lowerRFunc vcp rf with
              | .ok af => emitReady af
              | .error _ => false
          | .error _ => false
        | .error _ => false
      | .error _ => false) = true := by
  native_decide

/-- **Non-vacuity of `leanAlloc_accepted`, `leanCheckAlloc` and
`backend_correct_final_leanAlloc`**: on `lowerWitness` the input conditions (other than
`InSubset`, as in `backend_correct_final_alloc_witness`) hold, the Lean allocator's allocation is
accepted by `checkAlloc` (so `AllocChecked`), is not the spill allocation, lowers and emits, and
the backend's Lean path lowers it. -/
theorem leanAlloc_witness :
    Dominated lowerWitness ∧ LowerScope lowerWitness ∧ Spill.arityOkB lowerWitness = true ∧
      ∃ vc vcp rf af, lowerFunction lowerWitness = .ok vc ∧ Backend.prepare vc = .ok vcp ∧
        leanAlloc vcp = .ok rf ∧ checkAlloc vcp rf = .ok () ∧ AllocChecked vcp rf ∧
        rf.blocks ≠ (spillAlloc vcp).blocks ∧ lowerRFunc vcp rf = .ok af ∧
        lowerAllocReady vcp (leanAlloc vcp) = .ok af := by
  obtain ⟨hd, hs, -, -⟩ := lowerWitness_checks
  have h := lowerWitness_lean
  refine ⟨dominated_of hd, lowerScope_of hs, by native_decide, ?_⟩
  cases hl : lowerFunction lowerWitness with
  | error e => rw [hl] at h; cases h
  | ok vc =>
    rw [hl] at h
    simp only at h
    cases hp : Backend.prepare vc with
    | error e => rw [hp] at h; cases h
    | ok vcp =>
      rw [hp] at h
      simp only at h
      cases hla : leanAlloc vcp with
      | error e => rw [hla] at h; cases h
      | ok rf =>
        rw [hla] at h
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        cases hc : checkAlloc vcp rf with
        | error e => rw [hc] at h1; cases h1
        | ok u =>
          cases hr : lowerRFunc vcp rf with
          | error e => rw [hr] at h3; cases h3
          | ok af =>
            rw [hr] at h3
            exact ⟨vc, vcp, rf, af, rfl, hp, hla, hc, allocChecked_of_checkAlloc hc, h2, hr,
              (lowerAllocReady_leanAlloc hla hc hr h3).2⟩

end E2E
