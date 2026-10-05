import FV.E2E.FinalDirect
import FV.Backend.Proof.SpillInvariant
import FV.Backend.Proof.SpillStep4
import FV.Backend.Proof.SpillArity
import FV.Backend.Proof.SpillEdges
import FV.Backend.Proof.SpillClasses
import FV.E2E.SpillCtlWitness

/-!
# The final theorem without the register-allocation checker premise (V4)

`backend_correct_final_of_lower` still assumed `checkAlloc vcp rf = .ok ()` for the allocation
`rf` regalloc2 computed. The backend now lowers `allocResult vcp ra` (`FV/Backend/SpillAlloc.lean`;
`lowerAlloc_eq` relates it to the compiler's `lowerAlloc`): regalloc2's answer `ra` if
`checkAlloc` accepts it, else the spill allocation `spillAlloc vcp`. So the checker's verdict on
regalloc2's output is no longer a premise: whatever regalloc2 returns (or if it fails or is
absent), the allocation that is lowered is `AllocChecked`, provided the spill allocation is
(`SpillAccepted`).

`SpillAccepted` is reduced to the availability sets of the pipeline's output
(`spillAccepted_of_avail`: `SpillAvailable`); the step-3 local facts (`spillLocalAll`) and the
step-4 invariant proof (`Spill.spillStep4`) are proven, and `SpillAccepted` itself is proven in
`FV/E2E/SpillKillFree.lean` (`E2E.spillAccepted`; `E2E.backend_correct_final_alloc_proven` is this
file's theorem without the premise). `lean-e2e-check` still decides `checkAlloc`'s acceptance of the
spill allocation on every in-scope function of the corpus and the runtests ("spill fallback" line).

An earlier statement (PR #54) asked for `checkAlloc vcp (spillAlloc vcp) = .ok ()` under
`Dominated`/`LowerScope` only; that is false (`E2E.not_ctlSpillHyp`: two `sret` parameters), and was
replaced by this one, which also takes `InSubset` and `Spill.ArityOk`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Cov

/-! ## V4 restated: verified in-states, the initial vreg file chosen by the theorem

Asking `checkAlloc` (its untrusted fixpoint iteration and `verify`, from an entry state without
vregs) to accept the spill allocation would imply that every use of the VCode is defined on every
path. The downstream proofs need less: `AllocChecked` (verified in-states with an
`EntryOk` entry state; `CompiledA`, `RegLevelCorrectEx`, `backend_correct_final_ex`). For the spill
allocation that is `SpillAccepted`, which follows from the local facts (`SpillLocalAll`, step 3),
the availability sets of the pipeline's output (`SpillAvailable`) and the step-4 invariant proof
(`Spill.SpillStep4`, proven: `Spill.spillStep4`): `spillAccepted_of`, `spillAccepted_of_avail`. -/

/-- **The spill allocation is `AllocChecked`** (V4, restated; an explicit hypothesis, not an axiom):
for every prepared VCode `vcp` the pipeline produces from in-scope input, the spill allocation has
verified in-states with an `EntryOk` entry state. Reduced to the step-3/4 facts by
`spillAccepted_of`. -/
def SpillAccepted : Prop :=
  ∀ (p : Clif.Program) (f : Clif.Function) (vc vcp : VCode), InSubset p f → Spill.ArityOk f → Dominated f →
    LowerScope f → lowerFunction f = .ok vc → Backend.prepare vc = .ok vcp →
      AllocChecked vcp (spillAlloc vcp)

/-- The instruction-local and CFG facts (V4 step 3, `Spill.SpillLocalOk`) of the pipeline's
output. -/
def SpillLocalAll : Prop :=
  ∀ (p : Clif.Program) (f : Clif.Function) (vc vcp : VCode), InSubset p f → Spill.ArityOk f → Dominated f →
    LowerScope f → lowerFunction f = .ok vc → Backend.prepare vc = .ok vcp → Spill.SpillLocalOk vcp

/-- **The local facts of the pipeline's output** (V4 step 3): the straight-line forms by
`formsCovered_complete`, the control forms by `ctlSpillHyp` (`InSubset`'s ABI conditions), the
classes by `classesHyp`, the CFG by `edgesHyp_of` (`ArityOk`), all kept by `prepare`. -/
theorem spillLocalAll : SpillLocalAll := by
  intro p f vc vcp hsub har hd hs hl hp
  refine ⟨fun b vb k i hvb hi => ?_, Spill.classesHyp f vc vcp hd hs hl hp,
    Spill.edgesHyp_of hd hs har hl hp⟩
  cases hct : i.isCtl
  · have hcov := formsCovered_complete hs hl hp default b vb k i hvb hi
    rw [hct] at hcov
    exact Spill.spillInstOk_of_formOk (hcov.resolve_left (by simp))
  · exact Spill.spillCtl_of_prepare hp (prepDomain_of_lower hs hl hs.nonempty)
      (ctlSpillHyp hsub hd hs hl) b vb k i hvb hi hct

/-- **The availability sets of the pipeline's output exist** (V4 step 4, its VCode part; open, an
explicit hypothesis, not an axiom): the in-state facts the spill allocation satisfies
(`Spill.SpillAvail`: every vreg available at the entry, every use available where it is read, every
edge delivering its target's set). -/
def SpillAvailable : Prop :=
  ∀ (p : Clif.Program) (f : Clif.Function) (vc vcp : VCode), InSubset p f → Spill.ArityOk f → Dominated f →
    LowerScope f → lowerFunction f = .ok vc → Backend.prepare vc = .ok vcp →
      ∃ D, Spill.SpillAvail vcp D

/-- **The assembly**: the step-4 invariant proof, the local facts and the availability sets give
`SpillAccepted`. -/
theorem spillAccepted_of (h4 : Spill.SpillStep4) (hloc : SpillLocalAll) (hav : SpillAvailable) :
    SpillAccepted :=
  fun p f vc vcp hsub har hd hs hl hp =>
    let ⟨D, hD⟩ := hav p f vc vcp hsub har hd hs hl hp
    h4 vcp D (Spill.cfg_ok_of_prepare hp (prepDomain_of_lower hs hl hs.nonempty))
      (hloc p f vc vcp hsub har hd hs hl hp) hD

/-- **The assembly with step 3 proven**: the step-4 invariant proof and the availability sets give
`SpillAccepted`. -/
theorem spillAccepted_of_step4 (h4 : Spill.SpillStep4) (hav : SpillAvailable) : SpillAccepted :=
  spillAccepted_of h4 spillLocalAll hav

/-- **The assembly with steps 3 and 4 proven** (`spillLocalAll`, `Spill.spillStep4`): the
availability sets of the pipeline's output give `SpillAccepted`. -/
theorem spillAccepted_of_avail (hav : SpillAvailable) : SpillAccepted :=
  spillAccepted_of_step4 Spill.spillStep4 hav

/-- The allocation the backend lowers is `AllocChecked`, whatever regalloc2 answered. -/
theorem allocChecked_allocResult (hsa : SpillAccepted) {p : Clif.Program} {f : Clif.Function}
    {vc vcp : VCode} (hsub : InSubset p f) (har : Spill.ArityOk f) (hd : Dominated f)
    (hs : LowerScope f) (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (ra : Except String RFunc) : AllocChecked vcp (allocResult vcp ra) := by
  unfold allocResult
  cases ra with
  | error _ => exact hsa p f vc vcp hsub har hd hs hl hp
  | ok rf =>
    simp only
    by_cases hc : (checkAlloc vcp rf).isOk = true
    · rw [ite_eq_left_iff.mpr (fun h => absurd hc h)]
      cases h : checkAlloc vcp rf with
      | ok u => exact allocChecked_of_checkAlloc h
      | error e => rw [h] at hc; cases hc
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hc)]; exact hsa p f vc vcp hsub har hd hs hl hp

/-- **The backend's end-to-end theorem for the fallback-composed allocation, V4 restated**:
`backend_correct_final_of_lower` with `rf := allocResult vcp ra` for any answer `ra` of the
untrusted allocator and no `checkAlloc` premise, under `SpillAccepted` (`spillAccepted_of_avail`
reduces it to `SpillAvailable`), with the input condition `arityOkB` (every
branch passes as many arguments as its target has parameters; `lowerFunction` does not check it,
and the spill allocation's parameter copies need it). -/
theorem backend_correct_final_alloc (hsa : SpillAccepted) {p : Clif.Program}
    {f : Clif.Function} {k : Nat} {vc vcp : VCode} {ra : Except String RFunc} {rf : RFunc}
    {af : AFunc} {fa : FnAsm}
    {fb : FnBin} (hsub : InSubset p f) (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (har : Spill.arityOkB f = true)
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
  backend_correct_final_of_lower_ex hsub hd hs hl hp
    (hrf ▸ allocChecked_allocResult hsa hsub (Spill.arityOk_of har) (dominated_of hd) (lowerScope_of hs) hl hp ra) ha he hla
    hC hCT hTls hX hXI hsym hslot hent hres hbe hargs hcs hrel htr fuel

/-! ## Non-vacuity

`lowerWitness` (a loop with block parameters, `LowerDirect.lean`) meets the input conditions, and
with no answer from regalloc2 (`ra := .error _`: the oracle is absent) the pipeline runs through
the spill allocation: `allocResult` is `spillAlloc`, `checkAlloc` accepts it and `lowerRFunc` lowers it. -/

theorem lowerWitness_spills :
    (match lowerFunction lowerWitness with
      | .ok vc => match Backend.prepare vc with
        | .ok vcp => (checkAlloc vcp (spillAlloc vcp)).isOk &&
            (lowerRFunc vcp (allocResult vcp (.error "regalloc2 absent"))).isOk
        | .error _ => false
      | .error _ => false) = true := by
  native_decide

/-- On `lowerWitness`, with regalloc2 absent, `checkAlloc` accepts the spill allocation and
`lowerRFunc` lowers `allocResult`. -/
theorem lowerWitness_spill_facts :
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

/-- **Non-vacuity of `backend_correct_final_alloc`**: on `lowerWitness`, with regalloc2 absent,
the pipeline's premises hold together, and the conclusion of `SpillAccepted` holds for it. -/
theorem backend_correct_final_alloc_witness :
    Dominated lowerWitness ∧ LowerScope lowerWitness ∧ Spill.arityOkB lowerWitness = true ∧
      ∃ vc vcp af, lowerFunction lowerWitness = .ok vc ∧ Backend.prepare vc = .ok vcp ∧
        AllocChecked vcp (spillAlloc vcp) ∧
        lowerRFunc vcp (allocResult vcp (.error "regalloc2 absent")) = .ok af :=
  let ⟨hd, hs, vc, vcp, af, hl, hp, hc, hr⟩ := lowerWitness_spill_facts
  ⟨hd, hs, by native_decide, vc, vcp, af, hl, hp, allocChecked_of_checkAlloc hc, hr⟩

end E2E
