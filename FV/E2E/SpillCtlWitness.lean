import FV.E2E.SpillLocalWitness
import FV.Backend.Proof.SpillCtlPipe
import FV.Backend.Proof.IselShpDriver

/-!
# The control part of the spill allocator's local facts: assembly, witness, counterexample

`ctlSpillHyp`: the control part `CtlSpillHyp` on the end-to-end subset `InSubset` (whose
`abiSigs`/`indSigs` fields are `AbiSigsOk`, `abiSigsOk_of_inSubset`), by `ctlSpillHyp_of` and the
ISLE inversion `iselCtlHyp` (`IselShpDriver`). `spillLocalOk_of_ctl`: `spillLocalOk_of_pipeline`
with its control part discharged.
`not_ctlSpillHyp`: without the ABI condition the statement is false: two `sret` parameters are
both fixed to x8 (`sretWitness`), so the entry block's `Args` has two fixed defs in one register.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill

theorem abiSigsOk_of_inSubset {p : Clif.Program} {f : Clif.Function} (h : InSubset p f) :
    AbiSigsOk f :=
  ⟨h.abiSigs, h.indSigs⟩

/-- **`CtlSpillHyp` on the end-to-end subset**: the control forms the lowering emits meet
`SpillInstOk`. -/
theorem ctlSpillHyp {p : Clif.Program} {f : Clif.Function} {vc : VCode} (hsub : InSubset p f)
    (hd : Dominated f) (hs : LowerScope f) (hl : lowerFunction f = .ok vc) :
    ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true → SpillInstOk i :=
  ctlSpillHyp_of iselCtlHyp hd hs (abiSigsOk_of_inSubset hsub) hl

/-- **The local facts on the pipeline's output**, the control part by `ctlSpillHyp`. -/
theorem spillLocalOk_of_ctl (hC : ClassesHyp) (hE : EdgesHyp)
    {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode} (hsub : InSubset p f)
    (hd : Dominated f) (hs : LowerScope f) (hl : lowerFunction f = .ok vc)
    (hp : Backend.prepare vc = .ok vcp) : SpillLocalOk vcp := by
  refine ⟨fun b vb k i hvb hi => ?_, hC f vc vcp hd hs hl hp, hE f vc vcp hd hs hl hp⟩
  cases hct : i.isCtl
  · have hcov := formsCovered_complete hs hl hp default b vb k i hvb hi
    rw [hct] at hcov
    exact spillInstOk_of_formOk (hcov.resolve_left (by simp))
  · exact spillCtl_of_prepare hp (prepDomain_of_lower hs hl hs.nonempty)
      (ctlSpillHyp hsub hd hs hl) b vb k i hvb hi hct

/-! ## Non-vacuity -/

theorem lowerWitness_abi :
    (sigAbiOk lowerWitness.sig && lowerWitness.externs.all (fun e => sigAbiOk e.2.sig) &&
      (indSigs lowerWitness).all fun s => decide (s.params.length ≤ 8) && sigAbiOk s) = true := by
  native_decide

theorem abiSigsOk_lowerWitness : AbiSigsOk lowerWitness := by
  have h := lowerWitness_abi
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨⟨h.1.1, h.1.2⟩, h.2⟩

/-- **Non-vacuity of `ctlSpillHyp_of iselCtlHyp`**: its input premises hold for `lowerWitness`. -/
theorem ctlSpillHyp_of_witness :
    Dominated lowerWitness ∧ LowerScope lowerWitness ∧ AbiSigsOk lowerWitness ∧
      ∃ vc, lowerFunction lowerWitness = .ok vc ∧
        ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true → SpillInstOk i := by
  obtain ⟨hd, hs, vc, -, hl, -, -⟩ := formsCovered_complete_witness default
  exact ⟨hd, hs, abiSigsOk_lowerWitness, vc, hl, ctlSpillHyp_of iselCtlHyp hd hs abiSigsOk_lowerWitness hl⟩

/-- **Non-vacuity of `CallOk`/`spillInstOk_callReg`**: an indirect call with two arguments and
one result meets `SpillInstOk`. -/
theorem spillInstOk_call_witness :
    SpillInstOk (.call ⟨.reg (.vreg 5 .int), retPairs [(1, .x 0), (2, .x 1)], callDefs [(.x 0, 7)]⟩) :=
  spillInstOk_callReg (N := 7) 5
    ⟨fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact ⟨0, by omega, rfl⟩
        · exact ⟨1, by omega, rfl⟩,
      by decide,
      fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        subst hq; exact ⟨0, by omega, rfl⟩,
      by decide, by decide, by decide⟩

/-! ## Without the ABI condition: a counterexample -/

def sretWitnessSrc : String := "function %f(i64 sret, i64 sret) system_v {
block0(v0: i64, v1: i64):
    return
}"

def sretWitness : Clif.Function :=
  match (Clif.parseFile sretWitnessSrc).funcs[0]? with
  | some p => match p.func with
    | .ok f => f
    | .error _ => default
  | none => default

theorem sretWitness_checks :
    dominatedB sretWitness = true ∧ lowerScopeB sretWitness = true ∧
      ((lowerFunction sretWitness).toOption.bind fun vc => vc.blocks[0]?.bind (·.insts[0]?)) =
        some (.args [(.vreg 0 .int, .x 8), (.vreg 1 .int, .x 8)]) := by
  native_decide

theorem not_spillInstOk_args_x8 :
    ¬ SpillInstOk (.args [(.vreg 0 .int, .x 8), (.vreg 1 .int, .x 8)]) := by
  rintro ⟨ops, hops, hok, -⟩
  have e : (MInst.args [(.vreg 0 .int, .x 8), (.vreg 1 .int, .x 8)]).operands =
      .ok #[⟨0, .int, .def, .late, .fixed (.x 8)⟩, ⟨1, .int, .def, .late, .fixed (.x 8)⟩] := rfl
  rw [e] at hops
  cases hops
  exact absurd (hok.fixedDefs 0 1 _ _ (.x 8) rfl rfl rfl rfl rfl rfl) (by decide)

/-- **`CtlSpillHyp` is false**: `sretWitness` (two `sret` parameters, `Dominated`, `LowerScope`)
lowers to an `Args` with two fixed defs in x8. Hence the ABI condition `AbiSigsOk` of
`ctlSpillHyp_of` (part of `InSubset`). -/
theorem not_ctlSpillHyp : ¬ CtlSpillHyp := by
  intro h
  obtain ⟨hd, hs, hl⟩ := sretWitness_checks
  cases hlf : lowerFunction sretWitness with
  | error e => rw [hlf] at hl; simp [Except.toOption] at hl
  | ok vc =>
    rw [hlf] at hl
    simp only [Except.toOption, Option.bind_some] at hl
    cases hb : vc.blocks[0]? with
    | none => rw [hb] at hl; cases hl
    | some vb =>
      rw [hb] at hl
      simp only [Option.bind_some] at hl
      exact not_spillInstOk_args_x8 (h sretWitness vc (dominated_of hd) (lowerScope_of hs) hlf vb
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hb)) _
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hl)) rfl)

end E2E
