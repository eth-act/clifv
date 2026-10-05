import FV.Backend.Proof.SpillLocalForms
import FV.Backend.Proof.FormsCoverComplete
import FV.Backend.Proof.PrepareSound

/-!
# The spill allocator's local facts on the pipeline's output (V4 (a), step 3)

`spillLocalOk_of_pipeline`: for `Dominated`/`LowerScope` input, `prepare (lowerFunction f)`
meets `SpillLocalOk`, given `SpillLocalHyp`, the part not proven yet:

* `CtlSpillHyp`: the control forms (`MInst.isCtl`: calls, `Args`/`Rets`, branches, the LL/SC
  loops, `ElfTlsGetAddr`) the lowering emits meet `SpillInstOk` (the call ABI register lists of
  `gen_call_args`/`gen_call_rets`, `Rets`'s x0..x7, `Args`'s x0..x8, fresh distinct defs);
* `ClassesHyp`: every vreg of the prepared code has the class `classes` records;
* `EdgesHyp`: the CFG facts `EdgesOk` of the prepared code.

Proven here: every straight-line instruction (`FormOk`, by `formsCovered_complete`) meets
`SpillInstOk` (`spillInstOk_of_formOk`), and `prepare` keeps `SpillInstOk` (retargeting changes
neither the operands nor the clobbers; its edge blocks' `jump`s have no operands).
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof Backend.Proof.Driver

theorem clobbers_setTargets {i i' : MInst} {ls : List Label} (h : i.setTargets ls = some i') :
    i'.clobbers = i.clobbers := by
  unfold MInst.setTargets at h
  split at h
  all_goals (try split at h)
  all_goals (cases h; try rfl)

/-- Retargeting keeps `SpillInstOk`. -/
theorem spillInstOk_setTargets {i i' : MInst} {ls : List Label} (h : i.setTargets ls = some i')
    (hi : SpillInstOk i) : SpillInstOk i' := by
  obtain ⟨ops, hops, hok, -⟩ := hi
  obtain ⟨h1, -, -, h4⟩ := Driver.setTargets_facts h
  exact ⟨ops, h1.trans hops, clobbers_setTargets h ▸ hok, fun us e => absurd e (h4 us)⟩

theorem spillInstOk_jump (l : Label) : SpillInstOk (.jump l) :=
  ⟨#[], rfl, opsOk_simple (by simp) (by simp) (by simp) (by simp), fun _ h => by cases h⟩

theorem setTargets_src_isCtl {i i' : MInst} {ls : List Label} (h : i.setTargets ls = some i') :
    i.isCtl = true := by
  unfold MInst.setTargets at h
  split at h
  all_goals first | rfl | (cases h; done) | skip

/-- The control forms of `prepare`'s output meet `SpillInstOk` if those of its input do. -/
theorem spillCtl_of_prepare {vc vcp : VCode} (h : prepare vc = .ok vcp) (hd : Prep.PrepDomain vc)
    (hc : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true → SpillInstOk i) :
    ∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst), vcp.blocks[b]? = some vb → vb.insts[k]? = some i →
      i.isCtl = true → SpillInstOk i := by
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, hc0, hc1, hS, hc2, rfl⟩ := Prep.prepare_facts h
  have cs0 := Prep.cfg_spec hc0
  have cs2 : Prep.CfgSpec (B ++ E) ss2 := Prep.cfg_spec hc2
  intro b vb k i hvb hi hct
  rcases Prep.insts3 hd cs0 cs2 hS (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hvb))
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi)) with
    ⟨vb0, hvb0, hi0⟩ | ⟨vb0, hvb0, i0, hi0, ls, hset⟩ | ⟨l, rfl⟩
  · exact hc vb0 hvb0 i hi0 hct
  · exact spillInstOk_setTargets hset (hc vb0 hvb0 i0 hi0 (setTargets_src_isCtl hset))
  · exact spillInstOk_jump l

/-- The control forms of the lowering's output meet `SpillInstOk` (open). -/
def CtlSpillHyp : Prop :=
  ∀ (f : Clif.Function) (vc : VCode), Dominated f → LowerScope f → lowerFunction f = .ok vc →
    ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true → SpillInstOk i

/-- The prepared code's vreg classes are consistent (open). -/
def ClassesHyp : Prop :=
  ∀ (f : Clif.Function) (vc vcp : VCode), Dominated f → LowerScope f → lowerFunction f = .ok vc →
    prepare vc = .ok vcp → ClassesOk vcp

/-- The prepared code's CFG facts (open). -/
def EdgesHyp : Prop :=
  ∀ (f : Clif.Function) (vc vcp : VCode), Dominated f → LowerScope f → lowerFunction f = .ok vc →
    prepare vc = .ok vcp → ∀ succs preds, vcp.cfg = .ok (succs, preds) → EdgesOk vcp succs preds

/-- **What remains of the local facts** (program-independent). -/
def SpillLocalHyp : Prop := CtlSpillHyp ∧ ClassesHyp ∧ EdgesHyp

/-- **The local facts on the pipeline's output.** -/
theorem spillLocalOk_of_pipeline (hyp : SpillLocalHyp) {f : Clif.Function} {vc vcp : VCode}
    (hd : Dominated f) (hs : LowerScope f) (hl : lowerFunction f = .ok vc)
    (hp : prepare vc = .ok vcp) : SpillLocalOk vcp := by
  refine ⟨fun b vb k i hvb hi => ?_, hyp.2.1 f vc vcp hd hs hl hp, hyp.2.2 f vc vcp hd hs hl hp⟩
  cases hct : i.isCtl
  · have hcov := formsCovered_complete hs hl hp default b vb k i hvb hi
    rw [hct] at hcov
    exact spillInstOk_of_formOk (hcov.resolve_left (by simp))
  · exact spillCtl_of_prepare hp (prepDomain_of_lower hs hl hs.nonempty) (hyp.1 f vc hd hs hl)
      b vb k i hvb hi hct

end Backend.Proof.Spill
