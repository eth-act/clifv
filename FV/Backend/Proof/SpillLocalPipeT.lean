import FV.Backend.Proof.SpillClassesT
import FV.Backend.Proof.SpillAvail
import FV.Backend.Proof.SpillInvariant
import FV.Backend.Proof.SpillStep4
import FV.Backend.Proof.SpillInstCheck

/-!
# The spill allocator's local facts and acceptance on the typed pipeline's output
(S11e5 Stage C, slice 6)

`spillLocalOk_of_pipelineT`: `spillLocalOk_of_pipeline` over the typed scope `LowerScopeT`, with
the per-function facts not proven for float functions yet as explicit premises:

* `hctl`: the control forms of `lowerFunction`'s VCode meet `SpillInstOk` (slice 5,
  `ctlSpill_typed`; decided by `ctlSpillB`);
* `hform`: the prepared code's straight-line forms are covered (`FormsCovered default`, decided by
  `formsCoveredB`; the conclusion of `formsCovered_complete` over `LowerScope`, whose typed version
  needs a typed coverage analysis);
* `ResClassOk f`: the lowering returns results in vregs of their types' classes (`classesHypT`;
  decided by `resClassOkB`).

The CFG facts are proven (`edgesHyp_ofT`, with the input check `Compile.tryArgClassOk`).

`spillAcceptedT`: then the spill allocation is `AllocChecked` when the prepared code passes the
syntactic availability check `killFreeB` (`spillAvail_of_killFree`), by the proven step-4
invariant (`spillStep4`); `allocChecked_allocResultT`: so is the allocation the backend lowers,
whatever regalloc2 answered. The integer theorems are the instances with `LowerScope`
(`spillLocalOk_of_pipelineT_int`).
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof Backend.Proof.Driver

/-- **The local facts on the typed pipeline's output** (`spillLocalOk_of_pipeline` over
`LowerScopeT`; control forms `hctl`, covered forms `hform` and result classes `hrc` explicit). -/
theorem spillLocalOk_of_pipelineT {f : Clif.Function} {vc vcp : VCode}
    (hd : Dominated f) (hs : LowerScopeT f) (ha : ArityOk f)
    (htc : Compile.tryArgClassOk f = true) (hrc : ResClassOk f)
    (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp)
    (hctl : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true → SpillInstOk i)
    (hform : FormsCovered default vcp) : SpillLocalOk vcp := by
  refine ⟨fun b vb k i hvb hi => ?_, classesHypT f vc vcp hd hs hrc hl hp,
    edgesHyp_ofT hd hs ha htc hl hp⟩
  cases hct : i.isCtl
  · have hcov := hform b vb k i hvb hi
    rw [hct] at hcov
    exact spillInstOk_of_covered (hcov.resolve_left (by simp))
  · exact spillCtl_of_prepare hp (prepDomain_ofT hd hs hl) hctl b vb k i hvb hi hct

/-- **Integer specialization**: on `LowerScope` input the typed premises are theorems
(`formsCovered_complete`, `resClassOk_of_lowerScope`, `Compile.tryArgClassOk_of_functionE`). -/
theorem spillLocalOk_of_pipelineT_int {f : Clif.Function} {vc vcp : VCode}
    (hd : Dominated f) (hs : LowerScope f) (ha : ArityOk f)
    (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp)
    (hctl : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true → SpillInstOk i) :
    SpillLocalOk vcp :=
  spillLocalOk_of_pipelineT hd hs.toT ha (Compile.tryArgClassOk_of_functionE hs.subsetE)
    (resClassOk_of_lowerScope hs) hl hp hctl (formsCovered_complete hs hl hp default)

/-- **The spill allocation of the typed pipeline's output is `AllocChecked`** given the local
facts' premises and the syntactic availability check `killFreeB`. -/
theorem spillAcceptedT {f : Clif.Function} {vc vcp : VCode}
    (hd : Dominated f) (hs : LowerScopeT f) (ha : ArityOk f)
    (htc : Compile.tryArgClassOk f = true) (hrc : ResClassOk f)
    (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp)
    (hctl : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true → SpillInstOk i)
    (hform : FormsCovered default vcp) (hk : killFreeB vcp = true) :
    AllocChecked vcp (spillAlloc vcp) :=
  spillStep4 vcp (killD vcp) (cfg_ok_of_prepare hp (prepDomain_ofT hd hs hl))
    (spillLocalOk_of_pipelineT hd hs ha htc hrc hl hp hctl hform)
    (spillAvail_of_killFree hk (edgesHyp_ofT hd hs ha htc hl hp))

/-- **The allocation the backend lowers is `AllocChecked`** on the typed pipeline's output,
whatever regalloc2 answered (`E2E.allocChecked_allocResult`, typed). -/
theorem allocChecked_allocResultT {f : Clif.Function} {vc vcp : VCode}
    (hd : Dominated f) (hs : LowerScopeT f) (ha : ArityOk f)
    (htc : Compile.tryArgClassOk f = true) (hrc : ResClassOk f)
    (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp)
    (hctl : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true → SpillInstOk i)
    (hform : FormsCovered default vcp) (hk : killFreeB vcp = true)
    (ra : Except String RFunc) : AllocChecked vcp (allocResult vcp ra) := by
  have hsa := spillAcceptedT hd hs ha htc hrc hl hp hctl hform hk
  unfold allocResult
  cases ra with
  | error _ => exact hsa
  | ok rf =>
    simp only
    by_cases hc : (checkAlloc vcp rf).isOk = true
    · simp only [hc, ite_true]
      cases hlr : lowerRFunc vcp rf with
      | ok af =>
        cases h : checkAlloc vcp rf with
        | ok u => exact allocChecked_of_checkAlloc h
        | error e => rw [h] at hc; cases hc
      | error e => exact hsa
    · simp only [hc]; exact hsa

end Backend.Proof.Spill
