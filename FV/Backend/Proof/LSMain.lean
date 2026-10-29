import FV.Backend.Proof.LSRunMain
import FV.Backend.Proof.SpillStep4

/-!
# The Lean allocator's validated plans are accepted (V4b-3, #275)

**`planOk_allocChecked`**: a plan of a VCode that passes the validator (`planOk`: `Ctx.structOk`
and the builder succeeds) builds (`buildPlan`) an allocation that is `AllocChecked`, given the
in-scope local facts (`SpillLocalOk`) and availability sets (`SpillAvail`) — the premises of the
spill allocator's `spillStep4`. The proof: `planOk` gives the function view (`fnOk_of_make`), the
plan's facts (`planFacts_of_structOk`), the builder's output (`buildFacts`) and its instruction
step (`inst_facts`), which are the hypotheses `Hyps` of the runs (`LSRun*.lean`), and
`allocChecked` concludes.

`planOk_allocChecked_witness`: the premises hold together on a VCode with a block argument and a
plan of the linear scan.
-/

namespace Backend.Proof.LS

open Backend Backend.LinearScan Backend.Proof Backend.Proof.Spill

/-- What `planOk` gives: the function view, and the plan's context passes `structOk` and builds
the function `buildPlan` returns. -/
theorem planOk_spec {vc : VCode} {pl : LinearScan.Plan} (h : planOk vc pl = true) :
    ∃ fn rf, Fn.make vc = .ok fn ∧ (LinearScan.Ctx.ofPlan fn pl).structOk = true ∧
      (LinearScan.Ctx.ofPlan fn pl).build = .ok rf ∧ buildPlan vc pl = .ok rf := by
  unfold planOk at h
  split at h
  · rename_i fn hmk
    unfold LinearScan.Ctx.checked at h
    split at h
    · rename_i hs
      cases hb : (LinearScan.Ctx.ofPlan fn pl).build with
      | error e => rw [hb] at h; cases h
      | ok rf =>
        refine ⟨fn, rf, hmk, hs, hb, ?_⟩
        simp only [buildPlan, hmk, bind, Except.bind]
        exact hb
    · cases h
  · cases h

/-- The hypotheses of the runs hold for the allocation of a plan that passes the validator. -/
theorem hyps_of_planOk {vc : VCode} {fn : Fn} {pl : LinearScan.Plan} {rf : RFunc} {D : Nat → Nat → Bool}
    (hmk : Fn.make vc = .ok fn) (hs : (LinearScan.Ctx.ofPlan fn pl).structOk = true)
    (hb : (LinearScan.Ctx.ofPlan fn pl).build = .ok rf) (hloc : SpillLocalOk vc)
    (hav : SpillAvail vc D) : Hyps vc (LinearScan.Ctx.ofPlan fn pl) rf D := by
  have hf := fnOk_of_make hmk
  have hpf := planFacts_of_structOk hf hs
  exact ⟨hf, hpf, rfl, buildFacts hf hb, hloc, hav,
    fun _ _ _ _ hi hos hok hcls h => inst_facts hf hpf hi hos hok hcls h⟩

/-- **A validated plan builds an `AllocChecked` allocation** (V4b-3, #275). -/
theorem planOk_allocChecked {vc : VCode} {pl : LinearScan.Plan} {D : Nat → Nat → Bool}
    (h : planOk vc pl = true) (hloc : SpillLocalOk vc) (hav : SpillAvail vc D) :
    ∃ rf, buildPlan vc pl = .ok rf ∧ AllocChecked vc rf := by
  obtain ⟨fn, rf, hmk, hs, hb, hbp⟩ := planOk_spec h
  exact ⟨rf, hbp, allocChecked (hyps_of_planOk hmk hs hb hloc hav)⟩

/-! ## Non-vacuity -/

/-- The linear scan's plan of `step4Ex` (a `jump` passing `v5` to a block with parameter `v7`). -/
def lsExPlan : LinearScan.Plan :=
  match Fn.make step4Ex with
  | .ok fn => fn.plan (reserved 0)
  | .error _ => default

theorem lsExPlan_ok : planOk step4Ex lsExPlan = true := by native_decide

/-- **Non-vacuity of `planOk_allocChecked`**: its premises hold together on a VCode with a block
argument and the linear scan's plan. -/
theorem planOk_allocChecked_witness : ∃ vc pl D, planOk vc pl = true ∧ SpillLocalOk vc ∧
    SpillAvail vc D ∧ (∃ vb ∈ vc.blocks.toList, vb.branchArgs ≠ #[]) ∧
    ∃ rf, buildPlan vc pl = .ok rf ∧ AllocChecked vc rf :=
  ⟨step4Ex, lsExPlan, _, lsExPlan_ok, step4Ex_local, step4Ex_avail,
    ⟨_, List.mem_cons_self, by decide⟩,
    planOk_allocChecked lsExPlan_ok step4Ex_local step4Ex_avail⟩

end Backend.Proof.LS
