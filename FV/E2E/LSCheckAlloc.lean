module

public import FV.E2E.SpillCheckAllocFix
public import FV.Backend.Proof.LSMain

@[expose] public section

/-!
# `checkAlloc` accepts the Lean allocator's validated plans (V4b-3, #275)

`planOk_checkAlloc`: the allocation a validated plan builds (`planOk_allocChecked`) is accepted by
the allocation checker itself, when the availability sets hold nothing on entry to the function
(`checkAlloc`'s iteration starts from `entryState`, where no location holds a vreg) and every
block is reachable. The proof is the completeness of `checkAlloc`
(`CheckComplete.checkAlloc_complete`) applied to the in-states `LS.inState`, as for the spill
allocation (`spillCheckAlloc_sets`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.LS

/-- **`checkAlloc` accepts the allocation of a validated plan** (availability sets holding
nothing on entry, every block reachable). -/
theorem planOk_checkAlloc {vc : VCode} {pl : LinearScan.Plan} {D : Nat → Nat → Bool}
    (h : planOk vc pl = true) (hloc : Spill.SpillLocalOk vc) (hav : Spill.SpillAvail vc D)
    (hD0 : ∀ v, D 0 v = false)
    (hreach : ∀ succs preds, vc.cfg = .ok (succs, preds) → ∀ b < vc.blocks.size,
      Prep.Reach succs b) :
    ∃ rf, buildPlan vc pl = .ok rf ∧ checkAlloc vc rf = .ok () := by
  obtain ⟨fn, rf, hmk, hs, hb, hbp⟩ := planOk_spec h
  have H : Hyps vc (LinearScan.Ctx.ofPlan fn pl) rf D := hyps_of_planOk hmk hs hb hloc hav
  have hcfg := H.fn.cfg
  have hE := hloc.2.2 _ _ hcfg
  have hpos : 0 < vc.blocks.size := Nat.pos_of_ne_zero hE.entry.1
  refine ⟨rf, hbp, CheckComplete.checkAlloc_complete
    (W := insOf vc (LinearScan.Ctx.ofPlan fn pl) rf D) hcfg H.build.size hE.entry.2.1
    hE.entry.2.2 H.build.saved ?_ (hreach _ _ hcfg) ⟨rfl, hE.entry.1, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- every instruction has an operand view
    intro vb hvb i hi
    obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hvb
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
    rw [Array.getElem?_toList] at hb hk
    obtain ⟨ops, hops, -⟩ := hloc.1 b vb k i hb hk
    exact ⟨ops, hops⟩
  · -- successors are blocks
    intro b s hs'
    obtain ⟨hb, _, _, _, -, -, hlab⟩ := Prep.succ_of (Prep.cfg_spec hcfg) hs'
    exact ⟨hb, (Prep.lab_some hlab).1⟩
  · -- operand vregs have a class
    intro b vb hvb i hi ops hops o ho
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
    rw [Array.getElem?_toList] at hk
    exact (Array.getElem?_eq_some_iff.mp (hloc.2.1.1 b vb k i ops hvb hk hops o ho)).1
  · -- parameters have a class
    intro s sb hsb r hr n hn
    obtain ⟨m, cl, rfl, hm⟩ := hloc.2.1.2 s sb hsb r (List.mem_append_left _ hr)
    have : m = n := Except.ok.inj hn
    subst this
    exact (Array.getElem?_eq_some_iff.mp hm).1
  · -- the witness in-states
    intro b hb
    exact ⟨_, insOf_get hb, size_inState b⟩
  · intro b hb
    exact verify_block H hb
  · exact ⟨_, insOf_get hpos, inState_le_entry H hD0⟩

/-- Nothing available anywhere is an availability set of `step4Ex` (it reads no vreg). -/
theorem step4Ex_avail0 : Spill.SpillAvail Spill.step4Ex fun _ _ => false := by
  refine ⟨fun succs preds h b vb k i ops hb hi hops o ho _ => ?_,
    fun _ _ _ _ _ _ _ _ _ _ _ _ v hv => by cases hv⟩
  match b, hb with
  | 0, hb =>
    cases hb
    match k, hi with
    | 0, hi => cases hi; cases hops; simp at ho
  | 1, hb =>
    cases hb
    match k, hi with
    | 0, hi => cases hi; cases hops; simp at ho

/-- **Non-vacuity of `planOk_checkAlloc`**: its premises hold together on a VCode with a block
argument and the linear scan's plan. -/
theorem planOk_checkAlloc_witness : ∃ vc pl D, planOk vc pl = true ∧ Spill.SpillLocalOk vc ∧
    Spill.SpillAvail vc D ∧ (∀ v, D 0 v = false) ∧
    (∀ succs preds, vc.cfg = .ok (succs, preds) → ∀ b < vc.blocks.size, Prep.Reach succs b) ∧
    (∃ vb ∈ vc.blocks.toList, vb.branchArgs ≠ #[]) ∧
    ∃ rf, buildPlan vc pl = .ok rf ∧ checkAlloc vc rf = .ok () := by
  have hreach : ∀ succs preds, Spill.step4Ex.cfg = .ok (succs, preds) →
      ∀ b < Spill.step4Ex.blocks.size, Prep.Reach succs b := by
    intro succs preds h b hb
    rw [Spill.step4Ex_cfg] at h
    cases h
    match b, hb with
    | 0, _ => exact .entry
    | 1, _ => exact .step (b := 0) .entry (by decide)
  exact ⟨Spill.step4Ex, lsExPlan, _, lsExPlan_ok, Spill.step4Ex_local, step4Ex_avail0,
    fun _ => rfl, hreach, ⟨_, List.mem_cons_self, by decide⟩,
    planOk_checkAlloc lsExPlan_ok Spill.step4Ex_local step4Ex_avail0 (fun _ => rfl) hreach⟩

end E2E
