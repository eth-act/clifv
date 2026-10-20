import FV.Backend.Proof.SpillInstCheck

/-!
# `spillInstOkB` is complete (S11e5 Stage C, slice 8)

`opsOkB_of_opsOk`, `spillInstOkB_of_spillInstOk`: the run-time deciders of
`SpillInstCheck.lean` accept every instruction meeting `SpillInstOk`; `ctlSpillB_of`: `ctlSpillB`
accepts every VCode whose control forms meet it. With the integer chain's `ctlSpillHyp` this
decides `ctlSpillB` on subset-E input (`FV/E2E/LinkScopeIntT.lean`).
-/

namespace Backend.Proof.Spill

open Backend

/-- **Completeness of `opsOkB`.** -/
theorem opsOkB_of_opsOk {ops : Array Operand} {clob : List Reg} (h : OpsOk ops clob) :
    opsOkB ops clob = true := by
  simp only [opsOkB, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨fun o ho => decide_eq_true (h.noStack o ho),
    fun o ho => decide_eq_true (h.useEarly o ho)⟩, fun o ho => ?_⟩, fun o ho o' ho' => ?_⟩,
    fun j hj j' hj' => ?_⟩, fun o ho => ?_⟩, fun o ho => decide_eq_true (h.earlyDef o ho)⟩,
    fun j hj => ?_⟩, decide_eq_true (h.enough .int)⟩, decide_eq_true (h.enough .float)⟩,
    decide_eq_true h.defsNodup⟩
  · split
    · rename_i p hp
      obtain ⟨h1, h2⟩ := h.fixedReg o ho p hp
      simp [h1, h2]
    · rfl
  · split
    · rename_i p p' hp hp'
      exact decide_eq_true fun hk hk' e => h.fixedUse o ho o' ho' p hk hk' hp (e ▸ hp')
    · rfl
  · split
    · rename_i o o' hj1 hj2
      split
      · rename_i p p' hp hp'
        exact decide_eq_true fun hk hk' e => h.fixedDefs j j' o o' p hj1 hj2 hk hk' hp (e ▸ hp')
      · rfl
    · rfl
  · split
    · rename_i p hp
      exact decide_eq_true fun hk => h.fixedDefClob o ho p hk hp
    · rfl
  · split
    · rename_i o hj1
      split
      · rename_i i hr
        obtain ⟨hk, hpos, oi, hoi, hu, hsc, hcl, honly⟩ := h.reuse j o i hj1 hr
        simp only [Bool.and_eq_true, decide_eq_true_eq, hoi, List.all_eq_true, List.mem_range]
        refine ⟨⟨⟨hk, hpos⟩, ⟨⟨hu, hsc⟩, hcl⟩⟩, fun j' _ => ?_⟩
        split
        · rename_i o' hj'
          exact decide_eq_true fun hr' => honly j' o' hj' hr'
        · rfl
      · rfl
    · rfl

/-- **Completeness of `spillInstOkB`.** -/
theorem spillInstOkB_of_spillInstOk {i : MInst} (h : SpillInstOk i) : spillInstOkB i = true := by
  obtain ⟨ops, hops, hok, hrets⟩ := h
  unfold spillInstOkB
  rw [hops]
  simp only [Bool.and_eq_true]
  refine ⟨opsOkB_of_opsOk hok, ?_⟩
  split
  · rename_i us
    refine List.all_eq_true.mpr fun o ho => ?_
    obtain ⟨p, hp, hcs⟩ := hrets us rfl o ho
    rw [hp]
    exact decide_eq_true hcs
  · rfl

/-- **Completeness of `ctlSpillB`**: a VCode whose control forms meet `SpillInstOk` passes it. -/
theorem ctlSpillB_of {vc : VCode}
    (h : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true → SpillInstOk i) :
    ctlSpillB vc = true := by
  unfold ctlSpillB
  refine List.all_eq_true.mpr fun vb hvb => List.all_eq_true.mpr fun i hi => ?_
  cases hc : i.isCtl
  · rfl
  · simpa using spillInstOkB_of_spillInstOk (h vb hvb i hi hc)

end Backend.Proof.Spill
