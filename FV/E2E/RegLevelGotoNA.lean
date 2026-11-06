import FV.E2E.RegLevelQW
import FV.E2E.RegLevelFRFree
import FV.E2E.RegLevelGotoNR

/-!
# Block-ending branches, at a witness (SEM1 #537, item (3), route (a))

`reach_bXNR`, `reach_rcbXNR`, `reach_cbXNR` with where their states are (`RL.SegIn`: inside the
branch lines, which are instruction lines, and no step only when the first line is none), and
`realizes_gotoNR` from `QW`: the block entered is reached at its chosen entry witness at the
arrival pc, at the first arrival at a pc entering it (no line inside the branch lines represents
a block, `RL.entryWit_ne`).
-/

namespace Backend.Proof

open Backend E2E

/-- **The states of a segment from line `j0` are inside `[j0, lim)`, whose lines are instruction
lines, and the segment is empty exactly when line `j0` is no instruction line.** -/
def RL.SegIn (R : RL) (s : Arm.ArmState) (n j0 lim : Nat) : Prop :=
  R.Inside s n j0 lim ∧ (∀ k, j0 ≤ k → k < lim → ∃ x t, R.L[k]? = some (.ins x t)) ∧
    (n = 0 ↔ ∀ x t, R.L[j0]? ≠ some (.ins x t))

/-- **A segment `SegIn` inside the lines `ls` at `j0`** runs no frame-record line and no `ret`
when `ls` holds none. -/
theorem RL.frFree_segIn {R : RL} (hR : R.Wf) {s : Arm.ArmState} {n j0 lim : Nat}
    {ls T : List Line} (hd : R.L.drop j0 = ls ++ T) (hlim : lim ≤ j0 + ls.length) (hne : ls ≠ [])
    (hls : ∀ x t, Line.ins x t ∈ ls → x.frLine = false) (hpc : Arm.r .PC s = R.pcOf j0)
    (hseg : R.SegIn s n j0 lim) : R.FRFree s n := by
  apply RL.frFree_of hR
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · obtain ⟨x, t, hj⟩ : ∃ x t, R.L[j0]? = some (.ins x t) :=
      Classical.byContradiction fun hno =>
        absurd (hseg.2.2.mpr fun x t hx => hno ⟨x, t, hx⟩) (by omega)
    have hl : 0 < ls.length := List.length_pos_iff.2 hne
    exact ⟨j0, x, t, hj, hpc, hls x t (RL.mem_of_drop hd hj (Nat.le_refl _) (by omega))⟩
  · obtain ⟨jj, x, t, h1, h2, h3, h4⟩ := hseg.1 i hi0 hi
    exact ⟨jj, x, t, h3, h4, hls x t (RL.mem_of_drop hd h3 (by omega) (by omega))⟩

/-- **`FRFree` of two runs in a row.** -/
theorem RL.FRFree.append {R : RL} {s : Arm.ArmState} {a b : Nat} (h : R.FRFree s a)
    (h' : R.FRFree (iterN R.step a s) b) : R.FRFree s (a + b) := by
  intro i hi x hx
  rcases Nat.lt_or_ge i a with hlt | hge
  · exact h i hlt x hx
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
    rw [iterN_add] at hx
    exact h' k (by omega) x hx

/-- **`reach_bXNA` with the segment's lines** (`RL.FRFree`). -/
theorem reach_bXNAF {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {j0 : Nat}
    {x : Label} {o : List Line} {nxt : Nat}
    (hdrop : R.L.drop j0 = relaxLines R.far o ++ R.L.drop (rix R.far (planLines R.fa.k R.af) nxt))
    (ho : (∃ l', o = [.ins (.b l') none] ∧
        RepLbl (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) x l') ∨
      (o = [] ∧ planRep R.fa.k R.af x nxt = true))
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) (hsp : spOf s = R.spB) :
    ∃ n jl lim, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      RepL R.af (planOwn R.fa.k R.af) R.L x jl ∧
      (∀ i < n, spOf (iterN R.step i s) = spOf s) ∧ (∀ i < n, R.GoodXNY Y (iterN R.step i s)) ∧
      R.SegIn s n j0 lim ∧ n ≤ 1 ∧ R.FRFree s n := by
  rcases ho with ⟨l', rfl, hl⟩ | ⟨rfl, hr⟩
  · obtain ⟨hsk, jl, hjl, hrep⟩ := repLbl_line hR hl
    have hj : R.L[j0]? = some (.ins (.b l') none) := by
      have := congrArg (·[0]?) hdrop
      rw [relaxLines_cons, relaxLine_of_none rfl] at this
      simpa [List.getElem?_drop] using this
    obtain ⟨a, jl', ha, hjl', hstep⟩ := step_branch hR hj (.inl rfl) hsk hprog hpc herr
    have hg := RL.goodXNR_branch (Y := Y) hR hj (.inl rfl) hsk hprog hpc herr hsp
    obtain rfl : jl' = jl := labelOffsets_uniq hR.lm hjl' hjl
    refine ⟨1, jl', j0 + 1, ?_, hrep, fun i hi => ?_, fun i hi => ?_,
      ⟨RL.Inside.one, fun k h1 h2 => ?_, ⟨fun h => absurd h (by omega),
        fun h => absurd hj (h _ _)⟩⟩, Nat.le_refl _,
        RL.frFree_one hR (Nat.le_refl _) hj rfl hpc⟩
    · simp only [iterN]; rw [hstep, brCond_b ha]; rfl
    · obtain rfl : i = 0 := by omega
      rfl
    · obtain rfl : i = 0 := by omega
      exact hg
    · obtain rfl : k = j0 := by omega
      exact ⟨_, _, hj⟩
  · have hrep := rep_nxt hR hr
    simp only [relaxLines, List.flatMap_nil, List.nil_append] at hdrop
    have hj0e := drop_idx hdrop hrep.lt
    rw [← hj0e] at hrep
    refine ⟨0, j0, j0, by simp only [iterN]; rw [← hpc, Arm.w_irrelevant], hrep,
      fun i hi => by omega, fun i hi => by omega,
      ⟨RL.Inside.zero, fun k h1 h2 => by omega, ⟨fun _ => RL.not_ins_of_repL hrep, fun _ => rfl⟩⟩,
      by omega, RL.frFree_zero R s⟩

/-- `reach_bXNR` with `RL.SegIn`. -/
theorem reach_bXNA {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {j0 : Nat}
    {x : Label} {o : List Line} {nxt : Nat}
    (hdrop : R.L.drop j0 = relaxLines R.far o ++ R.L.drop (rix R.far (planLines R.fa.k R.af) nxt))
    (ho : (∃ l', o = [.ins (.b l') none] ∧
        RepLbl (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) x l') ∨
      (o = [] ∧ planRep R.fa.k R.af x nxt = true))
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) (hsp : spOf s = R.spB) :
    ∃ n jl lim, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      RepL R.af (planOwn R.fa.k R.af) R.L x jl ∧
      (∀ i < n, spOf (iterN R.step i s) = spOf s) ∧ (∀ i < n, R.GoodXNY Y (iterN R.step i s)) ∧
      R.SegIn s n j0 lim ∧ n ≤ 1 :=
  let ⟨n, jl, lim, h1, h2, h3, h4, h5, h6, _⟩ := reach_bXNAF (Y := Y) hR hdrop ho hprog hpc herr hsp
  ⟨n, jl, lim, h1, h2, h3, h4, h5, h6⟩

/-- `reach_rcbXNR` with `RL.SegIn`. -/
theorem reach_rcbXNA {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {j0 : Nat}
    {bc : Insn} {t : Lbl}
    {T : List Line} (hdrop : R.L.drop j0 = relaxLine R.far (.ins bc none) ++ T)
    (hbc : (∃ c, bc = .bcond c t) ∨ (∃ nz w r, bc = .cbz nz w r t) ∨ (∃ nz r bit, bc = .tbz nz r bit t))
    (ht : t ≠ .skip) (cond : Bool) (hc : ∀ env a, bc.toArmInst env = .ok a → brCond a s = cond)
    (hcs : bc.condTarget? = some t → ∀ env a, (bc.invertTo .skip).toArmInst env = .ok a →
      brCond a s = !cond)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) (hsp : spOf s = R.spB) :
    ∃ n jl, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      (cond = true → R.L[jl]? = some (.label t)) ∧
      (cond = false → jl = j0 + (relaxLine R.far (.ins bc none)).length) ∧
      (∀ i < n, spOf (iterN R.step i s) = spOf s) ∧ (cond = false → n = 1) ∧
      (∀ i < n, R.GoodXNY Y (iterN R.step i s)) ∧
      R.SegIn s n j0 (j0 + (relaxLine R.far (.ins bc none)).length) ∧ 0 < n := by
  have h1 : ∀ i < 1, spOf (iterN R.step i s) = spOf s := fun i hi => by
    obtain rfl : i = 0 := by omega
    rfl
  have hform : bc = .b t ∨ (∃ c, bc = .bcond c t) ∨ (∃ nz w r, bc = .cbz nz w r t) ∨
      (∃ nz r bit, bc = .tbz nz r bit t) := .inr hbc
  rcases relaxLine_cases R.far bc with h | ⟨t', ht', h⟩
  · rw [h] at hdrop
    have hj := drop_get (Z := []) (by simpa using hdrop)
    obtain ⟨a, jl, ha, hjl, hstep⟩ := step_branch hR hj hform ht hprog hpc herr
    have hg : ∀ i < 1, R.GoodXNY Y (iterN R.step i s) := fun i hi => by
      obtain rfl : i = 0 := by omega
      exact RL.goodXNR_branch hR hj hform ht hprog hpc herr hsp
    have hin : R.SegIn s 1 j0 (j0 + (relaxLine R.far (.ins bc none)).length) :=
      ⟨RL.Inside.one, fun k h1 h2 => by
        rw [h] at h2
        obtain rfl : k = j0 := by simp at h2; omega
        exact ⟨_, _, hj⟩, ⟨fun h => absurd h (by omega), fun h' => absurd hj (h' _ _)⟩⟩
    rw [hc _ _ ha] at hstep
    cases cond
    · exact ⟨1, j0 + 1, by simp only [iterN]; rw [hstep]; rfl, by simp, by simp [h], h1, fun _ => rfl,
        hg, hin, by omega⟩
    · exact ⟨1, jl, by simp only [iterN]; rw [hstep]; rfl, fun _ => hjl, by simp, h1, by simp, hg,
        hin, by omega⟩
  · have hct := relaxTarget_condTarget ht'
    obtain rfl : t' = t := by
      rcases hbc with ⟨c, rfl⟩ | ⟨nz, w, r, rfl⟩ | ⟨nz, r, bit, rfl⟩ <;>
        simp only [Insn.condTarget?] at hct
      · split at hct <;> simp_all
      · simp_all
      · simp_all
    rw [h] at hdrop
    have hj0 := drop_get (Z := [_]) (by simpa using hdrop)
    have hj1 := drop_succ2 hdrop
    obtain ⟨a, ha, hstep⟩ := step_skip hR hj0 hj1 (invertTo_form hbc) hprog hpc herr
    have hg0 := RL.goodXNR_skip (Y := Y) hR hj0 hj1 (invertTo_form hbc) rfl hprog hpc herr hsp
    have hall : ∀ k, j0 ≤ k → k < j0 + (relaxLine R.far (.ins bc none)).length →
        ∃ x t, R.L[k]? = some (.ins x t) := fun k h1 h2 => by
      rw [h] at h2
      simp at h2
      rcases (by omega : k = j0 ∨ k = j0 + 1) with rfl | rfl
      · exact ⟨_, _, hj0⟩
      · exact ⟨_, _, hj1⟩
    rw [hcs hct _ _ ha] at hstep
    cases cond
    · exact ⟨1, j0 + 2, by simp only [iterN]; rw [hstep]; rfl, by simp, by simp [h], h1, fun _ => rfl,
        fun i hi => by
          obtain rfl : i = 0 := by omega
          exact hg0,
        ⟨RL.Inside.one, hall, ⟨fun h => absurd h (by omega), fun h' => absurd hj0 (h' _ _)⟩⟩,
        by omega⟩
    · have hprog1 : (Arm.w .PC (R.pcOf (j0 + 1)) s).program = R.fb.program R.base := by
        rw [Arm.w_program, hprog]
      have herr1 : Arm.r .ERR (Arm.w .PC (R.pcOf (j0 + 1)) s) = .None := by
        rw [Arm.r_of_w_different (by simp), herr]
      obtain ⟨a', jl, ha', hjl, hstep'⟩ := step_branch hR hj1 (.inl rfl) ht hprog1
        (Arm.r_of_w_same ..) herr1
      have hg1 := RL.goodXNR_branch (Y := Y) hR hj1 (.inl rfl) ht hprog1 (Arm.r_of_w_same ..) herr1
        (by rw [spOf_w_pc, hsp])
      rw [brCond_b ha'] at hstep'
      simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hstep
      have hin : R.Inside s 2 j0 (j0 + (relaxLine R.far (.ins bc none)).length) := by
        intro i h0 hi
        obtain rfl : i = 1 := by omega
        refine ⟨j0 + 1, _, _, by omega, by rw [h]; simp, hj1, ?_⟩
        simp only [iterN]; rw [hstep]; exact Arm.r_of_w_same ..
      refine ⟨2, jl, ?_, fun _ => hjl, by simp, fun i hi => ?_, by simp, fun i hi => ?_,
        ⟨hin, hall, ⟨fun h => absurd h (by omega), fun h' => absurd hj0 (h' _ _)⟩⟩, by omega⟩
      · simp only [iterN]
        rw [hstep, hstep', Arm.w_of_w_shadow]
        rfl
      · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · rfl
        · simp only [iterN]
          rw [hstep]
          exact spOf_w_pc _ _
      · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · exact hg0
        · simp only [iterN]
          rw [hstep]
          exact hg1

/-- `reach_cbXNR` with `RL.SegIn`. -/
theorem reach_cbXNAF {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {j0 : Nat}
    {s1 s2 : Label} {ci : Insn} {o : List Line} {nxt : Nat}
    (hdrop : R.L.drop j0 = relaxLines R.far o ++ R.L.drop (rix R.far (planLines R.fa.k R.af) nxt))
    (hco : CondOut (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) s1 s2 ci o nxt)
    (hci : (∃ c t, ci = .bcond c t) ∨ (∃ nz w r t, ci = .cbz nz w r t) ∨
      (∃ nz r bit t, ci = .tbz nz r bit t))
    (cond : Bool)
    (hcT : ∀ l env a, (ci.setTarget l).toArmInst env = .ok a → brCond a s = cond)
    (hcF : ci.condTarget?.isSome = true → ∀ l env a, (ci.invertTo l).toArmInst env = .ok a →
      brCond a s = !cond)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) (hsp : spOf s = R.spB) :
    ∃ n jl lim, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      RepL R.af (planOwn R.fa.k R.af) R.L (if cond then s1 else s2) jl ∧
      (∀ i < n, spOf (iterN R.step i s) = spOf s) ∧ (∀ i < n, R.GoodXNY Y (iterN R.step i s)) ∧
      R.SegIn s n j0 lim ∧ R.FRFree s n := by
  have hne : ∀ y t', relaxLine R.far (.ins y t') ≠ [] := fun y t' h => by
    obtain ⟨_, _, hy⟩ := relaxLine_ins_head R.far y t'
    rw [h] at hy
    cases hy
  rcases hco with ⟨c, t', e', rfl, hct, rfl, hl1, hl2⟩ | ⟨c, t', rfl, hct, hc⟩ | ⟨rfl, hr1, hr2⟩
  · -- `b.c t'; b e'`
    obtain ⟨hsk1, jt, hjt, hrep1⟩ := repLbl_line hR hl1
    rw [relaxLines_cons, List.append_assoc] at hdrop
    have hbcf : (ci.setTarget t').frLine = false := by
      rcases setTarget_form hci t' with ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [h] <;> rfl
    obtain ⟨n, jl, hn, hjT, hjF, hsp1, hn1, hg, hin, -⟩ := reach_rcbXNA (Y := Y) hR hdrop
      (setTarget_form hci t') hsk1 cond (hcT t') (fun hct' env a ha => by
        rw [setTarget_invertTo hci] at ha
        exact hcF (condTarget_setTarget_isSome hci hct') _ env a ha) hprog hpc herr hsp
    have hfr0 : R.FRFree s n := RL.frFree_segIn hR hdrop (Nat.le_refl _) (hne _ _)
      (frLine_relaxLine R.far fun x t'' e => by cases e; exact hbcf) hpc hin
    cases cond
    · -- the fall-through `b e'`
      obtain rfl := hn1 rfl
      have hd1 : R.L.drop jl = relaxLines R.far [.ins (.b e') none] ++
          R.L.drop (rix R.far (planLines R.fa.k R.af) nxt) := by
        rw [hjF rfl, ← List.drop_drop, hdrop, List.drop_left]
      have hs1 : (Arm.w .PC (R.pcOf jl) s).program = R.fb.program R.base := by
        rw [Arm.w_program, hprog]
      obtain ⟨n', jl', lim', hn', hrep', hsp', hg', hin', hn'1, hfr'⟩ := reach_bXNAF (Y := Y) hR hd1
        (.inl ⟨e', rfl, hl2⟩) hs1 (Arm.r_of_w_same ..)
        (by rw [Arm.r_of_w_different (by simp), herr]) (by rw [spOf_w_pc, hsp])
      obtain ⟨hN, hS, hG⟩ := reach_then hn hn' hsp1 hsp' hg hg'
      have hlen0 : 0 < (relaxLine R.far (.ins (ci.setTarget t') none)).length := by
        have := relaxLines_single_ne R.far (.ins (ci.setTarget t') none)
        simp only [relaxLines, List.flatMap_cons, List.flatMap_nil, List.append_nil] at this
        omega
      have hjl_ins : 0 < n' → ∃ x t, R.L[jl]? = some (.ins x t) := fun hpos =>
        Classical.byContradiction fun hno =>
          absurd (hin'.2.2.mpr fun x t hx => hno ⟨x, t, hx⟩) (by omega)
      have hjle : jl = j0 + (relaxLine R.far (.ins (ci.setTarget t') none)).length := hjF rfl
      have hseg : R.SegIn s (1 + n') j0
          (j0 + (relaxLine R.far (.ins (ci.setTarget t') none)).length + n') := by
        obtain ⟨x0, t0, hx0⟩ := hin.2.1 j0 (Nat.le_refl _) (by omega)
        refine ⟨fun i h0 hi => ?_, fun k h1 h2 => ?_, ⟨fun h => absurd h (by omega),
          fun h' => absurd hx0 (h' _ _)⟩⟩
        · obtain rfl : i = 1 := by omega
          obtain ⟨x1, t1, hx1⟩ := hjl_ins (by omega)
          exact ⟨jl, x1, t1, by omega, by omega, hx1, by rw [hn]; exact Arm.r_of_w_same ..⟩
        · rcases Nat.lt_or_ge k (j0 + (relaxLine R.far (.ins (ci.setTarget t') none)).length) with
            hk | hk
          · exact hin.2.1 k h1 hk
          · obtain rfl : k = jl := by omega
            exact hjl_ins (by omega)
      refine ⟨1 + n', jl', _, hN, by simpa using hrep', hS, hG, hseg, hfr0.append ?_⟩
      rw [hn]; exact hfr'
    · obtain rfl : jl = jt := labelOffsets_uniq hR.lm (hjT rfl) hjt
      exact ⟨n, jl, _, hn, by simpa using hrep1, hsp1, hg, hin, hfr0⟩
  · -- one branch
    rcases hc with ⟨rfl, hl1, hr2⟩ | ⟨rfl, hl2, hr1⟩
    · obtain ⟨hsk1, jt, hjt, hrep1⟩ := repLbl_line hR hl1
      rw [relaxLines_cons] at hdrop
      simp only [relaxLines, List.flatMap_nil, List.append_nil] at hdrop
      have hbcf : (ci.setTarget t').frLine = false := by
        rcases setTarget_form hci t' with ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [h] <;> rfl
      obtain ⟨n, jl, hn, hjT, hjF, hsp1, -, hg, hin, -⟩ := reach_rcbXNA (Y := Y) hR hdrop
        (setTarget_form hci t') hsk1 cond (hcT t') (fun hct' env a ha => by
          rw [setTarget_invertTo hci] at ha
          exact hcF (condTarget_setTarget_isSome hci hct') _ env a ha) hprog hpc herr hsp
      have hfr0 : R.FRFree s n := RL.frFree_segIn hR hdrop (Nat.le_refl _) (hne _ _)
        (frLine_relaxLine R.far fun x t'' e => by cases e; exact hbcf) hpc hin
      cases cond
      · have hrep2 := rep_nxt hR hr2
        have hd : R.L.drop jl = R.L.drop (rix R.far (planLines R.fa.k R.af) nxt) := by
          rw [hjF rfl, ← List.drop_drop, hdrop, List.drop_left]
        obtain rfl := drop_idx hd hrep2.lt
        exact ⟨n, _, _, hn, by simpa using hrep2, hsp1, hg, hin, hfr0⟩
      · obtain rfl : jl = jt := labelOffsets_uniq hR.lm (hjT rfl) hjt
        exact ⟨n, jl, _, hn, by simpa using hrep1, hsp1, hg, hin, hfr0⟩
    · obtain ⟨hsk2, jt, hjt, hrep2⟩ := repLbl_line hR hl2
      rw [relaxLines_cons] at hdrop
      simp only [relaxLines, List.flatMap_nil, List.append_nil] at hdrop
      have hbcf : (ci.invertTo t').frLine = false := by
        rcases invertTo_form' hci t' with ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [h] <;> rfl
      obtain ⟨n, jl, hn, hjT, hjF, hsp1, -, hg, hin, -⟩ := reach_rcbXNA (Y := Y) hR hdrop
        (invertTo_form' hci t') hsk2 (!cond) (hcF (condTarget_invertTo_isSome hci hct) t')
        (fun _ env a ha => by
          rw [invertTo_invertTo hci] at ha
          rw [Bool.not_not]
          exact hcT _ env a ha) hprog hpc herr hsp
      have hfr0 : R.FRFree s n := RL.frFree_segIn hR hdrop (Nat.le_refl _) (hne _ _)
        (frLine_relaxLine R.far fun x t'' e => by cases e; exact hbcf) hpc hin
      cases cond
      · obtain rfl : jl = jt := labelOffsets_uniq hR.lm (hjT rfl) hjt
        exact ⟨n, jl, _, hn, by simpa using hrep2, hsp1, hg, hin, hfr0⟩
      · have hrep1 := rep_nxt hR hr1
        have hd : R.L.drop jl = R.L.drop (rix R.far (planLines R.fa.k R.af) nxt) := by
          rw [hjF rfl, ← List.drop_drop, hdrop, List.drop_left]
        obtain rfl := drop_idx hd hrep1.lt
        exact ⟨n, _, _, hn, by simpa using hrep1, hsp1, hg, hin, hfr0⟩
  · -- no lines: both successors next
    simp only [relaxLines, List.flatMap_nil, List.nil_append] at hdrop
    have hrep1 := rep_nxt hR hr1
    have hrep2 := rep_nxt hR hr2
    have hj0e := drop_idx hdrop hrep1.lt
    rw [← hj0e] at hrep1 hrep2
    refine ⟨0, j0, j0, by simp only [iterN]; rw [← hpc, Arm.w_irrelevant], ?_, fun i hi => by omega,
      fun i hi => by omega,
      ⟨RL.Inside.zero, fun k h1 h2 => by omega, ⟨fun _ => RL.not_ins_of_repL hrep1, fun _ => rfl⟩⟩,
      RL.frFree_zero R s⟩
    cases cond
    · simpa using hrep2
    · simpa using hrep1

/-- `reach_cbXNR` with `RL.SegIn`. -/
theorem reach_cbXNA {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {j0 : Nat}
    {s1 s2 : Label} {ci : Insn} {o : List Line} {nxt : Nat}
    (hdrop : R.L.drop j0 = relaxLines R.far o ++ R.L.drop (rix R.far (planLines R.fa.k R.af) nxt))
    (hco : CondOut (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) s1 s2 ci o nxt)
    (hci : (∃ c t, ci = .bcond c t) ∨ (∃ nz w r t, ci = .cbz nz w r t) ∨
      (∃ nz r bit t, ci = .tbz nz r bit t))
    (cond : Bool)
    (hcT : ∀ l env a, (ci.setTarget l).toArmInst env = .ok a → brCond a s = cond)
    (hcF : ci.condTarget?.isSome = true → ∀ l env a, (ci.invertTo l).toArmInst env = .ok a →
      brCond a s = !cond)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) (hsp : spOf s = R.spB) :
    ∃ n jl lim, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      RepL R.af (planOwn R.fa.k R.af) R.L (if cond then s1 else s2) jl ∧
      (∀ i < n, spOf (iterN R.step i s) = spOf s) ∧ (∀ i < n, R.GoodXNY Y (iterN R.step i s)) ∧
      R.SegIn s n j0 lim :=
  let ⟨n, jl, lim, h1, h2, h3, h4, h5, _⟩ :=
    reach_cbXNAF (Y := Y) hR hdrop hco hci cond hcT hcF hprog hpc herr hsp
  ⟨n, jl, lim, h1, h2, h3, h4, h5⟩

/-- **`realizes_gotoNA` with the segment's lines** (`RL.FRFree`). -/
theorem realizes_gotoNAF {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {b k : Nat}
    {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {c' : MConf CV Arm.ArmState}
    {j : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {i : MInst}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    (hbr : (∃ l, i = .jump l) ∨ (∃ t e kk, i = .condBr t e kk) ∨
      (∃ kd t e rn bit, i = .testBitAndBranch kd t e rn bit))
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c') :
    ∃ n, R.SegNA Y s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c' n ∧ R.FRFree s n := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  obtain ⟨c, ins, _, hc, -⟩ := hR.check
  obtain ⟨preds, hcfg⟩ := hc.cfg
  obtain ⟨t0, ts, hback, hss, hlab⟩ := cfg_block hcfg hvb
  by_cases hT : T = []
  rotate_left
  · -- a forwarding block entered without a step: its `jump` takes no machine step
    obtain ⟨vbf, allocsf, regsf, if_, xf, bx, itx, hvbf, he, hits, half, hins, hasgf, hsuccf, hitx,
      ⟨itb, hitb, hilb⟩, hE, hpcj, hstj⟩ := hq.fwd hT
    rw [hvb] at hvbf
    cases hvbf
    simp only [RItem.op.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    subst hits
    have hi1 := hi
    rw [hins] at hi1
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hi1
    subst hi1
    have htg := (assign_shape hasgf).1
    rcases hbr with ⟨l, rfl⟩ | ⟨t, e, kk, rfl⟩ | ⟨kd, t, e, rn, bit, rfl⟩
    rotate_left
    · simp [MInst.targets] at htg
    · simp [MInst.targets] at htg
    cases h with
    | @op b k allocs its m w vb' i ops outs outs' w' ctl m2 c' hvb' hi' hops' hsz hsem hlen hho hcl
      hn =>
    rw [hvb] at hvb'
    cases hvb'
    rw [hi] at hi'
    cases hi'
    simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
    obtain ⟨rfl, rfl, rfl⟩ := hsem
    obtain rfl : outs' = [] := List.eq_nil_of_length_eq_zero hho.1
    have hm2 : m2 = m := by
      funext l'
      refine (hcl.1 l' (by simp [MInst.clobbers])).trans ?_
      simp [writeM]
    subst m2
    cases hn with
    | @goto _ st items' hk1 hsucc hitems =>
    rw [hsuccf] at hsucc
    cases hsucc
    rw [hitx] at hitems
    cases hitems
    have hwm : ∀ L : List (Operand × Loc), writeM m ((L.zip ([] : List CV)).filter
        (·.1.1.isLate)) = m := fun L => by simp [writeM]
    rw [hwm]
    have hns : ¬ (bx = b ∧ itx.toList = []) := by
      rintro ⟨rfl, he⟩
      rw [hitx] at hitb
      cases hitb
      rw [hilb] at he
      cases he
    have hE' : ∃ W, R.EntryWit bx (Arm.r .PC s) W := by rw [hpcj]; exact hE
    refine ⟨0, ⟨?_, fun i hi => by omega, ⟨?_, fun i h0 hi => by omega⟩, ?_⟩, RL.frFree_zero R s⟩
    · unfold RL.QWn
      rw [RL.nextW_entry hns]
      exact qW_entryW hitx hE' hstj
    · rw [RL.tgtS_entry hns]
      exact hE'
    · rw [RL.emptyW_entry_iff hns]
      exact ⟨fun _ => .inl hT, fun _ => rfl⟩
  rcases hq with ⟨-, hqs⟩ | ⟨hT', -⟩
  rotate_left
  · exact absurd hT hT'
  obtain ⟨vb0, _, _, code, _, _, _, _, hvb0, -, -, hchk0, hcode, -⟩ := id hqs
  rw [hvb] at hvb0; cases hvb0
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
  rw [hi] at hi0; cases hi0
  obtain ⟨cc, wh, i2, ops2, hi2, hops2, hstat, -⟩ := op_checked hchk0
  rw [hi] at hi2; cases hi2
  cases h with
  | @op b k allocs its m w vb' i ops outs outs' w' ctl m2 c' hvb' hi' hops' hsz hsem hlen hho hcl hn =>
  rw [hvb] at hvb'; cases hvb'
  rw [hi] at hi'; cases hi'
  rw [hops2] at hops'; cases hops'
  -- the semantics: no defs, same world, `goto j`
  generalize hU : (((ops2.zip (regs.map Loc.reg)).toList.filter (·.1.isUse)).map (m ·.2)) = U at hsem
  have hsem' : outs = [] ∧ w' = w ∧ ∃ jt, ctl = .goto jt ∧ (∀ l, i = .jump l → jt = 0) ∧
      (∀ t e kk, i = .condBr t e kk → jt = if kk.holds U w then 0 else 1) ∧
      (∀ kd t e rn bit, i = .testBitAndBranch kd t e rn bit →
        ∃ a, U = [a] ∧ jt = if ((lo64 a).getLsbD bit == (kd == .nz)) then 0 else 1) := by
    rcases hbr with ⟨l, rfl⟩ | ⟨t, e, kk, rfl⟩ | ⟨kd, t, e, rn, bit, rfl⟩
    · simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
      obtain ⟨rfl, rfl, rfl⟩ := hsem
      refine ⟨rfl, rfl, 0, rfl, fun _ _ => rfl, ?_, ?_⟩
      · intro _ _ _ h; cases h
      · intro _ _ _ _ _ h; cases h
    · simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
      obtain ⟨rfl, rfl, rfl⟩ := hsem
      refine ⟨rfl, rfl, _, rfl, ?_, ?_, ?_⟩
      · intro _ h; cases h
      · intro t' e' kk' h; cases h; rfl
      · intro _ _ _ _ _ h; cases h
    · simp only [RL.sem, csemV, csem] at hsem
      split at hsem
      · rename_i a
        simp only [Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        refine ⟨rfl, rfl, _, rfl, ?_, ?_, ?_⟩
        · intro _ h; cases h
        · intro _ _ _ h; cases h
        intro kd' t' e' rn' bit' h
        cases h
        exact ⟨a, rfl, rfl⟩
      · cases hsem
  obtain ⟨rfl, hw', jt, rfl, hj0, hjc, hjt⟩ := hsem'
  obtain rfl : outs' = [] := List.eq_nil_of_length_eq_zero hho.1
  subst w'
  -- the store is unchanged
  have hm2 : m2 = m := by
    funext l
    refine (hcl.1 l ?_).trans ?_
    · rcases hbr with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ <;> simp [MInst.clobbers]
    · simp [writeM]
  subst m2
  cases hn with
  | @goto _ st items' hk1 hsucc hitems =>
  have hwm : writeM m ((((ops2.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip
      ([] : List CV)).filter (·.1.1.isLate)) = m := by simp [writeM]
  rw [hwm]
  -- the successor's label
  have hti : t0 = i := by
    rw [Array.back?_eq_getElem?, show vb.insts.size - 1 = k by omega, hi] at hback
    cases hback; rfl
  subst hti
  have hsucc' := hsucc
  simp only [succOf, hcfg, hss, Option.bind_some] at hsucc'
  obtain ⟨vs, hvs, hlj⟩ := hlab jt st hsucc'
  have hst0 : st ≠ 0 := ctlCheck_succ hck hsucc
  -- the block's last item: its final lines and the branch check's verdict on them
  obtain rfl : its = [] := hchk0.tail_nil (by omega)
  obtain ⟨vb0, items, pre, c1', X, psm, ps2, x, hvb0, hit, hsplit, -, hc1'', hX, -, htr,
    hdrop, hpc, hst, hterm⟩ := qWs_term hR hqs
  rw [hvb] at hvb0; cases hvb0
  rw [hc1] at hc1''; cases hc1''
  have hone : ∀ a, c1 = [a] → X = [] ∧ R.L.drop j = relaxLines R.far x.2.1 ++
      R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2) := by
    intro a ha
    subst ha
    simp only [List.dropLast_singleton, codeLinesE, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hX
    obtain ⟨rfl, rfl⟩ := hX
    exact ⟨rfl, by simpa using hdrop⟩
  -- the machine reaches a line representing the successor
  have hreach : ∃ n jl lim, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      RepL R.af (planOwn R.fa.k R.af) R.L vs.label jl ∧ (∀ i < n, R.GoodXNY Y (iterN R.step i s)) ∧
      R.SegIn s n j lim ∧ R.FRFree s n := by
    rcases hbr with ⟨l, rfl⟩ | ⟨t, e, kk, rfl⟩ | ⟨kd, t, e, rn, bit, rfl⟩
    · obtain ⟨rfl, rfl⟩ := assign_none (fun f => rfl) hasg
      obtain rfl : c1 = [.inst _] := by
        rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
        · exact h
        · cases h
        · cases h
      obtain ⟨-, hd⟩ := hone _ rfl
      simp only [List.getLast?_singleton] at hterm
      rw [hj0 l rfl] at hlj
      simp only [MInst.targets, List.getElem?_cons_zero, Option.some.injEq] at hlj
      rw [← hlj]
      obtain ⟨n, jl, lim, hn, hrep, -, hg, hseg, -, hfr⟩ := reach_bXNAF (Y := Y) hR hd
        (termOk_jump hterm) (by rw [hst.prog]) hpc hst.err hst.sp
      exact ⟨n, jl, lim, hn, hrep, hg, hseg, hfr⟩
    · have hkk : ∀ r sz, kk = .zero r sz ∨ kk = .notZero r sz → r.isVregInt = true := by
        intro r sz hr
        have := ctlCheck_inst hck hvb hi
        rcases hr with rfl | rfl <;> simpa [ctlInstOk] using this
      obtain ⟨k', rfl, hkr⟩ := kind_alloc hkk (mk := fun k => MInst.condBr t e k) rfl
        (fun f => rfl) (fun f => rfl) hops2 hstat hasg m
      obtain rfl : c1 = [.inst _] := by
        rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
        · exact h
        · cases h
        · cases h
      obtain ⟨-, hd⟩ := hone _ rfl
      simp only [List.getLast?_singleton] at hterm
      have hci : (∃ c t', k'.insn (.block t) = .bcond c t') ∨
          (∃ nz w r t', k'.insn (.block t) = .cbz nz w r t') ∨
          (∃ nz r bit t', k'.insn (.block t) = .tbz nz r bit t') := by
        cases k' <;> simp [CondBrKind.insn]
      have hset : ∀ l, (k'.insn (.block t)).setTarget l = k'.insn l := by
        intro l; cases k' <;> rfl
      have hct : (k'.insn (.block t)).condTarget?.isSome = true →
          (k'.insn (.block t)).condTarget? = some (.block t) := by
        intro h
        cases k' <;> simp_all [CondBrKind.insn, Insn.condTarget?]
      obtain ⟨n, jl, lim, hn, hrep, -, hg, hseg, hfr⟩ := reach_cbXNAF (Y := Y) hR hd
        (termOk_condBr hterm) hci (kk.holds _ w)
        (fun l env a ha => kind_brCond hst hkr l (by rwa [hset] at ha))
        (fun hs l env a ha => kind_brCond_inv hst hkr (.block t) l (hct hs) ha)
        (by rw [hst.prog]) hpc hst.err hst.sp
      refine ⟨n, jl, lim, hn, ?_, hg, hseg, hfr⟩
      rw [hU] at hrep
      rw [hjc t e kk rfl] at hlj
      simp only [MInst.targets] at hlj
      cases hcond : kk.holds U w <;> simp only [hcond] at hlj hrep <;> simp at hlj <;> rw [← hlj] <;>
        simpa using hrep
    · obtain ⟨nr, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
      obtain ⟨r', rfl, rfl⟩ := assign_one (n := nr) (sp := OpSpec.use)
        (mk := fun r => MInst.testBitAndBranch kd t e r bit) (fun f => by simp [MInst.visitOperands])
        hasg
      have hops' : ops2 = #[⟨nr, .int, .use, .early, .reg⟩] := by
        have e : (MInst.testBitAndBranch kd t e (.vreg nr .int) bit).operands =
            .ok #[⟨nr, .int, .use, .early, .reg⟩] := rfl
        rw [e] at hops2
        injection hops2 with h
        exact h.symm
      subst hops'
      obtain ⟨⟨n', rfl, hn', -⟩, -⟩ := (allocOk_of_checkStatic hstat).fits
        (⟨nr, .int, .use, .early, .reg⟩, r') (by simp)
      obtain rfl : c1 = [.inst _] := by
        rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
        · exact h
        · cases h
        · cases h
      obtain ⟨-, hd⟩ := hone _ rfl
      simp only [List.getLast?_singleton] at hterm
      have hal := ((checkStatic_facts hstat).2.1 (⟨nr, .int, .use, .early, .reg⟩, .reg (.x n'))
        (by simp)).1
      simp only [CheckCtx.locOk, Bool.and_eq_true] at hal
      have hm : m (.reg (.x n')) = (Arm.r (.GPR (rnum n')) s).setWidth 128 := by
        rw [hst.store (.reg (.x n')) (fun r e => by cases e; exact hal.2) trivial]; rfl
      obtain ⟨n, jl, lim, hn, hrep, -, hg, hseg, hfr⟩ := reach_cbXNAF (Y := Y) hR hd
        (termOk_tbz hterm) (.inr (.inr ⟨_, _, _, _, rfl⟩))
        ((Arm.r (.GPR (rnum n')) s).getLsbD bit == (kd == .nz))
        (fun l env a ha => brCond_tbz (by omega) ha s)
        (fun _ l env a ha => by
          simp only [Insn.invertTo] at ha
          rw [brCond_tbz (by omega) ha s, beq_not_right])
        (by rw [hst.prog]) hpc hst.err hst.sp
      refine ⟨n, jl, lim, hn, ?_, hg, hseg, hfr⟩
      obtain ⟨a, hUa, hja⟩ := hjt kd t e _ bit rfl
      have ha : a = m (.reg (.x n')) := by
        rw [← hU] at hUa
        simp [Operand.isUse] at hUa
        exact hUa.symm
      subst ha
      rw [hja] at hlj
      simp only [MInst.targets, hm, lo64_regX] at hlj
      cases hcond : ((Arm.r (.GPR (rnum n')) s).getLsbD bit == (kd == .nz)) <;>
        simp only [hcond] at hlj hrep <;> simp at hlj <;> rw [← hlj] <;> simpa using hrep
  obtain ⟨n, jl, lim, hn, hrep, hg, hseg, hfr⟩ := hreach
  have hns : ¬ (st = b ∧ items'.toList = []) := by
    rintro ⟨rfl, he⟩
    rw [hit] at hitems; cases hitems
    have := congrArg List.length hsplit
    rw [he] at this
    simp at this
  obtain ⟨hE, hqE⟩ := qW_entry hR hst0 hvs hitems hrep (Arm.r_of_w_same ..) (hst.pc _)
  refine ⟨n, ⟨?_, hg, ?_, ?_⟩, hfr⟩
  · unfold RL.QWn
    rw [RL.nextW_entry hns, hn]
    exact hqE
  · rw [RL.tgtS_entry hns]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      refine ⟨?_, fun i h0 hi => absurd hi (by omega)⟩
      show ∃ W, R.EntryWit st (Arm.r .PC (iterN R.step 0 s)) W
      rw [hn]; exact hE
    · obtain ⟨x0, t0, hx0⟩ : ∃ x t, R.L[j]? = some (.ins x t) :=
        Classical.byContradiction fun hno =>
          absurd (hseg.2.2.mpr fun x t hx => hno ⟨x, t, hx⟩) (by omega)
      refine RL.firstArrS_of_inside hseg.1 (RL.entryWit_ne hR hx0 (fun k l h1 h2 e => ?_)) ?_
      · obtain ⟨x', t', hx'⟩ := hseg.2.1 k (by omega) h2
        rw [hx'] at e; cases e
      · show ∃ W, R.EntryWit st (Arm.r .PC (iterN R.step n s)) W
        rw [hn]; exact hE
  · rw [RL.emptyW_entry_iff hns]
    exact hseg.2.2.trans ⟨fun h => .inr h, fun h => h.resolve_left fun h' => h' hT⟩

/-- **Block-ending branches on the machine, at a witness** (`realizes_gotoNR`): the successor's
items at its chosen entry witness, reached at the first arrival. -/
theorem realizes_gotoNA {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {b k : Nat}
    {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {c' : MConf CV Arm.ArmState}
    {j : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {i : MInst}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    (hbr : (∃ l, i = .jump l) ∨ (∃ t e kk, i = .condBr t e kk) ∨
      (∃ kd t e rn bit, i = .testBitAndBranch kd t e rn bit))
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c') :
    ∃ n, R.SegNA Y s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c' n :=
  let ⟨n, h1, _⟩ := realizes_gotoNAF (Y := Y) hR hq hvb hi hbr h
  ⟨n, h1⟩

end Backend.Proof
