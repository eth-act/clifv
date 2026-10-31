import FV.E2E.RegLevelFRFree
import FV.E2E.RegLevelQW

/-!
# Moves, at a witness, with their segment length (SEM1 #537, item (3), route (a))

`realizes_moveNR` from `QW` at the witness `(j, ps1, T)`: the move ends at `QW` at
`RL.nextW`'s witness, and its segment is the first arrival at that line (`RL.SegLen`).
-/

namespace Backend.Proof

open Backend E2E

/-- A callee save or restore (a move into or out of a save slot) emits no code: the witness
after it is the witness before it. -/
theorem nextW_move_save {R : RL} {s : Arm.ArmState} {b : Nat} {src dst : Loc} {its : List RItem}
    {m m' : Loc → CV} {w w' : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j ps1 T (.run ⟨b, .move src dst :: its, m, w⟩))
    (h : src.isSave = true ∨ dst.isSave = true) {p : BitVec 64} :
    R.nextW j ps1 T (.run ⟨b, .move src dst :: its, m, w⟩) (.run ⟨b, its, m', w'⟩) p =
      (j, ps1, T) := by
  obtain ⟨-, vb, items, pre, code, X, psm, ps2, x, hvb, -, -, -, hcode, -⟩ :=
    hq.qws (fun _ h => by cases h)
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  have hc1o := hc1
  rw [itemCode_move] at hc1
  have hc1' : c1 = [] := by
    rcases h with h | h
    · obtain ⟨r, rfl⟩ : ∃ r, src = .save r := by
        cases src <;> simp [Loc.isSave] at h; exact ⟨_, rfl⟩
      cases dst <;> simp only [RAFrame.moveInsts, pure, Except.pure, Except.ok.injEq] at hc1 <;>
        first | exact hc1.symm | exact hc1
    · obtain ⟨r, rfl⟩ : ∃ r, dst = .save r := by
        cases dst <;> simp [Loc.isSave] at h; exact ⟨_, rfl⟩
      simp only [RAFrame.moveInsts, pure, Except.pure, Except.ok.injEq] at hc1
      cases src <;> exact hc1.symm
  subst hc1'
  have h0 : codeLinesE R.ctx R.af [] ps1 = .ok ([], ps1) := by
    simp only [codeLinesE, pure, Except.pure]
  rw [RL.nextW_straight, RL.straightW_eq hvb hc1o h0]
  simp [relaxLines]

/-- **A callee save at a witness**: `QW` at the same witness after the save (`q_save`). -/
theorem qW_save {R : RL} {s : Arm.ArmState} {b : Nat} {src dst : Loc} {its : List RItem}
    {m : Loc → CV} {w : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    (hds : dst.isSave = true) (hq : QW R s j ps1 T (.run ⟨b, .move src dst :: its, m, w⟩)) :
    QW R s j ps1 T (.run ⟨b, its, upd m dst (m src), w⟩) := by
  obtain ⟨hT0, vb, items, pre, code, X, psm, ps2, x, hvb, hit, hsplit, hchk, hcode, hX, hT,
    htr, hdrop, hpc, hst, hx, hsc⟩ := hq.qws (fun _ h => by cases h)
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  rw [itemCode_move] at hc1
  obtain ⟨r, rfl⟩ : ∃ r, dst = .save r := by cases dst <;> simp [Loc.isSave] at hds; exact ⟨_, rfl⟩
  have hc1' : c1 = [] := by
    simp only [RAFrame.moveInsts, pure, Except.pure, Except.ok.injEq] at hc1
    cases src <;> exact hc1.symm
  subst hc1'
  refine .inl ⟨hT0, vb, items, pre ++ [.move src (.save r)], c2, X, psm, ps2, x, hvb, hit,
    by rw [hsplit]; simp, itemsChecked_move_tail hchk, hc2, by simpa using hX, by simpa using hT,
    htr, hdrop, hpc,
    ⟨fun l hv hL => ?_, hst.world, hst.err, hst.prog, hst.sp, hst.align, hst.fplr, hst.code,
      hst.gkeep, hst.fp⟩, hx, hsc⟩
  have hne : l ≠ .save r := by rintro rfl; exact hL
  simp only [upd, hne, ite_false]
  exact hst.store l hv hL

/-- **A callee restore at a witness**: `QW` at the same witness after the restore, the store
unchanged (`q_restore`). -/
theorem qW_restore {R : RL} {s : Arm.ArmState} {b : Nat} {src dst : Loc} {its : List RItem}
    {m : Loc → CV} {w : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    (hss : src.isSave = true) (hq : QW R s j ps1 T (.run ⟨b, .move src dst :: its, m, w⟩)) :
    QW R s j ps1 T (.run ⟨b, its, m, w⟩) := by
  obtain ⟨hT0, vb, items, pre, code, X, psm, ps2, x, hvb, hit, hsplit, hchk, hcode, hX, hT,
    htr, hdrop, hpc, hst, hx, hsc⟩ := hq.qws (fun _ h => by cases h)
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  rw [itemCode_move] at hc1
  obtain ⟨r, rfl⟩ : ∃ r, src = .save r := by cases src <;> simp [Loc.isSave] at hss; exact ⟨_, rfl⟩
  have hc1' : c1 = [] := by
    cases dst <;> simp only [RAFrame.moveInsts, pure, Except.pure, Except.ok.injEq] at hc1 <;>
      first | exact hc1.symm | exact hc1
  subst hc1'
  exact .inl ⟨hT0, vb, items, pre ++ [.move (.save r) dst], c2, X, psm, ps2, x, hvb, hit,
    by rw [hsplit]; simp, itemsChecked_move_tail hchk, hc2, by simpa using hX, by simpa using hT,
    htr, hdrop, hpc, hst, hx, hsc⟩

/-- **`realizes_moveNA` with the segment's lines** (`RL.FRFree`: the move's lines are no
frame-record line and no `ret`). -/
theorem realizes_moveNAF {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {b : Nat}
    {src dst : Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {j : Nat} {ps1 : PState}
    {T : List Line} (hq : QW R s j ps1 T (.run ⟨b, .move src dst :: its, m, w⟩))
    (hns : src.isSave = false) :
    ∃ n, R.QWn j ps1 T (.run ⟨b, .move src dst :: its, m, w⟩)
        (.run ⟨b, its, upd m dst (m src), w⟩) (iterN R.step n s) ∧
      (∀ i < n, R.GoodXNY Y (iterN R.step i s)) ∧
      R.SegLen j ps1 T (.run ⟨b, .move src dst :: its, m, w⟩)
        (.run ⟨b, its, upd m dst (m src), w⟩) s n ∧ R.FRFree s n := by
  by_cases hds : dst.isSave = true
  · have hS : R.straightW b (.move src dst) j ps1 T = (j, ps1, T) := by
      rw [← RL.nextW_straight (m := m) (m' := upd m dst (m src)) (w := w) (w' := w) (p := 0)]
      exact nextW_move_save hq (.inr hds)
    refine ⟨0, ?_, fun _ h => absurd h (Nat.not_lt_zero _), ⟨⟨?_, fun i h0 h => by omega⟩, ?_⟩,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
    · unfold RL.QWn
      rw [nextW_move_save hq (.inr hds)]
      exact qW_save hds hq
    · rw [RL.tgtS_straight, hS]; exact hq.pc
    · rw [RL.segLen_straight_iff, hS]
      exact ⟨fun _ => rfl, fun _ => rfl⟩
  obtain ⟨hT0, hq'⟩ := hq.qws (fun _ h => by cases h)
  have hne : its ≠ [] := by
    obtain ⟨_, _, _, _, _, _, _, _, -, -, -, hchk0, -⟩ := hq'
    obtain ⟨c, k, a, out, -, -, hrun⟩ := hchk0
    obtain ⟨hk, h'⟩ := runItems_move hrun
    rintro rfl
    exact hk (runItems_nil h').1
  obtain ⟨vb, items, pre, c1, c2, ls1, X', psm, psm', ps2, x, hvb, hit, hsplit, hchk, hc1,
    hc2, h1, h2, h3, htr, hdrop, hpc, hst, hx, hsc⟩ := qWs_split hR hq' hne
  obtain ⟨⟨c, wh, hcm⟩, hLs, hLd, hT, hchk'⟩ := move_facts hit hsplit hchk hns (by simpa using hds)
  have hc1o := hc1
  have h1o := h1
  rw [itemCode_move] at hc1
  obtain ⟨hvs, -, is, s', rfl, hmi, hex, hmo⟩ := lower_move (R.frameOk hR) R.ctx hcm
    hLs hLd hT hc1 hst.world hst.sp hst.align
  obtain ⟨ls1', hcl, hlen, hins, hpl, hrun, hint, hprog, herr⟩ :=
    run_oneLines R.ctx R.af is s s' (fun i hi => oneLine_of_moveInst R.ctx (hmi i hi)) hex hst.err
  rw [hcl ps1] at h1
  simp only [Except.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  have hS : R.straightW b (.move src dst) j ps1 T = (j + (relaxLines R.far ls1').length, ps1, T) :=
    RL.straightW_eq hvb hc1o h1o
  -- the lines at `j`
  have hdrop' : R.L.drop j = ls1' ++ (relaxLines R.far (X' ++ x.2.1) ++
      R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2)) := by
    rw [hdrop, relaxLines_plain hpl]
  have hat : ∀ k ln, ls1'[k]? = some ln → R.fa.lines.toList[j + k]? = some ln := by
    intro k ln hk
    have := congrArg (·[k]?) hdrop'
    simp only [List.getElem?_drop, RL.L] at this
    rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk).1]
    exact hk
  have hins' : ∀ ln ∈ ls1', ∃ i t, ln = .ins i t := fun ln h => by
    obtain ⟨i, t, e, -⟩ := hins ln h; exact ⟨i, t, e⟩
  have hhook : ∀ i t, Line.ins i t ∈ ls1' → i.hooked = false := fun i t h => by
    obtain ⟨i', t', e, hh⟩ := hins _ h; cases e; exact hh
  have hiter : iterN R.step ls1'.length s = s' :=
    iterN_execLines hR.layout hR.lm hR.fit ls1' j s s' hat hhook
      (by rw [hst.prog]) (by rw [hpc]; rfl) hst.err (hint _) (hrun _)
  have hpcs : ∀ i ≤ ls1'.length, Arm.r .PC (iterN R.step i s) = R.pcOf (j + i) :=
    iterN_execLines_pc (X := R.X) (H := R.H) hR.layout hR.lm hR.fit ls1' j s s' hat hhook
      (by rw [hst.prog]) (by rw [hpc]; rfl) hst.err (hint _) (hrun _)
  -- the move's reads: bytes of the frame's slot area, which `G` avoids
  have hrd : LinesReads (R.envOf j) ls1' s (R.ReadInY Y false) := by
    obtain ⟨is', e, hrd⟩ := moveInsts_reads (vc := R.vc) (rf := R.rf) R.ctx hcm hLs hLd hT hc1
      hst.align
    obtain rfl := (List.map_inj_right fun _ _ h => AInst.inst.inj h).1 e
    refine (linesReads_of_insts R.ctx R.af is s s'
      (fun i hi => oneLine_of_moveInst R.ctx (hmi i hi)) hex hrd ls1' ps1 ps1 (hcl ps1) _).mono ?_
    rintro a ⟨o, ho, rfl⟩
    exact .inr (.inl (by rw [show spOf s = R.spB from hst.sp]; exact RL.frameRd_slot hR ho))
  have hst' : StRel R (iterN R.step ls1'.length s) (upd m dst (m src)) w := by
    rw [hiter]
    have hsp' : spOf s' = R.spB := hmo.sp
    have hw' := hmo.world
    refine ⟨move_agree hst.store hvs hLs hmo.store, hw', herr, by rw [hprog, hst.prog], hsp',
      align_of_sp (by rw [hsp', hst.sp]) hst.align, fun hframe => ?_,
      code_frameKeep hR hmo.mem hst.code,
      fun a ha => (hmo.mem a (RL.G_not_slot hR ha)).trans (hst.gkeep a ha),
      fun hf => (xreg29_sw hst.world hw').trans (hst.fp hf)⟩
    rw [← hst.fplr hframe]
    apply read_mem_bytes_congr
    intro k hk
    exact hmo.mem _ (fun o ho => by
      have := fplr_outside hR hframe k hk o ho
      rwa [show R.spB = spOf s by rw [hst.sp]] at this ⊢)
  refine ⟨ls1'.length, ?_, fun i hi => ?_, ⟨?_, ?_⟩, ?_⟩
  · unfold RL.QWn
    rw [RL.nextW_straight, hS]
    exact .inl ⟨hT0, qWs_next hvb hit hsplit hchk' hc2 h2 h3 htr hdrop
      (by rw [relaxLines_plain hpl]; exact hpcs _ (Nat.le_refl _)) hst' hx hsc⟩
  · exact R.goodXNR_execLines hR hat hhook
      (codeLinesE_noTlsTail (is.map .inst) ps1 ps1 ls1' (fun n rd tmp h => by
        simp only [List.mem_map] at h
        obtain ⟨a, ha, e⟩ := h
        cases e
        exact (oneLine_of_moveInst R.ctx (hmi _ ha)).not_tls n rd tmp rfl) (hcl ps1))
      (by rw [hst.prog]) hpc hst.err hst.sp (hint _) (hrun _) hrd i hi
  · rw [RL.tgtS_straight, hS, relaxLines_plain hpl]
    refine firstArrS_singleton.mpr (RL.firstArr_lines hR (fun k hk => ?_) hpcs)
    obtain ⟨ln, hln⟩ : ∃ ln, ls1'[k]? = some ln := ⟨_, List.getElem?_eq_getElem hk⟩
    obtain ⟨x, t, rfl⟩ := hins' _ (List.mem_of_getElem? hln)
    exact ⟨x, t, hat k _ hln⟩
  · rw [RL.segLen_straight_iff, hS, relaxLines_plain hpl]
    simp
  · refine RL.frFree_of hR fun i hi => ?_
    obtain ⟨ln, hln⟩ : ∃ ln, ls1'[i]? = some ln := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨x, t, rfl⟩ := hins' _ (List.mem_of_getElem? hln)
    exact ⟨j + i, x, t, hat i _ hln, hpcs i (Nat.le_of_lt hi),
      frLine_codeLinesE (by simp) (hcl ps1) x t (List.mem_of_getElem? hln)⟩

/-- **A move on the machine, at a witness** (`realizes_moveNR`): the segment ends at `QW` at the
next witness, at its first arrival. -/
theorem realizes_moveNA {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {b : Nat}
    {src dst : Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {j : Nat} {ps1 : PState}
    {T : List Line} (hq : QW R s j ps1 T (.run ⟨b, .move src dst :: its, m, w⟩))
    (hns : src.isSave = false) :
    ∃ n, R.QWn j ps1 T (.run ⟨b, .move src dst :: its, m, w⟩)
        (.run ⟨b, its, upd m dst (m src), w⟩) (iterN R.step n s) ∧
      (∀ i < n, R.GoodXNY Y (iterN R.step i s)) ∧
      R.SegLen j ps1 T (.run ⟨b, .move src dst :: its, m, w⟩)
        (.run ⟨b, its, upd m dst (m src), w⟩) s n :=
  let ⟨n, h1, h2, h3, _⟩ := realizes_moveNAF hR (Y := Y) hq hns
  ⟨n, h1, h2, h3⟩

end Backend.Proof
