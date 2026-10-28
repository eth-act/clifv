import FV.E2E.RegLevelSegAlign
import FV.E2E.RegLevelMoveNR

/-!
# Moves, at a witness, with their segment length (SEM1 #537, item (3), route (a))

`realizes_moveNR` from `QW` at the witness `(j, ps1, T)`: the move ends at `QW` at
`RL.nextW`'s witness, and its segment is the first arrival at that line (`RL.SegLen`).
-/

namespace Backend.Proof

open Backend E2E

theorem RL.segLen_straight_iff {R : RL} {j : Nat} {ps1 : PState} {T : List Line} {b : Nat}
    {it : RItem} {its : List RItem} {m m' : Loc → CV} {w w' : Arm.ArmState} :
    R.EmptyW j ps1 T (.run ⟨b, it :: its, m, w⟩) (.run ⟨b, its, m', w'⟩) ↔
      (R.straightW b it j ps1 T).1 = j := by
  unfold RL.EmptyW
  rw [if_pos (by simp [RL.Straight]), RL.nextW_straight]

/-- **A straight run of instruction lines is a first arrival at the line after it.** -/
theorem RL.firstArr_lines {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j n : Nat}
    (hins : ∀ k < n, ∃ x t, R.L[j + k]? = some (.ins x t))
    (hpcs : ∀ i ≤ n, Arm.r .PC (iterN R.step i s) = R.pcOf (j + i)) :
    FirstArr R.step s n (R.pcOf (j + n)) := by
  refine ⟨hpcs n (Nat.le_refl _), fun i hi0 hin => ?_⟩
  rw [hpcs i (by omega)]
  obtain ⟨x0, t0, h0⟩ := hins 0 (by omega)
  obtain ⟨x1, t1, h1⟩ := hins i hin
  exact RL.pcOf_ne hR (by simpa using h0) (by omega) h1 (by omega)

/-- **A move on the machine, at a witness** (`realizes_moveNR`): the segment ends at `QW` at the
next witness, at its first arrival. -/
theorem realizes_moveNA {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {b : Nat}
    {src dst : Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {j : Nat} {ps1 : PState}
    {T : List Line} (hq : QW R s j ps1 T (.run ⟨b, .move src dst :: its, m, w⟩)) :
    ∃ n, QW R (iterN R.step n s)
        (R.nextW j ps1 T (.run ⟨b, .move src dst :: its, m, w⟩)
          (.run ⟨b, its, upd m dst (m src), w⟩)).1
        (R.nextW j ps1 T (.run ⟨b, .move src dst :: its, m, w⟩)
          (.run ⟨b, its, upd m dst (m src), w⟩)).2.1
        (R.nextW j ps1 T (.run ⟨b, .move src dst :: its, m, w⟩)
          (.run ⟨b, its, upd m dst (m src), w⟩)).2.2
        (.run ⟨b, its, upd m dst (m src), w⟩) ∧
      (∀ i < n, R.GoodXNY Y (iterN R.step i s)) ∧
      R.SegLen j ps1 T (.run ⟨b, .move src dst :: its, m, w⟩)
        (.run ⟨b, its, upd m dst (m src), w⟩) s n := by
  obtain ⟨vb, items, pre, code, ls, ps2, hvb, hit, hsplit, hchk, hcode, hls, htr, hdrop,
    hpc, hst⟩ := hq
  obtain ⟨⟨c, wh, hcm⟩, hLs, hLd, hT, hchk'⟩ := move_facts hit hsplit hchk
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  have hc1o := hc1
  rw [itemCode_move] at hc1
  obtain ⟨ls1, ls2, psm, h1, h2, rfl⟩ := codeLinesE_append _ _ _ _ _ hls
  have h1o := h1
  obtain ⟨hvs, -, is, s', rfl, hmi, hex, hmo⟩ := lower_move (R.frameOk hR) R.ctx hcm
    hLs hLd hT hc1 hst.world hst.sp hst.align
  obtain ⟨ls1', hcl, hlen, hins, hpl, hrun, hint, hprog, herr⟩ :=
    run_oneLines R.ctx R.af is s s' (fun i hi => oneLine_of_moveInst R.ctx (hmi i hi)) hex hst.err
  rw [hcl ps1] at h1
  simp only [Except.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  have hW : R.nextW j ps1 T (.run ⟨b, .move src dst :: its, m, w⟩)
      (.run ⟨b, its, upd m dst (m src), w⟩) = (j + ls1'.length, ps1, T) := by
    rw [RL.nextW_straight, RL.straightW_eq hvb hc1o h1o, relaxLines_plain hpl]
  rw [hW]
  -- the lines at `j`
  have hZ : ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  have hdrop' : R.L.drop j = ls1' ++ (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T) := by
    rw [hdrop, List.append_assoc, ftR_plain_append _ _ _ hpl hZ, List.append_assoc]
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
  refine ⟨ls1'.length, ⟨vb, items, pre ++ [.move src dst], c2, ls2, ps2, hvb,
    hit, by rw [hsplit]; simp, hchk', hc2, h2, htr, ?_, ?_, ?_⟩, fun i hi => ?_, ?_, ?_⟩
  · rw [← List.drop_drop, hdrop', List.drop_left]
  · exact hpcs _ (Nat.le_refl _)
  · rw [hiter]
    have hsp' : spOf s' = R.spB := hmo.sp
    have hw' := hmo.world
    refine ⟨move_agree hst.store hvs hLs hmo.store, hw', herr, by rw [hprog, hst.prog], hsp',
      align_of_sp (by rw [hsp', hst.sp]) hst.align, fun hframe => ?_,
      code_frameKeep hR hmo.mem hst.code,
      fun a ha => (hmo.mem a (RL.G_not_slot hR ha)).trans (hst.gkeep a ha)⟩
    rw [← hst.fplr hframe]
    apply read_mem_bytes_congr
    intro k hk
    exact hmo.mem _ (fun o ho => by
      have := fplr_outside hR hframe k hk o ho
      rwa [show R.spB = spOf s by rw [hst.sp]] at this ⊢)
  · exact R.goodXNR_execLines hR hat hhook
      (codeLinesE_noTlsTail (is.map .inst) ps1 ps1 ls1' (fun n rd tmp h => by
        simp only [List.mem_map] at h
        obtain ⟨a, ha, e⟩ := h
        cases e
        exact (oneLine_of_moveInst R.ctx (hmi _ ha)).not_tls n rd tmp rfl) (hcl ps1))
      (by rw [hst.prog]) hpc hst.err hst.sp (hint _) (hrun _) hrd i hi
  · rw [hW]
    refine RL.firstArr_lines hR (fun k hk => ?_) hpcs
    obtain ⟨ln, hln⟩ : ∃ ln, ls1'[k]? = some ln := ⟨_, List.getElem?_eq_getElem hk⟩
    obtain ⟨x, t, rfl⟩ := hins' _ (List.mem_of_getElem? hln)
    exact ⟨x, t, hat k _ hln⟩
  · rw [RL.segLen_straight_iff, RL.nextW_straight.symm.trans hW]
    simp
end Backend.Proof
