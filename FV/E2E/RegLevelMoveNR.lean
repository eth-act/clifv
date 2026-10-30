import FV.E2E.RegLevelGoodX
import FV.E2E.RegLevelNoCall
import FV.E2E.RegLevelReadsIn


/-!
# Moves with no call state (SEM1 #537, step 2k)

`realizes_move` with `RL.GoodXNR` (docs/plans/uninit.md §5.5): a move runs unhooked lines.
-/

namespace Backend.Proof

open Backend E2E

/-- **A move on the machine**: from `Q` at a move item other than a callee restore, the machine
runs the move's lines and reaches `Q` at the next item with `MStep.move`'s store. -/
theorem realizes_moveNR {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {b : Nat}
    {src dst : Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .move src dst :: its, m, w⟩)) (hns : src.isSave = false) :
    ∃ n, Q R (iterN R.step n s) (.run ⟨b, its, upd m dst (m src), w⟩) ∧
      ∀ i < n, R.GoodXNY Y (iterN R.step i s) := by
  by_cases hds : dst.isSave = true
  · exact ⟨0, q_save hds hq, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hq' := Q.qs hq (fun _ h => by cases h)
  have hne : its ≠ [] := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, -, -, -, hchk0, -⟩ := hq'
    obtain ⟨c, k, a, out, -, -, hrun⟩ := hchk0
    obtain ⟨hk, h'⟩ := runItems_move hrun
    rintro rfl
    exact hk (runItems_nil h').1
  obtain ⟨j, vb, items, pre, c1, c2, ls1, X', ps1, psm, psm', ps2, x, hvb, hit, hsplit, hchk, hc1,
    hc2, h1, h2, h3, htr, hdrop, hpc, hst, hx, hsc⟩ := qs_split hR hq' hne
  obtain ⟨⟨c, wh, hcm⟩, hLs, hLd, hT, hchk'⟩ := move_facts hit hsplit hchk hns (by simpa using hds)
  rw [itemCode_move] at hc1
  obtain ⟨hvs, -, is, s', rfl, hmi, hex, hmo⟩ := lower_move (R.frameOk hR) R.ctx hcm
    hLs hLd hT hc1 hst.world hst.sp hst.align
  obtain ⟨ls1', hcl, hlen, hins, hpl, hrun, hint, hprog, herr⟩ :=
    run_oneLines R.ctx R.af is s s' (fun i hi => oneLine_of_moveInst R.ctx (hmi i hi)) hex hst.err
  rw [hcl ps1] at h1
  simp only [Except.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
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
  have hiter : iterN R.step ls1'.length s = s' :=
    iterN_execLines hR.layout hR.lm hR.fit ls1' j s s' hat
      (fun i t h => by obtain ⟨i', t', e, hh⟩ := hins _ h; cases e; exact hh)
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
  refine ⟨ls1'.length, qs_next hvb hit hsplit hchk' hc2 h2 h3 htr hdrop ?_ ?_ hx hsc,
    fun i hi => ?_⟩
  rotate_right
  · exact R.goodXNR_execLines hR hat
      (fun i t h => by obtain ⟨i', t', e, hh⟩ := hins _ h; cases e; exact hh)
      (codeLinesE_noTlsTail (is.map .inst) ps1 ps1 ls1' (fun n rd tmp h => by
        simp only [List.mem_map] at h
        obtain ⟨a, ha, e⟩ := h
        cases e
        exact (oneLine_of_moveInst R.ctx (hmi _ ha)).not_tls n rd tmp rfl) (hcl ps1))
      (by rw [hst.prog]) hpc hst.err hst.sp (hint _) (hrun _) hrd i hi
  · rw [relaxLines_plain hpl, hiter, execLines_pc (hrun ⟨lineOffset R.fa.lines.toList j, (R.lm[·]?)⟩),
      hpc]
    simp only [RL.pcOf, RL.L]
    rw [lineOffset_drop_ins (by simpa [RL.L] using hdrop') hins', BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add]
  · rw [hiter]
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

end Backend.Proof
