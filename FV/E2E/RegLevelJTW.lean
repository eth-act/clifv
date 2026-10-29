import FV.E2E.RegLevelJT
import FV.E2E.RegLevelGotoW
import FV.E2E.RegLevelWrites

/-!
# Jump tables on the machine with their writes (A3, #412, slice F8b)

`RegLevelJT`'s `jt_machine` and `realizes_jt` with `RL.GoodXW` (`GoodX` and the writes
`RL.WritesAt` of the unhooked instruction at the pc, which avoids the kept addresses `R.G`):
the jump-table code has no stores (`RL.writesAt_noStore`).
-/

namespace Backend.Proof

open Backend E2E


/-- **The machine runs a jump table** (its default branch possibly relaxed). -/
theorem jt_machineW {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j0 : Nat} {d : Label}
    {ts : List Label} {nr na nb : Nat} (hr : nr < 29) (ha : na < 29) (hb : nb < 29)
    (hab : na ≠ nb) {jt : Lbl} (hjt : jt ≠ .skip) {T : List Line}
    (hdrop : R.L.drop j0 = relaxLine R.far (.ins (.bcond .hs (.block d)) none) ++
      (jtTail ts (.x nr) (.x na) (.x nb) jt ++ T))
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) (hspB : spOf s = R.spB)
    (hcode : ∀ k w, R.fb.words[k]? = some w →
      Arm.read_mem_bytes 4 (R.base + BitVec.ofNat 64 (4 * k)) s = w) :
    (Arm.ConditionHolds Cond.hs.bits s = true → ∃ n jl, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      R.L[jl]? = some (.label (.block d)) ∧ ∀ i < n, R.GoodXW (iterN R.step i s)) ∧
    (Arm.ConditionHolds Cond.hs.bits s = false → ∀ i l,
      (Arm.r (.GPR (rnum nr)) s).toNat % 2 ^ 32 = i → ts[i]? = some l →
      ∃ n jl s', iterN R.step n s = s' ∧ Arm.r .PC s' = R.pcOf jl ∧
        R.L[jl]? = some (.label (.block l)) ∧
        (∀ f, f ≠ .PC → f ≠ .GPR (rnum na) → f ≠ .GPR (rnum nb) → Arm.r f s' = Arm.r f s) ∧
        s'.mem = s.mem ∧ s'.program = s.program ∧
        ∀ i < n, R.GoodXW (iterN R.step i s)) := by
  obtain ⟨n0, j1, hn0, hj1t, hj1f, -, hn1, hgx0⟩ := reach_rcbXW hR hdrop (.inl ⟨.hs, rfl⟩) (by simp)
    (Arm.ConditionHolds Cond.hs.bits s) (fun env a ha => brCond_bcond ha s)
    (fun _ env a ha => by
      simp only [Insn.invertTo] at ha
      rw [brCond_bcond ha s, condHolds_invert _ (by decide) (by decide)])
    hprog hpc herr hspB
  refine ⟨fun hhs => ⟨n0, j1, hn0, hj1t hhs, hgx0⟩, fun hhs i l hi hl => ?_⟩
  have hdrop1 : R.L.drop j1 = jtTail ts (.x nr) (.x na) (.x nb) jt ++ T := by
    rw [hj1f hhs, ← List.drop_drop, hdrop, List.drop_left]
  have hL : ∀ t ln, (jtTail ts (.x nr) (.x na) (.x nb) jt)[t]? = some ln → R.L[j1 + t]? = some ln := by
    intro t ln ht
    have := congrArg (·[t]?) hdrop1
    simp only [List.getElem?_drop] at this
    rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 ht).1]
    exact ht
  have h1 : R.L[j1]? = some (.ins (.csel (.x nb) .xzr (.x nr) .hs)) := hL 0 _ rfl
  have h2 : R.L[j1 + 1]? = some (.ins (.adr (.x na) jt)) := hL 1 _ rfl
  have h3 : R.L[j1 + 2]? = some (.ins (.load .sload32 (.x nb) (.regScaledExtended (.x na) (.x nb) .uxtw))) :=
    hL 2 _ rfl
  have h4 : R.L[j1 + 3]? = some (.ins (.aluRRR .add true (.x na) (.x na) (.x nb))) := hL 3 _ rfl
  have h5 : R.L[j1 + 4]? = some (.ins (.br (.x na))) := hL 4 _ rfl
  have h6 : R.L[j1 + 5]? = some (.label jt) := hL 5 _ rfl
  -- not taken: five more steps
  have hne : ∀ {x y : Nat}, x < 29 → y < 29 → x ≠ y → Arm.StateField.GPR (rnum x) ≠ .GPR (rnum y) :=
    fun hx hy hxy e => by injection e with e; exact rnum_ne (by omega) (by omega) hxy e
  have hnp : ∀ {x : Nat}, Arm.StateField.GPR (rnum x) ≠ .PC := fun e => by cases e
  have hpe : Arm.StateField.PC ≠ .ERR := by simp
  have hge : ∀ {x : Nat}, Arm.StateField.GPR (rnum x) ≠ .ERR := fun e => by cases e
  let X := Arm.r (.GPR (rnum nr)) s
  -- step 1: `b.hs` not taken
  have e1 : R.step s = Arm.w .PC (R.pcOf j1) s := by
    rw [hn1 hhs] at hn0; exact hn0
  -- step 2: csel
  let s1 := Arm.w .PC (R.pcOf (j1)) s
  have hp1 : s1.program = R.fb.program R.base := by simp [s1, Arm.w_program, hprog]
  have hr1 : Arm.r .ERR s1 = .None := by simp only [s1]; rw [Arm.r_of_w_different (Ne.symm hpe)]; exact herr
  obtain ⟨b1, hb1, hst1⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit h1 rfl hp1
    (by simp only [s1, Arm.r_of_w_same]; rfl) hr1
  obtain ⟨b1', hb1', hx1⟩ := exec_csel_hs (⟨lineOffset R.fa.lines.toList (j1), (R.lm[·]?)⟩) hb hr s1
  rw [hb1'] at hb1; cases hb1
  have hc1 : Arm.ConditionHolds Cond.hs.bits s1 = false := by
    rw [← hhs]; exact ConditionHolds_sameWorld (F := fun _ => True)
      (SameWorld.w_left (by simp [Masked]) (SameWorld.refl _ s)) _
  let s2 := Arm.w (.GPR (rnum nb)) X (Arm.w .PC (R.pcOf (j1 + 1)) s1)
  have e2 : R.step s1 = s2 := by
    simp only [RL.step]
    rw [hst1, hx1, hc1]
    simp only [s2, s1, Bool.false_eq_true, ite_false, Arm.r_of_w_same]
    rw [Arm.r_of_w_different hnp, RL.pcOf_succ_ins h1]
  have hp2 : s2.program = R.fb.program R.base := by simp [s2, Arm.w_program, hp1]
  have hr2 : Arm.r .ERR s2 = .None := by
    simp only [s2]; rw [Arm.r_of_w_different (Ne.symm hge), Arm.r_of_w_different (Ne.symm hpe)]; exact hr1
  have hpc2 : Arm.r .PC s2 = R.pcOf (j1 + 1) := by
    simp only [s2]; rw [Arm.r_of_w_different (Ne.symm hnp), Arm.r_of_w_same]
  -- step 3: adr
  obtain ⟨b2, hb2, hst2⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit h2 rfl hp2
    hpc2 hr2
  obtain ⟨o, ho, hx2⟩ := exec_adr ha hb2 s2
  obtain ⟨ojt, hojt, hoff, -⟩ := Insn.toArmInst_pcRel hb2 (t := jt) (reach := 2 ^ 20) (align := 1) rfl
  rw [hoff] at ho; cases ho
  have hojt' : ojt = lineOffset R.L (j1 + 5) := by
    have := labelOffsets_label hR.lm h6
    simp only [RL.L] at this ⊢
    rw [Env.target_of_ne hjt] at hojt
    simp only at hojt
    rw [hojt] at this; exact Option.some.inj this
  let A := R.base + BitVec.ofNat 64 ojt
  have hjtaddr : Arm.r .PC s2 + BitVec.ofInt 64 ((ojt : Int) - lineOffset R.fa.lines.toList (j1 + 1)) = A := by
    rw [hpc2]; simp only [RL.pcOf, RL.L, A]; rw [BitVec.add_assoc, ofNat_add_ofInt_sub]
  let s3 := Arm.w .PC (R.pcOf (j1 + 2)) (Arm.w (.GPR (rnum na)) A s2)
  have e3 : R.step s2 = s3 := by
    simp only [RL.step]
    rw [hst2, hx2, hjtaddr, hpc2, ← RL.pcOf_succ_ins h2]
  have hp3 : s3.program = R.fb.program R.base := by simp [s3, Arm.w_program, hp2]
  have hr3 : Arm.r .ERR s3 = .None := by
    simp only [s3]; rw [Arm.r_of_w_different (Ne.symm hpe), Arm.r_of_w_different (Ne.symm hge)]; exact hr2
  have hpc3 : Arm.r .PC s3 = R.pcOf (j1 + 2) := by simp only [s3, Arm.r_of_w_same]
  -- step 4: ldrsw
  obtain ⟨b3, hb3, hst3⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit h3 rfl hp3
    hpc3 hr3
  obtain ⟨b3', hb3', hx3⟩ := exec_load_line (⟨lineOffset R.fa.lines.toList (j1 + 2), (R.lm[·]?)⟩)
    R.ctx .sload32 (by simp) nb (by omega) (.regScaledExtended (.x na) (.x nb) .uxtw)
    ⟨show na ≤ 30 by omega, show nb ≤ 30 by omega, .inl rfl⟩ s3 (fun h => by cases h)
  rw [hb3'] at hb3; cases hb3
  have hXa3 : regX s3 (.x na) = A := by
    simp only [regX, s3]; rw [Arm.r_of_w_different hnp, Arm.r_of_w_same]
  have hXb3 : regX s3 (.x nb) = X := by
    simp only [regX, s3, s2]
    rw [Arm.r_of_w_different hnp, Arm.r_of_w_different (hne hb ha (Ne.symm hab)), Arm.r_of_w_same]
  have hmem3 : s3.mem = s.mem := by simp [s3, s2, s1, Arm.ArmState.mem_w_eq_mem]
  have haddr : AMode.addr R.ctx (.regScaledExtended (.x na) (.x nb) .uxtw) LoadOp.sload32.bytes s3 =
      A + BitVec.ofNat 64 (4 * i) := by
    simp only [AMode.addr, hXa3, hXb3, LoadOp.bytes]
    rw [extend_uxtw2, hi]
  -- the table word
  have hws : R.L.drop (j1 + 6) = ts.map (fun l => Line.word (.block l) jt) ++ T := by
    rw [← List.drop_drop, hdrop1]; simp [jtTail]
  have hil : i < ts.length := (List.getElem?_eq_some_iff.1 hl).1
  have hwo := lineOffset_words hws (by simp) i (by simp; omega)
  have h7 : lineOffset R.L (j1 + 6) = lineOffset R.L (j1 + 5) := by
    rw [lineOffset_succ _ _ _ h6]; simp [Line.size]
  have hwi : R.L[j1 + 6 + i]? = some (.word (.block l) jt) := by
    have := congrArg (·[i]?) hws
    simp only [List.getElem?_drop] at this
    rw [this, List.getElem?_append_left (by simpa using hil)]
    simp [hl]
  obtain ⟨wd, hwd, ⟨jtl, jbl, hjtl, -⟩, hwv⟩ := FnAsm.layout_jumpTable hR.layout hR.lm hwi
  have hwv' := hwv jtl (j1 + 5) hjtl h6
  have hal4 := (FnAsm.layout_word hR.layout hR.lm hwi rfl).1
  have hofs : lineOffset R.L (j1 + 6 + i) = ojt + 4 * i := by rw [hwo, h7, hojt']
  have hmem : Arm.read_mem_bytes 4 (A + BitVec.ofNat 64 (4 * i)) s3 = wd := by
    rw [read_mem_bytes_congr (t := s) 4 _ (fun k _ => by rw [hmem3])]
    have := hcode _ wd hwd
    simp only [RL.L] at hofs hal4
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hal4), hofs] at this
    simp only [A]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact this
  let V := (wd.signExtend 64 : BitVec 64)
  have hV : A + V = R.pcOf jtl := by
    simp only [A, V, RL.pcOf, RL.L]
    simp only [RL.L] at hojt'
    rw [show wd.signExtend 64 = BitVec.ofInt 64 wd.toInt by simp [BitVec.signExtend], hwv',
      ← hojt', BitVec.add_assoc, ofNat_add_ofInt_sub]
  let s4 := Arm.w .PC (R.pcOf (j1 + 3)) (Arm.w (.GPR (rnum nb)) V s3)
  have e4 : R.step s3 = s4 := by
    simp only [RL.step]
    rw [hst3, hx3, haddr, hpc3, ← RL.pcOf_succ_ins h3]
    simp only [ldX, hmem]; rfl
  have hp4 : s4.program = R.fb.program R.base := by simp [s4, Arm.w_program, hp3]
  have hr4 : Arm.r .ERR s4 = .None := by
    simp only [s4]; rw [Arm.r_of_w_different (Ne.symm hpe), Arm.r_of_w_different (Ne.symm hge)]; exact hr3
  have hpc4 : Arm.r .PC s4 = R.pcOf (j1 + 3) := by simp only [s4, Arm.r_of_w_same]
  -- step 5: add
  obtain ⟨b4, hb4, hst4⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit h4 rfl hp4
    hpc4 hr4
  obtain ⟨b4', hb4', hx4⟩ := exec_add64 (⟨lineOffset R.fa.lines.toList (j1 + 3), (R.lm[·]?)⟩) ha ha hb s4
  rw [hb4'] at hb4; cases hb4
  have hXa4 : Arm.r (.GPR (rnum na)) s4 = A := by
    simp only [s4, s3]
    rw [Arm.r_of_w_different hnp, Arm.r_of_w_different (hne ha hb hab), Arm.r_of_w_different hnp,
      Arm.r_of_w_same]
  have hXb4 : Arm.r (.GPR (rnum nb)) s4 = V := by
    simp only [s4]; rw [Arm.r_of_w_different hnp, Arm.r_of_w_same]
  let s5 := Arm.w (.GPR (rnum na)) (A + V) (Arm.w .PC (R.pcOf (j1 + 4)) s4)
  have e5 : R.step s4 = s5 := by
    simp only [RL.step]
    rw [hst4, hx4, hXa4, hXb4, hpc4, ← RL.pcOf_succ_ins h4]
  have hp5 : s5.program = R.fb.program R.base := by simp [s5, Arm.w_program, hp4]
  have hr5 : Arm.r .ERR s5 = .None := by
    simp only [s5]; rw [Arm.r_of_w_different (Ne.symm hge), Arm.r_of_w_different (Ne.symm hpe)]; exact hr4
  have hpc5 : Arm.r .PC s5 = R.pcOf (j1 + 4) := by
    simp only [s5]; rw [Arm.r_of_w_different (Ne.symm hnp), Arm.r_of_w_same]
  -- step 6: br
  obtain ⟨b5, hb5, hst5⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit h5 rfl hp5
    hpc5 hr5
  obtain ⟨b5', hb5', hx5⟩ := exec_br (⟨lineOffset R.fa.lines.toList (j1 + 4), (R.lm[·]?)⟩) ha s5
  rw [hb5'] at hb5; cases hb5
  let s6 := Arm.w .PC (A + V) s5
  have e6 : R.step s5 = s6 := by
    simp only [RL.step]
    rw [hst5, hx5]
    simp only [s5, s6, Arm.r_of_w_same]
  have hsa : Arm.StateField.GPR 31#5 ≠ .GPR (rnum na) := fun e => by
    injection e with e; exact rnum_ne31 ha e.symm
  have hsb : Arm.StateField.GPR 31#5 ≠ .GPR (rnum nb) := fun e => by
    injection e with e; exact rnum_ne31 hb e.symm
  have hsp : Arm.StateField.GPR 31#5 ≠ .PC := by simp
  refine ⟨6, jtl, s6, ?_, by simp only [s6, Arm.r_of_w_same, hV], hjtl, ?_, ?_, ?_, fun k hk => ?_⟩
  · simp only [iterN]; rw [e1]; exact (by rw [e2, e3, e4, e5, e6])
  rotate_left 3
  · have hg : ∀ {u : Arm.ArmState}, spOf u = spOf s → R.Good u := fun h => .inr (h.trans hspB)
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hgx0 0 (by rw [hn1 hhs]; omega)
    · have e : iterN R.step 1 s = s1 := by simp only [iterN]; rw [e1]
      rw [e]
      exact ⟨RL.goodX_ofIns hR h1 (by simp only [s1, Arm.r_of_w_same]) rfl rfl
        (hg (Arm.r_of_w_different hsp)) hr1 hp1 (by rw [e2]; exact RL.nextOk_succ h1 rfl hpc2)
        (RL.readsAt_noLoad hR h1 (by simp only [s1, Arm.r_of_w_same]) rfl),
        RL.writesAt_noStore hR h1 (by simp only [s1, Arm.r_of_w_same]) rfl⟩
    · have e : iterN R.step 2 s = s2 := by simp only [iterN]; rw [e1, e2]
      rw [e]
      exact ⟨RL.goodX_ofIns hR h2 hpc2 rfl rfl
        (hg (by simp only [spOf, s2, s1, Arm.r_of_w_different hsb, Arm.r_of_w_different hsp]))
        hr2 hp2 (by rw [e3]; exact RL.nextOk_succ h2 rfl hpc3) (RL.readsAt_noLoad hR h2 hpc2 rfl),
        RL.writesAt_noStore hR h2 hpc2 rfl⟩
    · have e : iterN R.step 3 s = s3 := by simp only [iterN]; rw [e1, e2, e3]
      rw [e]
      exact ⟨RL.goodX_ofIns hR h3 hpc3 rfl rfl
        (hg (by simp only [spOf, s3, s2, s1, Arm.r_of_w_different hsa, Arm.r_of_w_different hsb,
          Arm.r_of_w_different hsp])) hr3 hp3 (by rw [e4]; exact RL.nextOk_succ h3 rfl hpc4)
        (RL.readsAt_of_line hR h3 hpc3 fun _ env a hab3 p hp q hq => by
          rw [memReads_load R.ctx (show FinalAM LoadOp.sload32.bytes
              (.regScaledExtended (.x na) (.x nb) .uxtw) from
              ⟨show na ≤ 30 by omega, show nb ≤ 30 by omega, .inl rfl⟩)
            (fun h => by cases h) hab3, List.mem_singleton] at hp
          subst hp
          simp only [LoadOp.bytes] at hq
          refine .inr (.inl ⟨j1 + 6 + i, _, _, hwi, q, hq, ?_⟩)
          simp only [RL.pcOf]
          rw [haddr, hofs, BitVec.ofNat_add]
          simp only [A, BitVec.add_assoc]),
        RL.writesAt_noStore hR h3 hpc3 rfl⟩
    · have e : iterN R.step 4 s = s4 := by simp only [iterN]; rw [e1, e2, e3, e4]
      rw [e]
      exact ⟨RL.goodX_ofIns hR h4 hpc4 rfl rfl
        (hg (by simp only [spOf, s4, s3, s2, s1, Arm.r_of_w_different hsa, Arm.r_of_w_different hsb,
          Arm.r_of_w_different hsp])) hr4 hp4 (by rw [e5]; exact RL.nextOk_succ h4 rfl hpc5) (RL.readsAt_noLoad hR h4 hpc4 rfl),
        RL.writesAt_noStore hR h4 hpc4 rfl⟩
    · have e : iterN R.step 5 s = s5 := by simp only [iterN]; rw [e1, e2, e3, e4, e5]
      rw [e]
      exact ⟨RL.goodX_ofIns hR h5 hpc5 rfl rfl
        (hg (by simp only [spOf, s5, s4, s3, s2, s1, Arm.r_of_w_different hsa,
          Arm.r_of_w_different hsb, Arm.r_of_w_different hsp])) hr5 hp5
        (by rw [e6]; exact RL.nextOk_label hjtl (by simp only [s6, Arm.r_of_w_same, hV]))
        (RL.readsAt_noLoad hR h5 hpc5 rfl),
        RL.writesAt_noStore hR h5 hpc5 rfl⟩
  · intro f hfp hfa hfb
    simp only [s6, s5, s4, s3, s2, s1]
    rw [Arm.r_of_w_different hfp, Arm.r_of_w_different hfa, Arm.r_of_w_different hfp,
      Arm.r_of_w_different hfp, Arm.r_of_w_different hfb, Arm.r_of_w_different hfp,
      Arm.r_of_w_different hfa, Arm.r_of_w_different hfb, Arm.r_of_w_different hfp,
      Arm.r_of_w_different hfp]
  · simp [s6, s5, s4, s3, s2, s1, Arm.ArmState.mem_w_eq_mem]
  · simp [s6, s5, s4, s3, s2, s1, Arm.w_program]


/-- **A jump table on the machine**: from `Q` at a `jtSequence` item, the machine reaches `Q`
at an `MStep` successor (the temporaries havocked to the machine's values). -/
theorem realizes_jtW {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {c' : MConf CV Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {d : Label}
    {ts : List Label} {ridx t1 t2 : Reg}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.jtSequence d ts ridx t1 t2))
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c') :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.GoodXW (iterN R.step i s) := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  have hok := ctlCheck_inst hck hvb hi
  simp only [ctlInstOk, Bool.and_eq_true] at hok
  obtain ⟨⟨hr0, ha0⟩, hb0⟩ := hok
  obtain ⟨vr, rfl⟩ := isVregInt_iff hr0
  obtain ⟨va, rfl⟩ := isVregInt_iff ha0
  obtain ⟨vb', rfl⟩ := isVregInt_iff hb0
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, rfl, hit, hsplit,
    hasg, hc1', hops, hstat, hchk', hc2, h1, h2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  have hops' : ops = #[⟨vr, .int, .use, .early, .reg⟩, ⟨va, .int, .def, .early, .reg⟩,
      ⟨vb', .int, .def, .early, .reg⟩] := by
    have e : (MInst.jtSequence d ts (.vreg vr .int) (.vreg va .int) (.vreg vb' .int)).operands =
        .ok #[⟨vr, .int, .use, .early, .reg⟩, ⟨va, .int, .def, .early, .reg⟩,
          ⟨vb', .int, .def, .early, .reg⟩] := rfl
    rw [e] at hops; injection hops with h; exact h.symm
  subst hops'
  obtain ⟨hsz, hloc, hnd, -⟩ := checkStatic_facts hstat
  obtain ⟨r0, r1, r2, rfl⟩ := regs3 (by simpa using hsz.symm)
  have hl0 := (hloc (⟨vr, .int, .use, .early, .reg⟩, .reg r0) (by simp)).1
  have hl1 := (hloc (⟨va, .int, .def, .early, .reg⟩, .reg r1) (by simp)).1
  have hl2 := (hloc (⟨vb', .int, .def, .early, .reg⟩, .reg r2) (by simp)).1
  obtain ⟨nr, rfl, hnr, -, -, hnr18⟩ := locOk_int hl0
  obtain ⟨na, rfl, hna, -, -, hna18⟩ := locOk_int hl1
  obtain ⟨nb, rfl, hnb, -, -, hnb18⟩ := locOk_int hl2
  have hab : na ≠ nb := by
    intro e; subst e
    simp [Operand.isDef] at hnd
  have hasg' : (MInst.jtSequence d ts (.vreg vr .int) (.vreg va .int) (.vreg vb' .int)).assign
      #[.x nr, .x na, .x nb] = .ok (.jtSequence d ts (.x nr) (.x na) (.x nb)) := rfl
  rw [hasg'] at hasg; cases hasg
  obtain rfl : c1 = [.inst (.jtSequence d ts (.x nr) (.x na) (.x nb))] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  have hl1 := codeLinesE_single h1
  simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
  obtain ⟨hls1, -⟩ := hl1
  have hdrop' : R.L.drop j0 = relaxLine R.far (.ins (.bcond .hs (.block d)) none) ++
      (jtTail ts (.x nr) (.x na) (.x nb) (.jt ps1.jt) ++
        (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T)) := by
    rw [hdrop, ← hls1, show [Line.ins (.bcond .hs (.block d)), .ins (.csel (.x nb) .xzr (.x nr) .hs),
      .ins (.adr (.x na) (.jt ps1.jt)),
      .ins (.load .sload32 (.x nb) (.regScaledExtended (.x na) (.x nb) .uxtw)),
      .ins (.aluRRR .add true (.x na) (.x na) (.x nb)), .ins (.br (.x na)), .label (.jt ps1.jt)] ++
      ts.map (fun l => Line.word (.block l) (.jt ps1.jt)) = jtBody d ts (.x nr) (.x na) (.x nb) (.jt ps1.jt)
      from rfl, ftList_jt, relaxLines_append, relaxLines_jtBody, List.append_assoc, List.append_assoc]
  obtain ⟨hmTaken, hmNot⟩ := jt_machineW hR hnr hna hnb hab (by simp) hdrop' hst.prog hpc hst.err hst.sp
    hst.code
  obtain ⟨c, ins, _, hc, -⟩ := hR.check
  obtain ⟨preds, hcfg⟩ := hc.cfg
  obtain ⟨t0, tss, hback, hss, hlab⟩ := cfg_block hcfg hvb
  cases h with
  | @op b k allocs its m w vb'' i ops outs outs' w' ctl m2 c' hvb' hi' hops' hsz' hsem hlen hho hcl hn =>
  rw [hvb] at hvb'; cases hvb'
  rw [hi] at hi'; cases hi'
  rw [hops] at hops'; cases hops'
  have hU : (((#[(⟨vr, .int, .use, .early, .reg⟩ : Operand), ⟨va, .int, .def, .early, .reg⟩,
      ⟨vb', .int, .def, .early, .reg⟩].zip (#[Reg.x nr, .x na, .x nb].map Loc.reg)).toList.filter
      (·.1.isUse)).map (m ·.2)) = [regVal s (.x nr)] := by
    have := hst.store (.reg (.x nr)) (fun r e => by cases e; exact (locOk_int hl0 |> fun ⟨_, e, _⟩ => by
      cases e; simp only [CheckCtx.locOk, Bool.and_eq_true] at hl0; exact hl0.2)) trivial
    simp [Operand.isUse, this, locVal]
  rw [hU] at hsem
  have hhs : Arm.ConditionHolds Cond.hs.bits w = Arm.ConditionHolds Cond.hs.bits s :=
    (ConditionHolds_sameWorld hst.world _).symm
  simp only [RL.sem, csemV, csem] at hsem
  rw [hhs] at hsem
  -- the successor
  have hti : t0 = MInst.jtSequence d ts (.vreg vr .int) (.vreg va .int) (.vreg vb' .int) := by
    cases hn with
    | goto hk1 _ _ =>
      rw [Array.back?_eq_getElem?, show vb.insts.size - 1 = k by omega, hi] at hback
      cases hback; rfl
    | next _ => split at hsem <;> (try split at hsem) <;> simp at hsem
    | ret h => cases h
    | halt => split at hsem <;> (try split at hsem) <;> simp at hsem
  subst hti
  -- the store the chosen successor gets: the temporaries hold the machine's values
  have hstore : ∀ (o1 o2 : CV),
      writeM (writeM m ((((#[(⟨vr, .int, .use, .early, .reg⟩ : Operand), ⟨va, .int, .def, .early, .reg⟩,
        ⟨vb', .int, .def, .early, .reg⟩].zip (#[Reg.x nr, .x na, .x nb].map Loc.reg)).toList.filter
        (·.1.isDef)).zip [o1, o2]).filter (·.1.1.isEarly)))
        ((((#[(⟨vr, .int, .use, .early, .reg⟩ : Operand), ⟨va, .int, .def, .early, .reg⟩,
        ⟨vb', .int, .def, .early, .reg⟩].zip (#[Reg.x nr, .x na, .x nb].map Loc.reg)).toList.filter
        (·.1.isDef)).zip [o1, o2]).filter (·.1.1.isLate)) =
      upd (upd m (.reg (.x na)) o1) (.reg (.x nb)) o2 := by
    intro o1 o2
    simp [Operand.isDef, Operand.isEarly, Operand.isLate, writeM]
  have hcl0 : ∀ (m' : Loc → CV), Clobbered ckeep
      (MInst.jtSequence d ts (.vreg vr .int) (.vreg va .int) (.vreg vb' .int)).clobbers m' m' :=
    fun m' => ⟨fun _ _ => rfl, fun c hc => by simp [MInst.clobbers] at hc⟩
  cases hn with
  | next _ => split at hsem <;> (try split at hsem) <;> simp at hsem
  | ret h => cases h
  | halt => split at hsem <;> (try split at hsem) <;> simp at hsem
  | @goto jj st items' hk1 hsucc hitems =>
  have hsucc' := hsucc
  simp only [succOf, hcfg, hss, Option.bind_some] at hsucc'
  have hst0 : st ≠ 0 := ctlCheck_succ hck hsucc
  obtain ⟨vs, hvs, hlj⟩ := hlab _ st hsucc'
  have hw2 : w' = w ∧ outs.length = 2 := by
    split at hsem
    · simp only [Option.some.injEq, Prod.mk.injEq] at hsem; rw [← hsem.1, ← hsem.2.1]; exact ⟨rfl, rfl⟩
    · split at hsem
      · simp only [Option.some.injEq, Prod.mk.injEq] at hsem; rw [← hsem.1, ← hsem.2.1]; exact ⟨rfl, rfl⟩
      · cases hsem
  obtain ⟨hw', hout2⟩ := hw2
  subst w'
  -- the MStep with the machine's temporaries, and `Q` at the successor
  have fin : ∀ (s' : Arm.ArmState) (n jl : Nat), iterN R.step n s = s' →
      Arm.r .PC s' = R.pcOf jl → R.L[jl]? = some (.label (.block vs.label)) →
      (∀ f, f ≠ .PC → f ≠ .GPR (rnum na) → f ≠ .GPR (rnum nb) → Arm.r f s' = Arm.r f s) →
      s'.mem = s.mem → s'.program = s.program → (∀ i < n, R.GoodXW (iterN R.step i s)) →
      ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k (#[Reg.x nr, .x na, .x nb].map Loc.reg) :: its, m, w⟩) c'' ∧
        Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.GoodXW (iterN R.step i s) := by
    intro s' n jl hn hpc' hjl hf hmem hprog hsp
    have hsem' : R.sem (.jtSequence d ts (.vreg vr .int) (.vreg va .int) (.vreg vb' .int))
        (((#[(⟨vr, .int, .use, .early, .reg⟩ : Operand), ⟨va, .int, .def, .early, .reg⟩,
          ⟨vb', .int, .def, .early, .reg⟩].zip (#[Reg.x nr, .x na, .x nb].map Loc.reg)).toList.filter
          (·.1.isUse)).map (m ·.2)) w = some (outs, w, .goto jj) := by
      rw [hU]; simp only [RL.sem, csemV, csem, hhs]; exact hsem
    refine ⟨n, _, MStep.op (outs' := [regVal s' (.x na), regVal s' (.x nb)]) (w' := w) hvb hi hops hsz'
      hsem' hlen ⟨by rw [hout2]; rfl,
        fun h => by simp [havocFrom, MInst.keptDefs, MInst.isBranch] at h,
        fun n h => by simp [havocFrom, MInst.keptDefs, MInst.isBranch] at h; subst h; rfl⟩
      (hcl0 _) (MNext.goto hk1 hsucc hitems), ?_, hsp⟩
    rw [hstore, hn]
    exact q_entry hR hst0 hvs hitems hjl hpc' (stRel_regs hst hna hnb hna18 hnb18 hf hmem hprog)
  -- which successor
  split at hsem
  · rename_i hhs'
    simp only [Option.some.injEq, Prod.mk.injEq] at hsem
    obtain ⟨-, -, hj⟩ := hsem
    injection hj with hj
    subst hj
    obtain ⟨n, jl, hn', hjl, hsp⟩ := hmTaken hhs'
    simp only [MInst.targets, List.getElem?_cons_zero, Option.some.injEq] at hlj
    rw [hlj] at hjl
    exact fin _ n jl hn' (Arm.r_of_w_same ..) hjl
      (fun f hf _ _ => Arm.r_of_w_different hf) (by simp [Arm.ArmState.mem_w_eq_mem])
      (by simp [Arm.w_program]) hsp
  · rename_i hhs'
    split at hsem
    · rename_i hlt
      simp only [Option.some.injEq, Prod.mk.injEq] at hsem
      obtain ⟨-, -, hj⟩ := hsem
      injection hj with hj
      subst hj
      simp only [MInst.targets, List.getElem?_cons_succ] at hlj
      obtain ⟨n, jl, s', hn', hpc', hjl, hf, hmem, hprog, hsp⟩ := hmNot (by simpa using hhs') _ vs.label
        (by simp [lo64, regVal, BitVec.toNat_setWidth]) hlj
      exact fin s' n jl hn' hpc' hjl hf hmem hprog hsp
    · cases hsem


end Backend.Proof
