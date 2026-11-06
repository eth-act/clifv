import FV.E2E.RegLevelGoodXNR
import FV.E2E.RegLevelGotoNA
import FV.E2E.RegLevelJT

/-!
# Jump tables, at a witness (SEM1 #537, item (3), route (a))

`jt_machineNR` with where the states are (`RL.SegIn`), and `realizes_jtNR` from `QW`: the chosen
successor at its entry witness, reached at the first arrival.
-/

namespace Backend.Proof

open Backend E2E

/-- The lines of a jump-table tail hold no frame-record line and no `ret`. -/
theorem frLine_jtTail (ts : List Label) (r a b : Reg) (jt : Lbl) :
    ∀ x t, Line.ins x t ∈ jtTail ts r a b jt → x.frLine = false := by
  intro x t hx
  simp only [jtTail, List.mem_cons, List.mem_append, List.mem_map, Line.ins.injEq, reduceCtorEq,
    List.not_mem_nil, or_false, false_or, and_false, exists_false] at hx
  rcases hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl

/-- **`jt_machineNA` with the segment's lines** (`RL.FRFree`). -/
theorem jt_machineNAF {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {j0 : Nat}
    {d : Label}
    {ts : List Label} {nr na nb : Nat} (hr : nr < 29) (ha : na < 29) (hb : nb < 29)
    (hab : na ≠ nb) {jt : Lbl} (hjt : jt ≠ .skip) {bc : Line} {W T : List Line}
    (hdrop : R.L.drop j0 = relaxLine R.far bc ++
      (jtHead ts (.x nr) (.x na) (.x nb) jt ++ W ++ T))
    (hbc : ∃ l', bc = .ins (.bcond .hs l') none ∧
      RepLbl (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) d l')
    (hW : ∀ (i : Nat) (l : Label), ts[i]? = some l → ∃ l', W[i]? = some (Line.word l' jt) ∧
      RepLbl (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) l l')
    (hWl : W.length = ts.length)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) (hspB : spOf s = R.spB)
    (hcode : ∀ k w, R.fb.words[k]? = some w →
      Arm.read_mem_bytes 4 (R.base + BitVec.ofNat 64 (4 * k)) s = w) :
    (Arm.ConditionHolds Cond.hs.bits s = true → ∃ n jl lim, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      RepL R.af (planOwn R.fa.k R.af) R.L d jl ∧ (∀ i < n, R.GoodXNY Y (iterN R.step i s)) ∧
      R.SegIn s n j0 lim ∧ R.FRFree s n) ∧
    (Arm.ConditionHolds Cond.hs.bits s = false → ∀ i l,
      (Arm.r (.GPR (rnum nr)) s).toNat % 2 ^ 32 = i → ts[i]? = some l →
      ∃ n jl lim s', iterN R.step n s = s' ∧ Arm.r .PC s' = R.pcOf jl ∧
        RepL R.af (planOwn R.fa.k R.af) R.L l jl ∧
        (∀ f, f ≠ .PC → f ≠ .GPR (rnum na) → f ≠ .GPR (rnum nb) → Arm.r f s' = Arm.r f s) ∧
        s'.mem = s.mem ∧ s'.program = s.program ∧
        (∀ i < n, R.GoodXNY Y (iterN R.step i s)) ∧ R.SegIn s n j0 lim ∧ R.FRFree s n) := by
  obtain ⟨l', rfl, hrepd⟩ := hbc
  have hnskip : l' ≠ .skip := by
    obtain ⟨l0, -, rfl, -, -⟩ := hrepd
    simp
  have hne0 : relaxLine R.far (.ins (.bcond .hs l') none) ≠ [] := fun h => by
    obtain ⟨_, _, hy⟩ := relaxLine_ins_head R.far (.bcond .hs l') none
    rw [h] at hy
    cases hy
  have hfl0 := frLine_relaxLine R.far (ln := .ins (.bcond .hs l') none)
    fun x t e => by cases e; rfl
  obtain ⟨n0, j1, hn0, hj1t, hj1f, -, hn1, hgx0, hseg0, -⟩ := reach_rcbXNA (Y := Y) hR hdrop
    (.inl ⟨.hs, rfl⟩) hnskip
    (Arm.ConditionHolds Cond.hs.bits s) (fun env a ha => brCond_bcond ha s)
    (fun _ env a ha => by
      simp only [Insn.invertTo] at ha
      rw [brCond_bcond ha s, condHolds_invert _ (by decide) (by decide)])
    hprog hpc herr hspB
  refine ⟨fun hhs => ?_, fun hhs i l hi hl => ?_⟩
  · obtain ⟨-, jl0, hjl0, hrep0⟩ := repLbl_line hR hrepd
    have hj1 : j1 = jl0 := labelOffsets_uniq hR.lm (hj1t hhs) hjl0
    refine ⟨n0, jl0, _, ?_, hrep0, hgx0, hseg0,
      RL.frFree_segIn hR hdrop (Nat.le_refl _) hne0 hfl0 hpc hseg0⟩
    rw [hj1] at hn0; exact hn0
  have hdrop1 : R.L.drop j1 = jtHead ts (.x nr) (.x na) (.x nb) jt ++ W ++ T := by
    rw [hj1f hhs, ← List.drop_drop, hdrop, List.drop_left]
  have hL : ∀ t ln, (jtHead ts (.x nr) (.x na) (.x nb) jt ++ W ++ T)[t]? = some ln →
      R.L[j1 + t]? = some ln := by
    intro t ln ht
    have h1 : R.L.drop j1 = jtHead ts (.x nr) (.x na) (.x nb) jt ++ W ++ T := hdrop1
    have h2 := congrArg (·[t]?) h1
    simp only [List.getElem?_drop] at h2
    rw [h2]
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
  have hil : i < ts.length := (List.getElem?_eq_some_iff.1 hl).1
  obtain ⟨l2, hwiW, hrepw⟩ := hW i l hl
  have hhead : (jtHead ts (.x nr) (.x na) (.x nb) jt).length = 6 := by simp [jtHead]
  have hdW : R.L.drop (j1 + 6) = W ++ T := by
    rw [← List.drop_drop, hdrop1, List.append_assoc, ← hhead, List.drop_left]
  have hWw : ∀ ln ∈ W, ∃ x y, ln = .word x y := by
    intro ln hln
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hln
    have hkW : k < W.length := by
      simpa using (List.getElem?_eq_some_iff.1 hk).1
    rw [hWl] at hkW
    obtain ⟨l3, hl3⟩ : ∃ l3, ts[k]? = some l3 := ⟨_, List.getElem?_eq_getElem hkW⟩
    obtain ⟨l4, hw4, -⟩ := hW k l3 hl3
    rw [hw4] at hk
    exact ⟨_, _, (Option.some.inj hk).symm⟩
  have hwo := lineOffset_words hdW hWw i (by rw [hWl]; omega)
  have h7 : lineOffset R.L (j1 + 6) = lineOffset R.L (j1 + 5) := by
    rw [lineOffset_succ _ _ _ h6]; simp [Line.size]
  have hwi : R.L[j1 + 6 + i]? = some (Line.word l2 jt) := by
    have hcon := congrArg (·[i]?) hdW
    simp only [List.getElem?_drop] at hcon
    rw [hcon, List.getElem?_append_left (by rw [hWl]; omega)]
    exact hwiW
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
  have ei1 : iterN R.step 1 s = s1 := by simp only [iterN]; rw [e1]
  have ei2 : iterN R.step 2 s = s2 := by simp only [iterN]; rw [e1, e2]
  have ei3 : iterN R.step 3 s = s3 := by simp only [iterN]; rw [e1, e2, e3]
  have ei4 : iterN R.step 4 s = s4 := by simp only [iterN]; rw [e1, e2, e3, e4]
  have ei5 : iterN R.step 5 s = s5 := by simp only [iterN]; rw [e1, e2, e3, e4, e5]
  have hj1 : j1 = j0 + (relaxLine R.far (.ins (.bcond .hs l') none)).length := hj1f hhs
  have hlt : j0 < j1 := by
    rw [hj1]
    have := relaxLines_single_ne R.far (.ins (.bcond .hs l') none)
    simp only [relaxLines, List.flatMap_cons, List.flatMap_nil, List.append_nil] at this
    omega
  have hseg : R.SegIn s 6 j0 (j1 + 5) := by
    obtain ⟨x0, t0, hx0⟩ := hseg0.2.1 j0 (Nat.le_refl _) (by omega)
    refine ⟨fun i h0 hi => ?_, fun k h1' h2' => ?_, ⟨fun h => absurd h (by omega),
      fun h' => absurd hx0 (h' _ _)⟩⟩
    · have : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · exact ⟨j1, _, _, hlt, by omega, h1, by rw [ei1]; simp only [s1, Arm.r_of_w_same]⟩
      · exact ⟨j1 + 1, _, _, by omega, by omega, h2, by rw [ei2]; exact hpc2⟩
      · exact ⟨j1 + 2, _, _, by omega, by omega, h3, by rw [ei3]; exact hpc3⟩
      · exact ⟨j1 + 3, _, _, by omega, by omega, h4, by rw [ei4]; exact hpc4⟩
      · exact ⟨j1 + 4, _, _, by omega, by omega, h5, by rw [ei5]; exact hpc5⟩
    · rcases Nat.lt_or_ge k j1 with hk | hk
      · exact hseg0.2.1 k h1' (by omega)
      · have : k = j1 ∨ k = j1 + 1 ∨ k = j1 + 2 ∨ k = j1 + 3 ∨ k = j1 + 4 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl
        · exact ⟨_, _, h1⟩
        · exact ⟨_, _, h2⟩
        · exact ⟨_, _, h3⟩
        · exact ⟨_, _, h4⟩
        · exact ⟨_, _, h5⟩
  obtain ⟨-, jl0, hjl0, hrep0⟩ := repLbl_line hR hrepw
  have hjtl0 : jtl = jl0 := labelOffsets_uniq hR.lm hjtl hjl0
  have hdrop2 : R.L.drop j0 = (relaxLine R.far (.ins (.bcond .hs l') none) ++
      jtHead ts (.x nr) (.x na) (.x nb) jt) ++ (W ++ T) := by
    rw [hdrop]; simp only [List.append_assoc]
  refine ⟨6, jl0, j1 + 5, s6, ?_, by simp only [s6, Arm.r_of_w_same, hV]; rw [hjtl0], hrep0, ?_, ?_,
    ?_, fun k hk => ?_, hseg, RL.frFree_segIn hR hdrop2 (by simp [jtHead]; omega)
      (by simp [jtHead]) (fun x t hx => by
        rcases List.mem_append.1 hx with hx | hx
        · exact hfl0 x t hx
        · exact frLine_jtTail _ _ _ _ _ x t (by rw [jtTail_eq]; exact List.mem_append_left _ hx))
      hpc hseg⟩
  · simp only [iterN]; rw [e1]; exact (by rw [e2, e3, e4, e5, e6])
  rotate_left 3
  · have hg : ∀ {u : Arm.ArmState}, spOf u = spOf s → R.Good u := fun h => .inr (h.trans hspB)
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hgx0 0 (by rw [hn1 hhs]; omega)
    · rw [ei1]
      exact RL.goodXNR_ofIns hR h1 (by simp only [s1, Arm.r_of_w_same]) rfl rfl
        (hg (Arm.r_of_w_different hsp)) hr1 hp1 (by rw [e2]; exact RL.nextOk_succ h1 rfl hpc2)
        (RL.readsIn_noLoad hR h1 (by simp only [s1, Arm.r_of_w_same]) rfl)
    · rw [ei2]
      exact RL.goodXNR_ofIns hR h2 hpc2 rfl rfl
        (hg (by simp only [spOf, s2, s1, Arm.r_of_w_different hsb, Arm.r_of_w_different hsp]))
        hr2 hp2 (by rw [e3]; exact RL.nextOk_succ h2 rfl hpc3) (RL.readsIn_noLoad hR h2 hpc2 rfl)
    · rw [ei3]
      exact RL.goodXNR_ofIns hR h3 hpc3 rfl rfl
        (hg (by simp only [spOf, s3, s2, s1, Arm.r_of_w_different hsa, Arm.r_of_w_different hsb,
          Arm.r_of_w_different hsp])) hr3 hp3 (by rw [e4]; exact RL.nextOk_succ h3 rfl hpc4)
        (RL.readsIn_of_line hR h3 hpc3 fun _ env a hab3 p hp q hq => by
          rw [memReads_load R.ctx (show FinalAM LoadOp.sload32.bytes
              (.regScaledExtended (.x na) (.x nb) .uxtw) from
              ⟨show na ≤ 30 by omega, show nb ≤ 30 by omega, .inl rfl⟩)
            (fun h => by cases h) hab3, List.mem_singleton] at hp
          subst hp
          simp only [LoadOp.bytes] at hq
          refine .inl ⟨j1 + 6 + i, _, _, hwi, q, hq, ?_⟩
          simp only [RL.pcOf]
          rw [haddr, hofs, BitVec.ofNat_add]
          simp only [A, BitVec.add_assoc])
    · rw [ei4]
      exact RL.goodXNR_ofIns hR h4 hpc4 rfl rfl
        (hg (by simp only [spOf, s4, s3, s2, s1, Arm.r_of_w_different hsa, Arm.r_of_w_different hsb,
          Arm.r_of_w_different hsp])) hr4 hp4 (by rw [e5]; exact RL.nextOk_succ h4 rfl hpc5)
          (RL.readsIn_noLoad hR h4 hpc4 rfl)
    · rw [ei5]
      exact RL.goodXNR_ofIns hR h5 hpc5 rfl rfl
        (hg (by simp only [spOf, s5, s4, s3, s2, s1, Arm.r_of_w_different hsa,
          Arm.r_of_w_different hsb, Arm.r_of_w_different hsp])) hr5 hp5
        (by rw [e6]; exact RL.nextOk_label hjtl (by simp only [s6, Arm.r_of_w_same, hV]))
        (RL.readsIn_noLoad hR h5 hpc5 rfl)
  · intro f hfp hfa hfb
    simp only [s6, s5, s4, s3, s2, s1]
    rw [Arm.r_of_w_different hfp, Arm.r_of_w_different hfa, Arm.r_of_w_different hfp,
      Arm.r_of_w_different hfp, Arm.r_of_w_different hfb, Arm.r_of_w_different hfp,
      Arm.r_of_w_different hfa, Arm.r_of_w_different hfb, Arm.r_of_w_different hfp,
      Arm.r_of_w_different hfp]
  · simp [s6, s5, s4, s3, s2, s1, Arm.ArmState.mem_w_eq_mem]
  · simp [s6, s5, s4, s3, s2, s1, Arm.w_program]

/-- `jt_machineNR` with `RL.SegIn`. -/
theorem jt_machineNA {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {j0 : Nat}
    {d : Label}
    {ts : List Label} {nr na nb : Nat} (hr : nr < 29) (ha : na < 29) (hb : nb < 29)
    (hab : na ≠ nb) {jt : Lbl} (hjt : jt ≠ .skip) {bc : Line} {W T : List Line}
    (hdrop : R.L.drop j0 = relaxLine R.far bc ++
      (jtHead ts (.x nr) (.x na) (.x nb) jt ++ W ++ T))
    (hbc : ∃ l', bc = .ins (.bcond .hs l') none ∧
      RepLbl (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) d l')
    (hW : ∀ (i : Nat) (l : Label), ts[i]? = some l → ∃ l', W[i]? = some (Line.word l' jt) ∧
      RepLbl (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) l l')
    (hWl : W.length = ts.length)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) (hspB : spOf s = R.spB)
    (hcode : ∀ k w, R.fb.words[k]? = some w →
      Arm.read_mem_bytes 4 (R.base + BitVec.ofNat 64 (4 * k)) s = w) :
    (Arm.ConditionHolds Cond.hs.bits s = true → ∃ n jl lim, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      RepL R.af (planOwn R.fa.k R.af) R.L d jl ∧ (∀ i < n, R.GoodXNY Y (iterN R.step i s)) ∧
      R.SegIn s n j0 lim) ∧
    (Arm.ConditionHolds Cond.hs.bits s = false → ∀ i l,
      (Arm.r (.GPR (rnum nr)) s).toNat % 2 ^ 32 = i → ts[i]? = some l →
      ∃ n jl lim s', iterN R.step n s = s' ∧ Arm.r .PC s' = R.pcOf jl ∧
        RepL R.af (planOwn R.fa.k R.af) R.L l jl ∧
        (∀ f, f ≠ .PC → f ≠ .GPR (rnum na) → f ≠ .GPR (rnum nb) → Arm.r f s' = Arm.r f s) ∧
        s'.mem = s.mem ∧ s'.program = s.program ∧
        (∀ i < n, R.GoodXNY Y (iterN R.step i s)) ∧ R.SegIn s n j0 lim) := by
  obtain ⟨h1, h2⟩ := jt_machineNAF (Y := Y) hR hr ha hb hab hjt hdrop hbc hW hWl hprog hpc herr
    hspB hcode
  refine ⟨fun hh => ?_, fun hh i l hi hl => ?_⟩
  · obtain ⟨n, jl, lim, a, b, c, d, -⟩ := h1 hh
    exact ⟨n, jl, lim, a, b, c, d⟩
  · obtain ⟨n, jl, lim, s', a, b, c, d, e, f, g, k, -⟩ := h2 hh i l hi hl
    exact ⟨n, jl, lim, s', a, b, c, d, e, f, g, k⟩

/-- **The end of a branch segment at a block entry** has `SegLen`: the segment is inside the
branch lines (`RL.SegIn`, which hold no block label) and ends at an entry pc of the entered
block. -/
theorem RL.segLen_entry_of {R : RL} (hR : R.Wf) {j : Nat} {ps1 : PState} {T : List Line}
    {b st : Nat} {it : RItem} {its its'' : List RItem} {m m' : Loc → CV} {w w' : Arm.ArmState}
    {s : Arm.ArmState} {n lim : Nat}
    (hns : ¬ (st = b ∧ its'' = its)) (hT : T = [])
    (hE : ∃ W, R.EntryWit st (Arm.r .PC (iterN R.step n s)) W) (hseg : R.SegIn s n j lim) :
    R.SegLen j ps1 T (.run ⟨b, it :: its, m, w⟩) (.run ⟨st, its'', m', w'⟩) s n := by
  refine ⟨?_, ?_⟩
  · rw [RL.tgtS_entry hns]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      exact ⟨hE, fun i h0 hi => absurd hi (by omega)⟩
    · obtain ⟨x0, t0, hx0⟩ : ∃ x t, R.L[j]? = some (.ins x t) :=
        Classical.byContradiction fun hno =>
          absurd (hseg.2.2.mpr fun x t hx => hno ⟨x, t, hx⟩) (by omega)
      refine RL.firstArrS_of_inside hseg.1 (RL.entryWit_ne hR hx0 (fun k l h1 h2 e => ?_)) hE
      obtain ⟨x', t', hx'⟩ := hseg.2.1 k (by omega) h2
      rw [hx'] at e; cases e
  · rw [RL.emptyW_entry_iff hns]
    exact hseg.2.2.trans ⟨fun h => .inr h, fun h => h.resolve_left fun h' => h' hT⟩

/-- **`realizes_jtNA` with the segment's lines** (`RL.FRFree`). -/
theorem realizes_jtNAF {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {b k : Nat}
    {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {c' : MConf CV Arm.ArmState}
    {j : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {d : Label}
    {ts : List Label} {ridx t1 t2 : Reg}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.jtSequence d ts ridx t1 t2))
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c') :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      R.SegNA Y s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' n ∧ R.FRFree s n := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  have hok := ctlCheck_inst hck hvb hi
  simp only [ctlInstOk, Bool.and_eq_true] at hok
  obtain ⟨⟨hr0, ha0⟩, hb0⟩ := hok
  obtain ⟨vr, rfl⟩ := isVregInt_iff hr0
  obtain ⟨va, rfl⟩ := isVregInt_iff ha0
  obtain ⟨vb', rfl⟩ := isVregInt_iff hb0
  cases h with
  | @op b k allocs its m w vb'' i ops outs outs' w' ctl m2 c' hvb' hi' hops' hsz' hsem hlen hho hcl hn =>
  rw [hvb] at hvb'; cases hvb'
  rw [hi] at hi'; cases hi'
  -- the control outcome: a `jtSequence`'s run always goes to a successor block
  have hnc := hn
  have hk1 : k + 1 = vb.insts.size := by
    cases hnc with
    | @goto _ _ _ hk1 _ _ => exact hk1
    | next _ =>
      have h0 := hsem
      simp only [RL.sem, csemV, csem] at h0
      split at h0 <;> (try split at h0) <;> (try split at h0) <;> simp at h0
    | ret hh => simp at hh
    | halt =>
      have h0 := hsem
      simp only [RL.sem, csemV, csem] at h0
      split at h0 <;> (try split at h0) <;> (try split at h0) <;> simp at h0
  -- the forwarding-block case of `QW` (`T ≠ []`): the item's assigned form is a `jump`, which
  -- no `jtSequence` assigns to
  have hqq := hq
  rcases hqq with ⟨hT0, hqs⟩ | ⟨hT', -⟩
  rotate_left
  · obtain ⟨vbf, allocsf, regsf, if_, xf, bxf, itxf, hvbf, he, -, -, hins, hasgf, -⟩ := hq.fwd hT'
    rw [hvb] at hvbf; cases hvbf
    simp only [RItem.op.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hi2 := hi
    rw [hins] at hi2
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hi2
    subst hi2
    obtain ⟨_, _, _, he2⟩ := assign_jtVreg hasgf
    simp at he2
  obtain ⟨c, ins, _, hc, -⟩ := hR.check
  obtain ⟨preds, hcfg⟩ := hc.cfg
  obtain ⟨t0, tss, hback, hss, hlab⟩ := cfg_block hcfg hvb
  -- the block's own segment: the item is its last instruction
  obtain ⟨vb0, _, _, code, _, _, _, _, hvb0, -, -, hchk0, hcode, -⟩ := id hqs
  rw [hvb] at hvb0; cases hvb0
  obtain rfl : its = [] := hchk0.tail_nil hk1
  obtain ⟨vb0, items, pre, c1, X, psm, ps2, x, hvb0, hit, hsplit, hchk, hc1, hX, hT,
    htr, hdrop, hpc, hst, hterm⟩ := qWs_term hR hqs
  rw [hvb] at hvb0; cases hvb0
  obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
  rw [hi] at hi0; cases hi0
  obtain ⟨cc, wh, i2, ops2, hi2, hops2, hstat, -⟩ := op_checked hchk
  rw [hi] at hi2; cases hi2
  rw [hops'] at hops2; cases hops2
  have hopsA : ops = #[⟨vr, .int, .use, .early, .reg⟩, ⟨va, .int, .def, .early, .reg⟩,
      ⟨vb', .int, .def, .early, .reg⟩] := by
    have e : (MInst.jtSequence d ts (.vreg vr .int) (.vreg va .int) (.vreg vb' .int)).operands =
        .ok #[⟨vr, .int, .use, .early, .reg⟩, ⟨va, .int, .def, .early, .reg⟩,
          ⟨vb', .int, .def, .early, .reg⟩] := rfl
    rw [e] at hops'; injection hops' with hh; exact hh.symm
  subst hopsA
  obtain ⟨hsz2, hloc, hnd, -⟩ := checkStatic_facts hstat
  obtain ⟨r0, r1, r2, rfl⟩ := regs3 (by simpa using hsz2.symm)
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
  -- the block's last instruction's lines: the jump-table body
  have hdl : ([AInst.inst (.jtSequence d ts (.x nr) (.x na) (.x nb))]).dropLast = [] := by
    simp
  have hgl : ([AInst.inst (.jtSequence d ts (.x nr) (.x na) (.x nb))]).getLast?.toList =
      [AInst.inst (.jtSequence d ts (.x nr) (.x na) (.x nb))] := by
    simp
  rw [hdl] at hX
  rw [hgl] at hT
  have hXe : codeLinesE R.ctx R.af [] ps1 = .ok ([], ps1) := by simp [codeLinesE]
  rw [hXe] at hX
  simp only [Except.ok.injEq, Prod.mk.injEq] at hX
  obtain ⟨hX0, hpsm0⟩ := hX
  subst hX0
  subst hpsm0
  have hl3 := codeLinesE_single hT
  simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl3
  obtain ⟨hls1, -⟩ := hl3
  have htJ : x.1.term = jtBody d ts (.x nr) (.x na) (.x nb) (.jt ps1.jt) := by
    rw [← hls1]; simp [jtBody]
  have hlenT : x.1.term.length = 7 + ts.length := by rw [htJ]; simp [jtBody]; omega
  -- the emitted segment: each line kept or retargeted (`LineOut`; a kept line has no block
  -- target, so the default branch and the table words are retargeted to representing labels)
  obtain ⟨hlenO, hLO⟩ := termOk_kept (by simp) (by simp) (by simp) (by simp) hterm
  have hlen2' : x.2.1.length = 7 + ts.length := by rw [hlenO]; exact hlenT
  have jtBody_cons : jtBody d ts (.x nr) (.x na) (.x nb) (.jt ps1.jt) =
      Line.ins (.bcond .hs (.block d)) :: (jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt) ++
        ts.map (fun l => Line.word (.block l) (.jt ps1.jt))) := rfl
  have hhead : (jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt)).length = 6 := by simp [jtHead]
  have hheadT : ∀ ln ∈ jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt), Line.target? ln = none := by
    intro ln hln
    simp only [jtHead, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hln
    rcases hln with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  -- the raw line at a segment index `k` with `1 ≤ k ≤ 6`
  have htermK : ∀ k, 1 ≤ k → k < 7 → x.1.term[k]? =
      (jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt))[k - 1]? := by
    intro k h1 h2
    obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk', htJ, jtBody_cons, List.getElem?_cons_succ,
      List.getElem?_append_left (by rw [hhead]; omega),
      show (k':Nat) + 1 - 1 = k' from by omega]
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
    rw [Array.back?_eq_getElem?, show vb.insts.size - 1 = k by omega, hi] at hback
    cases hback; rfl
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
  -- the default branch's line: retargeted to a label representing `d`
  have hlen1 : 0 < x.2.1.length := by omega
  have ht0 : x.1.term[0]? = some (Line.ins (Insn.bcond Cond.hs (Lbl.block d)) none) := by
    rw [htJ]; simp [jtBody]
  obtain ⟨y0, hy0⟩ : ∃ y, x.2.1[0]? = some y := ⟨_, List.getElem?_eq_getElem hlen1⟩
  rcases hLO 0 _ _ ht0 hy0 with ⟨-, hnb0⟩ | ⟨lb, l2, hxt0, hyt0, hre0, hrep0⟩
  · exact (hnb0 d rfl).elim
  · simp only [Line.target?, Option.some.injEq, Lbl.block.injEq] at hxt0
    subst hxt0
    have hbc0 : y0 = .ins (.bcond .hs l2) none := by
      rw [hre0]; rfl
    have hcons : x.2.1 = y0 :: x.2.1.drop 1 := by
      cases h21 : x.2.1 with
      | nil => rw [h21] at hlen1; simp at hlen1
      | cons a as =>
        rw [h21] at hy0
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hy0
        subst hy0
        simp [h21]
    have hWlJ : (x.2.1.drop 7).length = ts.length := by
      rw [List.length_drop]; omega
    have hWJ : ∀ (i : Nat) (l : Label), ts[i]? = some l → ∃ l', (x.2.1.drop 7)[i]? =
        some (Line.word l' (.jt ps1.jt)) ∧
        RepLbl (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) l l' := by
      intro i l hiw
      have hil' : i < ts.length := (List.getElem?_eq_some_iff.1 hiw).1
      have hleni : 7 + i < x.2.1.length := by omega
      obtain ⟨y, hy⟩ : ∃ y, x.2.1[7 + i]? = some y := ⟨_, List.getElem?_eq_getElem hleni⟩
      have htword : x.1.term[7 + i]? = some (Line.word (Lbl.block l) (.jt ps1.jt)) := by
        rw [show (7:Nat) + i = 6 + i + 1 from by omega, htJ, jtBody_cons,
          List.getElem?_cons_succ, List.getElem?_append_right (by rw [hhead]; omega), hhead,
          show (6:Nat) + i - 6 = i from by omega, List.getElem?_map, hiw]
        simp
      rcases hLO (7 + i) _ _ htword hy with ⟨-, hnb⟩ | ⟨l3, l4, hxt, hyt, hre, hrep⟩
      · exact (hnb l rfl).elim
      · simp only [Line.target?, Option.some.injEq, Lbl.block.injEq] at hxt
        subst hxt
        refine ⟨l4, ?_, hrep⟩
        rw [List.getElem?_drop, hy, hre]
        rfl
    have hrelNone : ∀ ln ∈ jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt) ++ x.2.1.drop 7,
        ln.relaxable? = none := by
      intro ln hln
      rcases List.mem_append.1 hln with hln | hln
      · simp only [jtHead, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hln
        rcases hln with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hln
        have hkL : k < ts.length := by
          have := (List.getElem?_eq_some_iff.1 hk).1
          rw [hWlJ] at this; exact this
        obtain ⟨l5, hw5, -⟩ := hWJ k _ (List.getElem?_eq_getElem hkL)
        rw [hw5] at hk
        rw [(Option.some.inj hk).symm]
        rfl
    have hrest : x.2.1.drop 1 = jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt) ++ x.2.1.drop 7 := by
      apply List.ext_getElem?
      intro k
      rw [List.getElem?_drop]
      rcases Nat.lt_or_ge (k + 1) 7 with h7 | h7
      · obtain ⟨y, hy⟩ : ∃ y, x.2.1[1 + k]? = some y := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have htk : x.1.term[1 + k]? =
            (jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt))[k]? := by
          have h0 := htermK (k + 1) (by omega) (by omega)
          rw [show (k:Nat) + 1 = 1 + k from Nat.add_comm k 1,
            show (1:Nat) + k - 1 = k from by omega] at h0
          exact h0
        obtain ⟨xl, hxl⟩ : ∃ xw, x.1.term[1 + k]? = some xw := by
          refine ⟨(jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt))[k], ?_⟩
          rw [htk, List.getElem?_eq_some_iff]
          exact ⟨by rw [hhead]; omega, rfl⟩
        rcases hLO (1 + k) xl y hxl hy with ⟨heq, -⟩ | ⟨l3, l4, hxt, -, -, -⟩
        · rw [hy, heq, List.getElem?_append_left (by rw [hhead]; omega), ← htk, hxl]
        · exfalso
          have hk6 : (k:Nat) < (jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt)).length := by
            rw [hhead]; omega
          have hxe : (jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt))[k]? = some xl := by
            rw [← htk, hxl]
          obtain ⟨hik2, hxe2⟩ := List.getElem?_eq_some_iff.1 hxe
          have hxT0 : Line.target? ((jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt))[k]) = none :=
            hheadT _ (List.getElem_mem (l := jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt)) hk6)
          rw [hxe2] at hxT0
          have hxT : Line.target? xl = none := hxT0
          rw [hxT] at hxt
          simp at hxt
      · rw [List.getElem?_append_right (by rw [hhead]; omega), hhead, List.getElem?_drop,
          show (7:Nat) + (k - 6) = k + 1 from by omega, Nat.add_comm 1 k]
    have hbcJ : ∃ l', y0 = .ins (.bcond .hs l') none ∧
        RepLbl (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) d l' :=
      ⟨l2, hbc0, hrep0⟩
    have hdropJT : R.L.drop j = relaxLine R.far y0 ++
        (jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt) ++ x.2.1.drop 7 ++
          R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2)) := by
      rw [hdrop, List.nil_append, hcons, relaxLines_cons, hrest,
        relaxLines_of_none hrelNone]
      have hd7 : List.drop 7 (y0 :: (jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt) ++
          List.drop 7 x.snd.fst)) = List.drop 7 x.snd.fst := by
        rw [List.drop_cons (by omega), List.drop_append,
          List.drop_eq_nil_of_le (by rw [hhead]; omega), List.nil_append,
          show (7:Nat) - 1 - (jtHead ts (.x nr) (.x na) (.x nb) (.jt ps1.jt)).length = 0
            from by omega, List.drop_zero]
      rw [hd7]
      simp only [List.append_assoc]
    obtain ⟨hmTaken, hmNot⟩ := jt_machineNAF (Y := Y) hR hnr hna hnb hab (by simp) hdropJT hbcJ hWJ
      hWlJ hst.prog hpc hst.err hst.sp hst.code
    cases hn with
    | next _ => split at hsem <;> (try split at hsem) <;> simp at hsem
    | ret h => simp at h
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
    have hns : ¬ (st = b ∧ items'.toList = []) := by
      rintro ⟨rfl, he⟩
      rw [hit] at hitems; cases hitems
      have := congrArg List.length hsplit
      rw [he] at this
      simp at this
    -- the MStep with the machine's temporaries, and `QW` at the successor's entry witness
    have fin : ∀ (s' : Arm.ArmState) (n jl lim : Nat), iterN R.step n s = s' →
        Arm.r .PC s' = R.pcOf jl → RepL R.af (planOwn R.fa.k R.af) R.L vs.label jl →
        (∀ f, f ≠ .PC → f ≠ .GPR (rnum na) → f ≠ .GPR (rnum nb) → Arm.r f s' = Arm.r f s) →
        s'.mem = s.mem → s'.program = s.program → (∀ i < n, R.GoodXNY Y (iterN R.step i s)) →
        R.SegIn s n j lim → R.FRFree s n →
        ∃ n c'', MStep R.vc R.sem ckeep R.rf
          (.run ⟨b, .op k (#[Reg.x nr, .x na, .x nb].map Loc.reg) :: [], m, w⟩) c'' ∧
          R.SegNA Y s j ps1 T (.run ⟨b, .op k (#[Reg.x nr, .x na, .x nb].map Loc.reg) :: [], m, w⟩)
            c'' n ∧ R.FRFree s n := by
      intro s' n jl lim hn hpc' hjl hf hmem hprog hsp hseg hfr
      have hsem' : R.sem (.jtSequence d ts (.vreg vr .int) (.vreg va .int) (.vreg vb' .int))
          (((#[(⟨vr, .int, .use, .early, .reg⟩ : Operand), ⟨va, .int, .def, .early, .reg⟩,
            ⟨vb', .int, .def, .early, .reg⟩].zip (#[Reg.x nr, .x na, .x nb].map Loc.reg)).toList.filter
            (·.1.isUse)).map (m ·.2)) w = some (outs, w, .goto jj) := by
        rw [hU]; simp only [RL.sem, csemV, csem, hhs]; exact hsem
      obtain ⟨hE, hqE⟩ := qW_entry hR hst0 hvs hitems hjl hpc'
        (stRel_regs hst hna hnb hna18 hnb18 hf hmem hprog)
      refine ⟨n, _, MStep.op (outs' := [regVal s' (.x na), regVal s' (.x nb)]) (w' := w) hvb hi hops'
        hsz' hsem' hlen ⟨by rw [hout2]; rfl,
          fun h => by simp [havocFrom, MInst.keptDefs, MInst.isBranch] at h,
          fun n h => by simp [havocFrom, MInst.keptDefs, MInst.isBranch] at h; subst h; rfl⟩
        (hcl0 _) (MNext.goto hk1 hsucc hitems), ⟨?_, hsp, ?_⟩, hfr⟩
      · unfold RL.QWn
        rw [hstore, RL.nextW_entry hns, hn]
        exact hqE
      · rw [hstore]
        exact RL.segLen_entry_of hR hns hT0 (by rw [hn]; exact hE) hseg
    -- which successor
    split at hsem
    · rename_i hhs'
      simp only [Option.some.injEq, Prod.mk.injEq] at hsem
      obtain ⟨-, -, hj⟩ := hsem
      injection hj with hj
      subst hj
      obtain ⟨n, jl, lim, hn', hrep, hsp, hseg, hfr⟩ := hmTaken hhs'
      simp only [MInst.targets, List.getElem?_cons_zero, Option.some.injEq] at hlj
      rw [hlj] at hrep
      exact fin _ n jl lim hn' (Arm.r_of_w_same ..) hrep
        (fun f hf _ _ => Arm.r_of_w_different hf) (by simp [Arm.ArmState.mem_w_eq_mem])
        (by simp [Arm.w_program]) hsp hseg hfr
    · rename_i hhs'
      split at hsem
      · rename_i hlt
        simp only [Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨-, -, hj⟩ := hsem
        injection hj with hj
        subst hj
        simp only [MInst.targets, List.getElem?_cons_succ] at hlj
        obtain ⟨n, jl, lim, s', hn', hpc', hrep, hf, hmem, hprog, hsp, hseg, hfr⟩ :=
          hmNot (by simpa using hhs') _ vs.label (by simp [lo64, regVal, BitVec.toNat_setWidth]) hlj
        exact fin s' n jl lim hn' hpc' hrep hf hmem hprog hsp hseg hfr
      · cases hsem

/-- **A jump table on the machine, at a witness** (`realizes_jtNR`). -/
theorem realizes_jtNA {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {b k : Nat}
    {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {c' : MConf CV Arm.ArmState}
    {j : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {d : Label}
    {ts : List Label} {ridx t1 t2 : Reg}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.jtSequence d ts ridx t1 t2))
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c') :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      R.SegNA Y s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' n :=
  let ⟨n, c'', h1, h2, _⟩ := realizes_jtNAF (Y := Y) hR hq hvb hi h
  ⟨n, c'', h1, h2⟩

end Backend.Proof
