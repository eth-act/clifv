import FV.E2E.RegLevelReadsIn
import FV.E2E.RegLevelGoto
import FV.E2E.RegLevelNoCall


/-!
# Block-ending branches with no call state (SEM1 #537, step 2k)

`reach_bX`, `reach_rcbX`, `reach_cbX`, `realizes_goto` with `RL.GoodXNR` (docs/plans/uninit.md §5.5): branch lines are no call lines.
-/

namespace Backend.Proof

open Backend E2E

/-- `step_branchX` with no call state. -/
theorem RL.goodXNR_branch {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {j : Nat}
    {i : Insn} {l : Lbl}
    (hj : R.L[j]? = some (.ins i none))
    (hi : i = .b l ∨ (∃ c, i = .bcond c l) ∨ (∃ nz w r, i = .cbz nz w r l) ∨
      (∃ nz r bit, i = .tbz nz r bit l)) (hl : l ≠ .skip)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (hsp : spOf s = R.spB) : R.GoodXNY Y s :=
  ⟨⟨step_branchX hR hj hi hl hprog hpc herr hsp, RL.noCallAt_of_line hR hj hpc (by
    rcases hi with rfl | ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl)⟩,
    RL.readsIn_noLoad hR hj hpc (by
      rcases hi with rfl | ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl)⟩

/-- `step_skipX` with no call state. -/
theorem RL.goodXNR_skip {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {j : Nat}
    {i x : Insn}
    (hj : R.L[j]? = some (.ins i none)) (hj1 : R.L[j + 1]? = some (.ins x none))
    (hi : (∃ c, i = .bcond c .skip) ∨ (∃ nz w r, i = .cbz nz w r .skip) ∨
      (∃ nz r bit, i = .tbz nz r bit .skip)) (hx : x.pairFirst = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (hsp : spOf s = R.spB) : R.GoodXNY Y s :=
  ⟨⟨step_skipX hR hj hj1 hi hx hprog hpc herr hsp, RL.noCallAt_of_line hR hj hpc (by
    rcases hi with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl)⟩,
    RL.readsIn_noLoad hR hj hpc (by
      rcases hi with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl)⟩

/-- `reach_b` with the body's `sp`: the states before reaching the label satisfy `GoodX`. -/
theorem reach_bXNR {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {j0 : Nat} {x : Lbl}
    {Z T : List Line}
    (hdrop : R.L.drop j0 = relaxLines R.far (ftList (.ins (.b x) none :: Z)) ++ T) (hx : x ≠ .skip)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) (hsp : spOf s = R.spB) :
    ∃ n jl, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧ R.L[jl]? = some (.label x) ∧
      (∀ i < n, spOf (iterN R.step i s) = spOf s) ∧ ∀ i < n, R.GoodXNY Y (iterN R.step i s) := by
  rcases ft_b x Z with ⟨Z', rfl, he⟩ | he
  · rw [he, ft_label, relaxLines_cons, relaxLine_label, List.singleton_append] at hdrop
    refine ⟨0, j0, ?_, drop_get hdrop, fun i hi => by omega, fun i hi => by omega⟩
    simp only [iterN]; rw [← hpc, Arm.w_irrelevant]
  · rw [he, relaxLines_cons, relaxLine_of_none rfl, List.singleton_append] at hdrop
    obtain ⟨a, jl, ha, hjl, hstep⟩ := step_branch hR (drop_get hdrop) (.inl rfl) hx hprog hpc herr
    have hg := RL.goodXNR_branch (Y := Y) hR (drop_get hdrop) (.inl rfl) hx hprog hpc herr hsp
    refine ⟨1, jl, ?_, hjl, fun i hi => ?_, fun i hi => ?_⟩
    · simp only [iterN]; rw [hstep, brCond_b ha]; rfl
    · obtain rfl : i = 0 := by omega
      rfl
    · obtain rfl : i = 0 := by omega
      exact hg
/-- `reach_rcb` with the body's `sp`: the states before reaching the target satisfy `GoodX`. -/
theorem reach_rcbXNR {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {j0 : Nat}
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
      ∀ i < n, R.GoodXNY Y (iterN R.step i s) := by
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
    rw [hc _ _ ha] at hstep
    cases cond
    · exact ⟨1, j0 + 1, by simp only [iterN]; rw [hstep]; rfl, by simp, by simp [h], h1, fun _ => rfl,
        hg⟩
    · exact ⟨1, jl, by simp only [iterN]; rw [hstep]; rfl, fun _ => hjl, by simp, h1, by simp, hg⟩
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
    rw [hcs hct _ _ ha] at hstep
    cases cond
    · exact ⟨1, j0 + 2, by simp only [iterN]; rw [hstep]; rfl, by simp, by simp [h], h1, fun _ => rfl,
        fun i hi => by
          obtain rfl : i = 0 := by omega
          exact hg0⟩
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
      refine ⟨2, jl, ?_, fun _ => hjl, by simp, fun i hi => ?_, by simp, fun i hi => ?_⟩
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

/-- `reach_cb` with the body's `sp`: the states before reaching the label satisfy `GoodX`. -/
theorem reach_cbXNR {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {j0 : Nat}
    {bc : Insn} {t e : Lbl}
    {Z T : List Line}
    (hdrop : R.L.drop j0 = relaxLines R.far (ftList (.ins bc none :: .ins (.b e) none :: Z)) ++ T)
    (hbc : (∃ c, bc = .bcond c t) ∨ (∃ nz w r, bc = .cbz nz w r t) ∨ (∃ nz r bit, bc = .tbz nz r bit t))
    (ht : t ≠ .skip) (he : e ≠ .skip)
    (cond : Bool) (hc : ∀ env a, bc.toArmInst env = .ok a → brCond a s = cond)
    (hc' : bc.condTarget? = some t → ∀ e' env a, (bc.invertTo e').toArmInst env = .ok a →
      brCond a s = !cond)
    (hcc : bc.condTarget? = some t → ∀ env a, ((bc.invertTo e).invertTo .skip).toArmInst env = .ok a →
      brCond a s = cond)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) (hsp : spOf s = R.spB) :
    ∃ n jl, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      R.L[jl]? = some (.label (if cond then t else e)) ∧
      (∀ i < n, spOf (iterN R.step i s) = spOf s) ∧ ∀ i < n, R.GoodXNY Y (iterN R.step i s) := by
  have hnb : ∀ x, bc ≠ .b x := by
    rcases hbc with ⟨c, rfl⟩ | ⟨nz, w, r, rfl⟩ | ⟨nz, r, bit, rfl⟩ <;> intro x h <;> cases h
  rcases ft_cb bc e Z hnb with ⟨L, Z', rfl, hct, hft⟩ | hft
  · have hLt : L = t := by
      rcases hbc with ⟨c, rfl⟩ | ⟨nz, w, r, rfl⟩ | ⟨nz, r, bit, rfl⟩ <;>
        simp only [Insn.condTarget?] at hct
      · split at hct <;> simp_all
      · simp_all
      · simp_all
    subst hLt
    rw [hft, ft_label, relaxLines_cons, relaxLines_cons, relaxLine_label, List.append_assoc] at hdrop
    have hform := invertTo_form (e := e) hbc
    have hct' : (bc.invertTo e).condTarget? = some e := by
      rcases hbc with ⟨c, rfl⟩ | ⟨nz, w, r, rfl⟩ | ⟨nz, r, bit, rfl⟩ <;>
        simp only [Insn.condTarget?] at hct ⊢
      · split at hct
        · cases hct
        · rename_i hc0
          simp only [Insn.invertTo, Insn.condTarget?]
          rcases c <;> simp_all [Cond.invert]
      · simp [Insn.invertTo, Insn.condTarget?]
      · simp [Insn.invertTo, Insn.condTarget?]
    obtain ⟨n, jl, hn, hjt, hjf, hsp', -, hg⟩ := reach_rcbXNR (Y := Y) hR hdrop hform he (!cond)
      (hc' hct e)
      (fun _ env a ha => by rw [hcc hct env a ha, Bool.not_not]) hprog hpc herr hsp
    refine ⟨n, jl, hn, ?_, hsp', hg⟩
    cases cond
    · simpa using hjt rfl
    · have hd' : R.L.drop jl = [Line.label L] ++ relaxLines R.far (ftList Z') ++ T := by
        rw [hjf rfl, ← List.drop_drop, hdrop, List.drop_left, List.append_assoc]
      simpa using drop_get (by simpa using hd')
  · rw [hft, relaxLines_cons, List.append_assoc] at hdrop
    obtain ⟨n, jl, hn, hjt, hjf, hsp', -, hg⟩ := reach_rcbXNR (Y := Y) hR hdrop hbc ht cond hc
      (fun hct' => hc' hct' .skip) hprog hpc herr hsp
    cases cond
    · have hd1 : R.L.drop jl = relaxLines R.far (ftList (.ins (.b e) none :: Z)) ++ T := by
        rw [hjf rfl, ← List.drop_drop, hdrop, List.drop_left]
      have hs1 : (iterN R.step n s).program = R.fb.program R.base := by rw [hn, Arm.w_program, hprog]
      obtain ⟨n', jl', hn', hjl', hsp'', hg'⟩ := reach_bXNR (Y := Y) hR hd1 he hs1
        (by rw [hn]; exact Arm.r_of_w_same ..)
        (by rw [hn, Arm.r_of_w_different (by simp), herr]) (by rw [hn, spOf_w_pc, hsp])
      refine ⟨n + n', jl', ?_, by simpa using hjl', fun i hi => ?_, fun i hi => ?_⟩
      · rw [iterN_add, hn', hn, Arm.w_of_w_shadow]
      · rcases Nat.lt_or_ge i n with h | h
        · exact hsp' i h
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
          rw [iterN_add, hsp'' k (by omega), hn]
          exact spOf_w_pc _ _
      · rcases Nat.lt_or_ge i n with h | h
        · exact hg i h
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
          rw [iterN_add]
          exact hg' k (by omega)
    · exact ⟨n, jl, hn, by simpa using hjt rfl, hsp', hg⟩

/-- **Block-ending branches on the machine**: from `Q` at a `jump`/`condBr`/`testBitAndBranch`
item, the machine reaches `Q` at the `MStep` successor (the chosen successor's items). -/
theorem realizes_gotoNR {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {b k : Nat}
    {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {c' : MConf CV Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {i : MInst}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    (hbr : (∃ l, i = .jump l) ∨ (∃ t e kk, i = .condBr t e kk) ∨
      (∃ kd t e rn bit, i = .testBitAndBranch kd t e rn bit))
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c') :
    ∃ n, Q R (iterN R.step n s) c' ∧ ∀ i < n, R.GoodXNY Y (iterN R.step i s) := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  obtain ⟨j0, vb0, items, pre, code, ls, ps1, ps2, T, hvb0, hit, hsplit, hchk, hcode, hls, htr, hdrop,
    hpc, hst⟩ := hq
  rw [hvb] at hvb0; cases hvb0
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
  rw [hi] at hi0; cases hi0
  obtain ⟨cc, wh, i2, ops2, hi2, hops2, hstat, -⟩ := op_checked hchk
  rw [hi] at hi2; cases hi2
  obtain ⟨ls1, ls2, psm, h1, h2, rfl⟩ := codeLinesE_append _ _ _ _ _ hls
  obtain ⟨c, ins, _, hc, -⟩ := hR.check
  obtain ⟨preds, hcfg⟩ := hc.cfg
  obtain ⟨t0, ts, hback, hss, hlab⟩ := cfg_block hcfg hvb
  cases h with
  | @op b k allocs its m w vb' i ops outs outs' w' ctl m2 c' hvb' hi' hops' hsz hsem hlen hho hcl hn =>
  rw [hvb] at hvb'; cases hvb'
  rw [hi] at hi'; cases hi'
  rw [hops2] at hops'; cases hops'
  -- the semantics: no defs, same world, `goto j`
  generalize hU : (((ops2.zip (regs.map Loc.reg)).toList.filter (·.1.isUse)).map (m ·.2)) = U at hsem
  have hsem' : outs = [] ∧ w' = w ∧ ∃ j, ctl = .goto j ∧ (∀ l, i = .jump l → j = 0) ∧
      (∀ t e kk, i = .condBr t e kk → j = if kk.holds U w then 0 else 1) ∧
      (∀ kd t e rn bit, i = .testBitAndBranch kd t e rn bit →
        ∃ a, U = [a] ∧ j = if ((lo64 a).getLsbD bit == (kd == .nz)) then 0 else 1) := by
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
  obtain ⟨rfl, hw', j, rfl, hj0, hjc, hjt⟩ := hsem'
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
  obtain ⟨vs, hvs, hlj⟩ := hlab j st hsucc'
  have hst0 : st ≠ 0 := ctlCheck_succ hck hsucc
  -- the machine reaches the successor's label
  have hreach : ∃ n jl, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      R.L[jl]? = some (.label (.block vs.label)) ∧ ∀ i < n, R.GoodXNY Y (iterN R.step i s) := by
    rw [List.append_assoc] at hdrop
    rcases hbr with ⟨l, rfl⟩ | ⟨t, e, kk, rfl⟩ | ⟨kd, t, e, rn, bit, rfl⟩
    · obtain ⟨rfl, rfl⟩ := assign_none (fun f => rfl) hasg
      obtain rfl : c1 = [.inst _] := by
        rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
        · exact h
        · cases h
        · cases h
      have hl1 := codeLinesE_single h1
      simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
      obtain ⟨rfl, -⟩ := hl1
      rw [hj0 l rfl] at hlj
      simp only [MInst.targets, List.getElem?_cons_zero, Option.some.injEq] at hlj
      rw [← hlj]
      obtain ⟨n, jl, hn, hjl, -, hg⟩ := reach_bXNR (Y := Y) hR (by simpa using hdrop) (by simp)
        (by rw [hst.prog])
        hpc hst.err hst.sp
      exact ⟨n, jl, hn, hjl, hg⟩
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
      have hl1 := codeLinesE_single h1
      simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
      obtain ⟨rfl, -⟩ := hl1
      have hbc : (∃ c, k'.insn (.block t) = .bcond c (.block t)) ∨
          (∃ nz w r, k'.insn (.block t) = .cbz nz w r (.block t)) ∨
          (∃ nz r bit, k'.insn (.block t) = .tbz nz r bit (.block t)) := by
        cases k' <;> simp [CondBrKind.insn]
      obtain ⟨n, jl, hn, hjl, -, hg⟩ := reach_cbXNR (Y := Y) hR (by simpa using hdrop) hbc (by simp)
        (by simp)
        (kk.holds _ w)
        (fun env a ha => kind_brCond hst hkr _ ha)
        (fun hct e' env a ha => kind_brCond_inv hst hkr _ _ hct ha)
        (fun _ env a ha => kind_brCond hst hkr _ (by rwa [CondBrKind.insn_invertTo_invertTo] at ha))
        (by rw [hst.prog]) hpc hst.err hst.sp
      refine ⟨n, jl, hn, ?_, hg⟩
      rw [hjl, hU]
      rw [hjc t e kk rfl] at hlj
      simp only [MInst.targets] at hlj
      cases hcond : kk.holds U w <;> simp only [hcond] at hlj ⊢ <;> simp at hlj <;> rw [hlj] <;> simp
    · obtain ⟨nr, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
      obtain ⟨r', rfl, rfl⟩ := assign_one (n := nr) (sp := OpSpec.use) (mk := fun r => MInst.testBitAndBranch kd t e r bit)
        (fun f => by simp [MInst.visitOperands]) hasg
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
      have hl1 := codeLinesE_single h1
      simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
      obtain ⟨rfl, -⟩ := hl1
      have hal := ((checkStatic_facts hstat).2.1 (⟨nr, .int, .use, .early, .reg⟩, .reg (.x n'))
        (by simp)).1
      simp only [CheckCtx.locOk, Bool.and_eq_true] at hal
      have hm : m (.reg (.x n')) = (Arm.r (.GPR (rnum n')) s).setWidth 128 := by
        rw [hst.store (.reg (.x n')) (fun r e => by cases e; exact hal.2) trivial]; rfl
      obtain ⟨n, jl, hn, hjl, -, hg⟩ := reach_cbXNR (Y := Y) hR (by simpa using hdrop)
        (bc := .tbz (kd == .nz) (.x n') bit (.block t)) (.inr (.inr ⟨_, _, _, rfl⟩)) (by simp) (by simp)
        ((Arm.r (.GPR (rnum n')) s).getLsbD bit == (kd == .nz))
        (fun env a ha => brCond_tbz (by omega) ha s)
        (fun _ e' env a ha => by
          simp only [Insn.invertTo] at ha
          rw [brCond_tbz (by omega) ha s, beq_not_right])
        (fun _ env a ha => by
          simp only [Insn.invertTo, Bool.not_not] at ha
          exact brCond_tbz (by omega) ha s)
        (by rw [hst.prog]) hpc hst.err hst.sp
      refine ⟨n, jl, hn, ?_, hg⟩
      rw [hjl]
      obtain ⟨a, hUa, hja⟩ := hjt kd t e _ bit rfl
      have ha : a = m (.reg (.x n')) := by
        rw [← hU] at hUa
        simp [Operand.isUse] at hUa
        exact hUa.symm
      subst ha
      rw [hja] at hlj
      simp only [MInst.targets, hm, lo64_regX] at hlj
      cases hcond : ((Arm.r (.GPR (rnum n')) s).getLsbD bit == (kd == .nz)) <;>
        simp only [hcond] at hlj ⊢ <;> simp at hlj <;> rw [hlj] <;> simp
  obtain ⟨n, jl, hn, hjl, hg⟩ := hreach
  refine ⟨n, ?_, hg⟩
  rw [hn]
  exact q_entry hR hst0 hvs hitems hjl (Arm.r_of_w_same ..) (hst.pc _)

end Backend.Proof
