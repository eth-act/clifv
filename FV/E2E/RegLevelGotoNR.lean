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

/-- **A `jump x`'s final lines** (`termOk_jump`): the machine reaches a line representing `x`,
by its `b` or at once when the branch was removed, changing only the pc. -/
theorem reach_bXNR {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {j0 : Nat} {x : Label}
    {o : List Line} {nxt : Nat}
    (hdrop : R.L.drop j0 = relaxLines R.far o ++ R.L.drop (rix R.far (planLines R.fa.k R.af) nxt))
    (ho : (∃ l', o = [.ins (.b l') none] ∧
        RepLbl (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) x l') ∨
      (o = [] ∧ planRep R.fa.k R.af x nxt = true))
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) (hsp : spOf s = R.spB) :
    ∃ n jl, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      RepL R.af (planOwn R.fa.k R.af) R.L x jl ∧
      (∀ i < n, spOf (iterN R.step i s) = spOf s) ∧ ∀ i < n, R.GoodXNY Y (iterN R.step i s) := by
  rcases ho with ⟨l', rfl, hl⟩ | ⟨rfl, hr⟩
  · obtain ⟨hsk, jl, hjl, hrep⟩ := repLbl_line hR hl
    have hj : R.L[j0]? = some (.ins (.b l') none) := by
      have := congrArg (·[0]?) hdrop
      rw [relaxLines_cons, relaxLine_of_none rfl] at this
      simpa [List.getElem?_drop] using this
    obtain ⟨a, jl', ha, hjl', hstep⟩ := step_branch hR hj (.inl rfl) hsk hprog hpc herr
    have hg := RL.goodXNR_branch (Y := Y) hR hj (.inl rfl) hsk hprog hpc herr hsp
    obtain rfl : jl' = jl := labelOffsets_uniq hR.lm hjl' hjl
    refine ⟨1, jl', ?_, hrep, fun i hi => ?_, fun i hi => ?_⟩
    · simp only [iterN]; rw [hstep, brCond_b ha]; rfl
    · obtain rfl : i = 0 := by omega
      rfl
    · obtain rfl : i = 0 := by omega
      exact hg
  · have hrep := rep_nxt hR hr
    simp only [relaxLines, List.flatMap_nil, List.nil_append] at hdrop
    obtain rfl := drop_idx hdrop hrep.lt
    exact ⟨0, _, by simp only [iterN]; rw [← hpc, Arm.w_irrelevant], hrep, fun i hi => by omega,
      fun i hi => by omega⟩

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


/-- **A conditional branch's final lines** (`CondOut`; `ci` the branch, whose condition holds iff
`cond`): the machine reaches a line representing the successor `cond` picks, changing only the
pc. -/
theorem reach_cbXNR {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {j0 : Nat}
    {s1 s2 : Label}
    {ci : Insn} {o : List Line} {nxt : Nat}
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
    ∃ n jl, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      RepL R.af (planOwn R.fa.k R.af) R.L (if cond then s1 else s2) jl ∧
      (∀ i < n, spOf (iterN R.step i s) = spOf s) ∧ ∀ i < n, R.GoodXNY Y (iterN R.step i s) := by
  rcases hco with ⟨c, t', e', rfl, hct, rfl, hl1, hl2⟩ | ⟨c, t', rfl, hct, hc⟩ | ⟨rfl, hr1, hr2⟩
  · -- `b.c t'; b e'`
    obtain ⟨hsk1, jt, hjt, hrep1⟩ := repLbl_line hR hl1
    rw [relaxLines_cons, List.append_assoc] at hdrop
    obtain ⟨n, jl, hn, hjT, hjF, hsp1, -, hg⟩ := reach_rcbXNR (Y := Y) hR hdrop (setTarget_form hci t') hsk1
      cond (hcT t') (fun hct' env a ha => by
        rw [setTarget_invertTo hci] at ha
        exact hcF (condTarget_setTarget_isSome hci hct') _ env a ha) hprog hpc herr hsp
    cases cond
    · -- the fall-through `b e'`
      have hd1 : R.L.drop jl = relaxLines R.far [.ins (.b e') none] ++
          R.L.drop (rix R.far (planLines R.fa.k R.af) nxt) := by
        rw [hjF rfl, ← List.drop_drop, hdrop, List.drop_left]
      have hs1 : (Arm.w .PC (R.pcOf jl) s).program = R.fb.program R.base := by
        rw [Arm.w_program, hprog]
      obtain ⟨n', jl', hn', hrep', hsp', hg'⟩ := reach_bXNR (Y := Y) hR hd1 (.inl ⟨e', rfl, hl2⟩) hs1
        (Arm.r_of_w_same ..) (by rw [Arm.r_of_w_different (by simp), herr])
        (by rw [spOf_w_pc, hsp])
      obtain ⟨hN, hS, hG⟩ := reach_then hn hn' hsp1 hsp' hg hg'
      exact ⟨n + n', jl', hN, by simpa using hrep', fun i hi => by rw [hS i hi], hG⟩
    · obtain rfl : jl = jt := labelOffsets_uniq hR.lm (hjT rfl) hjt
      exact ⟨n, jl, hn, by simpa using hrep1, hsp1, hg⟩
  · -- one branch
    rcases hc with ⟨rfl, hl1, hr2⟩ | ⟨rfl, hl2, hr1⟩
    · obtain ⟨hsk1, jt, hjt, hrep1⟩ := repLbl_line hR hl1
      rw [relaxLines_cons] at hdrop
      simp only [relaxLines, List.flatMap_nil, List.append_nil] at hdrop
      obtain ⟨n, jl, hn, hjT, hjF, hsp1, -, hg⟩ := reach_rcbXNR (Y := Y) hR hdrop (setTarget_form hci t') hsk1
        cond (hcT t') (fun hct' env a ha => by
          rw [setTarget_invertTo hci] at ha
          exact hcF (condTarget_setTarget_isSome hci hct') _ env a ha) hprog hpc herr hsp
      cases cond
      · have hrep2 := rep_nxt hR hr2
        have hd : R.L.drop jl = R.L.drop (rix R.far (planLines R.fa.k R.af) nxt) := by
          rw [hjF rfl, ← List.drop_drop, hdrop, List.drop_left]
        obtain rfl := drop_idx hd hrep2.lt
        exact ⟨n, _, hn, by simpa using hrep2, hsp1, hg⟩
      · obtain rfl : jl = jt := labelOffsets_uniq hR.lm (hjT rfl) hjt
        exact ⟨n, jl, hn, by simpa using hrep1, hsp1, hg⟩
    · obtain ⟨hsk2, jt, hjt, hrep2⟩ := repLbl_line hR hl2
      rw [relaxLines_cons] at hdrop
      simp only [relaxLines, List.flatMap_nil, List.append_nil] at hdrop
      obtain ⟨n, jl, hn, hjT, hjF, hsp1, -, hg⟩ := reach_rcbXNR (Y := Y) hR hdrop (invertTo_form' hci t') hsk2
        (!cond) (hcF (condTarget_invertTo_isSome hci hct) t') (fun _ env a ha => by
          rw [invertTo_invertTo hci] at ha
          rw [Bool.not_not]
          exact hcT _ env a ha) hprog hpc herr hsp
      cases cond
      · obtain rfl : jl = jt := labelOffsets_uniq hR.lm (hjT rfl) hjt
        exact ⟨n, jl, hn, by simpa using hrep2, hsp1, hg⟩
      · have hrep1 := rep_nxt hR hr1
        have hd : R.L.drop jl = R.L.drop (rix R.far (planLines R.fa.k R.af) nxt) := by
          rw [hjF rfl, ← List.drop_drop, hdrop, List.drop_left]
        obtain rfl := drop_idx hd hrep1.lt
        exact ⟨n, _, hn, by simpa using hrep1, hsp1, hg⟩
  · -- no lines: both successors next
    simp only [relaxLines, List.flatMap_nil, List.nil_append] at hdrop
    have hrep1 := rep_nxt hR hr1
    obtain rfl := drop_idx hdrop hrep1.lt
    refine ⟨0, _, by simp only [iterN]; rw [← hpc, Arm.w_irrelevant], ?_, fun i hi => by omega,
      fun i hi => by omega⟩
    cases cond
    · simpa using rep_nxt hR hr2
    · simpa using hrep1
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
  obtain ⟨c, ins, _, hc, -⟩ := hR.check
  obtain ⟨preds, hcfg⟩ := hc.cfg
  obtain ⟨t0, ts, hback, hss, hlab⟩ := cfg_block hcfg hvb
  rcases Q.cases hq with hqs | ⟨vbf, allocsf, regsf, if_, xf, bx, hvbf, he, hits, half, hins, hasgf,
    hsuccf, itx, hitx, hqx⟩
  rotate_left
  · -- a forwarding block: its `jump` takes no machine step
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
    refine ⟨0, ?_, fun i hi => by omega⟩
    simpa [iterN, writeM] using hqx
  obtain ⟨_, vb0, _, _, code, _, _, _, _, _, hvb0, -, -, hchk0, hcode, -⟩ := id hqs
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
  -- the block's last item: its final lines and the branch check's verdict on them
  obtain rfl : its = [] := hchk0.tail_nil (by omega)
  obtain ⟨j0, vb0, items, pre, c1', X, ps1, psm, ps2, x, hvb0, hit, hsplit, -, hc1'', hX, -, htr,
    hdrop, hpc, hst, hterm⟩ := qs_term hR hqs
  rw [hvb] at hvb0; cases hvb0
  rw [hc1] at hc1''; cases hc1''
  have hone : ∀ a, c1 = [a] → X = [] ∧ R.L.drop j0 = relaxLines R.far x.2.1 ++
      R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2) := by
    intro a ha
    subst ha
    simp only [List.dropLast_singleton, codeLinesE, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hX
    obtain ⟨rfl, rfl⟩ := hX
    exact ⟨rfl, by simpa using hdrop⟩
  -- the machine reaches a line representing the successor
  have hreach : ∃ n jl, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      RepL R.af (planOwn R.fa.k R.af) R.L vs.label jl ∧ ∀ i < n, R.GoodXNY Y (iterN R.step i s) := by
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
      obtain ⟨n, jl, hn, hrep, -, hg⟩ := reach_bXNR (Y := Y) hR hd (termOk_jump hterm) (by rw [hst.prog])
        hpc hst.err hst.sp
      exact ⟨n, jl, hn, hrep, hg⟩
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
      obtain ⟨n, jl, hn, hrep, -, hg⟩ := reach_cbXNR (Y := Y) hR hd (termOk_condBr hterm) hci (kk.holds _ w)
        (fun l env a ha => kind_brCond hst hkr l (by rwa [hset] at ha))
        (fun hs l env a ha => kind_brCond_inv hst hkr (.block t) l (hct hs) ha)
        (by rw [hst.prog]) hpc hst.err hst.sp
      refine ⟨n, jl, hn, ?_, hg⟩
      rw [hU] at hrep
      rw [hjc t e kk rfl] at hlj
      simp only [MInst.targets] at hlj
      cases hcond : kk.holds U w <;> simp only [hcond] at hlj hrep <;> simp at hlj <;> rw [← hlj] <;>
        simpa using hrep
    · obtain ⟨nr, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
      obtain ⟨r', rfl, rfl⟩ := assign_one (n := nr) (sp := OpSpec.use)
        (mk := fun r => MInst.testBitAndBranch kd t e r bit) (fun f => by simp [MInst.visitOperands]) hasg
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
      obtain ⟨n, jl, hn, hrep, -, hg⟩ := reach_cbXNR (Y := Y) hR hd (termOk_tbz hterm)
        (.inr (.inr ⟨_, _, _, _, rfl⟩))
        ((Arm.r (.GPR (rnum n')) s).getLsbD bit == (kd == .nz))
        (fun l env a ha => brCond_tbz (by omega) ha s)
        (fun _ l env a ha => by
          simp only [Insn.invertTo] at ha
          rw [brCond_tbz (by omega) ha s, beq_not_right])
        (by rw [hst.prog]) hpc hst.err hst.sp
      refine ⟨n, jl, hn, ?_, hg⟩
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
  obtain ⟨n, jl, hn, hrep, hg⟩ := hreach
  refine ⟨n, ?_, hg⟩
  rw [hn]
  exact q_entry hR hst0 hvs hitems hrep (Arm.r_of_w_same ..) (hst.pc _)

end Backend.Proof
