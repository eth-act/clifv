import FV.E2E.RegLevelGoto

/-!
# Items that fall through (M6): islands, `trapIf` not taken, symbol addresses

Common bookkeeping: `q_op` takes `Q` at an instruction item apart (its allocated form, its
lines, the lines after it); `qs_next` puts `Q` together at the next item after plain lines ran.
-/

namespace Backend.Proof

open Backend E2E

/-- `Q` at an instruction item, taken apart (`Q.qs_lt`: with control `next` the item is inside
the block, so the remaining items and their code are not empty). The new `Q`'s successor state
is assembled with `qs_next`, which needs the remaining code's `dropLast`/`getLast?` lines to be
the block's segment's lines — the checker's block correspondence (`R.Wf`, `itemsCode_ne_nil`)
rules out remaining items without code, which the old `ftList`/`nxtOf` bookkeeping did not
need. -/
theorem q_op {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    (hk : k + 1 < vb.insts.size) :
    ∃ j0 items pre regs i' c1 c2 X' ls1 ps1 psm psm' ps2 x,
      ∃ (cc : CheckCtx) (wh : String) (ops : Array Operand),
      allocs = regs.map Loc.reg ∧ R.rf.blocks[b]? = some items ∧
      items.toList = pre ++ .op k allocs :: its ∧ i.assign regs = .ok i' ∧
      ((c1 = [AInst.inst i'] ∧ (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us)) ∨
        (∃ ds, i' = .args ds ∧ c1 = []) ∨ (∃ us, i' = .rets us ∧ c1 = [AInst.epilogueRet])) ∧
      i.operands = .ok ops ∧ cc.checkStatic wh ops (regs.map Loc.reg) i.clobbers = .ok () ∧
      ItemsChecked R vb its ∧ itemsCode R.fr vb its = .ok c2 ∧
      codeLinesE R.ctx R.af c1 ps1 = .ok (ls1, psm) ∧
      codeLinesE R.ctx R.af c2.dropLast psm = .ok (X', psm') ∧
      codeLinesE R.ctx R.af c2.getLast?.toList psm' = .ok (x.1.term, ps2) ∧
      ps2.traps.toList <+: R.psF.traps.toList ∧
      R.L.drop j0 = relaxLines R.far ls1 ++ (relaxLines R.far (X' ++ x.2.1) ++
        R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2)) ∧
      Arm.r .PC s = R.pcOf j0 ∧ StRel R s m w ∧
      segX R.fa.k R.af b = some x ∧ SegChecked R.fa.k R.af b := by
  have hq' := Q.qs_lt hq hvb hk
  obtain ⟨j0, vb0, items, pre, code, X, ps1, psX, ps2, x, hvb0, hit, hsplit, hchk, hcode, hX, hT,
    htr, hdrop, hpc, hst, hx, hsc⟩ := hq'
  rw [hvb] at hvb0; cases hvb0
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
  rw [hi] at hi0; cases hi0
  obtain ⟨cc, wh, i2, ops, hi2, hops, hstat, hchk'⟩ := op_checked hchk
  rw [hi] at hi2; cases hi2
  have hne : its ≠ [] := by
    obtain ⟨c, k0, a, out, -, -, hrun⟩ := hchk
    obtain ⟨-, rfl, _, _, _, _, _, _, h'⟩ := runItems_op hrun
    rintro rfl
    have := (runItems_nil h').1
    omega
  obtain ⟨c, ins, _, hc, -⟩ := hR.check
  obtain ⟨preds, hcfg⟩ := hc.cfg
  obtain ⟨c0, k0, a0, out0, -, -, hrun'⟩ := id hchk'
  have hc2ne : c2 ≠ [] := itemsCode_ne_nil hcfg hvb hrun' hne hc2
  rw [List.dropLast_append_of_ne_nil hc2ne] at hX
  obtain ⟨ls1, X', psm, h1, h2, rfl⟩ := codeLinesE_append _ _ _ _ _ hX
  have hlast : (c1 ++ c2).getLast?.toList = c2.getLast?.toList := by
    rw [List.getLast?_append, List.getLast?_eq_getLast hc2ne]
    simp
  rw [hlast] at hT
  exact ⟨j0, items, pre, regs, i', c1, c2, X', ls1, ps1, psm, psX, ps2, x, cc, wh, ops, rfl, hit,
    hsplit, hasg, hc1', hops, hstat, hchk', hc2, h1, h2, hT, htr,
    by rw [hdrop]; simp only [List.append_assoc, relaxLines_append], hpc, hst, hx, hsc⟩

/-- An instruction without defs and clobbers leaves the store unchanged (`MStep.op`). -/
theorem store_nodefs {m m2 : Loc → CV} {L : List (Operand × Loc)} {cl : List Reg} (hcl0 : cl = [])
    (hcl : Clobbered ckeep cl (writeM m ((L.zip ([] : List CV)).filter (·.1.1.isEarly))) m2) :
    writeM m2 ((L.zip ([] : List CV)).filter (·.1.1.isLate)) = m := by
  subst hcl0
  have : m2 = m := funext fun l => (hcl.1 l (by simp)).trans (by simp [writeM])
  subst this
  simp [writeM]

/-! ## Islands -/

/-- **`emitIsland`**: no code. (`R.Wf` is new: the new `Q`'s successor state (`qs_next`) needs
the remaining items' code to be not empty, which the checker's block correspondence gives.) -/
theorem realizes_island {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {c' : MConf CV Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {nb : Nat}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.emitIsland nb))
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c') :
    Q R s c' := by
  cases h with
  | @op b k allocs its m w vb' i ops' outs outs' w' ctl m2 c' hvb' hi' hops' hsz hsem hlen hho hcl hn =>
  rw [hvb] at hvb'; cases hvb'
  rw [hi] at hi'; cases hi'
  obtain rfl := hho.2.1 rfl
  simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
  obtain ⟨rfl, rfl, rfl⟩ := hsem
  cases hn with
  | next hk =>
  obtain ⟨j0, items, pre, regs, i', c1, c2, X', ls1, ps1, psm, psm', ps2, x, cc, wh, ops, rfl, hit,
    hsplit, hasg, hc1', hops, hstat, hchk', hc2, h1, h2, h3, htr, hdrop, hpc, hst, hx, hsc⟩ :=
    q_op hR hq hvb hi hk
  obtain ⟨rfl, rfl⟩ := assign_none (fun f => rfl) hasg
  obtain rfl : c1 = [.inst (.emitIsland nb)] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  have hl1 := codeLinesE_single h1
  simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
  obtain ⟨rfl, rfl⟩ := hl1
  rw [store_nodefs rfl hcl]
  exact qs_next hvb hit hsplit hchk' hc2 h2 h3 htr hdrop (by rw [hpc]; simp [relaxLines]) hst hx
    hsc

/-! ## `trapIf` not taken -/

/-- **`trapIf` whose condition does not hold**: one conditional branch (to the trap section),
not taken. -/
theorem realizes_trapIf_next {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat}
    {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    {c' : MConf CV Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {kk : CondBrKind}
    {code : Clif.TrapCode} (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.trapIf kk code))
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c')
    (hnh : ∀ w', c' ≠ .halt w') :
    ∃ n, Q R (iterN R.step n s) c' ∧ ∀ i < n, R.GoodX (iterN R.step i s) := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  cases h with
  | @op b k allocs its m w vb' i ops' outs outs' w' ctl m2 c' hvb' hi' hops' hsz hsem hlen hho hcl hn =>
  rw [hvb] at hvb'; cases hvb'
  rw [hi] at hi'; cases hi'
  obtain rfl := hho.2.1 rfl
  simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
  obtain ⟨rfl, rfl, hctl⟩ := hsem
  cases hn with
  | halt => exact absurd rfl (hnh _)
  | ret h => cases h
  | goto _ _ _ => split at hctl <;> cases hctl
  | next hk =>
  obtain ⟨j0, items, pre, regs, i', c1, c2, X', ls1, ps1, psm, psm', ps2, x, cc, wh, ops, rfl, hit,
    hsplit, hasg, hc1', hops, hstat, hchk', hc2, h1, h2, h3, htr, hdrop, hpc, hst, hx, hsc⟩ :=
    q_op hR hq hvb hi hk
  rw [hops] at hops'
  cases hops'
  have hkk : ∀ r sz, kk = .zero r sz ∨ kk = .notZero r sz → r.isVregInt = true := by
    intro r sz hr
    have := ctlCheck_inst hck hvb hi
    rcases hr with rfl | rfl <;> simpa [ctlInstOk] using this
  obtain ⟨k', rfl, hkr⟩ := kind_alloc hkk (mk := fun k => MInst.trapIf k code) rfl
    (fun f => rfl) (fun f => rfl) hops hstat hasg m
  obtain rfl : c1 = [.inst (.trapIf k' code)] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  have hl1 := codeLinesE_single h1
  simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
  obtain ⟨rfl, -⟩ := hl1
  have hnot : kk.holds (((ops'.zip (regs.map Loc.reg)).toList.filter (·.1.isUse)).map (m ·.2)) w =
      false := by
    split at hctl
    · cases hctl
    · rename_i hh
      simpa using hh
  rw [store_nodefs rfl hcl]
  -- the branch to the trap label is not taken
  have hline : relaxLines R.far [Line.ins (k'.insn (.trap ps1.traps.size))] =
      relaxLine R.far (.ins (k'.insn (.trap ps1.traps.size))) := by simp [relaxLines]
  have hdrop' : R.L.drop j0 = relaxLine R.far (.ins (k'.insn (.trap ps1.traps.size)) none) ++
      (relaxLines R.far (X' ++ x.2.1) ++
        R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2)) := by
    rw [hdrop, hline]
  have hform : (∃ c, k'.insn (.trap ps1.traps.size) = .bcond c (.trap ps1.traps.size)) ∨
      (∃ nz w r, k'.insn (.trap ps1.traps.size) = .cbz nz w r (.trap ps1.traps.size)) ∨
      (∃ nz r bit, k'.insn (.trap ps1.traps.size) = .tbz nz r bit (.trap ps1.traps.size)) := by
    cases k' <;> simp [CondBrKind.insn]
  obtain ⟨n, jl, hn, -, hjf, -, -, hg⟩ := reach_rcbX hR hdrop' hform (by simp) false
    (fun env a ha => by rw [kind_brCond hst hkr _ ha, hnot])
    (fun hct env a ha => by rw [kind_brCond_inv hst hkr _ _ hct ha, hnot])
    (by rw [hst.prog]) hpc hst.err hst.sp
  refine ⟨n, ?_, hg⟩
  rw [hn]
  refine qs_next hvb hit hsplit hchk' hc2 h2 h3 htr hdrop ?_ ?_ hx hsc
  · rw [Arm.r_of_w_same, hjf rfl]
    simp [relaxLines]
  · exact hst.pc _

end Backend.Proof
