import FV.E2E.RegLevelGoto

/-!
# Items that fall through (M6): islands, `trapIf` not taken, symbol addresses

Common bookkeeping: `q_op` takes `Q` at an instruction item apart (its allocated form, its
lines, the lines after it); `q_next` puts `Q` together at the next item after plain lines ran.
-/

namespace Backend.Proof

open Backend E2E

/-- `Q` at an instruction item, taken apart. -/
theorem q_op {R : RL} {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc} {its : List RItem}
    {m : Loc → CV} {w : Arm.ArmState} (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) :
    ∃ j0 items pre regs i' c1 c2 ls1 ls2 ps1 psm ps2 T, ∃ (cc : CheckCtx) (wh : String) (ops : Array Operand),
      allocs = regs.map Loc.reg ∧ R.rf.blocks[b]? = some items ∧
      items.toList = pre ++ .op k allocs :: its ∧ i.assign regs = .ok i' ∧
      ((c1 = [AInst.inst i'] ∧ (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us)) ∨
        (∃ ds, i' = .args ds ∧ c1 = []) ∨ (∃ us, i' = .rets us ∧ c1 = [AInst.epilogueRet])) ∧
      i.operands = .ok ops ∧ cc.checkStatic wh ops (regs.map Loc.reg) i.clobbers = .ok () ∧
      ItemsChecked R vb its ∧ itemsCode R.fr vb its = .ok c2 ∧
      codeLinesE R.ctx R.af c1 ps1 = .ok (ls1, psm) ∧ codeLinesE R.ctx R.af c2 psm = .ok (ls2, ps2) ∧
      ps2.traps.toList <+: R.psF.traps.toList ∧
      R.L.drop j0 = ftList (ls1 ++ (ls2 ++ nxtOf R.af b)) ++ T ∧
      Arm.r .PC s = R.pcOf j0 ∧ StRel R s m w := by
  obtain ⟨j0, vb0, items, pre, code, ls, ps1, ps2, T, hvb0, hit, hsplit, hchk, hcode, hls, htr, hdrop,
    hpc, hst⟩ := hq
  rw [hvb] at hvb0; cases hvb0
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
  rw [hi] at hi0; cases hi0
  obtain ⟨cc, wh, i2, ops, hi2, hops, hstat, hchk'⟩ := op_checked hchk
  rw [hi] at hi2; cases hi2
  obtain ⟨ls1, ls2, psm, h1, h2, rfl⟩ := codeLinesE_append _ _ _ _ _ hls
  exact ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, rfl, hit, hsplit,
    hasg, hc1', hops, hstat, hchk', hc2, h1, h2, htr, by rw [hdrop, List.append_assoc], hpc, hst⟩

/-- `Q` at the next item, after the item's plain instruction lines `ls1` ran. -/
theorem q_next {R : RL} {s : Arm.ArmState} {b : Nat} {it : RItem} {its : List RItem}
    {m : Loc → CV} {w : Arm.ArmState} {vb : VBlock} {items : Array RItem} {pre : List RItem}
    {c2 : List AInst} {ls1 ls2 : List Line} {psm ps2 : PState} {T : List Line} {j0 : Nat}
    (hvb : R.vc.blocks[b]? = some vb) (hit : R.rf.blocks[b]? = some items)
    (hsplit : items.toList = pre ++ it :: its) (hchk : ItemsChecked R vb its)
    (hc2 : itemsCode R.fr vb its = .ok c2) (h2 : codeLinesE R.ctx R.af c2 psm = .ok (ls2, ps2))
    (htr : ps2.traps.toList <+: R.psF.traps.toList)
    (hdrop : R.L.drop j0 = ftList (ls1 ++ (ls2 ++ nxtOf R.af b)) ++ T)
    (hpl : ∀ ln ∈ ls1, ln.plain = true)
    (hpc : Arm.r .PC s = R.pcOf (j0 + ls1.length)) (hst : StRel R s m w) :
    Q R s (.run ⟨b, its, m, w⟩) := by
  have hZ : ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  have hdrop' : R.L.drop j0 = ls1 ++ (ftList (ls2 ++ nxtOf R.af b) ++ T) := by
    rw [hdrop, ftList_plain_append _ _ hpl hZ, List.append_assoc]
  refine ⟨j0 + ls1.length, vb, items, pre ++ [it], c2, ls2, psm, ps2, T, hvb, hit,
    by rw [hsplit]; simp, hchk, hc2, h2, htr, ?_, ?_, hst⟩
  · rw [← List.drop_drop, hdrop', List.drop_left]
  · exact hpc

theorem plain_kind_trap (k' : CondBrKind) (n : Nat) :
    (Line.ins (k'.insn (.trap n)) none).plain = true := by
  cases k' <;> simp [Line.plain, CondBrKind.insn, Insn.condTarget?]
  split
  · rfl
  · rfl
  · rename_i hn heq
    exfalso
    split at heq
    · cases heq
    · simp only [Option.some.injEq] at heq; exact hn _ heq.symm

/-- An instruction without defs and clobbers leaves the store unchanged (`MStep.op`). -/
theorem store_nodefs {m m2 : Loc → CV} {L : List (Operand × Loc)} {cl : List Reg} (hcl0 : cl = [])
    (hcl : Clobbered ckeep cl (writeM m ((L.zip ([] : List CV)).filter (·.1.1.isEarly))) m2) :
    writeM m2 ((L.zip ([] : List CV)).filter (·.1.1.isLate)) = m := by
  subst hcl0
  have : m2 = m := funext fun l => (hcl.1 l (by simp)).trans (by simp [writeM])
  subst this
  simp [writeM]

/-! ## Islands -/

/-- **`emitIsland`**: no code. -/
theorem realizes_island {R : RL} {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {c' : MConf CV Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {nb : Nat}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.emitIsland nb))
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c') :
    Q R s c' := by
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, rfl, hit, hsplit,
    hasg, hc1', hops, hstat, hchk', hc2, h1, h2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  obtain ⟨rfl, rfl⟩ := assign_none (fun f => rfl) hasg
  obtain rfl : c1 = [.inst (.emitIsland nb)] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  have hl1 := codeLinesE_single h1
  simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
  obtain ⟨rfl, rfl⟩ := hl1
  cases h with
  | @op b k allocs its m w vb' i ops' outs outs' w' ctl m2 c' hvb' hi' hops' hsz hsem hlen hho hcl hn =>
  rw [hvb] at hvb'; cases hvb'
  rw [hi] at hi'; cases hi'
  obtain rfl := hho.2.1 rfl
  simp only [RL.sem, csem, Option.some.injEq, Prod.mk.injEq] at hsem
  obtain ⟨rfl, rfl, rfl⟩ := hsem
  cases hn with
  | next hk =>
  rw [store_nodefs rfl hcl]
  exact q_next hvb hit hsplit hchk' hc2 h2 htr hdrop (by simp) (by simpa using hpc) hst

/-! ## `trapIf` not taken -/

/-- **`trapIf` whose condition does not hold**: one conditional branch (to the trap section),
not taken. -/
theorem realizes_trapIf_next {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {c' : MConf CV Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {kk : CondBrKind}
    {code : Clif.TrapCode} (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.trapIf kk code))
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c')
    (hnh : ∀ w', c' ≠ .halt w') :
    ∃ n, Q R (iterN R.step n s) c' := by
  have hck := (lowerRFunc_ok hR.alloc).2.2.2
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, rfl, hit, hsplit,
    hasg, hc1', hops, hstat, hchk', hc2, h1, h2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
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
  cases h with
  | @op b k allocs its m w vb' i ops' outs outs' w' ctl m2 c' hvb' hi' hops' hsz hsem hlen hho hcl hn =>
  rw [hvb] at hvb'; cases hvb'
  rw [hi] at hi'; cases hi'
  rw [hops] at hops'; cases hops'
  obtain rfl := hho.2.1 rfl
  simp only [RL.sem, csem, Option.some.injEq, Prod.mk.injEq] at hsem
  obtain ⟨rfl, rfl, hctl⟩ := hsem
  cases hn with
  | halt => exact absurd rfl (hnh _)
  | ret h => cases h
  | goto _ _ _ => split at hctl <;> cases hctl
  | next hk =>
  have hnot : kk.holds (((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isUse)).map (m ·.2)) w = false := by
    split at hctl
    · cases hctl
    · rename_i hh
      simpa using hh
  rw [store_nodefs rfl hcl]
  -- the branch to the trap label is not taken
  have hj0 : R.L[j0]? = some (.ins (k'.insn (.trap ps1.traps.size)) none) := by
    have hpl := plain_kind_trap k' ps1.traps.size
    have hZ : ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
      intro n e
      have hm := List.mem_of_getElem? e
      rcases List.mem_append.1 hm with hm | hm
      · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
      · simp only [nxtOf] at hm
        split at hm <;> simp at hm
    rw [show [Line.ins (k'.insn (.trap ps1.traps.size)) none] ++ (ls2 ++ nxtOf R.af b) =
      Line.ins (k'.insn (.trap ps1.traps.size)) none :: (ls2 ++ nxtOf R.af b) from rfl,
      show Line.ins (k'.insn (.trap ps1.traps.size)) none :: (ls2 ++ nxtOf R.af b) =
        [Line.ins (k'.insn (.trap ps1.traps.size)) none] ++ (ls2 ++ nxtOf R.af b) from rfl,
      ftList_plain_append _ _ (by simpa using hpl) hZ] at hdrop
    exact drop_get (by simpa using hdrop)
  have hform : (∃ c, k'.insn (.trap ps1.traps.size) = .bcond c (.trap ps1.traps.size)) ∨
      (∃ nz w r, k'.insn (.trap ps1.traps.size) = .cbz nz w r (.trap ps1.traps.size)) := by
    cases k' <;> simp [CondBrKind.insn]
  obtain ⟨a, jl, ha, -, hstep⟩ := step_branch hR hj0
    (by rcases hform with h | h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inl h))) (by rw [hst.prog]) hpc hst.err
  rw [kind_brCond hst hkr _ ha, hnot] at hstep
  refine ⟨1, ?_⟩
  simp only [iterN]
  rw [hstep]
  exact q_next hvb hit hsplit hchk' hc2 h2 htr hdrop
    (by intro ln hln; simp at hln; subst hln; exact plain_kind_trap k' _)
    (by simp [Arm.r_of_w_same]) (hst.pc _)

end Backend.Proof
