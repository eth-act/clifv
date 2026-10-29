import FV.E2E.RegLevelMemTrap
import FV.E2E.RegLevelGotoN

/-!
# Taken `trapIf` on the machine with no call state (SEM1 #537, step 2k)

`RegLevelTrap`'s `trap_trapIf` and `RegLevelMemTrap`'s `trap_trapIf_line` with `RL.GoodXN`
(docs/plans/uninit.md §5.5): the branch to the trap label (`reach_rcbXN`) passes no call state.
-/

namespace Backend.Proof

open Backend E2E

/-- **A taken `trapIf` on the machine**: one branch to the deferred trap label, whose next
line is the trap site; every state after the trap site's step errs. -/
theorem trap_trapIfN {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {kk : CondBrKind}
    {code : Clif.TrapCode} (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.trapIf kk code)) {ops : Array Operand}
    (hops : (MInst.trapIf kk code).operands = .ok ops)
    (hholds : kk.holds (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = true) :
    ∃ n, TrapAt R.fb R.base code (iterN R.step n s) ∧ (∀ i < n, R.GoodXN (iterN R.step i s)) ∧
      ∀ m, Arm.r .ERR (iterN R.step (n + m + 1) s) ≠ .None := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops', rfl, hit, hsplit,
    hasg, hc1', hops', hstat, hchk', hc2, h1, h2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  rw [hops] at hops'; cases hops'
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
  obtain ⟨rfl, hpsm⟩ := hl1
  -- the branch (relaxed or not) to the trap label is taken
  have hZ : ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  have hdrop' : R.L.drop j0 = relaxLine R.far (.ins (k'.insn (.trap ps1.traps.size)) none) ++
      (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T) := by
    rw [hdrop, List.singleton_append, ftList_kind_trap k' ps1.traps.size _ hZ, relaxLines_cons,
      List.append_assoc]
  have hform : (∃ c, k'.insn (.trap ps1.traps.size) = .bcond c (.trap ps1.traps.size)) ∨
      (∃ nz w r, k'.insn (.trap ps1.traps.size) = .cbz nz w r (.trap ps1.traps.size)) ∨
      (∃ nz r bit, k'.insn (.trap ps1.traps.size) = .tbz nz r bit (.trap ps1.traps.size)) := by
    cases k' <;> simp [CondBrKind.insn]
  obtain ⟨nst, jl, hnst, hjt, -, -, -, hgx⟩ := reach_rcbXN hR hdrop' hform (by simp) true
    (fun env a ha => by rw [kind_brCond hst hkr _ ha, hholds])
    (fun hct env a ha => by rw [kind_brCond_inv hst hkr _ _ hct ha, hholds])
    (by rw [hst.prog]) hpc hst.err hst.sp
  have hjl := hjt rfl
  -- the trap section entry of this trap
  have hpre : psm.traps.toList <+: R.psF.traps.toList :=
    (codeLinesE_traps h2).trans htr
  have hn : R.psF.traps.toList[ps1.traps.size]? = some (.trap ps1.traps.size, code) := by
    obtain ⟨t, ht⟩ := hpre
    rw [← ht, ← hpsm]
    simp
  obtain ⟨body, psF', hb, hL, -⟩ := emit_block hR.emit
  rw [relaxLines_append, relaxLines_trapLines, List.append_assoc,
    show emitFar ⟨R.fa.k, R.af.slotBase⟩ R.af = R.far from rfl] at hL
  obtain ⟨body', hb'⟩ := hR.psF
  have hk : R.ctx = ⟨R.fa.k, R.af.slotBase⟩ := rfl
  rw [hk, hb] at hb'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hb'
  obtain ⟨-, rfl⟩ := hb'
  obtain ⟨hlab, hudf⟩ := trapLines_get_append _ _ _ _ hn
  have hlab' : R.L[(relaxLines R.far (ftList body)).length + 2 * ps1.traps.size]? = some (.label (.trap ps1.traps.size)) := by
    simp only [RL.L, hL]; rw [List.getElem?_append_right (by omega)]; simpa using hlab
  have hudf' : R.L[(relaxLines R.far (ftList body)).length + 2 * ps1.traps.size + 1]? =
      some (.ins (.udf 0xc11f) (some code)) := by
    simp only [RL.L, hL]; rw [List.getElem?_append_right (by omega)]
    simpa [Nat.add_assoc] using hudf
  -- the branch reaches the label's offset, which is the trap site's
  have hoff : R.pcOf jl = R.pcOf ((relaxLines R.far (ftList body)).length + 2 * ps1.traps.size + 1) := by
    have e1 := labelOffsets_label hR.lm hjl
    have e2 := labelOffsets_label hR.lm hlab'
    simp only [RL.pcOf]
    rw [lineOffset_succ _ _ _ hlab']
    simp only [RL.L] at e1 e2 ⊢
    rw [e1] at e2
    simp only [Option.some.injEq] at e2
    rw [e2]; simp [Line.size]
  have hpcF : Arm.r .PC (iterN R.step nst s) =
      R.pcOf ((relaxLines R.far (ftList body)).length + 2 * ps1.traps.size + 1) := by
    rw [hnst, Arm.r_of_w_same, hoff]
  have herrF : Arm.r .ERR (iterN R.step nst s) = .None := by
    rw [hnst, Arm.r_of_w_different (by simp)]; exact hst.err
  have hprogF : (iterN R.step nst s).program = R.fb.program R.base := by
    rw [hnst, Arm.w_program, hst.prog]
  refine ⟨nst, trapAt_line hR hudf' hpcF herrF, hgx, fun m => ?_⟩
  rw [show nst + m + 1 = nst + (m + 1) by omega, iterN_add]
  exact RL.udf_stuck hR hudf' hpcF hprogF herrF m

/-- `trap_trapIf` with the trap site's `udf` line. -/
theorem trap_trapIf_lineN {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {kk : CondBrKind}
    {code : Clif.TrapCode} (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.trapIf kk code)) {ops : Array Operand}
    (hops : (MInst.trapIf kk code).operands = .ok ops)
    (hholds : kk.holds (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = true) :
    ∃ n, TrapAt R.fb R.base code (iterN R.step n s) ∧ UdfLine R.fa R.base (iterN R.step n s) ∧
      ∀ i < n, R.GoodXN (iterN R.step i s) := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops', rfl, hit, hsplit,
    hasg, hc1', hops', hstat, hchk', hc2, h1, h2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  rw [hops] at hops'; cases hops'
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
  obtain ⟨rfl, hpsm⟩ := hl1
  -- the branch (relaxed or not) to the trap label is taken
  have hZ : ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  have hdrop' : R.L.drop j0 = relaxLine R.far (.ins (k'.insn (.trap ps1.traps.size)) none) ++
      (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T) := by
    rw [hdrop, List.singleton_append, ftList_kind_trap k' ps1.traps.size _ hZ, relaxLines_cons,
      List.append_assoc]
  have hform : (∃ c, k'.insn (.trap ps1.traps.size) = .bcond c (.trap ps1.traps.size)) ∨
      (∃ nz w r, k'.insn (.trap ps1.traps.size) = .cbz nz w r (.trap ps1.traps.size)) ∨
      (∃ nz r bit, k'.insn (.trap ps1.traps.size) = .tbz nz r bit (.trap ps1.traps.size)) := by
    cases k' <;> simp [CondBrKind.insn]
  obtain ⟨nst, jl, hnst, hjt, -, -, -, hgx⟩ := reach_rcbXN hR hdrop' hform (by simp) true
    (fun env a ha => by rw [kind_brCond hst hkr _ ha, hholds])
    (fun hct env a ha => by rw [kind_brCond_inv hst hkr _ _ hct ha, hholds])
    (by rw [hst.prog]) hpc hst.err hst.sp
  have hjl := hjt rfl
  -- the trap section entry of this trap
  have hpre : psm.traps.toList <+: R.psF.traps.toList :=
    (codeLinesE_traps h2).trans htr
  have hn : R.psF.traps.toList[ps1.traps.size]? = some (.trap ps1.traps.size, code) := by
    obtain ⟨t, ht⟩ := hpre
    rw [← ht, ← hpsm]
    simp
  obtain ⟨body, psF', hb, hL, -⟩ := emit_block hR.emit
  rw [relaxLines_append, relaxLines_trapLines, List.append_assoc,
    show emitFar ⟨R.fa.k, R.af.slotBase⟩ R.af = R.far from rfl] at hL
  obtain ⟨body', hb'⟩ := hR.psF
  have hk : R.ctx = ⟨R.fa.k, R.af.slotBase⟩ := rfl
  rw [hk, hb] at hb'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hb'
  obtain ⟨-, rfl⟩ := hb'
  obtain ⟨hlab, hudf⟩ := trapLines_get_append _ _ _ _ hn
  have hlab' : R.L[(relaxLines R.far (ftList body)).length + 2 * ps1.traps.size]? = some (.label (.trap ps1.traps.size)) := by
    simp only [RL.L, hL]; rw [List.getElem?_append_right (by omega)]; simpa using hlab
  have hudf' : R.L[(relaxLines R.far (ftList body)).length + 2 * ps1.traps.size + 1]? =
      some (.ins (.udf 0xc11f) (some code)) := by
    simp only [RL.L, hL]; rw [List.getElem?_append_right (by omega)]
    simpa [Nat.add_assoc] using hudf
  -- the branch reaches the label's offset, which is the trap site's
  have hoff : R.pcOf jl = R.pcOf ((relaxLines R.far (ftList body)).length + 2 * ps1.traps.size + 1) := by
    have e1 := labelOffsets_label hR.lm hjl
    have e2 := labelOffsets_label hR.lm hlab'
    simp only [RL.pcOf]
    rw [lineOffset_succ _ _ _ hlab']
    simp only [RL.L] at e1 e2 ⊢
    rw [e1] at e2
    simp only [Option.some.injEq] at e2
    rw [e2]; simp [Line.size]
  have hpcF : Arm.r .PC (iterN R.step nst s) =
      R.pcOf ((relaxLines R.far (ftList body)).length + 2 * ps1.traps.size + 1) := by
    rw [hnst, Arm.r_of_w_same, hoff]
  have herrF : Arm.r .ERR (iterN R.step nst s) = .None := by
    rw [hnst, Arm.r_of_w_different (by simp)]; exact hst.err
  exact ⟨nst, trapAt_line hR hudf' hpcF herrF, ⟨_, _, hudf', hpcF⟩, hgx⟩

end Backend.Proof
