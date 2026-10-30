import FV.E2E.RegLevelMemTrap
import FV.E2E.RegLevelGotoNR

/-!
# Taken `trapIf` on the machine with no call state (SEM1 #537, step 2k)

`RegLevelTrap`'s `trap_trapIf` and `RegLevelMemTrap`'s `trap_trapIf_line` with `RL.GoodXNR`
(docs/plans/uninit.md §5.5): the branch to the trap label (`reach_rcbXNR`) passes no call state.
-/

namespace Backend.Proof

open Backend E2E

/-- The taken branch of a `trapIf` reaches the trap section's `udf` site with the code
(the continuation shared by the mid-block and last-instruction cases). -/
private theorem trapIf_reachNR {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {m : Loc → CV}
    {w : Arm.ArmState} {kk k' : CondBrKind} {code : Clif.TrapCode} {n j0 : Nat} {T : List Line}
    {us : List CV} (hst : StRel R s m w) (hkr : KindRel m kk k' us)
    (hholds : kk.holds us w = true)
    (hdrop : R.L.drop j0 = relaxLine R.far (.ins (k'.insn (.trap n)) none) ++ T)
    (hpc : Arm.r .PC s = R.pcOf j0)
    (hn : R.psF.traps[n]? = some (.trap n, code)) :
    ∃ nst jl, iterN R.step nst s = Arm.w .PC (R.pcOf jl) s ∧
      TrapAt R.fb R.base code (iterN R.step nst s) ∧ (∀ i < nst, R.GoodXNY Y (iterN R.step i s)) ∧
      ∀ mm, Arm.r .ERR (iterN R.step (nst + mm + 1) s) ≠ .None := by
  have hbc : (∃ c, k'.insn (.trap n) = .bcond c (.trap n)) ∨
      (∃ nz wv r, k'.insn (.trap n) = .cbz nz wv r (.trap n)) ∨
      (∃ nz r bit, k'.insn (.trap n) = .tbz nz r bit (.trap n)) := by
    cases k' <;> simp [CondBrKind.insn]
  obtain ⟨nst, jl, hnst, hjt, -, -, -, hgx⟩ := reach_rcbXNR (Y := Y) hR hdrop hbc (by simp) true
    (fun env a ha => by rw [kind_brCond hst hkr _ ha, hholds])
    (fun hct env a ha => by rw [kind_brCond_inv hst hkr _ _ hct ha, hholds])
    (by rw [hst.prog]) hpc hst.err hst.sp
  have hjl := hjt rfl
  -- the final lines: the body's segments' relaxation and the trap section
  obtain ⟨p, hp, hL0, -⟩ := emit_seg hR.emit
  obtain ⟨p2, hplan, hps⟩ := hR.psF
  rw [hplan] at hp
  simp only [Except.ok.injEq] at hp
  subst hp
  have hL : R.L = relaxLines R.far (segLines p2.segs p2.outs) ++ trapLines R.psF := by
    show R.fa.lines.toList = _
    rw [hL0, show (emitFar ⟨R.fa.k, R.af.slotBase⟩ R.af) = R.far from rfl, Plan.lines,
      relaxLines_append, relaxLines_trapLines, hps]
  obtain ⟨hlab, hudf⟩ := trapLines_get R.psF n (.trap n, code) hn
  have hlab' : R.L[(relaxLines R.far (segLines p2.segs p2.outs)).length + 2 * n]? =
      some (.label (.trap n)) := by
    rw [hL, List.getElem?_append_right (by omega)]
    simpa using hlab
  have hudf' : R.L[(relaxLines R.far (segLines p2.segs p2.outs)).length + 2 * n + 1]? =
      some (.ins (.udf 0xc11f) (some code)) := by
    rw [hL, List.getElem?_append_right (by omega)]
    simpa [Nat.add_assoc] using hudf
  -- the branch reaches the label's offset, which is the trap site's
  have hoff : R.pcOf jl = R.pcOf ((relaxLines R.far (segLines p2.segs p2.outs)).length + 2 * n + 1) := by
    have e1 := labelOffsets_label hR.lm hjl
    have e2 := labelOffsets_label hR.lm hlab'
    simp only [RL.pcOf]
    rw [lineOffset_succ _ _ _ hlab']
    simp only [RL.L] at e1 e2 ⊢
    rw [e1] at e2
    simp only [Option.some.injEq] at e2
    rw [e2]; simp [Line.size]
  have hpcF : Arm.r .PC (iterN R.step nst s) =
      R.pcOf ((relaxLines R.far (segLines p2.segs p2.outs)).length + 2 * n + 1) := by
    rw [hnst, Arm.r_of_w_same, hoff]
  have herrF : Arm.r .ERR (iterN R.step nst s) = .None := by
    rw [hnst, Arm.r_of_w_different (by simp)]; exact hst.err
  have hprogF : (iterN R.step nst s).program = R.fb.program R.base := by
    rw [hnst, Arm.w_program, hst.prog]
  refine ⟨nst, jl, hnst, trapAt_line hR hudf' hpcF herrF, hgx, fun mm => ?_⟩
  rw [show nst + mm + 1 = nst + (mm + 1) by omega, iterN_add]
  exact RL.udf_stuck hR hudf' hpcF hprogF herrF mm

/-- **A taken `trapIf` on the machine**: one branch to the deferred trap label, whose next
line is the trap site; every state after the trap site's step errs. -/
theorem trap_trapIfNR {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {b k : Nat}
    {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {kk : CondBrKind}
    {code : Clif.TrapCode} (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.trapIf kk code)) {ops : Array Operand}
    (hops : (MInst.trapIf kk code).operands = .ok ops)
    (hholds : kk.holds (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = true) :
    ∃ n, TrapAt R.fb R.base code (iterN R.step n s) ∧ (∀ i < n, R.GoodXNY Y (iterN R.step i s)) ∧
      ∀ m, Arm.r .ERR (iterN R.step (n + m + 1) s) ≠ .None := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  rcases Q.cases hq with hqs | ⟨vbf, allocsf, regsf, if_, xf, bx, hvbf, he, hits, half, hins,
    hasgf, hsuccf, itx, hitx, hqx⟩
  rotate_left
  · -- a forwarding block: its `jump` takes no machine step, but a `trapIf`'s assigned form
    -- is no `jump`
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
    simp [MInst.targets] at htg
  rcases Nat.lt_or_ge (k + 1) vb.insts.size with hkl | hkge
  · -- not the block's last instruction
    obtain ⟨j0, items, pre, regs, i', c1, c2, X', ls1, ps1, psm, psm', ps2, x, cc, wh, ops'',
      rfl, -, -, hasg, hc1', hops', hstat, -, -, h1, hX2, hT2, htr, hdrop, hpc, hst, -, -⟩ :=
      q_op hR hq hvb hi hkl
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
    have hdrop' : R.L.drop j0 = relaxLine R.far (.ins (k'.insn (.trap ps1.traps.size)) none) ++
        (relaxLines R.far (X' ++ x.2.1) ++ R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2)) := by
      rw [hdrop, relaxLines_cons, relaxLines_nil, List.append_assoc, List.nil_append]
    have hpre : psm.traps.toList <+: R.psF.traps.toList :=
      (codeLinesE_traps hX2).trans ((codeLinesE_traps hT2).trans htr)
    have hnL : R.psF.traps.toList[ps1.traps.size]? = some (.trap ps1.traps.size, code) := by
      obtain ⟨t, ht⟩ := hpre
      rw [← ht, ← hpsm]
      simp
    have hn : R.psF.traps[ps1.traps.size]? = some (.trap ps1.traps.size, code) := by
      simpa using hnL
    obtain ⟨nst, -, -, hTrap, hgx, hstuck⟩ := trapIf_reachNR hR hst hkr hholds hdrop' hpc hn
    exact ⟨nst, hTrap, hgx, hstuck⟩
  · -- the block's last instruction
    have hk1 : k + 1 = vb.insts.size := by
      have hks : k < vb.insts.size := (Array.getElem?_eq_some_iff.1 hi).1
      omega
    obtain ⟨_, vb0, _, _, code0, _, _, _, _, _, hvb0, -, -, hchk0, hcode, -⟩ := id hqs
    rw [hvb] at hvb0; cases hvb0
    obtain rfl : its = [] := hchk0.tail_nil hk1
    obtain ⟨j0, vb0, items, pre, c1, X, ps1, psm, ps2, x, hvb0, hit, hsplit, hchk, hc1, hX, hT,
      htr, hdrop, hpc, hst, hterm⟩ := qs_term hR hqs
    rw [hvb] at hvb0; cases hvb0
    obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
    rw [hi] at hi0; cases hi0
    obtain ⟨cc, wh, i2, ops2, hi2, hops2, hstat, -⟩ := op_checked hchk
    rw [hi] at hi2; cases hi2
    rw [hops] at hops2; cases hops2
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
    have hX' : codeLinesE R.ctx R.af [] ps1 = .ok (X, psm) := by
      simpa [List.dropLast_singleton] using hX
    have hXe : codeLinesE R.ctx R.af [] ps1 = .ok ([], ps1) := by simp [codeLinesE]
    rw [hXe] at hX'
    simp only [Except.ok.injEq, Prod.mk.injEq] at hX'
    obtain ⟨hX0, hpsm0⟩ := hX'
    subst hX0
    subst hpsm0
    have hT' : codeLinesE R.ctx R.af [.inst (.trapIf k' code)] ps1 = .ok (x.1.term, ps2) := by
      simpa using hT
    have hl1 := codeLinesE_single hT'
    simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
    obtain ⟨hxe, hpsm⟩ := hl1
    have hxterm : x.1.term = [.ins (k'.insn (.trap ps1.traps.size)) none] := by
      first | exact hxe.symm | exact hxe
    -- the emitted `trapIf` line is kept (its target is the trap label, no block label)
    obtain ⟨hlenO, hLO⟩ := termOk_kept (by simp) (by simp) (by simp) (by simp) hterm
    have hx21L : x.2.1.length = 1 := by rw [hlenO]; simp [hxterm]
    obtain ⟨y, hy⟩ : ∃ y, x.2.1[0]? = some y := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hx21 : x.2.1 = [y] := by
      cases h21 : x.2.1 with
      | nil => rw [h21] at hx21L; simp at hx21L
      | cons a as =>
        have hAs : as = [] := by
          rw [h21] at hx21L
          rw [List.length_cons] at hx21L
          exact List.eq_nil_of_length_eq_zero (by omega)
        rw [h21, hAs] at hy
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
        rw [hAs, hy]
    have hx0 : x.1.term[0]? = some (.ins (k'.insn (.trap ps1.traps.size)) none) := by
      rw [hxterm]; simp
    rcases hLO 0 _ _ hx0 hy with ⟨hyl, -⟩ | ⟨lb, l2, hxt, -, -, -⟩
    · subst hyl
      have hdrop' : R.L.drop j0 = relaxLine R.far (.ins (k'.insn (.trap ps1.traps.size)) none) ++
          R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2) := by
        rw [hdrop, List.nil_append, hx21, relaxLines_cons, relaxLines_nil, List.append_assoc,
          List.nil_append]
      have hpre : ps2.traps.toList <+: R.psF.traps.toList := htr
      have hnL : R.psF.traps.toList[ps1.traps.size]? = some (.trap ps1.traps.size, code) := by
        obtain ⟨t, ht⟩ := hpre
        rw [← ht, ← hpsm]
        simp
      have hn : R.psF.traps[ps1.traps.size]? = some (.trap ps1.traps.size, code) := by
        simpa using hnL
      obtain ⟨nst, -, -, hTrap, hgx, hstuck⟩ := trapIf_reachNR hR hst hkr hholds hdrop' hpc hn
      exact ⟨nst, hTrap, hgx, hstuck⟩
    · cases k' <;> simp [Line.target?, CondBrKind.insn] at hxt
/-- `trapIf_reach_line` with the writes. -/
private theorem trapIf_reach_lineNR {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {m : Loc → CV}
    {w : Arm.ArmState} {kk k' : CondBrKind} {code : Clif.TrapCode} {n j0 : Nat} {T : List Line}
    {us : List CV} (hst : StRel R s m w) (hkr : KindRel m kk k' us)
    (hholds : kk.holds us w = true)
    (hdrop : R.L.drop j0 = relaxLine R.far (.ins (k'.insn (.trap n)) none) ++ T)
    (hpc : Arm.r .PC s = R.pcOf j0)
    (hn : R.psF.traps[n]? = some (.trap n, code)) :
    ∃ nst, TrapAt R.fb R.base code (iterN R.step nst s) ∧ UdfLine R.fa R.base (iterN R.step nst s) ∧
      ∀ i < nst, R.GoodXNY Y (iterN R.step i s) := by
  have hbc : (∃ c, k'.insn (.trap n) = .bcond c (.trap n)) ∨
      (∃ nz wv r, k'.insn (.trap n) = .cbz nz wv r (.trap n)) ∨
      (∃ nz r bit, k'.insn (.trap n) = .tbz nz r bit (.trap n)) := by
    cases k' <;> simp [CondBrKind.insn]
  obtain ⟨nst, jl, hnst, hjt, -, -, -, hgx⟩ := reach_rcbXNR (Y := Y) hR hdrop hbc (by simp) true
    (fun env a ha => by rw [kind_brCond hst hkr _ ha, hholds])
    (fun hct env a ha => by rw [kind_brCond_inv hst hkr _ _ hct ha, hholds])
    (by rw [hst.prog]) hpc hst.err hst.sp
  have hjl := hjt rfl
  -- the final lines: the body's segments' relaxation and the trap section
  obtain ⟨p, hp, hL0, -⟩ := emit_seg hR.emit
  obtain ⟨p2, hplan, hps⟩ := hR.psF
  rw [hplan] at hp
  simp only [Except.ok.injEq] at hp
  subst hp
  have hL : R.L = relaxLines R.far (segLines p2.segs p2.outs) ++ trapLines R.psF := by
    show R.fa.lines.toList = _
    rw [hL0, show (emitFar ⟨R.fa.k, R.af.slotBase⟩ R.af) = R.far from rfl, Plan.lines,
      relaxLines_append, relaxLines_trapLines, hps]
  obtain ⟨hlab, hudf⟩ := trapLines_get R.psF n (.trap n, code) hn
  have hlab' : R.L[(relaxLines R.far (segLines p2.segs p2.outs)).length + 2 * n]? =
      some (.label (.trap n)) := by
    rw [hL, List.getElem?_append_right (by omega)]
    simpa using hlab
  have hudf' : R.L[(relaxLines R.far (segLines p2.segs p2.outs)).length + 2 * n + 1]? =
      some (.ins (.udf 0xc11f) (some code)) := by
    rw [hL, List.getElem?_append_right (by omega)]
    simpa [Nat.add_assoc] using hudf
  -- the branch reaches the label's offset, which is the trap site's
  have hoff : R.pcOf jl = R.pcOf ((relaxLines R.far (segLines p2.segs p2.outs)).length + 2 * n + 1) := by
    have e1 := labelOffsets_label hR.lm hjl
    have e2 := labelOffsets_label hR.lm hlab'
    simp only [RL.pcOf]
    rw [lineOffset_succ _ _ _ hlab']
    simp only [RL.L] at e1 e2 ⊢
    rw [e1] at e2
    simp only [Option.some.injEq] at e2
    rw [e2]; simp [Line.size]
  have hpcF : Arm.r .PC (iterN R.step nst s) =
      R.pcOf ((relaxLines R.far (segLines p2.segs p2.outs)).length + 2 * n + 1) := by
    rw [hnst, Arm.r_of_w_same, hoff]
  have herrF : Arm.r .ERR (iterN R.step nst s) = .None := by
    rw [hnst, Arm.r_of_w_different (by simp)]; exact hst.err
  exact ⟨nst, trapAt_line hR hudf' hpcF herrF, ⟨_, _, hudf', hpcF⟩, hgx⟩

/-- `trap_trapIf` with the trap site's `udf` line. -/
theorem trap_trapIf_lineNR {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState}
    {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {kk : CondBrKind}
    {code : Clif.TrapCode} (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.trapIf kk code)) {ops : Array Operand}
    (hops : (MInst.trapIf kk code).operands = .ok ops)
    (hholds : kk.holds (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = true) :
    ∃ n, TrapAt R.fb R.base code (iterN R.step n s) ∧ UdfLine R.fa R.base (iterN R.step n s) ∧
      ∀ i < n, R.GoodXNY Y (iterN R.step i s) := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  rcases Q.cases hq with hqs | ⟨vbf, allocsf, regsf, if_, xf, bx, hvbf, he, hits, half, hins,
    hasgf, hsuccf, itx, hitx, hqx⟩
  rotate_left
  · -- a forwarding block: its `jump` takes no machine step, but a `trapIf`'s assigned form
    -- is no `jump`
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
    simp [MInst.targets] at htg
  rcases Nat.lt_or_ge (k + 1) vb.insts.size with hkl | hkge
  · -- not the block's last instruction
    obtain ⟨j0, items, pre, regs, i', c1, c2, X', ls1, ps1, psm, psm', ps2, x, cc, wh, ops'',
      rfl, -, -, hasg, hc1', hops', hstat, -, -, h1, hX2, hT2, htr, hdrop, hpc, hst, -, -⟩ :=
      q_op hR hq hvb hi hkl
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
    have hdrop' : R.L.drop j0 = relaxLine R.far (.ins (k'.insn (.trap ps1.traps.size)) none) ++
        (relaxLines R.far (X' ++ x.2.1) ++ R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2)) := by
      rw [hdrop, relaxLines_cons, relaxLines_nil, List.append_assoc, List.nil_append]
    have hpre : psm.traps.toList <+: R.psF.traps.toList :=
      (codeLinesE_traps hX2).trans ((codeLinesE_traps hT2).trans htr)
    have hnL : R.psF.traps.toList[ps1.traps.size]? = some (.trap ps1.traps.size, code) := by
      obtain ⟨t, ht⟩ := hpre
      rw [← ht, ← hpsm]
      simp
    have hn : R.psF.traps[ps1.traps.size]? = some (.trap ps1.traps.size, code) := by
      simpa using hnL
    exact trapIf_reach_lineNR hR hst hkr hholds hdrop' hpc hn
  · -- the block's last instruction
    have hk1 : k + 1 = vb.insts.size := by
      have hks : k < vb.insts.size := (Array.getElem?_eq_some_iff.1 hi).1
      omega
    obtain ⟨_, vb0, _, _, code0, _, _, _, _, _, hvb0, -, -, hchk0, hcode, -⟩ := id hqs
    rw [hvb] at hvb0; cases hvb0
    obtain rfl : its = [] := hchk0.tail_nil hk1
    obtain ⟨j0, vb0, items, pre, c1, X, ps1, psm, ps2, x, hvb0, hit, hsplit, hchk, hc1, hX, hT,
      htr, hdrop, hpc, hst, hterm⟩ := qs_term hR hqs
    rw [hvb] at hvb0; cases hvb0
    obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
    rw [hi] at hi0; cases hi0
    obtain ⟨cc, wh, i2, ops2, hi2, hops2, hstat, -⟩ := op_checked hchk
    rw [hi] at hi2; cases hi2
    rw [hops] at hops2; cases hops2
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
    have hX' : codeLinesE R.ctx R.af [] ps1 = .ok (X, psm) := by
      simpa [List.dropLast_singleton] using hX
    have hXe : codeLinesE R.ctx R.af [] ps1 = .ok ([], ps1) := by simp [codeLinesE]
    rw [hXe] at hX'
    simp only [Except.ok.injEq, Prod.mk.injEq] at hX'
    obtain ⟨hX0, hpsm0⟩ := hX'
    subst hX0
    subst hpsm0
    have hT' : codeLinesE R.ctx R.af [.inst (.trapIf k' code)] ps1 = .ok (x.1.term, ps2) := by
      simpa using hT
    have hl1 := codeLinesE_single hT'
    simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
    obtain ⟨hxe, hpsm⟩ := hl1
    have hxterm : x.1.term = [.ins (k'.insn (.trap ps1.traps.size)) none] := by
      first | exact hxe.symm | exact hxe
    -- the emitted `trapIf` line is kept (its target is the trap label, no block label)
    obtain ⟨hlenO, hLO⟩ := termOk_kept (by simp) (by simp) (by simp) (by simp) hterm
    have hx21L : x.2.1.length = 1 := by rw [hlenO]; simp [hxterm]
    obtain ⟨y, hy⟩ : ∃ y, x.2.1[0]? = some y := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hx21 : x.2.1 = [y] := by
      cases h21 : x.2.1 with
      | nil => rw [h21] at hx21L; simp at hx21L
      | cons a as =>
        have hAs : as = [] := by
          rw [h21] at hx21L
          rw [List.length_cons] at hx21L
          exact List.eq_nil_of_length_eq_zero (by omega)
        rw [h21, hAs] at hy
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
        rw [hAs, hy]
    have hx0 : x.1.term[0]? = some (.ins (k'.insn (.trap ps1.traps.size)) none) := by
      rw [hxterm]; simp
    rcases hLO 0 _ _ hx0 hy with ⟨hyl, -⟩ | ⟨lb, l2, hxt, -, -, -⟩
    · subst hyl
      have hdrop' : R.L.drop j0 = relaxLine R.far (.ins (k'.insn (.trap ps1.traps.size)) none) ++
          R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2) := by
        rw [hdrop, List.nil_append, hx21, relaxLines_cons, relaxLines_nil, List.append_assoc,
          List.nil_append]
      have hpre : ps2.traps.toList <+: R.psF.traps.toList := htr
      have hnL : R.psF.traps.toList[ps1.traps.size]? = some (.trap ps1.traps.size, code) := by
        obtain ⟨t, ht⟩ := hpre
        rw [← ht, ← hpsm]
        simp
      have hn : R.psF.traps[ps1.traps.size]? = some (.trap ps1.traps.size, code) := by
        simpa using hnL
      exact trapIf_reach_lineNR hR hst hkr hholds hdrop' hpc hn
    · cases k' <;> simp [Line.target?, CondBrKind.insn] at hxt
end Backend.Proof
