import FV.E2E.RegLevelOp
import FV.E2E.RegLevelWrites

/-!
# Straight-line forms with their writes (A3, #412, slice F8b)

`RegLevelOp`'s `RunsAs`, `realizes_op_coreX`, `runsAs_of_linesOk`, `realizes_op_next` with
`RL.GoodXW` (`GoodX` and the writes, `RL.WritesAt`): `RunsAsW`, `realizes_op_coreXW`,
`runsAsW_of_linesOk`, `realizes_op_nextW` (the writes of the form's lines, outside the frame
addresses `F ⊇ G` whenever `csem` gives a result: `formOk_writes`).
-/

namespace Backend.Proof

open Backend E2E

/-- The machine runs the lines `ls1` of the allocated instruction `i'`, placed at line `j`, from a
state related to a store and world (`StRel`) and satisfying `pre`, to the state
`exec (R.envOf j) i'` gives, ending at the line after them (in some number of steps: one per
line, or fewer where the machine runs several lines as one hooked step, as for the TLSDESC
sequence of `tls_value`), every state before the end satisfying `GoodXW`. -/
def RunsAsW (R : RL) (exec : Env → MInst → Arm.ArmState → Option Arm.ArmState) (i' : MInst)
    (ls1 : List Line) (pre : Arm.ArmState → Prop) : Prop :=
  ∀ j T s m w s', R.L.drop j = ls1 ++ T → StRel R s m w → Arm.r .PC s = R.pcOf j → pre s →
    exec (R.envOf j) i' s = some s' →
    ∃ n, iterN R.step n s = s' ∧ Arm.r .PC s' = R.pcOf (j + ls1.length) ∧
      ∀ i < n, R.GoodXW (iterN R.step i s)

theorem RunsAsW.mono {R : RL} {exec : Env → MInst → Arm.ArmState → Option Arm.ArmState} {i' : MInst}
    {ls1 : List Line} {P Q : Arm.ArmState → Prop} (h : RunsAsW R exec i' ls1 Q)
    (hPQ : ∀ u, P u → Q u) : RunsAsW R exec i' ls1 P :=
  fun j T s m w s' hd hst hpc hp hex => h j T s m w s' hd hst hpc (hPQ s hp) hex

/-- **An instruction item that falls through, on the machine** (`MStep.op` with control
`next`), for any execution function `exec` of allocated instructions the machine realises from
states satisfying `Pre` (`RunsAs`, given the checker's static facts of the allocation): given
the operand-view obligation for `exec` at the state (`OperandsSoundCtlAt`, keeping the frame
`R.FK`), the machine reaches `Q` at the next item, every state before it satisfying `GoodX`. -/
theorem realizes_op_coreXW {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} {ops : Array Operand} {outs : List CV} {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hops : i.operands = .ok ops)
    (hsz : allocs.size = ops.size)
    (hsem : R.sem i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size)
    {exec : Env → MInst → Arm.ArmState → Option Arm.ArmState}
    (hOS : ∀ env, OperandsSoundCtlAtI R.F R.FK
      (fun i' => ∃ regs, allocs = regs.map Loc.reg ∧ i.assign regs = .ok i') (exec env) R.sem i .next s)
    {Pre : Arm.ArmState → Prop} (hpre : Pre s)
    (hL : ∀ regs i', i.assign regs = .ok i' → allocs = regs.map Loc.reg →
      (∃ env s s', exec env i' s = some s') →
      (∃ (c : CheckCtx) (wh : String), c.checkStatic wh ops (regs.map Loc.reg) i.clobbers = .ok ()) →
      ∃ ls1, (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) ∧
      (∀ ln ∈ ls1, ln.plain = true) ∧ (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us) ∧
      RunsAsW R exec i' ls1 Pre)
    (hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.GoodXW (iterN R.step i s) := by
  have hq' := Q.qs_lt hq hvb hk
  have hne : its ≠ [] := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hvb0, -, -, hchk0, -⟩ := hq'
    rw [hvb] at hvb0
    cases hvb0
    exact hchk0.tail_ne hk
  obtain ⟨j, vb0, items, pre, c1, c2, lsA, X', ps1, psm, psm', ps2, x, hvb0, hit, hsplit, hchk, hc1,
    hc2, h1, h2, h3, htr, hdrop, hpc, hst, hx, hsc⟩ := qs_split hR hq' hne
  rw [hvb] at hvb0
  cases hvb0
  obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
  rw [hi] at hi0
  cases hi0
  obtain ⟨c, wh, i2, ops2, hi2, hops2, hstat, hchk'⟩ := op_checked hchk
  rw [hi] at hi2
  cases hi2
  rw [hops] at hops2
  cases hops2
  -- the instruction's effect
  have hm : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
    hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
  obtain ⟨s', m2, hex, hW, hK, hc2', hr2, hl2⟩ := operandsSound_stepI (hOS (R.envOf j)) hops hstat
    hasg ⟨regs, rfl, hasg⟩ hm hst.world hst.align hst.err hsem hlen
  obtain ⟨ls1, hl1, hpl, hna, hnr, hruns⟩ := hL regs i' hasg rfl ⟨_, _, _, hex⟩ ⟨c, wh, hstat⟩
  rcases hc1' with ⟨rfl, -, -⟩ | ⟨ds, rfl, -⟩ | ⟨us, rfl, -⟩
  rotate_left
  · exact absurd rfl (hna ds)
  · exact absurd rfl (hnr us)
  have h1' : codeLinesE R.ctx R.af [AInst.inst i'] ps1 = .ok (ls1, ps1) := by
    simp [codeLinesE, ainstLines, hl1 ps1, bind, Except.bind, pure, Except.pure]
  rw [h1'] at h1
  simp only [Except.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨hA, -⟩ := h1
  rw [← hA] at hdrop
  -- the lines at `j`
  have hdrop' : R.L.drop j = ls1 ++ (relaxLines R.far (X' ++ x.2.1) ++
      R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2)) := by
    rw [hdrop, relaxLines_plain hpl]
  obtain ⟨nst, hiter, hpc', hgood⟩ := hruns j _ s m w s' hdrop' hst hpc hpre hex
  refine ⟨nst, _, MStep.op hvb hi hops hsz hsem hlen (HavocOuts.refl _ _ _) hc2' (MNext.next hk), ?_,
    hgood⟩
  have hfr := R.frameOkK hR
  refine qs_next hvb hit hsplit hchk' hc2 h2 h3 htr hdrop ?_ ?_ hx hsc
  · rw [relaxLines_plain hpl, hiter, hpc']
  · rw [hiter]
    have hsp' : spOf s' = R.spB := hK.1.trans hst.sp
    have herr' : Arm.r .ERR s' = .None := by
      rw [hW.1 .ERR (by simp [Masked]), hW'.1]
    refine ⟨fun l hl hL => ?_, hW, herr', ?_, hsp', align_of_sp (by rw [hsp', hst.sp]) hst.align,
      fun hframe => ?_, code_keep hR.prog0 hst.code fun a ha => hK.2.1 a (.inl (.inr (.inr ha))),
      fun a ha => (hK.2.1 a (.inr ha)).trans (hst.gkeep a ha), fun hf => hK.2.2.trans (hst.fp hf)⟩
    · cases l with
      | reg r => exact hr2 r (hl r rfl)
      | stack k' c =>
        rw [hl2 _ (fun r h => by cases h), hst.store _ hl hL,
          locVal_frame_keep hfr hst.sp hK hL (fun r h => by cases h)]
      | save r =>
        rw [hl2 _ (fun r h => by cases h), hst.store _ hl hL,
          locVal_frame_keep hfr hst.sp hK hL (fun r h => by cases h)]
    · rw [hW.2.2, hW'.2, ← hst.world.2.2, hst.prog]
    · rw [← hst.fplr hframe]
      exact read_mem_bytes_congr _ _ (fun k hk => hK.2.1 _ (fplr_inF hR hframe k hk))

/-- Straight-line lines (`LinesOk`) run on the machine as `execMInst` runs them. -/
theorem runsAsW_of_linesOk {R : RL} (hR : R.Wf) {i' : MInst} {ls1 : List Line}
    (hl1 : ∀ ps, i'.lines R.ctx ps = .ok (ls1, ps))
    (hins : ∀ ln ∈ ls1, ∃ x t, ln = .ins x t ∧ x.hooked = false)
    (hint : ∀ env s s', Arm.r .ERR s = .None → execLines env ls1 s = some s' → InterOk env ls1 s) :
    RunsAsW R (fun env => execMInst R.ctx env) i' ls1 fun u =>
      ∀ env, LinesReads env ls1 u R.ReadOk ∧ LinesWrites env ls1 u (fun a => ¬ R.G a) := by
  intro j T s _ _ s' hdrop' hst hpc hrd hex
  have hprog := hst.prog
  have herr := hst.err
  have hat : ∀ k ln, ls1[k]? = some ln → R.fa.lines.toList[j + k]? = some ln := by
    intro k ln hk
    have := congrArg (·[k]?) hdrop'
    simp only [List.getElem?_drop, RL.L] at this
    rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk).1]
    exact hk
  have hins' : ∀ ln ∈ ls1, ∃ i t, ln = .ins i t := fun ln h => by
    obtain ⟨i, t, e, -⟩ := hins ln h; exact ⟨i, t, e⟩
  have hrun : execLines (R.envOf j) ls1 s = some s' := by
    simp only [execMInst, hl1] at hex; exact hex
  have hhook : ∀ i t, Line.ins i t ∈ ls1 → i.hooked = false := fun i t h => by
    obtain ⟨i', t', e, hh⟩ := hins _ h; cases e; exact hh
  refine ⟨ls1.length, iterN_execLines hR.layout hR.lm hR.fit ls1 j s s' hat hhook
      hprog (by rw [hpc]; rfl) herr (hint _ _ _ herr hrun) hrun, ?_,
    R.goodXW_execLines hR hat hhook (noTlsTail_of_unhooked (hl1 {}) hhook) hprog hpc herr hst.sp
      (hint _ _ _ herr hrun) hrun (hrd _).1 (hrd _).2⟩
  rw [execLines_pc hrun, hpc]
  simp only [RL.pcOf, RL.L]
  rw [lineOffset_drop_ins (by simpa [RL.L] using hdrop') hins', BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

/-- **A straight-line instruction on the machine** (`MStep.op` with control `next`): given
`OperandsSound` for the instruction, `LinesOk` for its allocated form and the reads of its
allocated lines (outside the frame addresses whenever `csem` gives a result, `formOk_reads`), the
machine runs its lines and reaches `Q` at the next item, every state before it satisfying `GoodX`. -/
theorem realizes_op_nextW {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} {ops : Array Operand} {outs : List CV} {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hops : i.operands = .ok ops)
    (hsz : allocs.size = ops.size)
    (hsem : R.sem i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size)
    (hOS : ∀ env, OperandsSound R.F (execMInst R.ctx env) (csem R.F R.ctx R.X) i)
    (hL : ∀ regs i', i.assign regs = .ok i' →
      LinesOk R.ctx i' ∧ (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us))
    (hRd : ∀ {regs : Array Reg} {i' : MInst} {ls : List Line} {ps ps' : PState} {u v : Arm.ArmState}
      {r : List CV × Arm.ArmState × Ctl}, AllocOk ops regs → i.assign regs = .ok i' →
      i'.lines R.ctx ps = .ok (ls, ps') → SameWorld R.F u v → Arm.r .ERR v = .None →
      Arm.CheckSPAlignment v → csem R.F R.ctx R.X i (useVals ops regs u) v = some r → ∀ env,
      LinesReads env ls u (fun a => ¬ R.F a))
    (hWr : ∀ {regs : Array Reg} {i' : MInst} {ls : List Line} {ps ps' : PState} {u v : Arm.ArmState}
      {r : List CV × Arm.ArmState × Ctl}, AllocOk ops regs → i.assign regs = .ok i' →
      i'.lines R.ctx ps = .ok (ls, ps') → SameWorld R.F u v → Arm.r .ERR v = .None →
      Arm.CheckSPAlignment v → csem R.F R.ctx R.X i (useVals ops regs u) v = some r → ∀ env,
      LinesWrites env ls u (fun a => ¬ R.F a))
    (hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.GoodXW (iterN R.step i s) := by
  have hpre : ∀ regs i' ls1, allocs = regs.map Loc.reg → i.assign regs = .ok i' →
      (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) → ∀ env,
        LinesReads env ls1 s R.ReadOk ∧ LinesWrites env ls1 s (fun a => ¬ R.G a) := by
    intro regs i' ls1 hal' hasg hl1 env
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hvb0, -, -, hchk, -, -, -, -, -, -, hst, -⟩ :=
      Q.qs_lt hq hvb hk
    rw [hvb] at hvb0
    cases hvb0
    obtain ⟨c, wh, i2, ops2, hi2, hops2, hstat, -⟩ := op_checked hchk
    rw [hi] at hi2
    cases hi2
    rw [hops] at hops2
    cases hops2
    subst hal'
    have hm : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
      hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
    rw [useVals_of_store hstat hm] at hsem
    have herrw : Arm.r .ERR w = .None := by
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    have halw : Arm.CheckSPAlignment w := by
      simpa [Arm.CheckSPAlignment, Arm.read_gpr, (hst.world.1 (.GPR 31#5) (by simp [Masked])).symm]
        using hst.align
    exact ⟨(hRd (allocOk_of_checkStatic hstat) hasg (hl1 {}) hst.world herrw halw (R.sem_csem hsem)
      env).mono fun a ha => .inl fun hG => ha (RL.FK_F (.inr hG)),
      (hWr (allocOk_of_checkStatic hstat) hasg (hl1 {}) hst.world herrw halw (R.sem_csem hsem)
      env).mono fun a ha hG => ha (RL.FK_F (.inr hG))⟩
  exact realizes_op_coreXW hR hq hvb hi hops hsz hsem hlen hk (exec := fun env => execMInst R.ctx env)
    (fun env => (((hOS env).at (fun _ => RL.FK_F) s).toI _).v R.gv) (Pre := fun u =>
      ∀ regs i' ls1, allocs = regs.map Loc.reg → i.assign regs = .ok i' →
        (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) → ∀ env,
          LinesReads env ls1 u R.ReadOk ∧ LinesWrites env ls1 u (fun a => ¬ R.G a)) hpre
    (fun regs i' hasg hal' _ _ => by
      obtain ⟨⟨ls1, hl1, hins, hpl, hint⟩, hna, hnr⟩ := hL regs i' hasg
      exact ⟨ls1, hl1, hpl, hna, hnr, (runsAsW_of_linesOk hR hl1 hins hint).mono
        fun u hu env => hu regs i' ls1 hal' hasg hl1 env⟩) hW'

end Backend.Proof
