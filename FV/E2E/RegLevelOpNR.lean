import FV.E2E.RegLevelOp
import FV.E2E.RegLevelNoCall
import FV.E2E.RegLevelReadsIn


/-!
# Straight-line instructions with no call state (SEM1 #537, step 2k)

`RunsAs`, `realizes_op_coreX`, `runsAs_of_linesOk`, `realizes_op_next` with `RL.GoodXNR` (docs/plans/uninit.md §5.5).
-/

namespace Backend.Proof

open Backend E2E

/-- The machine runs the lines `ls1` of the allocated instruction `i'`, placed at line `j`, from a
state related to a store and world (`StRel`) and satisfying `pre`, to the state
`exec (R.envOf j) i'` gives, ending at the line after them (in some number of steps: one per
line, or fewer where the machine runs several lines as one hooked step, as for the TLSDESC
sequence of `tls_value`), every state before the end satisfying `GoodXNY Y`. -/
def RunsAsNY (R : RL) (Y : BitVec 64 → Prop) (exec : Env → MInst → Arm.ArmState → Option Arm.ArmState)
    (i' : MInst) (ls1 : List Line) (pre : Arm.ArmState → Prop) : Prop :=
  ∀ j T s m w s', R.L.drop j = ls1 ++ T → StRel R s m w → Arm.r .PC s = R.pcOf j → pre s →
    exec (R.envOf j) i' s = some s' →
    ∃ n, iterN R.step n s = s' ∧ Arm.r .PC s' = R.pcOf (j + ls1.length) ∧
      ∀ i < n, R.GoodXNY Y (iterN R.step i s)

/-- `RunsAsNY` at `Y := F`: every state before the end satisfying `GoodXNR`. -/
def RunsAsNR (R : RL) (exec : Env → MInst → Arm.ArmState → Option Arm.ArmState) (i' : MInst)
    (ls1 : List Line) (pre : Arm.ArmState → Prop) : Prop :=
  RunsAsNY R R.F exec i' ls1 pre

theorem RunsAsNY.mono {R : RL} {Y : BitVec 64 → Prop}
    {exec : Env → MInst → Arm.ArmState → Option Arm.ArmState} {i' : MInst}
    {ls1 : List Line} {P Q : Arm.ArmState → Prop} (h : RunsAsNY R Y exec i' ls1 Q)
    (hPQ : ∀ u, P u → Q u) : RunsAsNY R Y exec i' ls1 P :=
  fun j T s m w s' hd hst hpc hp hex => h j T s m w s' hd hst hpc (hPQ s hp) hex

theorem RunsAsNR.mono {R : RL} {exec : Env → MInst → Arm.ArmState → Option Arm.ArmState} {i' : MInst}
    {ls1 : List Line} {P Q : Arm.ArmState → Prop} (h : RunsAsNR R exec i' ls1 Q)
    (hPQ : ∀ u, P u → Q u) : RunsAsNR R exec i' ls1 P :=
  RunsAsNY.mono h hPQ

/-- **An instruction item that falls through, on the machine** (`MStep.op` with control
`next`), for any execution function `exec` of allocated instructions the machine realises from
states satisfying `Pre` (`RunsAsNR`, given the checker's static facts of the allocation): given
the operand-view obligation for `exec` at the state (`OperandsSoundCtlAt`, keeping the frame
`R.FK`), the machine reaches `Q` at the next item, every state before it satisfying `GoodX`. -/
theorem realizes_op_coreXNR {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {b k : Nat}
    {allocs : Array Loc}
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
      RunsAsNY R Y exec i' ls1 Pre)
    (hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.GoodXNY Y (iterN R.step i s) := by
  obtain ⟨j, vb0, items, pre, code, ls, ps1, ps2, T, hvb0, hit, hsplit, hchk, hcode, hls, htr, hdrop,
    hpc, hst⟩ := hq
  rw [hvb] at hvb0
  cases hvb0
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
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
  obtain ⟨ls1', ls2, psm, h1, h2, rfl⟩ := codeLinesE_append _ _ _ _ _ hls
  have h1' : codeLinesE R.ctx R.af [AInst.inst i'] ps1 = .ok (ls1, ps1) := by
    simp [codeLinesE, ainstLines, hl1 ps1, bind, Except.bind, pure, Except.pure]
  rw [h1'] at h1
  simp only [Except.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  -- the lines at `j`
  have hZ : ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  have hdrop' : R.L.drop j = ls1 ++ (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T) := by
    rw [hdrop, List.append_assoc, ftR_plain_append _ _ _ hpl hZ, List.append_assoc]
  obtain ⟨nst, hiter, hpc', hgood⟩ := hruns j _ s m w s' hdrop' hst hpc hpre hex
  refine ⟨nst, _, MStep.op hvb hi hops hsz hsem hlen (HavocOuts.refl _ _ _) hc2' (MNext.next hk), ?_,
    hgood⟩
  have hfr := R.frameOkK hR
  refine ⟨j + ls1.length, vb, items, pre ++ [.op k (regs.map Loc.reg)], c2, ls2, ps1, ps2, T, hvb,
    hit, by rw [hsplit]; simp, hchk', hc2, h2, htr, ?_, ?_, ?_⟩
  · rw [← List.drop_drop, hdrop', List.drop_left]
  · rw [hiter, hpc']
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
theorem runsAs_of_linesOkNR {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {i' : MInst} {ls1 : List Line}
    (hl1 : ∀ ps, i'.lines R.ctx ps = .ok (ls1, ps))
    (hins : ∀ ln ∈ ls1, ∃ x t, ln = .ins x t ∧ x.hooked = false)
    (hint : ∀ env s s', Arm.r .ERR s = .None → execLines env ls1 s = some s' → InterOk env ls1 s) :
    RunsAsNY R Y (fun env => execMInst R.ctx env) i' ls1 fun u =>
      ∀ env, LinesReads env ls1 u (R.ReadInY Y false) := by
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
    R.goodXNR_execLines hR hat hhook (noTlsTail_of_unhooked (hl1 {}) hhook) hprog hpc herr hst.sp
      (hint _ _ _ herr hrun) hrun (hrd _)⟩
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
theorem realizes_op_nextNR {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
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
    (hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.GoodXNR (iterN R.step i s) := by
  have hpre : ∀ regs i' ls1, allocs = regs.map Loc.reg → i.assign regs = .ok i' →
      (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) → ∀ env, LinesReads env ls1 s (R.ReadIn false) := by
    intro regs i' ls1 hal' hasg hl1 env
    obtain ⟨j, vb0, items, pre, code, ls, ps1, ps2, T, hvb0, hit, hsplit, hchk, hcode, hls, htr, hdrop,
      hpc, hst⟩ := hq
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
    exact (hRd (allocOk_of_checkStatic hstat) hasg (hl1 {}) hst.world herrw halw (R.sem_csem hsem)
      env).mono fun a ha => .inr (.inr ⟨ha, ha⟩)
  exact realizes_op_coreXNR hR hq hvb hi hops hsz hsem hlen hk (exec := fun env => execMInst R.ctx env)
    (fun env => (((hOS env).at (fun _ => RL.FK_F) s).toI _).v R.gv) (Pre := fun u =>
      ∀ regs i' ls1, allocs = regs.map Loc.reg → i.assign regs = .ok i' →
        (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) → ∀ env, LinesReads env ls1 u (R.ReadIn false)) hpre
    (fun regs i' hasg hal' _ _ => by
      obtain ⟨⟨ls1, hl1, hins, hpl, hint⟩, hna, hnr⟩ := hL regs i' hasg
      exact ⟨ls1, hl1, hpl, hna, hnr, (runsAs_of_linesOkNR hR hl1 hins hint).mono
        fun u hu env => hu regs i' ls1 hal' hasg hl1 env⟩) hW'

/-- **`realizes_op_nextNR` with the world reads guarded by `Y`** (SEM1 item (2)): when the
instruction's `csem` also gives a result at a guard set `Y ⊇ F` (`hsemY`), the reads of its
lines (`formOk_reads`, generic in the frame set) avoid `Y` too, so every state before the next
item satisfies `GoodXNY Y`. -/
theorem realizes_op_nextNY {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} (hYF : ∀ a, R.F a → Y a)
    {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} {ops : Array Operand} {outs : List CV} {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hops : i.operands = .ok ops)
    (hsz : allocs.size = ops.size)
    (hsem : R.sem i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    {rY : List CV × Arm.ArmState × Ctl}
    (hsemY : csem Y R.ctx R.X i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some rY)
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size)
    (hOS : ∀ env, OperandsSound R.F (execMInst R.ctx env) (csem R.F R.ctx R.X) i)
    (hL : ∀ regs i', i.assign regs = .ok i' →
      LinesOk R.ctx i' ∧ (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us))
    (hRd : ∀ {F' : BitVec 64 → Prop} {regs : Array Reg} {i' : MInst} {ls : List Line}
      {ps ps' : PState} {u v : Arm.ArmState}
      {r : List CV × Arm.ArmState × Ctl}, AllocOk ops regs → i.assign regs = .ok i' →
      i'.lines R.ctx ps = .ok (ls, ps') → SameWorld F' u v → Arm.r .ERR v = .None →
      Arm.CheckSPAlignment v → csem F' R.ctx R.X i (useVals ops regs u) v = some r → ∀ env,
      LinesReads env ls u (fun a => ¬ F' a))
    (hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.GoodXNY Y (iterN R.step i s) := by
  have hpre : ∀ regs i' ls1, allocs = regs.map Loc.reg → i.assign regs = .ok i' →
      (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) → ∀ env, LinesReads env ls1 s (R.ReadInY Y false) := by
    intro regs i' ls1 hal' hasg hl1 env
    obtain ⟨j, vb0, items, pre, code, ls, ps1, ps2, T, hvb0, hit, hsplit, hchk, hcode, hls, htr, hdrop,
      hpc, hst⟩ := hq
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
    rw [useVals_of_store hstat hm] at hsem hsemY
    have herrw : Arm.r .ERR w = .None := by
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    have halw : Arm.CheckSPAlignment w := by
      simpa [Arm.CheckSPAlignment, Arm.read_gpr, (hst.world.1 (.GPR 31#5) (by simp [Masked])).symm]
        using hst.align
    have hF := hRd (allocOk_of_checkStatic hstat) hasg (hl1 {}) hst.world herrw halw
      (R.sem_csem hsem) env
    have hswY : SameWorld Y s w :=
      ⟨hst.world.1, fun a ha => hst.world.2.1 a (fun hf => ha (hYF a hf)), hst.world.2.2⟩
    have hY := hRd (allocOk_of_checkStatic hstat) hasg (hl1 {}) hswY herrw halw hsemY env
    exact fun k x t hk s1 hs1 env' a ha p hp q hq =>
      .inr (.inr ⟨hF k x t hk s1 hs1 env' a ha p hp q hq, hY k x t hk s1 hs1 env' a ha p hp q hq⟩)
  exact realizes_op_coreXNR hR hq hvb hi hops hsz hsem hlen hk (exec := fun env => execMInst R.ctx env)
    (fun env => (((hOS env).at (fun _ => RL.FK_F) s).toI _).v R.gv) (Pre := fun u =>
      ∀ regs i' ls1, allocs = regs.map Loc.reg → i.assign regs = .ok i' →
        (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) → ∀ env, LinesReads env ls1 u (R.ReadInY Y false))
    hpre
    (fun regs i' hasg hal' _ _ => by
      obtain ⟨⟨ls1, hl1, hins, hpl, hint⟩, hna, hnr⟩ := hL regs i' hasg
      exact ⟨ls1, hl1, hpl, hna, hnr, (runsAs_of_linesOkNR hR hl1 hins hint).mono
        fun u hu env => hu regs i' ls1 hal' hasg hl1 env⟩) hW'


end Backend.Proof
