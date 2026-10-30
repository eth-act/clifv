import FV.E2E.RegLevelFRFree
import FV.E2E.RegLevelOpNR

/-!
# Straight-line instructions, at a witness (SEM1 #537, item (3), route (a))

`RunsAsNY` with where the states are (`RunsAsNA`: inside the instruction's lines, no step exactly
for no line), `realizes_op_coreXNR`/`realizes_op_nextNY` from `QW`: the next item at the straight
witness, reached at the first arrival.
-/

namespace Backend.Proof

open Backend E2E

/-- **`RunsAsNY` with the states inside the lines** (`RL.Inside`) and no step exactly when there
is no line. -/
def RunsAsNA (R : RL) (Y : BitVec 64 → Prop) (exec : Env → MInst → Arm.ArmState → Option Arm.ArmState)
    (i' : MInst) (ls1 : List Line) (pre : Arm.ArmState → Prop) : Prop :=
  ∀ j T s m w s', R.L.drop j = ls1 ++ T → StRel R s m w → Arm.r .PC s = R.pcOf j → pre s →
    exec (R.envOf j) i' s = some s' →
    ∃ n, iterN R.step n s = s' ∧ Arm.r .PC s' = R.pcOf (j + ls1.length) ∧
      (∀ i < n, R.GoodXNY Y (iterN R.step i s)) ∧ R.Inside s n j (j + ls1.length) ∧
      (n = 0 ↔ ls1 = [])

theorem RunsAsNA.mono {R : RL} {Y : BitVec 64 → Prop}
    {exec : Env → MInst → Arm.ArmState → Option Arm.ArmState} {i' : MInst}
    {ls1 : List Line} {P Q : Arm.ArmState → Prop} (h : RunsAsNA R Y exec i' ls1 Q)
    (hPQ : ∀ u, P u → Q u) : RunsAsNA R Y exec i' ls1 P :=
  fun j T s m w s' hd hst hpc hp hex => h j T s m w s' hd hst hpc (hPQ s hp) hex

/-- **`realizes_op_coreXNA` with the segment's lines** (`RL.FRFree`). -/
theorem realizes_op_coreXNAF {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState}
    {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩))
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
      RunsAsNA R Y exec i' ls1 Pre)
    (hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      R.SegNA Y s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' n ∧ R.FRFree s n := by
  obtain ⟨vb0, items, pre, code, ls, ps2, hvb0, hit, hsplit, hchk, hcode, hls, htr, hdrop,
    hpc, hst⟩ := hq
  rw [hvb] at hvb0
  cases hvb0
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  have hc1o := hc1
  obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
  rw [hi] at hi0
  cases hi0
  obtain ⟨c, wh, i2, ops2, hi2, hops2, hstat, hchk'⟩ := op_checked hchk
  rw [hi] at hi2
  cases hi2
  rw [hops] at hops2
  cases hops2
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
  have hWs := RL.straightW_eq (T := T) (j := j) hvb hc1o h1'
  rw [relaxLines_plain hpl] at hWs
  rw [h1'] at h1
  simp only [Except.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  have hZ : ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  have hdrop' : R.L.drop j = ls1 ++ (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T) := by
    rw [hdrop, List.append_assoc, ftR_plain_append _ _ _ hpl hZ, List.append_assoc]
  obtain ⟨nst, hiter, hpc', hgood, hin, hn0⟩ := hruns j _ s m w s' hdrop' hst hpc hpre hex
  have hW1 : ∀ (m' : Loc → CV) (w'' : Arm.ArmState),
      R.nextW j ps1 T (.run ⟨b, .op k (regs.map Loc.reg) :: its, m, w⟩) (.run ⟨b, its, m', w''⟩) =
        (j + ls1.length, ps1, T) := fun _ _ => RL.nextW_straight.trans hWs
  refine ⟨nst, _, MStep.op hvb hi hops hsz hsem hlen (HavocOuts.refl _ _ _) hc2' (MNext.next hk),
    ⟨?_, hgood, ?_, ?_⟩, ?_⟩
  · rw [hW1]
    have hfr := R.frameOkK hR
    refine ⟨vb, items, pre ++ [.op k (regs.map Loc.reg)], c2, ls2, ps2, hvb,
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
  · rw [hW1]
    have hpn : Arm.r .PC (iterN R.step nst s) = R.pcOf (j + ls1.length) := by rw [hiter, hpc']
    rcases Nat.eq_zero_or_pos nst with h0 | h0
    · subst h0
      exact ⟨hpn, fun i h0 hi => absurd hi (by omega)⟩
    · have hne : ls1 ≠ [] := fun he => absurd (hn0.mpr he) (by omega)
      obtain ⟨ln, lt, hcons⟩ := List.exists_cons_of_ne_nil hne
      have hj0 : R.L[j]? = some ln := by
        have := congrArg (·[0]?) hdrop'
        simp only [List.getElem?_drop, Nat.add_zero, hcons, List.cons_append,
          List.getElem?_cons_zero] at this
        exact this
      have hpln := hpl ln (by rw [hcons]; exact List.mem_cons_self ..)
      cases ln with
      | ins x t => exact RL.firstArr_of_inside hR hj0 hin (Nat.le_refl _) hpn
      | _ => simp [Line.plain] at hpln
  · rw [RL.segLen_straight_iff, hWs, hn0]
    simp
  · refine RL.frFree_inside hR hdrop' (Nat.le_refl _) (frLine_lines (hl1 ps1)) hpc (fun h0 => ?_) hin
    have hne : ls1 ≠ [] := fun he => absurd (hn0.mpr he) (by omega)
    obtain ⟨ln, lt, hcons⟩ := List.exists_cons_of_ne_nil hne
    have hj0 : R.L[j]? = some ln := by
      have := congrArg (·[0]?) hdrop'
      simp only [List.getElem?_drop, Nat.add_zero, hcons, List.cons_append,
        List.getElem?_cons_zero] at this
      exact this
    have hpln := hpl ln (by rw [hcons]; exact List.mem_cons_self ..)
    refine ⟨by rw [hcons]; simp, ?_⟩
    cases ln with
    | ins x t => exact ⟨x, t, hj0⟩
    | _ => simp [Line.plain] at hpln

/-- `realizes_op_coreXNR` from `QW`, on `RunsAsNA`: the next item at the straight witness, at the
first arrival. -/
theorem realizes_op_coreXNA {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState}
    {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩))
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
      RunsAsNA R Y exec i' ls1 Pre)
    (hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      R.SegNA Y s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' n :=
  let ⟨n, c'', h1, h2, _⟩ := realizes_op_coreXNAF hR hq hvb hi hops hsz hsem hlen hk hOS hpre hL hW'
  ⟨n, c'', h1, h2⟩

/-- **Straight-line lines** (`runsAs_of_linesOkNR`) **with where the states are.** -/
theorem runsAs_of_linesOkNA {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {i' : MInst}
    {ls1 : List Line}
    (hl1 : ∀ ps, i'.lines R.ctx ps = .ok (ls1, ps))
    (hins : ∀ ln ∈ ls1, ∃ x t, ln = .ins x t ∧ x.hooked = false)
    (hint : ∀ env s s', Arm.r .ERR s = .None → execLines env ls1 s = some s' → InterOk env ls1 s) :
    RunsAsNA R Y (fun env => execMInst R.ctx env) i' ls1 fun u =>
      ∀ env, LinesReads env ls1 u (R.ReadInY Y false) := by
  intro j T s m w s' hdrop' hst hpc hrd hex
  obtain ⟨n, hiter, hpc', hg⟩ := runsAs_of_linesOkNR hR (Y := Y) hl1 hins hint j T s m w s' hdrop'
    hst hpc hrd hex
  have hprog := hst.prog
  have herr := hst.err
  have hat : ∀ k ln, ls1[k]? = some ln → R.fa.lines.toList[j + k]? = some ln := by
    intro k ln hk
    have := congrArg (·[k]?) hdrop'
    simp only [List.getElem?_drop, RL.L] at this
    rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk).1]
    exact hk
  have hrun : execLines (R.envOf j) ls1 s = some s' := by
    simp only [execMInst, hl1] at hex; exact hex
  have hhook : ∀ i t, Line.ins i t ∈ ls1 → i.hooked = false := fun i t h => by
    obtain ⟨i', t', e, hh⟩ := hins _ h; cases e; exact hh
  have hit := iterN_execLines (X := R.X) (H := R.H) hR.layout hR.lm hR.fit ls1 j s s' hat hhook
    hprog (by rw [hpc]; rfl) herr (hint _ _ _ herr hrun) hrun
  have hpcs := iterN_execLines_pc (X := R.X) (H := R.H) hR.layout hR.lm hR.fit ls1 j s s' hat hhook
    hprog (by rw [hpc]; rfl) herr (hint _ _ _ herr hrun) hrun
  refine ⟨ls1.length, hit, hpc', ?_, fun i h0 hi => ?_, by simp⟩
  · intro i hi
    exact R.goodXNR_execLines hR hat hhook (noTlsTail_of_unhooked (hl1 {}) hhook) hprog hpc herr
      hst.sp (hint _ _ _ herr hrun) hrun (hrd _) i hi
  · obtain ⟨ln, hln⟩ : ∃ ln, ls1[i]? = some ln := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨x, t, rfl, -⟩ := hins _ (List.mem_of_getElem? hln)
    exact ⟨j + i, x, t, by omega, by omega, hat i _ hln, hpcs i (by omega)⟩

/-- **`realizes_op_nextNA` with the segment's lines** (`RL.FRFree`). -/
theorem realizes_op_nextNAF {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} (hYF : ∀ a, R.F a → Y a)
    {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩))
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
      R.SegNA Y s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' n ∧ R.FRFree s n := by
  have hpre : ∀ regs i' ls1, allocs = regs.map Loc.reg → i.assign regs = .ok i' →
      (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) → ∀ env, LinesReads env ls1 s (R.ReadInY Y false) := by
    intro regs i' ls1 hal' hasg hl1 env
    obtain ⟨vb0, items, pre, code, ls, ps2, hvb0, hit, hsplit, hchk, hcode, hls, htr, hdrop,
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
      .inr (.inr (.inl ⟨hF k x t hk s1 hs1 env' a ha p hp q hq, hY k x t hk s1 hs1 env' a ha p hp q hq⟩))
  exact realizes_op_coreXNAF hR hq hvb hi hops hsz hsem hlen hk (exec := fun env => execMInst R.ctx env)
    (fun env => (((hOS env).at (fun _ => RL.FK_F) s).toI _).v R.gv) (Pre := fun u =>
      ∀ regs i' ls1, allocs = regs.map Loc.reg → i.assign regs = .ok i' →
        (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) → ∀ env, LinesReads env ls1 u (R.ReadInY Y false))
    hpre
    (fun regs i' hasg hal' _ _ => by
      obtain ⟨⟨ls1, hl1, hins, hpl, hint⟩, hna, hnr⟩ := hL regs i' hasg
      exact ⟨ls1, hl1, hpl, hna, hnr, (runsAs_of_linesOkNA hR hl1 hins hint).mono
        fun u hu env => hu regs i' ls1 hal' hasg hl1 env⟩) hW'

/-- **`realizes_op_nextNY` from `QW`**: the next item at the straight witness, at the first
arrival. -/
theorem realizes_op_nextNA {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} (hYF : ∀ a, R.F a → Y a)
    {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩))
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
      R.SegNA Y s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' n :=
  let ⟨n, c'', h1, h2, _⟩ := realizes_op_nextNAF hR hYF hq hvb hi hops hsz hsem hsemY hlen hk hOS
    hL hRd hW'
  ⟨n, c'', h1, h2⟩

end Backend.Proof
