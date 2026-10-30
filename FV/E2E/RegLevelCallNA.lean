import FV.E2E.RegLevelFRFree
import FV.E2E.RegLevelCallN

/-!
# Calls and symbol addresses, at a witness (SEM1 #537, item (3), route (a))

`realizes_op_coreXS` from `QW` (`realizes_op_coreXSW`: the next item at the straight witness,
with the item's lines), `RL.segLen_straight_of` (a straight segment inside its lines is a first
arrival), and `realizes_callNR`/`realizes_symAddrNR` from `QW` (`realizes_callNA`,
`realizes_symAddrNA`).
-/

namespace Backend.Proof

open Backend E2E

/-- The targets of a straight step: the line of the step's next witness (at any arrival pc). -/
theorem RL.tgtS_of_straight {R : RL} {j : Nat} {ps1 : PState} {T : List Line}
    {c c'' : MConf CV Arm.ArmState} (hS : RL.Straight c c'') (p : BitVec 64) :
    R.TgtS j ps1 T c c'' = (· = R.pcOf (R.nextW j ps1 T c c'' p).1) := by
  unfold RL.Straight at hS
  split at hS
  · obtain ⟨rfl, rfl⟩ := hS
    rw [RL.tgtS_straight, RL.nextW_straight]
  · exact hS.elim

/-- **A straight segment inside its plain lines `ls1` from line `j`, ending at the line after them,
with no step exactly for no line, has `SegLen`.** -/
theorem RL.segLen_straight_of {R : RL} (hR : R.Wf) {j : Nat} {ps1 : PState} {T : List Line}
    {c c'' : MConf CV Arm.ArmState} {s : Arm.ArmState} {n : Nat} {ls1 : List Line}
    (hS : RL.Straight c c'') (hW : ∀ p, (R.nextW j ps1 T c c'' p).1 = j + ls1.length)
    (hT : ∃ T', R.L.drop j = ls1 ++ T') (hpl : ∀ ln ∈ ls1, ln.plain = true)
    (hpn : Arm.r .PC (iterN R.step n s) = R.pcOf (j + ls1.length))
    (hin : R.Inside s n j (j + ls1.length)) (hn0 : n = 0 ↔ ls1 = []) :
    R.SegLen j ps1 T c c'' s n := by
  refine ⟨?_, ?_⟩
  · rw [RL.tgtS_of_straight hS 0, hW]
    refine firstArrS_singleton.mpr ?_
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      exact ⟨hpn, fun i h0 hi => absurd hi (by omega)⟩
    · have hne : ls1 ≠ [] := fun he => absurd (hn0.mpr he) (by omega)
      obtain ⟨ln, lt, hcons⟩ := List.exists_cons_of_ne_nil hne
      obtain ⟨T', hT'⟩ := hT
      have hj0 : R.L[j]? = some ln := by
        have := congrArg (·[0]?) hT'
        simp only [List.getElem?_drop, Nat.add_zero, hcons, List.cons_append,
          List.getElem?_cons_zero] at this
        exact this
      have hpln := hpl ln (by rw [hcons]; exact List.mem_cons_self ..)
      cases ln with
      | ins x t => exact RL.firstArr_of_inside hR hj0 hin (Nat.le_refl _) hpn
      | _ => simp [Line.plain] at hpln
  · unfold RL.EmptyW
    rw [if_pos hS, hW, hn0]
    simp

/-- `RunsAsS` with a segment fact that sees the item's lines and their first line. -/
def RunsAsSJ (R : RL) (exec : Env → MInst → Arm.ArmState → Option Arm.ArmState) (i' : MInst)
    (ls1 : List Line) (pre : Arm.ArmState → Prop)
    (SegJ : List Line → Nat → Arm.ArmState → Nat → Prop) : Prop :=
  ∀ j T s m w s', R.L.drop j = ls1 ++ T → StRel R s m w → Arm.r .PC s = R.pcOf j → pre s →
    exec (R.envOf j) i' s = some s' →
    ∃ n, iterN R.step n s = s' ∧ Arm.r .PC s' = R.pcOf (j + ls1.length) ∧ SegJ ls1 j s n

/-- `realizes_op_coreXS` from `QW` (`RunsAsSJ`): the next item at the straight witness, with the
item's lines. -/
theorem realizes_op_coreXSW {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat}
    {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {j : Nat}
    {ps1 : PState} {T : List Line}
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
    {SegJ : List Line → Nat → Arm.ArmState → Nat → Prop}
    (hL : ∀ regs i', i.assign regs = .ok i' → allocs = regs.map Loc.reg →
      (∃ env s s', exec env i' s = some s') →
      (∃ (c : CheckCtx) (wh : String), c.checkStatic wh ops (regs.map Loc.reg) i.clobbers = .ok ()) →
      ∃ ls1, (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) ∧
      (∀ ln ∈ ls1, ln.plain = true) ∧ (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us) ∧
      RunsAsSJ R exec i' ls1 Pre SegJ)
    (hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    ∃ n c'' ls1, MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      R.QWn j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' (iterN R.step n s) ∧ SegJ ls1 j s n ∧
      (∀ p, (R.nextW j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' p).1 = j + ls1.length) ∧
      RL.Straight (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      (∃ T', R.L.drop j = ls1 ++ T') ∧ (∀ ln ∈ ls1, ln.plain = true) ∧
      Arm.r .PC (iterN R.step n s) = R.pcOf (j + ls1.length) := by
  obtain ⟨hT0, hq'⟩ := hq.qws_lt hvb hk
  have hne : its ≠ [] := by
    obtain ⟨vb0, _, _, _, _, _, _, _, hvb0, -, -, hchk0, -⟩ := hq'
    rw [hvb] at hvb0
    cases hvb0
    exact hchk0.tail_ne hk
  obtain ⟨vb0, items, pre, c1, c2, lsA, X', psm, psm', ps2, x, hvb0, hit, hsplit, hchk, hc1,
    hc2, h1, h2, h3, htr, hdrop, hpc, hst, hx, hsc⟩ := qWs_split hR hq' hne
  rw [hvb] at hvb0
  cases hvb0
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
  have h1' : codeLinesE R.ctx R.af [AInst.inst i'] ps1 = .ok (ls1, ps1) := by
    simp [codeLinesE, ainstLines, hl1 ps1, bind, Except.bind, pure, Except.pure]
  have hWs := RL.straightW_eq (T := T) (j := j) hvb hc1o h1'
  rw [h1'] at h1
  simp only [Except.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨hA, hpsm⟩ := h1
  subst hA hpsm
  have hdrop' : R.L.drop j = ls1 ++ (relaxLines R.far (X' ++ x.2.1) ++
      R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2)) := by
    rw [hdrop, relaxLines_plain hpl]
  obtain ⟨nst, hiter, hpc', hgood⟩ := hruns j _ s m w s' hdrop' hst hpc hpre hex
  refine ⟨nst, _, ls1, MStep.op hvb hi hops hsz hsem hlen (HavocOuts.refl _ _ _) hc2' (MNext.next hk),
    ?_, hgood, fun p => by rw [RL.nextW_straight, hWs, relaxLines_plain hpl], by simp [RL.Straight],
    ⟨_, hdrop'⟩, hpl, by rw [hiter, hpc']⟩
  unfold RL.QWn
  rw [RL.nextW_straight, hWs]
  have hfr := R.frameOkK hR
  refine .inl ⟨hT0, qWs_next hvb hit hsplit hchk' hc2 h2 h3 htr hdrop ?_ ?_ hx hsc⟩
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

/-- **`realizes_callNA` with the segment's lines** (`RL.FRFree`). -/
theorem realizes_callNAF {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop}
    {P : Arm.ArmState → Prop}
    (hC : CalleeOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    {s : Arm.ArmState} (hP : P s)
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    {j : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {info : CallInfo} {ops : Array Operand} {outs : List CV} {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.call info))
    (hops : (MInst.call info).operands = .ok ops) (hsz : allocs.size = ops.size)
    (hsem : R.sem (.call info) (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      R.QWn j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' (iterN R.step n s) ∧
      (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.ReadsInY Y (iterN R.step i s)) ∧
      (∃ i0 < n, R.CallSt (iterN R.step i0 s) ∧
        ∀ i < n, i ≠ i0 → R.NoCallAt (iterN R.step i s)) ∧
      R.SegLen j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' s n ∧ R.FRFree s n := by
  have hq' : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩) := hq.q
  have hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program := by
    have herr : Arm.r .ERR w = .None := by
      have hst := q_stRel hq'
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    have hsem := R.sem_csem hsem
    simp only [csem, Option.map_eq_some_iff] at hsem
    obtain ⟨⟨o, w2⟩, hx, he⟩ := hsem
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, -⟩ := he
    exact hC.ext _ _ _ _ _ hx herr
  have hpre : R.CallPre s := by
    obtain ⟨-, -, -, regs, i', -, -, -, -, -, -, -, -, -, cc, wh, ops', hal, -, -, hasg, -, hops',
      hstat, -, -, -, -, -, -, -, -, hst, -, -⟩ := q_op hR hq' hvb hi hk
    rw [hops] at hops'; cases hops'
    have hm : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
      hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
    have hsemU := hsem
    rw [hal, useVals_of_store hstat hm] at hsemU
    exact ⟨R.ctx, .call info, .next, ⟨info, ⟨b, vb, k, hvb, .inl hi⟩, .inl rfl⟩, by rw [hst.sp]; exact RL.K_le hR,
      fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha, hst.gkeep, cc, wh, ops, regs, i', w,
      outs, w', hops, hstat, hasg, callAt_of_q hR hq' hvb hi call_hcall regs i' hal hasg, hst.world,
      hst.align, hst.err, hsemU⟩
  have hgen : ∀ regs i', (MInst.call info).assign regs = .ok i' →
      (∃ (c : CheckCtx) (wh : String), c.checkStatic wh ops (regs.map Loc.reg)
        (MInst.call info).clobbers = .ok ()) →
      ∃ ls1, (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) ∧
        (∀ ln ∈ ls1, ln.plain = true) ∧ (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us) ∧
        RunsAsSJ R (fun _ => callExec R.H) i' ls1 R.CallPre fun _ _ s n =>
          ((∀ i < n, R.GoodX (iterN R.step i s) ∧ R.ReadsInY Y (iterN R.step i s)) ∧
            ∃ i0 < n, R.CallSt (iterN R.step i0 s) ∧
              ∀ i < n, i ≠ i0 → R.NoCallAt (iterN R.step i s)) ∧
          n = 1 ∧ Arm.r .PC (iterN R.step n s) ≠ Arm.r .PC s := by
    intro regs i' hasg hcs
    obtain ⟨info', rfl⟩ := assign_call_form hasg
    have hgen : ∀ x, (∀ ps, (MInst.call info').lines R.ctx ps = .ok ([.ins x], ps)) →
        (Line.ins x).plain = true → x.tlsTail = false → (∀ rd rn n, x ≠ .ldrGotLo12 rd rn n) →
        (∀ r, x = .blr r → R.vc.DestsInt → r ≠ .xzr) → x.hooked = true →
        ((∃ n, x = .bl n) ∨ ∃ r, x = .blr r) →
        (∀ s j, R.L[j]? = some (.ins x) → s.program = R.fb.program R.base →
          Arm.r .PC s = R.pcOf j → R.step s = R.H.call
            (match info'.dest with | .sym n => some n | .reg _ => none) s) →
        ∃ ls1, (∀ ps, (MInst.call info').lines R.ctx ps = .ok (ls1, ps)) ∧
          (∀ ln ∈ ls1, ln.plain = true) ∧ (∀ ds, MInst.call info' ≠ .args ds) ∧
          (∀ us, MInst.call info' ≠ .rets us) ∧
          RunsAsSJ R (fun _ => callExec R.H) (.call info') ls1 R.CallPre fun _ _ s n =>
            ((∀ i < n, R.GoodX (iterN R.step i s) ∧ R.ReadsInY Y (iterN R.step i s)) ∧
              ∃ i0 < n, R.CallSt (iterN R.step i0 s) ∧
                ∀ i < n, i ≠ i0 → R.NoCallAt (iterN R.step i s)) ∧
            n = 1 ∧ Arm.r .PC (iterN R.step n s) ≠ Arm.r .PC s := by
      intro x hl1 hpl hxt hxg hxz hxh hxc hstep
      refine ⟨[.ins x], hl1, fun ln hln => by simp only [List.mem_singleton] at hln; subst hln; exact hpl,
        fun _ h => MInst.noConfusion h, fun _ h => MInst.noConfusion h,
        fun j T s _ _ s' hd hst hpc hpre' hex => ?_⟩
      have hj : R.L[j]? = some (.ins x) := drop_get (Z := []) hd
      simp only [callExec] at hex
      split at hex
      · rename_i hal
        simp only [Option.some.injEq] at hex
        subst hex
        have hs := hstep s j hj hst.prog hpc
        have hp4 : Arm.r .PC (iterN R.step 1 s) = Arm.r .PC s + 4 := by
          simp only [iterN]; rw [hs, hC.pc _ _ hst.err hal]
        refine ⟨1, by simp only [iterN]; exact hs, ?_, ⟨⟨fun i hi => ?_,
          0, Nat.one_pos, RL.callSt_of_line hj hpc hxc, fun i hi hne => absurd (by omega) hne⟩,
          rfl, by rw [hp4]; intro h; bv_omega⟩⟩
        · rw [hC.pc _ _ hst.err hal, hpc, List.length_singleton, pcOf_succ hj]
        · obtain rfl : i = 0 := by omega
          show R.GoodX s ∧ R.ReadsInY Y s
          exact ⟨RL.goodX_line hR hj hpc hxt (RL.good_of_sp hst.sp) hst.err hst.prog
            (RL.nextOk_pc4 (by rw [hs, hC.pc _ _ hst.err hal]))
            (fun rd rn n e => absurd e (hxg rd rn n)) (fun r e => ⟨hxz r e, hst.code⟩) (fun _ => hpre')
            (RL.readsAt_hooked hR hj hpc hxh), RL.readsIn_hooked hR hj hpc hxh⟩
      · cases hex
    cases hd : info'.dest with
    | sym n =>
      refine hgen (.bl n) (fun ps => by simp [MInst.lines, hd, pure, Except.pure])
        (by simp [Line.plain, Insn.condTarget?]) rfl (fun _ _ _ h => by cases h)
        (fun _ h => by cases h) rfl (.inl ⟨n, rfl⟩) fun s j hj hprog hpc => ?_
      rw [step_bl (off := 0) (r := .xzr) (rd := .xzr) (rn := .xzr) hR hj hprog hpc, hd]
    | reg r =>
      obtain ⟨c, wh, hcs⟩ := hcs
      have hne : R.vc.DestsInt → r ≠ .xzr := fun hD =>
        callDest_ne_xzr (hD b vb k info hvb (.inl hi)) hcs hasg hd
      refine hgen (.blr r) (fun ps => by simp [MInst.lines, hd, pure, Except.pure])
        (by simp [Line.plain, Insn.condTarget?]) rfl (fun _ _ _ h => by cases h)
        (fun _ h => by cases h; exact hne) rfl (.inr ⟨r, rfl⟩) fun s j hj hprog hpc => ?_
      rw [step_blr (off := 0) (n := "") (rd := .xzr) (rn := .xzr) hR hj hprog hpc, hd]
  obtain ⟨n, c'', ls1, hms, hqn, ⟨⟨hgx, hcs⟩, hn1, hpcne⟩, hWn, hS, hT, hpl, hpn⟩ :=
    realizes_op_coreXSW hR hq hvb hi hops hsz hsem hlen hk (exec := fun _ => callExec R.H)
    (fun _ => RL.callAtGP hR (hC.os R.ctx info ⟨b, vb, k, hvb, .inl hi⟩) hP (q_stRel hq').sp
      (q_stRel hq').gkeep fun i' ⟨regs, hal, hasg⟩ =>
        callAt_of_q hR hq' hvb hi call_hcall regs i' hal hasg)
    hpre (fun regs i' hasg _ _ hcs => hgen regs i' hasg hcs) hW'
  subst hn1
  refine ⟨1, c'', hms, hqn, hgx, hcs, RL.segLen_straight_of hR hS hWn hT hpl hpn RL.Inside.one
    ⟨fun h => absurd h (by omega), fun he => ?_⟩, ?_⟩
  · subst he
    exact absurd (hpn.trans (by rw [List.length_nil, Nat.add_zero]; exact hq.pc.symm)) hpcne
  · obtain ⟨i0, hi0, hc0, -⟩ := hcs
    obtain rfl : i0 = 0 := by omega
    exact RL.frFree_callSt hR (Nat.le_refl _) hc0

/-- **A call on the machine, at a witness** (`realizes_callNR`): one step (the hooked
`bl`/`blr`), to the next item at the straight witness. -/
theorem realizes_callNA {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop}
    {P : Arm.ArmState → Prop}
    (hC : CalleeOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    {s : Arm.ArmState} (hP : P s)
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    {j : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {info : CallInfo} {ops : Array Operand} {outs : List CV} {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.call info))
    (hops : (MInst.call info).operands = .ok ops) (hsz : allocs.size = ops.size)
    (hsem : R.sem (.call info) (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      R.QWn j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' (iterN R.step n s) ∧
      (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.ReadsInY Y (iterN R.step i s)) ∧
      (∃ i0 < n, R.CallSt (iterN R.step i0 s) ∧
        ∀ i < n, i ≠ i0 → R.NoCallAt (iterN R.step i s)) ∧
      R.SegLen j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' s n :=
  let ⟨n, c'', h1, h2, h3, h4, h5, _⟩ :=
    realizes_callNAF (Y := Y) hR hC hP hq hvb hi hops hsz hsem hlen hk
  ⟨n, c'', h1, h2, h3, h4, h5⟩

/-- **The segment fact of a straight segment**: the located reads, inside the lines, no step
exactly for no line. -/
def RL.StraightSeg (R : RL) (Y : BitVec 64 → Prop) (ls1 : List Line) (j : Nat) (s : Arm.ArmState)
    (n : Nat) : Prop :=
  (∀ i < n, R.GoodXNY Y (iterN R.step i s)) ∧ R.Inside s n j (j + ls1.length) ∧ (n = 0 ↔ ls1 = [])

/-- `runsAs_symAddrNR` with `RL.StraightSeg`. -/
theorem runsAs_symAddrNA {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {i' : MInst} {x1 x2 : Insn}
    (hl : ∀ ps, i'.lines R.ctx ps = .ok ([.ins x1, .ins x2], ps))
    (hstep : ∀ s j, R.L[j]? = some (.ins x1) → R.L[j + 1]? = some (.ins x2) →
      s.program = R.fb.program R.base → Arm.r .PC s = R.pcOf j →
      R.step (R.step s) = match symExec R.X i' s with | some s' => s' | none => s)
    (hx1 : (∀ n, x1 ≠ .bl n) ∧ (∀ r, x1 ≠ .blr r)) (hx2 : (∀ n, x2 ≠ .bl n) ∧ (∀ r, x2 ≠ .blr r))
    (ht : x1.tlsTail = false ∧ x2.tlsTail = false) (hhk : x1.hooked = true ∧ x2.hooked = true)
    (hmid : ∀ s j, R.L[j]? = some (.ins x1) → s.program = R.fb.program R.base →
      Arm.r .PC s = R.pcOf j → Arm.r .PC (R.step s) = R.pcOf (j + 1) ∧
        Arm.r .ERR (R.step s) = Arm.r .ERR s ∧ (R.step s).program = s.program ∧
        (R.step s).mem = s.mem) :
    RunsAsSJ R (fun _ => symExec R.X) i' [.ins x1, .ins x2] (fun _ => True) (R.StraightSeg Y) := by
  intro j T s _ _ s' hd hst hpc _ hex
  have hprog := hst.prog
  have hj : R.L[j]? = some (.ins x1) := drop_get (Z := [.ins x2]) hd
  have hj1 : R.L[j + 1]? = some (.ins x2) := drop_get1 (ls := []) hd
  have e := hstep s j hj hj1 hprog hpc
  simp only [hex] at e
  have hpc8 : Arm.r .PC s' = Arm.r .PC s + 8 := by
    revert hex
    cases i' <;> simp only [symExec, Option.some.injEq, reduceCtorEq, false_implies] <;>
      intro hex <;> subst hex <;> simp [Arm.r_of_w_different, Arm.r_of_w_same]
  obtain ⟨hm1, hm2, hm3, hm4⟩ := hmid s j hj hprog hpc
  refine ⟨2, by simpa [iterN] using e, ?_, fun i hi => ?_, fun i h0 hi => ?_, by simp⟩
  · simp only [List.length_cons, List.length_nil, Nat.zero_add]
    rw [hpc8, hpc, ← Nat.add_assoc, pcOf_succ hj1, pcOf_succ hj, BitVec.add_assoc]
    rfl
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · show R.GoodXNY Y s
      exact ⟨⟨RL.goodX_line hR hj hpc ht.1 (RL.good_of_sp hst.sp) hst.err hprog
        (RL.nextOk_pc4 (by rw [hm1, pcOf_succ hj, hpc])) (fun _ _ _ _ a ha => hst.gkeep a ha)
        (fun r e => absurd e (hx1.2 r)) (not_call_insn hx1.1 hx1.2) (RL.readsAt_hooked hR hj hpc hhk.1),
        RL.noCallAt_of_noCall hR hj hpc hx1⟩, RL.readsIn_hooked hR hj hpc hhk.1⟩
    · show R.GoodXNY Y (R.step s)
      exact ⟨⟨RL.goodX_line hR hj1 hm1 ht.2 (R.good_succ hR hj hx1.1 hx1.2 hm1)
        (by rw [hm2]; exact hst.err) (by rw [hm3, hprog])
        (RL.nextOk_pc4 (by rw [e, hpc8, hm1, pcOf_succ hj, hpc]; bv_omega))
        (fun _ _ _ _ a ha => by rw [hm4]; exact hst.gkeep a ha) (fun r e => absurd e (hx2.2 r))
        (not_call_insn hx2.1 hx2.2) (RL.readsAt_hooked hR hj1 hm1 hhk.2),
        RL.noCallAt_of_noCall hR hj1 hm1 hx2⟩, RL.readsIn_hooked hR hj1 hm1 hhk.2⟩
  · obtain rfl : i = 1 := by omega
    exact ⟨j + 1, x2, none, by omega, by simp, hj1, by simpa [iterN] using hm1⟩

/-- `RunsAsSJ` with a fact of the lines added to its segment fact. -/
theorem RunsAsSJ.and_lines {R : RL} {exec : Env → MInst → Arm.ArmState → Option Arm.ArmState}
    {i' : MInst} {ls1 : List Line} {pre : Arm.ArmState → Prop}
    {SegJ : List Line → Nat → Arm.ArmState → Nat → Prop} (h : RunsAsSJ R exec i' ls1 pre SegJ)
    {P : List Line → Prop} (hP : P ls1) :
    RunsAsSJ R exec i' ls1 pre fun ls j s n => SegJ ls j s n ∧ P ls :=
  fun j T s m w s' hd hst hpc hp hex =>
    let ⟨n, h1, h2, h3⟩ := h j T s m w s' hd hst hpc hp hex
    ⟨n, h1, h2, h3, hP⟩

/-- **`realizes_symAddrNA` with the segment's lines** (`RL.FRFree`). -/
theorem realizes_symAddrNAF {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState}
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    {j : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} {ops : Array Operand} {outs : List CV} {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    (hform : (∃ d n, i = .loadExtNameGot (.vreg d .int) n) ∨
      (∃ d n off, i = .loadExtNameNear (.vreg d .int) n off))
    (hops : i.operands = .ok ops) (hsz : allocs.size = ops.size)
    (hsem : R.sem i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      R.SegNA Y s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' n ∧ R.FRFree s n := by
  have hq' : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩) := hq.q
  have hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program := by
    have herr : Arm.r .ERR w = .None := by
      have hst := q_stRel hq'
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    have hsem := R.sem_csem hsem
    rcases hform with ⟨d, n, rfl⟩ | ⟨d, n, off, rfl⟩ <;>
    · simp only [csem, Option.some.injEq, Prod.mk.injEq] at hsem
      obtain ⟨-, rfl, -⟩ := hsem
      exact ⟨herr, rfl⟩
  refine (fun H => ?_) (realizes_op_coreXSW hR hq hvb hi hops hsz hsem hlen hk
    (exec := fun _ => symExec R.X)
    (fun _ => (((os_symAddr hform).at (fun _ => RL.FK_F) s).toI _).v R.gv) (Pre := fun _ => True)
    trivial (SegJ := fun ls1 j s n => R.StraightSeg Y ls1 j s n ∧
      ∀ x t, Line.ins x t ∈ ls1 → x.frLine = false) (fun regs i' _ _ hex _ => ?_) hW')
  · obtain ⟨n, c'', ls1, hms, hqn, ⟨⟨hg, hin, hn0⟩, hfl⟩, hWn, hS, hT, hpl, hpn⟩ := H
    exact ⟨n, c'', hms, ⟨hqn, hg, RL.segLen_straight_of hR hS hWn hT hpl hpn hin hn0⟩,
      RL.frFree_straight hR hT hpl hfl hq.pc hin hn0⟩
  obtain ⟨_, s0, _, hex⟩ := hex
  cases i' with
  | loadExtNameGot rd n =>
    refine ⟨[.ins (.adrpGot rd n), .ins (.ldrGotLo12 rd rd n)],
      fun ps => by simp [MInst.lines, pure, Except.pure], ?_, fun _ h => MInst.noConfusion h,
      fun _ h => MInst.noConfusion h, (runsAs_symAddrNA hR (fun ps => by simp [MInst.lines, pure,
        Except.pure]) (fun s j hj hj1 hprog hpc => ?_) ⟨fun _ h => Insn.noConfusion h, fun _ h => Insn.noConfusion h⟩
        ⟨fun _ h => Insn.noConfusion h, fun _ h => Insn.noConfusion h⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
        (fun s j hj hprog hpc => ?_)).and_lines (P := fun ls1 =>
          ∀ x t, Line.ins x t ∈ ls1 → x.frLine = false) (by
        intro x t hx; simp at hx; rcases hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl)⟩
    · intro ln hln; simp at hln; rcases hln with rfl | rfl <;> simp [Line.plain, Insn.condTarget?]
    · rw [step_adrpGot (off := 0) (r := .xzr) (rn := .xzr) hR hj hprog hpc]
      rw [step_ldrGotLo12 (off := 0) (r := .xzr) hR hj1 (by simp [Arm.w_program, hprog])
        (by rw [Arm.r_of_w_same, hpc, pcOf_succ hj])]
      simp only [symExec, Arm.r_of_w_same, Arm.w_of_w_shadow, BitVec.add_assoc]
      rw [Arm.w_of_w_commute (by simp)]
      rfl
    · rw [step_adrpGot (off := 0) (r := .xzr) (rn := .xzr) hR hj hprog hpc]
      exact ⟨by rw [Arm.r_of_w_same, hpc, pcOf_succ hj],
        by rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)],
        by simp [Arm.w_program], by simp [Arm.ArmState.mem_w_eq_mem]⟩
  | loadExtNameNear rd n off =>
    refine ⟨[.ins (.adrp rd n off), .ins (.addLo12 rd rd n off)],
      fun ps => by simp [MInst.lines, pure, Except.pure], ?_, fun _ h => MInst.noConfusion h,
      fun _ h => MInst.noConfusion h, (runsAs_symAddrNA hR (fun ps => by simp [MInst.lines, pure,
        Except.pure]) (fun s j hj hj1 hprog hpc => ?_) ⟨fun _ h => Insn.noConfusion h, fun _ h => Insn.noConfusion h⟩
        ⟨fun _ h => Insn.noConfusion h, fun _ h => Insn.noConfusion h⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
        (fun s j hj hprog hpc => ?_)).and_lines (P := fun ls1 =>
          ∀ x t, Line.ins x t ∈ ls1 → x.frLine = false) (by
        intro x t hx; simp at hx; rcases hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl)⟩
    · intro ln hln; simp at hln; rcases hln with rfl | rfl <;> simp [Line.plain, Insn.condTarget?]
    · rw [step_adrp (r := .xzr) (rn := .xzr) hR hj hprog hpc]
      rw [step_addLo12 (r := .xzr) hR hj1 (by simp [Arm.w_program, hprog])
        (by rw [Arm.r_of_w_same, hpc, pcOf_succ hj])]
      simp only [symExec, Arm.r_of_w_same, Arm.w_of_w_shadow, BitVec.add_assoc]
      rw [Arm.w_of_w_commute (by simp)]
      rfl
    · rw [step_adrp (r := .xzr) (rn := .xzr) hR hj hprog hpc]
      exact ⟨by rw [Arm.r_of_w_same, hpc, pcOf_succ hj],
        by rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)],
        by simp [Arm.w_program], by simp [Arm.ArmState.mem_w_eq_mem]⟩
  | _ => simp [symExec] at hex

/-- **`loadExtNameGot/Near` on the machine, at a witness** (`realizes_symAddrNR`). -/
theorem realizes_symAddrNA {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState}
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    {j : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} {ops : Array Operand} {outs : List CV} {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    (hform : (∃ d n, i = .loadExtNameGot (.vreg d .int) n) ∨
      (∃ d n off, i = .loadExtNameNear (.vreg d .int) n off))
    (hops : i.operands = .ok ops) (hsz : allocs.size = ops.size)
    (hsem : R.sem i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      R.SegNA Y s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' n :=
  let ⟨n, c'', h1, h2, _⟩ := realizes_symAddrNAF (Y := Y) hR hq hvb hi hform hops hsz hsem hlen hk
  ⟨n, c'', h1, h2⟩

end Backend.Proof
