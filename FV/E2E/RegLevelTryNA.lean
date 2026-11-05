import FV.E2E.RegLevelTryN
import FV.E2E.RegLevelJTNA

/-!
# The call of a `try_call` on the machine, at a witness (SEM1 #537, item (3), route (a))

`realizes_tryCallNR` from `QW`: the hooked `bl`/`blr` (one step), then the branch to the
continuation (`reach_bXNA`); the continuation block is reached at its chosen entry witness, at
the first arrival (`RL.segLen_entry_of`).
-/

namespace Backend.Proof

open Backend E2E

/-- **`realizes_tryCallNA` with the segment's lines** (`RL.FRFree`). -/
theorem realizes_tryCallNAF {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {P : Arm.ArmState → Prop}
    (hC : CalleeOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : CalleeTryOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    {s : Arm.ArmState} (hP : P s) {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    {j0 : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j0 ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {info : CallInfo} {ti : TryInfo} {ops : Array Operand} {outs : List CV}
    {w' : Arm.ArmState} {ctl : Ctl}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.tryCall info ti))
    (hops : (MInst.tryCall info ti).operands = .ok ops) (hsz : allocs.size = ops.size)
    (hsem : R.sem (.tryCall info ti) (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', ctl))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    {j st : Nat} {items : Array RItem} (hk1 : k + 1 = vb.insts.size)
    (hsucc : succOf R.vc b j = some st) (hitems : R.rf.blocks[st]? = some items)
    (hctl : ctl = .goto j) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      R.QWn j0 ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' (iterN R.step n s) ∧
      (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.ReadsInY Y (iterN R.step i s)) ∧
      (∃ i0 < n, R.CallSt (iterN R.step i0 s) ∧
        ∀ i < n, i ≠ i0 → R.NoCallAt (iterN R.step i s)) ∧
      R.SegLen j0 ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' s n ∧ R.FRFree s n := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  have hcpc := callAt_of_q hR hq.q hvb hi tryCall_hcall
  -- the forwarding-block case of `QW` (`T ≠ []`): a `try_call`'s allocated form is no `jump`
  have hqq := hq
  rcases hqq with ⟨hT0, hqs⟩ | ⟨hT', -⟩
  rotate_left
  · exfalso
    obtain ⟨vbf, allocsf, regsf, if_, xf, bxf, itxf, hvbf, he, -, -, hins, hasgf, -⟩ := hq.fwd hT'
    rw [hvb] at hvbf; cases hvbf
    simp only [RItem.op.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hi1 := hi
    rw [hins] at hi1
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hi1
    subst hi1
    obtain ⟨ic, e, -⟩ := (assign_call_tryCall info regsf).2 ti (.jump xf) hasgf
    cases e
  obtain ⟨vb0, _, _, code, _, _, _, _, hvb0, -, -, hchk0, hcode, -⟩ := id hqs
  rw [hvb] at hvb0; cases hvb0
  obtain rfl : its = [] := hchk0.tail_nil hk1
  obtain ⟨vb0, items0, pre, c1, X, psm, ps2, x, hvb0, hit, hsplit, hchk, hc1, hX, hTq, htr,
    hdrop, hpc, hst, hterm⟩ := qWs_term hR hqs
  rw [hvb] at hvb0; cases hvb0
  obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
  rw [hi] at hi0; cases hi0
  obtain ⟨cc, wh, i2, ops2, hi2, hops2, hstat, -⟩ := op_checked hchk
  rw [hi] at hi2; cases hi2
  rw [hops] at hops2; cases hops2
  have hm : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
    hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
  have hsemU := hsem
  rw [useVals_of_store hstat hm] at hsemU
  have hpre : R.CallPre s := ⟨R.ctx, .tryCall info ti, ctl,
    ⟨info, ⟨b, vb, k, hvb, .inr ⟨ti, hi⟩⟩, .inr ⟨ti, rfl⟩⟩,
    by rw [hst.sp]; exact RL.K_le hR, fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha,
    hst.gkeep, cc, wh, ops, regs, i', w, outs, w', hops, hstat, hasg, hcpc regs i' rfl hasg,
    hst.world, hst.align, hst.err, hsemU⟩
  have hsem0 := hsemU
  replace hsem0 := R.sem_csem hsem0
  simp only [csem, Option.map_eq_some_iff, Option.filter_eq_some_iff] at hsem0
  obtain ⟨⟨xo, w2⟩, ⟨hx, -⟩, he⟩ := hsem0
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, rfl, rfl⟩ := he
  obtain rfl : j = ti.handlers.length := by cases hctl; rfl
  have herr : Arm.r .ERR w = .None := by
    rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
  have hW' : Arm.r .ERR w2 = .None ∧ w2.program = w.program := hC.ext _ _ _ _ _ hx herr
  have hcl : ti.clobberAll = false := by
    have := ctlCheck_inst hck hvb hi
    simpa [ctlInstOk] using this
  have hcpcT := hcpc regs i' rfl hasg
  obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall info regs).2 ti i' hasg
  have hsemC : csemV R.gv R.F R.ctx R.X (.call info) (useVals ops regs s) w =
      some (xo, w2, .next) := by
    have hg := csemV_guard_try hsemU
    simp only [csemV, hg, ↓reduceIte]
    simp [csem, hx]
  obtain ⟨s', hex, hW, hK, -, hoth, hkeep⟩ :=
    RL.callAtGP hR (hC.os R.ctx info ⟨b, vb, k, hvb, .inr ⟨ti, hi⟩⟩) hP hst.sp hst.gkeep
      (Pi := (· = .call ic)) (fun _ e => e ▸ callAt_tryCall_call hcpcT) cc wh ops regs (.call ic)
      w xo w2 (by rw [← operands_tryCall_call info ti]; exact hops)
      (by rw [← clobbers_tryCall hcl]; exact hstat) hasg' rfl hst.world hst.align hst.err hsemC
  have hexT : callExec R.H (.tryCall ic ti) s = some s' := by
    simp only [callExec] at hex ⊢; exact hex
  have hres := hT R.ctx info ti ⟨b, vb, k, hvb, hi⟩ cc wh ops regs (.tryCall ic ti) s w outs w2 s' hP
    (by rw [hst.sp]; exact RL.K_le hR) (fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha)
    hst.gkeep hops hstat hasg hcpcT hst.world hst.align hst.err hsemU hexT
  have hlenD : outs.length = ((ops.zip regs).toList.filter (·.1.isDef)).length := by
    rw [hlen, pairs_regs, List.filter_map, List.length_map]; rfl
  have hlen' : (((ops.zip regs).toList.filter (·.1.isDef)).map (fun p => regVal s' p.2)).length =
      ((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).length := by
    rw [List.length_map, ← hlenD, hlen]
  have hho : HavocOuts (MInst.tryCall ic ti) (.goto ti.handlers.length) outs
      (((ops.zip regs).toList.filter (·.1.isDef)).map (fun p => regVal s' p.2)) := by
    have hh : havocFrom (MInst.tryCall ic ti) (.goto ti.handlers.length) = some ti.rets := by
      simp [havocFrom, MInst.keptDefs, MInst.isBranch, MInst.normalDead]
    refine ⟨by rw [List.length_map, ← hlenD], fun h => (by rw [hh] at h; cases h), fun n h => ?_⟩
    rw [hh] at h; cases h
    exact take_machine_defs hlenD hres
  obtain ⟨m2, hc2', hr2, hl2⟩ := operandsSound_post (s' := s') hstat hm hlen'
    (fun p hp => (mem_zip_map_self _ _ p hp).symm)
    (fun r ha hnd hnc => hoth r ha hnd (by rw [← clobbers_tryCall hcl]; exact hnc))
    (fun r hr hcs => hkeep r (by rw [clobbers_tryCall hcl] at hr; exact hr) hcs)
  obtain ⟨c, ins, _, hc, -⟩ := hR.check
  obtain ⟨preds, hcfg⟩ := hc.cfg
  obtain ⟨t0, ts, hback, hss, hlab⟩ := cfg_block hcfg hvb
  have hti : t0 = .tryCall info ti := by
    rw [Array.back?_eq_getElem?, show vb.insts.size - 1 = k by omega, hi] at hback
    cases hback; rfl
  subst hti
  have hsucc' := hsucc
  simp only [succOf, hcfg, hss, Option.bind_some] at hsucc'
  obtain ⟨vs, hvs, hlj⟩ := hlab _ st hsucc'
  have hst0 : st ≠ 0 := ctlCheck_succ hck hsucc
  have hcont : vs.label = ti.continuation := by
    simp only [MInst.targets] at hlj
    rw [List.getElem?_append_right (by simp), List.length_map, Nat.sub_self] at hlj
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hlj
    exact hlj.symm
  -- the lines: the call, then `b continuation` (the try_call's own lines, the segment's term)
  obtain rfl : c1 = [.inst (.tryCall ic ti)] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  simp only [List.dropLast_singleton, codeLinesE, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq, Prod.mk.injEq] at hX
  obtain ⟨rfl, rfl⟩ := hX
  have hdrop0 : R.L.drop j0 = relaxLines R.far x.2.1 ++
      R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2) := by simpa using hdrop
  rw [show [AInst.inst (.tryCall ic ti)].getLast?.toList = [AInst.inst (.tryCall ic ti)] from by simp] at hTq
  have hlT := codeLinesE_single hTq
  obtain ⟨xI, hxterm, hxs, hplain, hxk⟩ : ∃ xI : Insn,
      x.1.term = [.ins xI none, .ins (.b (.block ti.continuation)) none] ∧
      (∀ s0 : Arm.ArmState, ∀ jj, R.L[jj]? = some (.ins xI) → s0.program = R.fb.program R.base →
        Arm.r .PC s0 = R.pcOf jj → R.step s0 = R.H.call
          (match ic.dest with | .sym n => some n | .reg _ => none) s0) ∧
      (Line.ins xI none).plain = true ∧
      ((∃ n, xI = .bl n) ∨ ∃ r, xI = .blr r ∧ (R.vc.DestsInt → r ≠ .xzr)) := by
    cases hd : ic.dest with
    | sym n =>
      simp only [MInst.lines, hd, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hlT
      refine ⟨.bl n, hlT.1.symm, fun s0 jj hj hprog hpc0 => ?_, by simp [Line.plain, Insn.condTarget?],
        .inl ⟨n, rfl⟩⟩
      exact step_bl (off := 0) (r := .xzr) (rd := .xzr) (rn := .xzr) hR hj hprog hpc0
    | reg r =>
      simp only [MInst.lines, hd, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hlT
      refine ⟨.blr r, hlT.1.symm, fun s0 jj hj hprog hpc0 => ?_, by simp [Line.plain, Insn.condTarget?],
        .inr ⟨r, rfl, fun hD => callDest_ne_xzr (hD b vb k info hvb (.inr ⟨ti, hi⟩)) hstat hasg' hd⟩⟩
      refine step_blr (off := 0) (n := "") (rd := .xzr) (rn := .xzr) hR hj hprog hpc0
  -- the branch check's verdict on the final lines
  obtain ⟨call, b0, htermL, hcase⟩ := termOk_tryCall hterm
  rw [hxterm] at htermL
  obtain ⟨rfl, rfl⟩ := htermL
  obtain ⟨O, hx21O, hcaseO⟩ : ∃ O, x.2.1 = .ins xI none :: O ∧
      ((∃ l', O = [.ins (.b l') none] ∧
          RepLbl (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) ti.continuation l') ∨
        (O = [] ∧ planRep R.fa.k R.af ti.continuation x.2.2 = true)) := by
    rcases hcase with ⟨l', hx21, hrl⟩ | ⟨hx21, hrn⟩
    · refine ⟨[.ins (.b l') none], hx21.trans rfl, .inl ⟨l', rfl, hrl⟩⟩
    · refine ⟨[], hx21.trans rfl, .inr ⟨rfl, hrn⟩⟩
  have hdropJ : R.L.drop j0 = [Line.ins xI none] ++ (relaxLines R.far O ++
      R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2)) := by
    rw [hdrop0, hx21O, relaxLines_cons,
      relaxLine_of_none (by rcases hxk with ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> rfl), List.append_assoc]
  have hj0 : R.L[j0]? = some (.ins xI none) := drop_get (Z := []) hdropJ
  -- the machine: the callee, then the branch to the successor
  have hs1 : R.step s = s' := by
    rw [hxs s j0 hj0 hst.prog hpc]
    simp only [callExec, if_pos hst.align, Option.some.injEq] at hex
    exact hex
  have herr' : Arm.r .ERR s' = .None := by rw [hW.1 .ERR (by simp [Masked]), hW'.1]
  have hprog' : s'.program = R.fb.program R.base := by
    rw [hW.2.2, hW'.2, ← hst.world.2.2, hst.prog]
  have hpc1 : Arm.r .PC s' = R.pcOf (j0 + 1) := by
    rw [← hs1, hxs s j0 hj0 hst.prog hpc, hC.pc _ _ hst.err hst.align, hpc, pcOf_succ hj0]
  have hsp' : spOf s' = R.spB := hK.1.trans hst.sp
  have hdrop1 : R.L.drop (j0 + 1) = relaxLines R.far O ++
      R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2) := by
    rw [← List.drop_drop, hdropJ]
    simp
  have hoo : (∃ l', O = [.ins (.b l') none] ∧
        RepLbl (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) vs.label l') ∨
      (O = [] ∧ planRep R.fa.k R.af vs.label x.2.2 = true) := by
    rcases hcaseO with ⟨l', hO, hrl⟩ | ⟨hO, hrn⟩
    · refine .inl ⟨l', hO, by rw [hcont]; refine hrl⟩
    · refine .inr ⟨hO, by rw [hcont]; refine hrn⟩
  obtain ⟨n, jl, lim, hn, hrep, -, hgx, hseg, -, hfrB⟩ :=
    reach_bXNAF (Y := Y) hR hdrop1 hoo hprog' hpc1 herr' hsp'
  have hiter : iterN R.step (n + 1) s = Arm.w .PC (R.pcOf jl) s' := by
    simp only [iterN]; rw [hs1, hn]
  have hfr := R.frameOkK hR
  have hstr : StRel R s' (writeM m2 ((((ops.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip
      (((ops.zip regs).toList.filter (·.1.isDef)).map (fun p => regVal s' p.2))).filter
        (·.1.1.isLate))) w2 := by
    refine ⟨fun l hl hL => ?_, hW, herr', hprog', hsp', align_of_sp (by rw [hsp', hst.sp]) hst.align,
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
    · rw [← hst.fplr hframe]
      exact read_mem_bytes_congr _ _ (fun k hk => hK.2.1 _ (fplr_inF hR hframe k hk))
  obtain ⟨hE, hqE⟩ := qW_entry hR hst0 hvs hitems hrep (Arm.r_of_w_same ..) (hstr.pc _)
  have hns : ¬ (st = b ∧ items.toList = []) := by
    rintro ⟨rfl, he⟩
    rw [hit] at hitems; cases hitems
    have := congrArg List.length hsplit
    rw [he] at this
    simp at this
  -- the segment: the call line, then the branch lines
  have hseg' : ∃ lim', R.SegIn s (n + 1) j0 lim' := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      exact ⟨j0 + 1, RL.Inside.one, fun k h1 h2 => by
          obtain rfl : k = j0 := by omega
          exact ⟨_, _, hj0⟩,
        ⟨fun h => absurd h (by omega), fun h => absurd hj0 (h _ _)⟩⟩
    · obtain ⟨x1, t1, hx1⟩ : ∃ x t, R.L[j0 + 1]? = some (.ins x t) :=
        Classical.byContradiction fun hno =>
          absurd (hseg.2.2.mpr fun x t hx => hno ⟨x, t, hx⟩) (by omega)
      have hI1 : R.Inside (iterN R.step 1 s) n (j0 + 1) (max lim (j0 + 2)) := by
        have e : iterN R.step 1 s = s' := by simp only [iterN]; exact hs1
        rw [e]; exact hseg.1.mono (Nat.le_max_left _ _)
      have hI := RL.Inside.append (n := 1) (RL.Inside.one (R := R) (s := s) (j0 := j0)
        (lim := max lim (j0 + 2))) hI1 (by omega) (by omega) hx1
        (fun _ => by simp only [iterN]; rw [hs1]; exact hpc1)
      rw [Nat.add_comm] at hI
      refine ⟨max lim (j0 + 2), hI, fun k h1 h2 => ?_,
        ⟨fun h => absurd h (by omega), fun h => absurd hj0 (h _ _)⟩⟩
      rcases Nat.lt_or_ge k (j0 + 1) with hk | hk
      · obtain rfl : k = j0 := by omega
        exact ⟨_, _, hj0⟩
      · rcases Nat.lt_or_ge k lim with hk' | hk'
        · exact hseg.2.1 k hk hk'
        · obtain rfl : k = j0 + 1 := by omega
          exact ⟨_, _, hx1⟩
  obtain ⟨lim', hseg'⟩ := hseg'
  have hfr1 : R.FRFree s (1 + n) := by
    refine RL.FRFree.append (RL.frFree_one hR (Nat.le_refl _) hj0
      (by rcases hxk with ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> rfl) hpc) ?_
    have e : iterN R.step 1 s = s' := by simp only [iterN]; exact hs1
    rw [e]; exact hfrB
  refine ⟨n + 1, _, MStep.op hvb hi hops hsz hsem hlen hho hc2'
    (MNext.goto hk1 hsucc hitems), ?_, fun i hi => ?_, ⟨0, by omega,
    RL.callSt_of_line hj0 hpc (hxk.imp id fun ⟨r, e, _⟩ => ⟨r, e⟩), fun i hi hne => ?_⟩, ?_,
    by rw [Nat.add_comm]; exact hfr1⟩
  · unfold RL.QWn
    rw [RL.nextW_entry hns, hiter]
    exact hqE
  · cases i with
    | zero =>
      show R.GoodX s ∧ R.ReadsInY Y s
      refine ⟨RL.goodX_line hR hj0 hpc (by rcases hxk with ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> rfl)
        (RL.good_of_sp hst.sp) hst.err hst.prog
        (RL.nextOk_pc4 (by rw [hs1, hpc1, pcOf_succ hj0, hpc]))
        (fun _ _ _ e => by rcases hxk with ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> cases e)
        (fun r e => by
          rcases hxk with ⟨_, rfl⟩ | ⟨_, rfl, hr⟩
          · cases e
          · cases e; exact ⟨hr, hst.code⟩)
        (fun _ => hpre)
        (RL.readsAt_hooked hR hj0 hpc (by rcases hxk with ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> rfl)),
        RL.readsIn_hooked hR hj0 hpc (by rcases hxk with ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> rfl)⟩
    | succ i =>
      simp only [iterN]; rw [hs1]
      exact ⟨(hgx i (by omega)).1.1, (hgx i (by omega)).2⟩
  · obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    simp only [iterN]; rw [hs1]
    exact (hgx i (by omega)).1.2
  · exact RL.segLen_entry_of hR hns hT0 (by rw [hiter]; exact hE) hseg'

/-- **The call of a `try_call` on the machine, at a witness** (`realizes_tryCallNR`): the
continuation's items at its chosen entry witness, reached at the first arrival; exactly one call
state (the first). -/
theorem realizes_tryCallNA {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {P : Arm.ArmState → Prop}
    (hC : CalleeOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : CalleeTryOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    {s : Arm.ArmState} (hP : P s) {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    {j0 : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j0 ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {info : CallInfo} {ti : TryInfo} {ops : Array Operand} {outs : List CV}
    {w' : Arm.ArmState} {ctl : Ctl}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.tryCall info ti))
    (hops : (MInst.tryCall info ti).operands = .ok ops) (hsz : allocs.size = ops.size)
    (hsem : R.sem (.tryCall info ti) (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', ctl))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    {j st : Nat} {items : Array RItem} (hk1 : k + 1 = vb.insts.size)
    (hsucc : succOf R.vc b j = some st) (hitems : R.rf.blocks[st]? = some items)
    (hctl : ctl = .goto j) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      R.QWn j0 ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' (iterN R.step n s) ∧
      (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.ReadsInY Y (iterN R.step i s)) ∧
      (∃ i0 < n, R.CallSt (iterN R.step i0 s) ∧
        ∀ i < n, i ≠ i0 → R.NoCallAt (iterN R.step i s)) ∧
      R.SegLen j0 ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' s n :=
  let ⟨n, c'', h1, h2, h3, h4, h5, _⟩ := realizes_tryCallNAF (Y := Y) hR hC hT hP hq hvb hi hops
    hsz hsem hlen hk1 hsucc hitems hctl
  ⟨n, c'', h1, h2, h3, h4, h5⟩

end Backend.Proof
