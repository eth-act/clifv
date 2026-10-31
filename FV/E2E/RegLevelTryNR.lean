import FV.E2E.RegLevelTryN
import FV.E2E.RegLevelGotoNR

/-!
# The call of a `try_call` on the machine with its call state (SEM1 #537, step 2k)

`RegLevelTry`'s `realizes_tryCall` with the call states (`RL.CallSt`, docs/plans/uninit.md §5.5):
the segment has exactly one call state (its `bl`/`blr`, the first), the branch to the
continuation none (`reach_bXNR`). The callee contracts are required at the segment's start only
(`CalleeOkGP`, `CalleeTryOkGP`: the count-indexed contract).
-/

namespace Backend.Proof

open Backend E2E

/-- **The call of a `try_call` on the machine** (`realizes_tryCall`) **with its call state**:
the segment's states satisfy `GoodX`, and exactly one of them (the first, at the `bl`/`blr`) is a
call state. -/
theorem realizes_tryCallNR {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {P : Arm.ArmState → Prop}
    (hC : CalleeOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : CalleeTryOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    {s : Arm.ArmState} (hP : P s) {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
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
      Q R (iterN R.step n s) c'' ∧ (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.ReadsInY Y (iterN R.step i s)) ∧
      ∃ i0 < n, R.CallSt (iterN R.step i0 s) ∧
        ∀ i < n, i ≠ i0 → R.NoCallAt (iterN R.step i s) := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  have hcpc := callAt_of_q hq hvb hi tryCall_hcall
  obtain ⟨j0, vb0, items0, pre, code, ls, ps1, ps2, T, hvb0, hit, hsplit, hchk, hcode, hls, htr,
    hdrop, hpc, hst⟩ := hq
  rw [hvb] at hvb0; cases hvb0
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
  rw [hi] at hi0; cases hi0
  obtain ⟨cc, wh, i2, ops2, hi2, hops2, hstat, hchk'⟩ := op_checked hchk
  rw [hi] at hi2; cases hi2
  rw [hops] at hops2; cases hops2
  have hm : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
    hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
  have hsemU := hsem
  rw [useVals_of_store hstat hm] at hsemU
  -- the callee contract's premise at the call state
  have hpre : R.CallPre s := ⟨R.ctx, .tryCall info ti, ctl,
    ⟨info, ⟨b, vb, k, hvb, .inr ⟨ti, hi⟩⟩, .inr ⟨ti, rfl⟩⟩,
    by rw [hst.sp]; exact RL.K_le hR, fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha,
    hst.gkeep, cc, wh, ops, regs, i', w, outs, w', hops, hstat, hasg, hcpc regs i' rfl hasg,
    hst.world, hst.align, hst.err, hsemU⟩
  -- the control outcome and the callee's world
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
  -- the instruction's effect: the callee contract of the plain call, then the results
  have hcl : ti.clobberAll = false := by
    have := ctlCheck_inst hck hvb hi
    simpa [ctlInstOk] using this
  have hcpcT := hcpc regs i' rfl hasg
  obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall info regs).2 ti i' hasg
  have hsemC : csemV R.gv R.F R.ctx R.X (.call info) (useVals ops regs s) w =
      some (xo.take info.defs.length, w2, .next) := by
    have hg := csemV_guard_try hsemU
    simp only [csemV, hg, ↓reduceIte]
    simp [csem, hx]
  obtain ⟨s', hex, hW, hK, -, hoth, hkeep⟩ :=
    RL.callAtGP hR (hC.os R.ctx info ⟨b, vb, k, hvb, .inr ⟨ti, hi⟩⟩) hP hst.sp hst.gkeep
      (Pi := (· = .call ic)) (fun _ e => e ▸ callAt_tryCall_call hcpcT) cc wh ops regs (.call ic)
      w (xo.take info.defs.length) w2 (by rw [← operands_tryCall_call info ti]; exact hops)
      (by rw [← clobbers_tryCall hcl]; exact hstat) hasg' rfl hst.world hst.align hst.err hsemC
  have hexT : callExec R.H (.tryCall ic ti) s = some s' := by
    simp only [callExec] at hex ⊢; exact hex
  have hres := hT R.ctx info ti ⟨b, vb, k, hvb, hi⟩ cc wh ops regs (.tryCall ic ti) s w outs w2 s' hP
    (by rw [hst.sp]; exact RL.K_le hR) (fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha)
    hst.gkeep hops hstat hasg hcpcT hst.world hst.align hst.err hsemU hexT
  -- the def values the allocated code writes: what the callee left in the def registers
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
  -- the successor's label
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
  -- the lines: the call, then `b continuation`
  obtain rfl : c1 = [.inst (.tryCall ic ti)] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  obtain ⟨ls1, ls2, psm, h1, h2, rfl⟩ := codeLinesE_append _ _ _ _ _ hls
  have hl1 := codeLinesE_single h1
  obtain ⟨x, hxl, hxs, hplain, hxk⟩ : ∃ x : Insn, ls1 = [.ins x, .ins (.b (.block ti.continuation))] ∧
      (∀ s0 : Arm.ArmState, ∀ jj, R.L[jj]? = some (.ins x) → s0.program = R.fb.program R.base →
        Arm.r .PC s0 = R.pcOf jj → R.step s0 = R.H.call
          (match ic.dest with | .sym n => some n | .reg _ => none) s0) ∧
      (Line.ins x none).plain = true ∧ ((∃ n, x = .bl n) ∨ ∃ r, x = .blr r ∧ (R.vc.DestsInt → r ≠ .xzr)) := by
    cases hd : ic.dest with
    | sym n =>
      simp only [MInst.lines, hd, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
      refine ⟨.bl n, hl1.1.symm, fun s0 jj hj hprog hpc0 => ?_, by simp [Line.plain, Insn.condTarget?],
        .inl ⟨n, rfl⟩⟩
      exact step_bl (off := 0) (r := .xzr) (rd := .xzr) (rn := .xzr) hR hj hprog hpc0
    | reg r =>
      simp only [MInst.lines, hd, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
      refine ⟨.blr r, hl1.1.symm, fun s0 jj hj hprog hpc0 => ?_, by simp [Line.plain, Insn.condTarget?],
        .inr ⟨r, rfl, fun hD => callDest_ne_xzr (hD b vb k info hvb (.inr ⟨ti, hi⟩)) hstat hasg' hd⟩⟩
      exact step_blr (off := 0) (n := "") (rd := .xzr) (rn := .xzr) hR hj hprog hpc0
  subst hxl
  have hZ : ∀ n, (Line.ins (.b (.block ti.continuation)) none :: (ls2 ++ nxtOf R.af b))[1]? ≠
      some (.label (.trap n)) := by
    intro n e
    simp only [List.getElem?_cons_succ] at e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  have hdrop' : R.L.drop j0 = Line.ins x none ::
      (relaxLines R.far (ftList (.ins (.b (.block ti.continuation)) none :: (ls2 ++ nxtOf R.af b))) ++ T) := by
    rw [hdrop, List.append_assoc]
    rw [show [Line.ins x, .ins (.b (.block ti.continuation))] ++ (ls2 ++ nxtOf R.af b) =
      [Line.ins x none] ++ (.ins (.b (.block ti.continuation)) none :: (ls2 ++ nxtOf R.af b)) from rfl,
      ftR_plain_append _ _ _ (by simpa using hplain) hZ]
    rfl
  have hj0 : R.L[j0]? = some (.ins x none) := drop_get (Z := []) hdrop'
  -- the machine: the callee, then `b continuation`
  have hs1 : R.step s = s' := by
    rw [hxs s j0 hj0 hst.prog hpc]
    simp only [callExec, if_pos hst.align, Option.some.injEq] at hex
    exact hex
  have herr' : Arm.r .ERR s' = .None := by rw [hW.1 .ERR (by simp [Masked]), hW'.1]
  have hprog' : s'.program = R.fb.program R.base := by
    rw [hW.2.2, hW'.2, ← hst.world.2.2, hst.prog]
  have hpc1 : Arm.r .PC s' = R.pcOf (j0 + 1) := by
    rw [← hs1, hxs s j0 hj0 hst.prog hpc, hC.pc _ _ hst.err hst.align, hpc, pcOf_succ hj0]
  have hdrop1 : R.L.drop (j0 + 1) =
      relaxLines R.far (ftList (.ins (.b (.block ti.continuation)) none :: (ls2 ++ nxtOf R.af b))) ++ T := by
    rw [← List.drop_drop, hdrop']; rfl
  have hsp' : spOf s' = R.spB := hK.1.trans hst.sp
  obtain ⟨n, jl, hn, hjl, -, hgx⟩ := reach_bXNR (Y := Y) hR hdrop1 (by simp) hprog' hpc1 herr' hsp'
  refine ⟨n + 1, _, MStep.op hvb hi hops hsz hsem hlen hho hc2'
    (MNext.goto hk1 hsucc hitems), ?_, fun i hi => ?_, 0, by omega,
    RL.callSt_of_line hj0 hpc (hxk.imp id fun ⟨r, e, _⟩ => ⟨r, e⟩), fun i hi hne => ?_⟩
  rotate_right
  · obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    simp only [iterN]; rw [hs1]
    exact (hgx i (by omega)).1.2
  rotate_right
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
  have hiter : iterN R.step (n + 1) s = Arm.w .PC (R.pcOf jl) s' := by
    simp only [iterN]; rw [hs1, hn]
  rw [hiter]
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
  exact q_entry hR hst0 hvs hitems (by rw [hjl, hcont]) (Arm.r_of_w_same ..) (hstr.pc _)

end Backend.Proof
