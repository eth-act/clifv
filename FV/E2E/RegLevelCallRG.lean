import FV.E2E.RegLevelGoodXRG

/-!
# Calls on the machine with the guarded per-state facts (#753, stage R3')

`RegLevelCallR`'s lemmas with the per-state facts `RL.GoodXR P` (`RegLevelGoodXRG`): at the call
line the callee contract's premise with the guarded step (`RL.CallPreR P`), every other state a
state of `R.noCall`.

* `RunsAsG`, `realizes_op_coreX_semG`: `RunsAs`, `realizes_op_coreX_sem` with any per-state
  predicate `Good`;
* `realizes_callRG`, `realizes_tryCallRG`: `realizes_callR`, `realizes_tryCallR` with `GoodXR P`.
-/

namespace Backend.Proof

open Backend E2E

set_option autoImplicit false

/-- `RunsAs` with the per-state predicate `Good` in place of `R.GoodX`. -/
def RunsAsG (R : RL) (exec : Env → MInst → Arm.ArmState → Option Arm.ArmState) (i' : MInst)
    (ls1 : List Line) (pre Good : Arm.ArmState → Prop) : Prop :=
  ∀ j T s m w s', R.L.drop j = ls1 ++ T → StRel R s m w → Arm.r .PC s = R.pcOf j → pre s →
    exec (R.envOf j) i' s = some s' →
    ∃ n, iterN R.step n s = s' ∧ Arm.r .PC s' = R.pcOf (j + ls1.length) ∧
      ∀ i < n, Good (iterN R.step i s)

/-- `realizes_op_coreX_sem` with any per-state predicate `Good` (`RunsAsG`). -/
theorem realizes_op_coreX_semG {R : RL} (hR : R.Wf) {sem : ISem CV Arm.ArmState} {s : Arm.ArmState}
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} {ops : Array Operand} {outs : List CV} {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hops : i.operands = .ok ops)
    (hsz : allocs.size = ops.size)
    (hsem : sem i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size)
    {exec : Env → MInst → Arm.ArmState → Option Arm.ArmState}
    (hOS : ∀ env, OperandsSoundCtlAtI R.F R.FK
      (fun i' => ∃ regs, allocs = regs.map Loc.reg ∧ i.assign regs = .ok i') (exec env) sem i .next s)
    {Pre Good : Arm.ArmState → Prop} (hpre : Pre s)
    (hL : ∀ regs i', i.assign regs = .ok i' → allocs = regs.map Loc.reg →
      (∃ env s s', exec env i' s = some s') →
      (∃ (c : CheckCtx) (wh : String), c.checkStatic wh ops (regs.map Loc.reg) i.clobbers = .ok ()) →
      ∃ ls1, (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) ∧
      (∀ ln ∈ ls1, ln.plain = true) ∧ (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us) ∧
      RunsAsG R exec i' ls1 Pre Good)
    (hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    ∃ n c'', MStep R.vc sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' ∧ ∀ i < n, Good (iterN R.step i s) := by
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

/-- **A call on the machine under the register-guarded semantics** with the per-state facts `GoodXR P`
(`realizes_callR` with the guarded premise `CallPreR P` at the call line). -/
theorem realizes_callRG {R : RL} (hR : R.Wf) {P : BitVec 64 → Clif.Signature → Prop}
    (hC : CalleeOkGR P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    {s : Arm.ArmState}
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {info : CallInfo} {ops : Array Operand} {outs : List CV} {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.call info))
    (hops : (MInst.call info).operands = .ok ops) (hsz : allocs.size = ops.size)
    (hsem : regG P R.sem (.call info) (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size) :
    ∃ n c'', MStep R.vc (regG P R.sem) ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.GoodXR P (iterN R.step i s) := by
  have hsemB := regG_sub hsem
  have hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program := by
    have herr : Arm.r .ERR w = .None := by
      have hst := q_stRel hq
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    have hsem := R.sem_csem hsemB
    simp only [csem, Option.map_eq_some_iff] at hsem
    obtain ⟨⟨o, w2⟩, hx, he⟩ := hsem
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, -⟩ := he
    exact hC.ext _ _ _ _ _ hx herr
  -- the callee contract's premise at the call state
  have hpre : R.CallPreR P s := by
    obtain ⟨-, -, -, regs, i', -, -, -, -, -, -, -, -, -, cc, wh, ops', hal, -, -, hasg, -, hops',
      hstat, -, -, -, -, -, -, -, -, hst, -, -⟩ := q_op hR hq hvb hi hk
    rw [hops] at hops'; cases hops'
    have hm : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
      hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
    have hsemU := hsem
    rw [hal, useVals_of_store hstat hm] at hsemU
    exact ⟨R.ctx, .call info, .next, ⟨info, ⟨b, vb, k, hvb, .inl hi⟩, .inl rfl⟩, by rw [hst.sp]; exact RL.K_le hR,
      fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha, hst.gkeep, cc, wh, ops, regs, i', w,
      outs, w', hops, hstat, hasg, callAt_of_q hR hq hvb hi call_hcall regs i' hal hasg, hst.world,
      hst.align, hst.err, hsemU⟩
  refine realizes_op_coreX_semG (Good := R.GoodXR P) hR hq hvb hi hops hsz hsem hlen hk (exec := fun _ => callExec R.H)
    (fun _ => RL.callAtG hR (hC.os R.ctx info ⟨b, vb, k, hvb, .inl hi⟩) (q_stRel hq).sp
      (q_stRel hq).gkeep fun i' ⟨regs, hal, hasg⟩ => callAt_of_q hR hq hvb hi call_hcall regs i' hal hasg)
    hpre (fun regs i' hasg _ _ hcs => ?_) hW'
  obtain ⟨info', rfl⟩ := assign_call_form hasg
  have hgen : ∀ x, (∀ ps, (MInst.call info').lines R.ctx ps = .ok ([.ins x], ps)) →
      (Line.ins x).plain = true → x.tlsTail = false → (∀ rd rn n, x ≠ .ldrGotLo12 rd rn n) →
      (∀ r, x = .blr r → R.vc.DestsInt → r ≠ .xzr) → x.hooked = true →
      (∀ s j, R.L[j]? = some (.ins x) → s.program = R.fb.program R.base →
        Arm.r .PC s = R.pcOf j → R.step s = R.H.call
          (match info'.dest with | .sym n => some n | .reg _ => none) s) →
      ∃ ls1, (∀ ps, (MInst.call info').lines R.ctx ps = .ok (ls1, ps)) ∧
        (∀ ln ∈ ls1, ln.plain = true) ∧ (∀ ds, MInst.call info' ≠ .args ds) ∧
        (∀ us, MInst.call info' ≠ .rets us) ∧
        RunsAsG R (fun _ => callExec R.H) (.call info') ls1 (R.CallPreR P) (R.GoodXR P) := by
    intro x hl1 hpl hxt hxg hxz hxh hstep
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
      refine ⟨1, by simp only [iterN]; exact hs, ?_, fun i hi => ?_⟩
      · rw [hC.pc _ _ hst.err hal, hpc, List.length_singleton, pcOf_succ hj]
      · obtain rfl : i = 0 := by omega
        show R.GoodXR P s
        exact .inr ⟨RL.goodX_line hR hj hpc hxt (RL.good_of_sp hst.sp) hst.err hst.prog
          (RL.nextOk_pc4 (by rw [hs, hC.pc _ _ hst.err hal]))
          (fun rd rn n e => absurd e (hxg rd rn n)) (fun r e => ⟨hxz r e, hst.code⟩)
          (fun _ => hpre'.toCallPre) (RL.readsAt_hooked hR hj hpc hxh), hpre'⟩
    · cases hex
  cases hd : info'.dest with
  | sym n =>
    refine hgen (.bl n) (fun ps => by simp [MInst.lines, hd, pure, Except.pure])
      (by simp [Line.plain, Insn.condTarget?]) rfl (fun _ _ _ h => by cases h)
      (fun _ h => by cases h) rfl fun s j hj hprog hpc => ?_
    rw [step_bl (off := 0) (r := .xzr) (rd := .xzr) (rn := .xzr) hR hj hprog hpc, hd]
  | reg r =>
    obtain ⟨c, wh, hcs⟩ := hcs
    have hne : R.vc.DestsInt → r ≠ .xzr := fun hD =>
      callDest_ne_xzr (hD b vb k info hvb (.inl hi)) hcs hasg hd
    refine hgen (.blr r) (fun ps => by simp [MInst.lines, hd, pure, Except.pure])
      (by simp [Line.plain, Insn.condTarget?]) rfl (fun _ _ _ h => by cases h)
      (fun _ h => by cases h; exact hne) rfl fun s j hj hprog hpc => ?_
    rw [step_blr (off := 0) (n := "") (rd := .xzr) (rn := .xzr) hR hj hprog hpc, hd]

/-- **The call of a `try_call` on the machine under the register-guarded semantics**
with the per-state facts `GoodXR P` (`realizes_tryCallR` with the
guarded premise at the call line; the branch to the successor's states at `R.noCall`). -/
theorem realizes_tryCallRG {R : RL} (hR : R.Wf) {P : BitVec 64 → Clif.Signature → Prop}
    (hC : CalleeOkGR P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : CalleeTryOkGR P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {info : CallInfo} {ti : TryInfo} {ops : Array Operand} {outs : List CV}
    {w' : Arm.ArmState} {ctl : Ctl}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.tryCall info ti))
    (hops : (MInst.tryCall info ti).operands = .ok ops) (hsz : allocs.size = ops.size)
    (hsemG : regG P R.sem (.tryCall info ti)
      (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = some (outs, w', ctl))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    {j st : Nat} {items : Array RItem} (hk1 : k + 1 = vb.insts.size)
    (hsucc : succOf R.vc b j = some st) (hitems : R.rf.blocks[st]? = some items)
    (hctl : ctl = .goto j) :
    ∃ n c'', MStep R.vc (regG P R.sem) ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.GoodXR P (iterN R.step i s) := by
  obtain ⟨hguard, hsem⟩ := regG_inv hsemG
  have hck := (hR.alloc.ok).2.2
  have hcpc := callAt_of_q hR hq hvb hi tryCall_hcall
  rcases Q.cases hq with hqs | ⟨vbf, allocsf, regsf, if_, xf, bx, hvbf, he, hits, half, hins, hasgf,
    hsuccf, itx, hitx, hqx⟩
  rotate_left
  · -- a forwarding block: its `jump` takes no machine step, but a `try_call`'s allocated form
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
    obtain ⟨ic, e, -⟩ := (assign_call_tryCall info regsf).2 ti (.jump xf) hasgf
    cases e
  obtain ⟨_, vb0, _, _, code, _, _, _, _, _, hvb0, -, -, hchk0, hcode, -⟩ := id hqs
  rw [hvb] at hvb0; cases hvb0
  obtain rfl : its = [] := hchk0.tail_nil hk1
  obtain ⟨j0, vb0, items, pre, c1, X, ps1, psm, ps2, x, hvb0, hit, hsplit, hchk, hc1, hX, hTq, htr,
    hdrop, hpc, hst, hterm⟩ := qs_term hR hqs
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
  have hguardU := hguard
  rw [useVals_of_store hstat hm] at hguardU
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
  have hsemCR : csemVR P R.gv R.F R.ctx R.X (.call info) (useVals ops regs s) w =
      some (xo.take info.defs.length, w2, .next) := by
    have hgC : RegGuardI P (.call info) (useVals ops regs s) := hguardU
    simp only [csemVR, regG_of hgC]
    exact hsemC
  have hsemUR : csemVR P R.gv R.F R.ctx R.X (.tryCall info ti) (useVals ops regs s) w =
      some (outs, w2, .goto ti.handlers.length) := by
    simp only [csemVR, regG_of hguardU]
    exact hsemU
  have hpreR : R.CallPreR P s := ⟨R.ctx, .tryCall info ti, .goto ti.handlers.length,
    ⟨info, ⟨b, vb, k, hvb, .inr ⟨ti, hi⟩⟩, .inr ⟨ti, rfl⟩⟩,
    by rw [hst.sp]; exact RL.K_le hR, fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha,
    hst.gkeep, cc, wh, ops, regs, .tryCall ic ti, w, outs, w2, hops, hstat, hasg, hcpcT,
    hst.world, hst.align, hst.err, hsemUR⟩
  obtain ⟨s', hex, hW, hK, -, hoth, hkeep⟩ :=
    RL.callAtG hR (hC.os R.ctx info ⟨b, vb, k, hvb, .inr ⟨ti, hi⟩⟩) hst.sp hst.gkeep
      (P := (· = .call ic)) (fun _ e => e ▸ callAt_tryCall_call hcpcT) cc wh ops regs (.call ic)
      w (xo.take info.defs.length) w2 (by rw [← operands_tryCall_call info ti]; exact hops)
      (by rw [← clobbers_tryCall hcl]; exact hstat) hasg' rfl hst.world hst.align hst.err hsemCR
  have hexT : callExec R.H (.tryCall ic ti) s = some s' := by
    simp only [callExec] at hex ⊢; exact hex
  have hres := hT R.ctx info ti ⟨b, vb, k, hvb, hi⟩ cc wh ops regs (.tryCall ic ti) s w outs w2 s'
    (by rw [hst.sp]; exact RL.K_le hR) (fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha)
    hst.gkeep hops hstat hasg hcpcT hst.world hst.align hst.err hsemUR hexT
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
      exact step_blr (off := 0) (n := "") (rd := .xzr) (rn := .xzr) hR hj hprog hpc0
  -- the branch check's verdict on the final lines
  obtain ⟨call, b0, htermL, hcase⟩ := termOk_tryCall hterm
  rw [hxterm] at htermL
  obtain ⟨rfl, rfl⟩ := htermL
  obtain ⟨O, hx21O, hcaseO⟩ : ∃ O, x.2.1 = .ins xI none :: O ∧
      ((∃ l', O = [.ins (.b l') none] ∧
          RepLbl (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) ti.continuation l') ∨
        (O = [] ∧ planRep R.fa.k R.af ti.continuation x.2.2 = true)) := by
    rcases hcase with ⟨l', hx21, hrl⟩ | ⟨hx21, hrn⟩
    · exact ⟨[.ins (.b l') none], hx21.trans rfl, .inl ⟨l', rfl, hrl⟩⟩
    · exact ⟨[], hx21.trans rfl, .inr ⟨rfl, hrn⟩⟩
  have hj0 : R.L[j0]? = some (.ins xI none) :=
    drop_get (Z := relaxLines R.far O) (by
      rw [hdrop0, hx21O, relaxLines_cons,
        relaxLine_of_none (by rcases hxk with ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> rfl),
        List.singleton_append])
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
    rw [← List.drop_drop, hdrop0, hx21O, relaxLines_cons,
      relaxLine_of_none (by rcases hxk with ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> rfl)]
    simp
  have hoo : (∃ l', O = [.ins (.b l') none] ∧
        RepLbl (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) vs.label l') ∨
      (O = [] ∧ planRep R.fa.k R.af vs.label x.2.2 = true) := by
    rcases hcaseO with ⟨l', hO, hrl⟩ | ⟨hO, hrn⟩
    · exact .inl ⟨l', hO, by rw [hcont]; exact hrl⟩
    · exact .inr ⟨hO, by rw [hcont]; exact hrn⟩
  obtain ⟨n, jl, hn, hrep, -, hgx⟩ := reach_jumpX hR.noCall hdrop1 hoo hprog' hpc1 herr' hsp'
  rw [RL.noCall_step] at hn hgx
  refine ⟨n + 1, _, MStep.op hvb hi hops hsz hsemG hlen hho hc2'
    (MNext.goto hk1 hsucc hitems), ?_, fun i hi => ?_⟩
  rotate_right
  · cases i with
    | zero =>
      show R.GoodXR P s
      refine .inr ⟨?_, hpreR⟩
      exact RL.goodX_line hR hj0 hpc (by rcases hxk with ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> rfl)
        (RL.good_of_sp hst.sp) hst.err hst.prog
        (RL.nextOk_pc4 (by rw [hs1, hpc1, pcOf_succ hj0, hpc]))
        (fun _ _ _ e => by rcases hxk with ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> cases e)
        (fun r e => by
          rcases hxk with ⟨_, rfl⟩ | ⟨_, rfl, hr⟩
          · cases e
          · cases e; exact ⟨hr, hst.code⟩)
        (fun _ => hpre)
        (RL.readsAt_hooked hR hj0 hpc (by rcases hxk with ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> rfl))
    | succ i =>
      simp only [iterN]; rw [hs1]
      exact .inl (hgx i (by omega))
  have hiter : iterN R.step (n + 1) s = Arm.w .PC (R.pcOf jl) s' := by
    simp only [iterN]; rw [hs1, hn]; rfl
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
  exact q_entry hR hst0 hvs hitems hrep (Arm.r_of_w_same ..) (hstr.pc _)

end Backend.Proof
