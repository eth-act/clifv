import FV.E2E.RegLevelCallN
import FV.E2E.RegLevelOpNR

/-!
# Calls and symbol addresses on the machine with their call states (SEM1 #537, step 2k)

`RegLevelCallN`'s `realizes_callN`, `runsAs_symAddrN`, `realizes_symAddrN` with the located
reads (`RL.GoodXNR`, SEM1 step 3p).
-/

namespace Backend.Proof

open Backend E2E
/-- **A call on the machine** (`realizes_callN`) **with its located reads**: the segment's states
satisfy `GoodX` and `ReadsIn`, and exactly one of them (the `bl`/`blr`) is a call state. -/
theorem realizes_callNR {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop}
    {P : Arm.ArmState → Prop}
    (hC : CalleeOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    {s : Arm.ArmState} (hP : P s)
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {info : CallInfo} {ops : Array Operand} {outs : List CV} {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.call info))
    (hops : (MInst.call info).operands = .ok ops) (hsz : allocs.size = ops.size)
    (hsem : R.sem (.call info) (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' ∧ (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.ReadsInY Y (iterN R.step i s)) ∧
      ∃ i0 < n, R.CallSt (iterN R.step i0 s) ∧
        ∀ i < n, i ≠ i0 → R.NoCallAt (iterN R.step i s) := by
  have hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program := by
    have herr : Arm.r .ERR w = .None := by
      have hst := q_stRel hq
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    have hsem := R.sem_csem hsem
    simp only [csem, Option.map_eq_some_iff] at hsem
    obtain ⟨⟨o, w2⟩, hx, he⟩ := hsem
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, -⟩ := he
    exact hC.ext _ _ _ _ _ hx herr
  -- the callee contract's premise at the call state
  have hpre : R.CallPre s := by
    obtain ⟨-, -, -, regs, i', -, -, -, -, -, -, -, -, cc, wh, ops', hal, -, -, hasg, -, hops', hstat,
      -, -, -, -, -, -, -, hst⟩ := q_op hq hvb hi
    rw [hops] at hops'; cases hops'
    have hm : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
      hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
    have hsemU := hsem
    rw [hal, useVals_of_store hstat hm] at hsemU
    exact ⟨R.ctx, .call info, .next, ⟨info, ⟨b, vb, k, hvb, .inl hi⟩, .inl rfl⟩, by rw [hst.sp]; exact RL.K_le hR,
      fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha, hst.gkeep, cc, wh, ops, regs, i', w,
      outs, w', hops, hstat, hasg, callAt_of_q hq hvb hi call_hcall regs i' hal hasg, hst.world,
      hst.align, hst.err, hsemU⟩
  refine realizes_op_coreXS hR hq hvb hi hops hsz hsem hlen hk (exec := fun _ => callExec R.H)
    (Seg := fun s n => (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.ReadsInY Y (iterN R.step i s)) ∧
      ∃ i0 < n, R.CallSt (iterN R.step i0 s) ∧
      ∀ i < n, i ≠ i0 → R.NoCallAt (iterN R.step i s))
    (fun _ => RL.callAtGP hR (hC.os R.ctx info ⟨b, vb, k, hvb, .inl hi⟩) hP (q_stRel hq).sp
      (q_stRel hq).gkeep fun i' ⟨regs, hal, hasg⟩ => callAt_of_q hq hvb hi call_hcall regs i' hal hasg)
    hpre (fun regs i' hasg _ _ hcs => ?_) hW'
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
        RunsAsS R (fun _ => callExec R.H) (.call info') ls1 R.CallPre fun s n =>
          (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.ReadsInY Y (iterN R.step i s)) ∧
          ∃ i0 < n, R.CallSt (iterN R.step i0 s) ∧
            ∀ i < n, i ≠ i0 → R.NoCallAt (iterN R.step i s) := by
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
      refine ⟨1, by simp only [iterN]; exact hs, ?_, fun i hi => ?_,
        0, Nat.one_pos, RL.callSt_of_line hj hpc hxc, fun i hi hne => absurd (by omega) hne⟩
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

/-- `runsAs_symAddr` with `GoodXNR`: neither line is a call line. -/
theorem runsAs_symAddrNR {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {i' : MInst} {x1 x2 : Insn}
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
    RunsAsNY R Y (fun _ => symExec R.X) i' [.ins x1, .ins x2] fun _ => True := by
  intro j T s _ _ s' hd hst hpc _ hex
  have hprog := hst.prog
  have hj : R.L[j]? = some (.ins x1) := drop_get (Z := [.ins x2]) hd
  have hj1 : R.L[j + 1]? = some (.ins x2) := drop_get1 (ls := []) hd
  have e := hstep s j hj hj1 hprog hpc
  simp only [hex] at e
  -- the pc: `symExec` advances by 8
  have hpc8 : Arm.r .PC s' = Arm.r .PC s + 8 := by
    revert hex
    cases i' <;> simp only [symExec, Option.some.injEq, reduceCtorEq, false_implies] <;>
      intro hex <;> subst hex <;> simp [Arm.r_of_w_different, Arm.r_of_w_same]
  obtain ⟨hm1, hm2, hm3, hm4⟩ := hmid s j hj hprog hpc
  refine ⟨2, by simpa [iterN] using e, ?_, fun i hi => ?_⟩
  rotate_left
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
  simp only [List.length_cons, List.length_nil, Nat.zero_add]
  rw [hpc8, hpc, ← Nat.add_assoc, pcOf_succ hj1, pcOf_succ hj, BitVec.add_assoc]
  rfl

/-- **`loadExtNameGot/Near` on the machine** (`realizes_symAddr`) with `GoodXNR`. -/
theorem realizes_symAddrNR {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState}
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
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
      Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.GoodXNY Y (iterN R.step i s) := by
  have hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program := by
    have herr : Arm.r .ERR w = .None := by
      have hst := q_stRel hq
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    have hsem := R.sem_csem hsem
    rcases hform with ⟨d, n, rfl⟩ | ⟨d, n, off, rfl⟩ <;>
    · simp only [csem, Option.some.injEq, Prod.mk.injEq] at hsem
      obtain ⟨-, rfl, -⟩ := hsem
      exact ⟨herr, rfl⟩
  refine realizes_op_coreXNR hR hq hvb hi hops hsz hsem hlen hk (exec := fun _ => symExec R.X)
    (fun _ => (((os_symAddr hform).at (fun _ => RL.FK_F) s).toI _).v R.gv) (Pre := fun _ => True) trivial
    (fun regs i' _ _ hex _ => ?_) hW'
  obtain ⟨_, s0, _, hex⟩ := hex
  cases i' with
  | loadExtNameGot rd n =>
    refine ⟨[.ins (.adrpGot rd n), .ins (.ldrGotLo12 rd rd n)],
      fun ps => by simp [MInst.lines, pure, Except.pure], ?_, fun _ h => MInst.noConfusion h,
      fun _ h => MInst.noConfusion h, runsAs_symAddrNR hR (fun ps => by simp [MInst.lines, pure,
        Except.pure]) (fun s j hj hj1 hprog hpc => ?_) ⟨fun _ h => Insn.noConfusion h, fun _ h => Insn.noConfusion h⟩
        ⟨fun _ h => Insn.noConfusion h, fun _ h => Insn.noConfusion h⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
        (fun s j hj hprog hpc => ?_)⟩
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
      fun _ h => MInst.noConfusion h, runsAs_symAddrNR hR (fun ps => by simp [MInst.lines, pure,
        Except.pure]) (fun s j hj hj1 hprog hpc => ?_) ⟨fun _ h => Insn.noConfusion h, fun _ h => Insn.noConfusion h⟩
        ⟨fun _ h => Insn.noConfusion h, fun _ h => Insn.noConfusion h⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
        (fun s j hj hprog hpc => ?_)⟩
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

end Backend.Proof
