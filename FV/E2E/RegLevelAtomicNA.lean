import FV.E2E.RegLevelQW
import FV.E2E.RegLevelCallNA
import FV.E2E.RegLevelFRFree
import FV.E2E.RegLevelAtomicNR

/-!
# Atomic loops, at a witness (SEM1 #537, item (3), route (a))

`realizes_rmwLoopNY` from `QW`: the loop's label, its body once and the `cbnz`, to the next item
at the straight witness, at the first arrival.
-/

namespace Backend.Proof

open Backend E2E

/-- **A nonempty straight segment inside its lines from an instruction line `jb`** has `SegLen`. -/
theorem RL.segLen_straight_base {R : RL} (hR : R.Wf) {j : Nat} {ps1 : PState} {T : List Line}
    {c c'' : MConf CV Arm.ArmState} {s : Arm.ArmState} {n jb jt : Nat} {xb : Insn}
    {tb : Option Clif.TrapCode}
    (hS : RL.Straight c c'') (hW : ∀ p, (R.nextW j ps1 T c c'' p).1 = jt)
    (hb : R.L[jb]? = some (.ins xb tb)) (hin : R.Inside s n jb jt)
    (hpn : Arm.r .PC (iterN R.step n s) = R.pcOf jt) (hpos : 0 < n) (hne : jt ≠ j) :
    R.SegLen j ps1 T c c'' s n := by
  refine ⟨?_, ?_⟩
  · rw [RL.tgtS_of_straight hS 0, hW]
    exact firstArrS_singleton.mpr (RL.firstArr_of_inside hR hb hin (Nat.le_refl _) hpn)
  · unfold RL.EmptyW
    rw [if_pos hS, hW]
    exact ⟨fun h => absurd h (by omega), fun h => absurd h hne⟩

theorem relaxLines_rmwLoopLines {ty : CTy} (hty : AtomTy ty) (op : AtomicRmwLoopOp)
    (fl : Clif.MemFlags) (n : Nat) (f : Lbl → Bool) :
    relaxLines f (rmwLoopLines ty.bits op fl (.loop n)) = rmwLoopLines ty.bits op fl (.loop n) := by
  have hb : rmwLoopLines ty.bits op fl (.loop n) =
      (.label (.loop n) :: rmwLoopBody ty.bits op fl) ++ [.ins (.cbz true true (.x 24) (.loop n)) none] := by
    simp [rmwLoopLines]
  have hP : ∀ ln ∈ Line.label (.loop n) :: rmwLoopBody ty.bits op fl,
      (∀ x t, ln ≠ .ins (.b x) t) ∧ ∀ c, ln = .ins c none → c.condTarget? = none := by
    rcases hty with rfl | rfl | rfl | rfl <;> cases op <;>
      simp (config := {decide := true}) [rmwLoopBody, rmwLoopMid, rmwLoopStored, rmwLoopSext,
        rmwLoopCmp, CTy.bits, Insn.condTarget?]
  rw [hb, relaxLines_append, relaxLines_of_none fun ln h => relaxable_none (hP ln h).2]
  rfl

theorem frLine_rmwLoopBody (bits : Nat) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags) :
    ∀ x t, Line.ins x t ∈ rmwLoopBody bits op fl → x.frLine = false := by
  intro x t hx
  simp only [rmwLoopBody, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil,
    or_false, Line.ins.injEq] at hx
  rcases hx with (⟨rfl, -⟩ | ⟨a, ha, rfl, -⟩) | ⟨rfl, -⟩
  · rfl
  · exact frLine_rmwLoopMid ha
  · rfl

set_option maxHeartbeats 4000000 in
/-- **`realizes_rmwLoopNA` with the segment's lines** (`RL.FRFree`). -/
theorem realizes_rmwLoopNAF {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {b k : Nat}
    {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {c' : MConf CV Arm.ArmState}
    {j0 : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j0 ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {ty : CTy}
    {op : AtomicRmwLoopOp} {fl : Clif.MemFlags} {ra ro rd r1 r2 : Reg}
    (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.atomicRmwLoop ty op fl ra ro rd r1 r2))
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c')
    (hsemY : ∀ ops, (MInst.atomicRmwLoop ty op fl ra ro rd r1 r2).operands = .ok ops →
      ∃ rY, csem Y R.ctx R.X (.atomicRmwLoop ty op fl ra ro rd r1 r2)
        (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = some rY) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      R.SegNA Y s j0 ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' n ∧ R.FRFree s n := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  have hok := ctlCheck_inst hck hvb hi
  simp only [ctlInstOk, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hok
  obtain ⟨va, rfl⟩ := isVregInt_iff h0
  obtain ⟨vo, rfl⟩ := isVregInt_iff h1
  obtain ⟨vd, rfl⟩ := isVregInt_iff h2
  obtain ⟨v1, rfl⟩ := isVregInt_iff h3
  obtain ⟨v2, rfl⟩ := isVregInt_iff h4
  cases h with
  | @op b k allocs its m w vb'' i opsm outs outs' w' ctl m2 c' hvb' hi' hopsm hsz' hsem hlen hho hcl hn =>
  rw [hvb] at hvb'; cases hvb'
  rw [hi] at hi'; cases hi'
  -- the loop's control outcome is always `.next`, so its item is not the block's last
  have hk : k + 1 < vb.insts.size := by
    simp only [RL.sem, csemV, csem] at hsem
    split at hsem
    · split at hsem
      · obtain ⟨-, -, -, -, hctl⟩ := loopSem_inv hsem
        cases hn with
        | next hk => exact hk
        | @goto jj st items' hk1 hsucc hitems => simp at hctl
        | ret hh => simp at hctl
        | halt => simp at hctl
      · split at hsem
        · simp only [Option.some.injEq, Prod.mk.injEq] at hsem
          have hctl := hsem.2.2.symm
          cases hn with
          | next hk => exact hk
          | @goto jj st items' hk1 hsucc hitems => simp at hctl
          | ret hh => simp at hctl
          | halt => simp at hctl
        · cases hsem
    · cases hsem
  obtain ⟨hT0, items, pre, regs, i', c1, c2, X', ls1, psm, psm', ps2, x, cc, wh, ops, hc1o, rfl,
    hit, hsplit, hasg, hc1', hops, hstat, hchk', hc2, hl1, hX2, hT2, htr, hdrop, hpc, hst, hx,
    hsc⟩ := qW_op hR hq hvb hi hk
  have hoppseq : opsm = ops := Except.ok.inj (hopsm.symm.trans hops)
  subst hoppseq
  have hops' : opsm = #[⟨va, .int, .use, .early, .fixed (.x 25)⟩, ⟨vo, .int, .use, .early, .fixed (.x 26)⟩,
      ⟨vd, .int, .def, .late, .fixed (.x 27)⟩, ⟨v1, .int, .def, .late, .fixed (.x 24)⟩,
      ⟨v2, .int, .def, .late, .fixed (.x 28)⟩] := by
    have e : (MInst.atomicRmwLoop ty op fl (.vreg va .int) (.vreg vo .int) (.vreg vd .int)
        (.vreg v1 .int) (.vreg v2 .int)).operands =
        .ok #[⟨va, .int, .use, .early, .fixed (.x 25)⟩, ⟨vo, .int, .use, .early, .fixed (.x 26)⟩,
          ⟨vd, .int, .def, .late, .fixed (.x 27)⟩, ⟨v1, .int, .def, .late, .fixed (.x 24)⟩,
          ⟨v2, .int, .def, .late, .fixed (.x 28)⟩] := rfl
    rw [e] at hopsm; injection hopsm with h; exact h.symm
  subst hops'
  obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts hstat
  obtain ⟨q0, q1, q2, q3, q4, rfl⟩ := regs5 (by simpa using hsz.symm)
  obtain rfl : q0 = .x 25 := fixed_reg (o := ⟨va, .int, .use, .early, .fixed (.x 25)⟩) hloc (by simp) rfl
  obtain rfl : q1 = .x 26 := fixed_reg (o := ⟨vo, .int, .use, .early, .fixed (.x 26)⟩) hloc (by simp) rfl
  obtain rfl : q2 = .x 27 := fixed_reg (o := ⟨vd, .int, .def, .late, .fixed (.x 27)⟩) hloc (by simp) rfl
  obtain rfl : q3 = .x 24 := fixed_reg (o := ⟨v1, .int, .def, .late, .fixed (.x 24)⟩) hloc (by simp) rfl
  obtain rfl : q4 = .x 28 := fixed_reg (o := ⟨v2, .int, .def, .late, .fixed (.x 28)⟩) hloc (by simp) rfl
  have hasg' : (MInst.atomicRmwLoop ty op fl (.vreg va .int) (.vreg vo .int) (.vreg vd .int)
      (.vreg v1 .int) (.vreg v2 .int)).assign #[.x 25, .x 26, .x 27, .x 24, .x 28] =
      .ok (.atomicRmwLoop ty op fl (.x 25) (.x 26) (.x 27) (.x 24) (.x 28)) := rfl
  rw [hasg'] at hasg; cases hasg
  obtain rfl : c1 = [.inst (.atomicRmwLoop ty op fl (.x 25) (.x 26) (.x 27) (.x 24) (.x 28))] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  have hl1o := hl1
  have hl1' := codeLinesE_single hl1
  simp only [MInst.lines, bne_self_eq_false, Bool.or_false, Bool.and_false, Bool.false_eq_true,
    ite_false, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1'
  obtain ⟨rfl, rfl⟩ := hl1'
  have hreg : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
    hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
  have hU : (((#[(⟨va, .int, .use, .early, .fixed (.x 25)⟩ : Operand),
      ⟨vo, .int, .use, .early, .fixed (.x 26)⟩, ⟨vd, .int, .def, .late, .fixed (.x 27)⟩,
      ⟨v1, .int, .def, .late, .fixed (.x 24)⟩, ⟨v2, .int, .def, .late, .fixed (.x 28)⟩].zip
      (#[Reg.x 25, .x 26, .x 27, .x 24, .x 28].map Loc.reg)).toList.filter (·.1.isUse)).map (m ·.2)) =
      [regVal s (.x 25), regVal s (.x 26)] := by
    simp [Operand.isUse, hreg (.x 25) rfl, hreg (.x 26) rfl]
  have hsem0 := hsem
  rw [hU] at hsem
  have herrw : Arm.r .ERR w = .None := by
    rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
  simp only [RL.sem, csemV, csem, herrw, ite_true] at hsem
  obtain ⟨hty, hav, hrunw, rfl, rfl⟩ := loopSem_inv hsem
  simp only [List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, setReg_x,
    lo64_regVal_x, rnum] at hrunw hav
  obtain ⟨rY, hY⟩ := hsemY _ hops
  rw [hU] at hY
  simp only [csem, herrw, ite_true] at hY
  obtain ⟨-, havY, -, -, -⟩ := loopSem_inv hY
  simp only [List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, setReg_x,
    lo64_regVal_x, rnum] at havY
  have hsw0 : SameWorld R.F s (Arm.w (.GPR 26#5) (Arm.r (.GPR 26#5) s)
      (Arm.w (.GPR 25#5) (Arm.r (.GPR 25#5) s) w)) :=
    SameWorld.w_right (by simp [Masked]) (SameWorld.w_right (by simp [Masked]) hst.world)
  have h25 : Arm.r (.GPR 25#5) s = Arm.r (.GPR 25#5) (Arm.w (.GPR 26#5) (Arm.r (.GPR 26#5) s)
      (Arm.w (.GPR 25#5) (Arm.r (.GPR 25#5) s) w)) := by simp
  have h26 : Arm.r (.GPR 26#5) s = Arm.r (.GPR 26#5) (Arm.w (.GPR 26#5) (Arm.r (.GPR 26#5) s)
      (Arm.w (.GPR 25#5) (Arm.r (.GPR 25#5) s) w)) := by simp
  have hav' := hav
  rw [h25] at hav'
  obtain ⟨s1, hrun1, hint1, -, h24, hfr1, hmem1, hprog1⟩ :=
    rmwBody_spec hty op fl (R.envOf (j0 + 1)) s hst.err
  obtain ⟨hsw1, h27⟩ := rmwBody_congr hty op fl (R.envOf (j0 + 1)) env0 hsw0 h25 h26 hav' hrun1 hrunw
  have hloop := relaxLines_rmwLoopLines hty op fl ps1.aloop R.far
  have hL0 : R.L[j0]? = some (.label (.loop ps1.aloop)) := by
    have h9 := congrArg (·[0]?) hdrop
    rw [List.getElem?_drop, Nat.add_zero, hloop,
      show rmwLoopLines ty.bits op fl (.loop ps1.aloop) = .label (.loop ps1.aloop) ::
        (rmwLoopBody ty.bits op fl ++ [.ins (.cbz true true (.x 24) (.loop ps1.aloop)) none]) from rfl,
      List.cons_append, List.append_assoc, List.getElem?_cons_zero] at h9
    exact h9
  have hd1 : R.L.drop (j0 + 1) = rmwLoopBody ty.bits op fl ++
      (.ins (.cbz true true (.x 24) (.loop ps1.aloop)) none ::
        (relaxLines R.far (X' ++ x.2.1) ++ R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2))) := by
    rw [← List.drop_drop, hdrop, hloop]
    simp [rmwLoopLines]
  have hpc1 : Arm.r .PC s = R.pcOf (j0 + 1) := by rw [hpc, RL.pcOf_succ_label hL0]
  obtain ⟨hit1, hpcs1, hgood1, hgx1⟩ := run_insNR (Y := Y) hR hd1 (rmwBody_ins hty op fl) hst.prog
    hpc1 hst.err
    hint1 hrun1
  have hatb : ∀ k ln, (rmwLoopBody ty.bits op fl)[k]? = some ln →
      R.fa.lines.toList[j0 + 1 + k]? = some ln := by
    intro k ln hk
    have := congrArg (·[k]?) hd1
    simp only [List.getElem?_drop, RL.L] at this
    rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk).1]
    exact hk
  have hpcsI := iterN_execLines_pc (X := R.X) (H := R.H) hR.layout hR.lm hR.fit _ (j0 + 1) s s1 hatb
    (fun i t h => by obtain ⟨i', t', e, hh⟩ := rmwBody_ins hty op fl _ h; cases e; exact hh)
    hst.prog (by rw [hpc1]; rfl) hst.err hint1 hrun1
  have herr1 : Arm.r .ERR s1 = .None := by
    rw [hfr1 .ERR (by simp) (by simp) (by simp)]; exact hst.err
  have hprog1' : s1.program = R.fb.program R.base := by rw [hprog1]; exact hst.prog
  have hLc : R.L[j0 + 1 + (rmwLoopBody ty.bits op fl).length]? =
      some (.ins (.cbz true true (.x 24) (.loop ps1.aloop)) none) := by
    have := congrArg (·[(rmwLoopBody ty.bits op fl).length]?) hd1
    simp only [List.getElem?_drop] at this
    rw [this]; simp
  obtain ⟨a, jl, ha, -, hstep⟩ := step_branch hR hLc (.inr (.inr (.inl ⟨true, true, .x 24, rfl⟩))) (by simp)
    hprog1' hpcs1 herr1
  have hbr : brCond a s1 = false := by
    rw [brCond_cbz (by decide) ha]; simp [rnum, h24]
  rw [hbr] at hstep
  simp only [Bool.false_eq_true, ite_false] at hstep
  have hiter : iterN R.step ((rmwLoopBody ty.bits op fl).length + 1) s =
      Arm.w .PC (R.pcOf (j0 + 1 + (rmwLoopBody ty.bits op fl).length + 1)) s1 := by
    rw [iterN_add, hit1]; simp [iterN, hstep]
  have hfr2 : ∀ f, f ≠ .PC → (∀ n ∈ [27, 24, 28], f ≠ .GPR (rnum n)) → (∀ g, f ≠ .FLAG g) →
      Arm.r f (Arm.w .PC (R.pcOf (j0 + 1 + (rmwLoopBody ty.bits op fl).length + 1)) s1) =
        Arm.r f s := by
    intro f h1 h2 h3
    rw [Arm.r_of_w_different h1]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, rnum] at h2
    exact hfr1 f h1 (by simp [h2.1, h2.2.1, h2.2.2]) h3
  have hlenL : (rmwLoopLines ty.bits op fl (.loop ps1.aloop)).length =
      (rmwLoopBody ty.bits op fl).length + 2 := by simp [rmwLoopLines]
  have hWs : ∀ (m' : Loc → CV) (w'' : Arm.ArmState) (p : BitVec 64),
      R.nextW j0 ps1 T (.run ⟨b, .op k (#[Reg.x 25, .x 26, .x 27, .x 24, .x 28].map Loc.reg) :: its, m, w⟩)
        (.run ⟨b, its, m', w''⟩) p = (j0 + (rmwLoopBody ty.bits op fl).length + 2,
          { ps1 with aloop := ps1.aloop + 1 }, T) := by
    intro m' w'' p
    rw [RL.nextW_straight, RL.straightW_eq hvb hc1o hl1o, relaxLines_rmwLoopLines hty, hlenL]
    rfl
  refine ⟨(rmwLoopBody ty.bits op fl).length + 1, _,
    MStep.op (outs' := [regVal (Arm.w .PC (R.pcOf (j0 + 1 + (rmwLoopBody ty.bits op fl).length + 1)) s1) (.x 27),
      regVal (Arm.w .PC (R.pcOf (j0 + 1 + (rmwLoopBody ty.bits op fl).length + 1)) s1) (.x 24),
      regVal (Arm.w .PC (R.pcOf (j0 + 1 + (rmwLoopBody ty.bits op fl).length + 1)) s1) (.x 28)])
      (m2 := m) hvb hi hops hsz' hsem0 hlen ⟨by simp, fun h => by simp [havocFrom, MInst.keptDefs] at h,
        fun n h => ?_⟩ ?_ (MNext.next hk), ⟨?_, fun i hi => ?_, ?_⟩, ?_⟩
  · simp only [havocFrom, MInst.keptDefs, Option.some.injEq] at h
    subst h
    simp [regVal, rnum, h27]
  · refine ⟨fun l _ => ?_, fun c hc => by simp [MInst.clobbers] at hc⟩
    simp [writeM, Operand.isDef, Operand.isEarly]
  · unfold RL.QWn
    rw [hWs, hiter]
    refine .inl ⟨hT0, vb, items, pre ++ [.op k (#[Reg.x 25, .x 26, .x 27, .x 24, .x 28].map Loc.reg)],
      c2, X', psm', ps2, x, hvb, hit, by rw [hsplit]; simp, hchk', hc2, hX2, hT2, htr, ?_, ?_, ?_,
      hx, hsc⟩
    · rw [show j0 + (rmwLoopBody ty.bits op fl).length + 2 =
        j0 + (rmwLoopLines ty.bits op fl (.loop ps1.aloop)).length by rw [hlenL]; omega,
        ← List.drop_drop, hdrop, hloop, List.drop_left' (by simp [rmwLoopLines])]
    · simp only [Arm.r_of_w_same]
      congr 1
      omega
    · refine stRel_after hR hst ?_ ?_ (SameWorld.w_left (by simp [Masked]) hsw1) ?_ ?_
        ⟨?_, fun a ha => ?_, ?_⟩
      · refine store_regs hst [27, 24, 28] (by simp) ?_ ?_ hfr2
        · intro n hn
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
          rcases hn with rfl | rfl | rfl <;>
            simp [writeM, upd, Operand.isDef, Operand.isLate]
        · intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
          simp [writeM, upd, Operand.isDef, Operand.isLate, hr.1, hr.2.1, hr.2.2]
      · intro l hl
        simp [writeM, upd, Operand.isDef, Operand.isLate, hl]
      · rw [hfr2 .ERR (by simp) (by simp) (by simp)]; exact hst.err
      · simp only [Arm.w_program]; exact hprog1
      · simp only [spOf]; exact hfr2 _ (by simp) (by simp [rnum]) (by simp)
      · simp only [Arm.ArmState.mem_w_eq_mem, hmem1]
        refine mem_write_mem_bytes_ne _ _ _ _ _ (fun k hk e => hav k hk ?_)
        rw [← e]; exact RL.FK_F ha
      · exact hfr2 _ (by simp) (by simp [rnum]) (by simp)
  · rcases Nat.lt_or_ge i (rmwLoopBody ty.bits op fl).length with hi1 | hi1
    · exact hgx1 (rmwBody_tail hty op fl) (RL.good_of_sp hst.sp)
        (rmwBody_reads hty op fl _ s fun q hq => .inr (.inr ⟨hav q hq, havY q hq⟩)) i hi1
    · obtain rfl : i = (rmwLoopBody ty.bits op fl).length := by omega
      rw [hit1]
      refine RL.goodXNR_ofIns hR hLc hpcs1 rfl rfl ?_ herr1 hprog1' ?_ ?_
      · rcases Nat.eq_zero_or_pos (rmwLoopBody ty.bits op fl).length with h0 | h0
        · rw [← hit1, h0]; exact RL.good_of_sp hst.sp
        · rw [← hit1]; exact hgood1 _ h0 (Nat.le_refl _)
      · rw [hstep]; exact RL.nextOk_succ hLc rfl (Arm.r_of_w_same ..)
      · exact RL.readsIn_noLoad hR hLc hpcs1 rfl
  · -- the segment length
    have hb0 : ∃ x t, R.L[j0 + 1]? = some (.ins x t) := by
      have := hatb 0 (.ins (.ldaxr ty.bits (.x 27) (.x 25)) fl.trapCode) (by simp [rmwLoopBody])
      exact ⟨_, _, by simpa [RL.L] using this⟩
    obtain ⟨xb, tb, hb⟩ := hb0
    refine RL.segLen_straight_base hR (by simp [RL.Straight]) (fun _ => by rw [hWs])
      hb (fun i h0 hi => ?_) (by rw [hiter, Arm.r_of_w_same]; congr 1; omega) (by omega) (by omega)
    rcases Nat.lt_or_ge i (rmwLoopBody ty.bits op fl).length with hi1 | hi1
    · obtain ⟨ln, hln⟩ : ∃ ln, (rmwLoopBody ty.bits op fl)[i]? = some ln :=
        ⟨_, List.getElem?_eq_getElem hi1⟩
      obtain ⟨x, t, rfl, -⟩ := rmwBody_ins hty op fl _ (List.mem_of_getElem? hln)
      exact ⟨j0 + 1 + i, x, t, by omega, by omega, hatb i _ hln, hpcsI i (by omega)⟩
    · obtain rfl : i = (rmwLoopBody ty.bits op fl).length := by omega
      exact ⟨_, _, _, by omega, by omega, hLc, hpcsI _ (Nat.le_refl _)⟩
  · refine RL.frFree_of hR fun i hi => ?_
    rcases Nat.lt_or_ge i (rmwLoopBody ty.bits op fl).length with hi1 | hi1
    · obtain ⟨ln, hln⟩ : ∃ ln, (rmwLoopBody ty.bits op fl)[i]? = some ln :=
        ⟨_, List.getElem?_eq_getElem hi1⟩
      obtain ⟨x, t, rfl, -⟩ := rmwBody_ins hty op fl _ (List.mem_of_getElem? hln)
      exact ⟨j0 + 1 + i, x, t, hatb i _ hln, hpcsI i (by omega),
        frLine_rmwLoopBody _ _ _ x t (List.mem_of_getElem? hln)⟩
    · obtain rfl : i = (rmwLoopBody ty.bits op fl).length := by omega
      exact ⟨_, _, _, hLc, hpcsI _ (Nat.le_refl _), rfl⟩

theorem frLine_casLoopLines (bits : Nat) (fl : Clif.MemFlags) (a o : Lbl) :
    ∀ x t, Line.ins x t ∈ casLoopLines bits fl a o → x.frLine = false := by
  intro x t hx
  simp only [casLoopLines, casLoopHead, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, Line.ins.injEq, reduceCtorEq, false_or] at hx
  rcases hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rfl
  · exact frLine_casLoopCmp _
  · rfl
  · rfl
  · rfl

set_option maxHeartbeats 8000000 in
/-- **`realizes_casLoopNA` with the segment's lines** (`RL.FRFree`). -/
theorem realizes_casLoopNAF {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {b k : Nat}
    {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {c' : MConf CV Arm.ArmState}
    {j0 : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j0 ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {ty : CTy}
    {fl : Clif.MemFlags} {ra re rx rd r1 : Reg}
    (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.atomicCasLoop ty fl ra re rx rd r1))
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c')
    (hsemY : ∀ ops, (MInst.atomicCasLoop ty fl ra re rx rd r1).operands = .ok ops →
      ∃ rY, csem Y R.ctx R.X (.atomicCasLoop ty fl ra re rx rd r1)
        (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = some rY) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      R.SegNA Y s j0 ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' n ∧ R.FRFree s n := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  have hok := ctlCheck_inst hck hvb hi
  simp only [ctlInstOk, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hok
  obtain ⟨va, rfl⟩ := isVregInt_iff h0
  obtain ⟨ve, rfl⟩ := isVregInt_iff h1
  obtain ⟨vx, rfl⟩ := isVregInt_iff h2
  obtain ⟨vd, rfl⟩ := isVregInt_iff h3
  obtain ⟨v1, rfl⟩ := isVregInt_iff h4
  cases h with
  | @op b k allocs its m w vb'' i opsm outs outs' w' ctl m2 c' hvb' hi' hopsm hsz' hsem hlen hho hcl hn =>
  rw [hvb] at hvb'; cases hvb'
  rw [hi] at hi'; cases hi'
  -- the loop's control outcome is always `.next`, so its item is not the block's last
  have hk : k + 1 < vb.insts.size := by
    have hctl : ctl = Ctl.next := by
      simp only [RL.sem, csemV, csem] at hsem
      split at hsem
      · split at hsem
        · split at hsem
          · split at hsem
            · simp only [Option.some.injEq, Prod.mk.injEq] at hsem
              exact hsem.2.2.symm
            · exact (loopSem_inv hsem).2.2.2.2
          · cases hsem
        · split at hsem
          · simp only [Option.some.injEq, Prod.mk.injEq] at hsem
            exact hsem.2.2.symm
          · cases hsem
      · cases hsem
    cases hn with
    | next hk => exact hk
    | @goto jj st items' hk1 hsucc hitems => simp at hctl
    | ret hh => simp at hctl
    | halt => simp at hctl
  obtain ⟨hT0, items, pre, regs, i', c1, c2, X', ls1, psm, psm', ps2, x, cc, wh, ops, hc1o, rfl,
    hit, hsplit, hasg, hc1', hops, hstat, hchk', hc2, hl1, hX2, hT2, htr, hdrop, hpc, hst, hx,
    hsc⟩ := qW_op hR hq hvb hi hk
  have hoppseq : opsm = ops := Except.ok.inj (hopsm.symm.trans hops)
  subst hoppseq
  have hops' : opsm = #[⟨va, .int, .use, .early, .fixed (.x 25)⟩, ⟨ve, .int, .use, .early, .fixed (.x 26)⟩,
      ⟨vx, .int, .use, .early, .fixed (.x 28)⟩, ⟨vd, .int, .def, .late, .fixed (.x 27)⟩,
      ⟨v1, .int, .def, .late, .fixed (.x 24)⟩] := by
    have e : (MInst.atomicCasLoop ty fl (.vreg va .int) (.vreg ve .int) (.vreg vx .int)
        (.vreg vd .int) (.vreg v1 .int)).operands =
        .ok #[⟨va, .int, .use, .early, .fixed (.x 25)⟩, ⟨ve, .int, .use, .early, .fixed (.x 26)⟩,
          ⟨vx, .int, .use, .early, .fixed (.x 28)⟩, ⟨vd, .int, .def, .late, .fixed (.x 27)⟩,
          ⟨v1, .int, .def, .late, .fixed (.x 24)⟩] := rfl
    rw [e] at hopsm; injection hopsm with h; exact h.symm
  subst hops'
  obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts hstat
  obtain ⟨q0, q1, q2, q3, q4, rfl⟩ := regs5 (by simpa using hsz.symm)
  obtain rfl : q0 = .x 25 := fixed_reg (o := ⟨va, .int, .use, .early, .fixed (.x 25)⟩) hloc (by simp) rfl
  obtain rfl : q1 = .x 26 := fixed_reg (o := ⟨ve, .int, .use, .early, .fixed (.x 26)⟩) hloc (by simp) rfl
  obtain rfl : q2 = .x 28 := fixed_reg (o := ⟨vx, .int, .use, .early, .fixed (.x 28)⟩) hloc (by simp) rfl
  obtain rfl : q3 = .x 27 := fixed_reg (o := ⟨vd, .int, .def, .late, .fixed (.x 27)⟩) hloc (by simp) rfl
  obtain rfl : q4 = .x 24 := fixed_reg (o := ⟨v1, .int, .def, .late, .fixed (.x 24)⟩) hloc (by simp) rfl
  have hasg' : (MInst.atomicCasLoop ty fl (.vreg va .int) (.vreg ve .int) (.vreg vx .int)
      (.vreg vd .int) (.vreg v1 .int)).assign #[.x 25, .x 26, .x 28, .x 27, .x 24] =
      .ok (.atomicCasLoop ty fl (.x 25) (.x 26) (.x 28) (.x 27) (.x 24)) := rfl
  rw [hasg'] at hasg; cases hasg
  obtain rfl : c1 = [.inst (.atomicCasLoop ty fl (.x 25) (.x 26) (.x 28) (.x 27) (.x 24))] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  have hl1o := hl1
  have hl1' := codeLinesE_single hl1
  simp only [MInst.lines, bne_self_eq_false, Bool.or_false, Bool.false_eq_true,
    ite_false, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1'
  obtain ⟨rfl, rfl⟩ := hl1'
  have hWs := fun (m' : Loc → CV) (w'' : Arm.ArmState) (p : BitVec 64) =>
    (RL.nextW_straight (R := R) (j := j0) (ps1 := ps1) (T := T) (b := b)
      (it := .op k (#[Reg.x 25, .x 26, .x 28, .x 27, .x 24].map Loc.reg)) (its := its) (m := m)
      (m' := m') (w := w) (w' := w'') (p := p)).trans (RL.straightW_eq hvb hc1o hl1o)
  have hreg : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
    hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
  have hU : (((#[(⟨va, .int, .use, .early, .fixed (.x 25)⟩ : Operand),
      ⟨ve, .int, .use, .early, .fixed (.x 26)⟩, ⟨vx, .int, .use, .early, .fixed (.x 28)⟩,
      ⟨vd, .int, .def, .late, .fixed (.x 27)⟩, ⟨v1, .int, .def, .late, .fixed (.x 24)⟩].zip
      (#[Reg.x 25, .x 26, .x 28, .x 27, .x 24].map Loc.reg)).toList.filter (·.1.isUse)).map (m ·.2)) =
      [regVal s (.x 25), regVal s (.x 26), regVal s (.x 28)] := by
    simp [Operand.isUse, hreg (.x 25) rfl, hreg (.x 26) rfl, hreg (.x 28) rfl]
  have hsem0 := hsem
  rw [hU] at hsem
  have herrw : Arm.r .ERR w = .None := by
    rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
  simp only [RL.sem, csemV, csem, herrw, ite_true] at hsem
  obtain ⟨outs1, t1, c1, hhead, hsem⟩ : ∃ outs1 t1 c1,
      loopSem R.F ty (regVal s (.x 25)) (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28]
        [regVal s (.x 25), regVal s (.x 26), regVal s (.x 28)] [.x 27, .x 24] w = some (outs1, t1, c1) ∧
      (if Arm.ConditionHolds Cond.ne.bits t1 = true then some (outs1, t1, Ctl.next)
        else loopSem R.F ty (regVal s (.x 25))
          [.ins (.stlxr ty.bits (.x 24) (.x 28) (.x 25)) fl.trapCode] [] [] [.x 27, .x 24] t1) =
        some (outs, w', ctl) := by
    split at hsem
    · exact ⟨_, _, _, ‹_›, hsem⟩
    · cases hsem
  obtain ⟨hty, hav, hrunh, rfl, rfl⟩ := loopSem_inv hhead
  simp only [List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, setReg_x,
    lo64_regVal_x, rnum] at hrunh hav
  obtain ⟨rY, hY⟩ := hsemY _ hops
  rw [hU] at hY
  simp only [csem, herrw, ite_true] at hY
  obtain ⟨o1Y, t1Y, c1Y, hheadY, -⟩ : ∃ outs1 t1 c1,
      loopSem Y ty (regVal s (.x 25)) (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28]
        [regVal s (.x 25), regVal s (.x 26), regVal s (.x 28)] [.x 27, .x 24] w = some (outs1, t1, c1) ∧
        True := by
    split at hY
    · exact ⟨_, _, _, ‹_›, trivial⟩
    · cases hY
  obtain ⟨-, havY, -, -, -⟩ := loopSem_inv hheadY
  simp only [List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, setReg_x,
    lo64_regVal_x, rnum] at havY
  have hsw0 : SameWorld R.F s (Arm.w (.GPR 28#5) (Arm.r (.GPR 28#5) s) (Arm.w (.GPR 26#5)
      (Arm.r (.GPR 26#5) s) (Arm.w (.GPR 25#5) (Arm.r (.GPR 25#5) s) w))) :=
    SameWorld.w_right (by simp [Masked]) (SameWorld.w_right (by simp [Masked])
      (SameWorld.w_right (by simp [Masked]) hst.world))
  have h25 : Arm.r (.GPR 25#5) s = Arm.r (.GPR 25#5) (Arm.w (.GPR 28#5) (Arm.r (.GPR 28#5) s)
      (Arm.w (.GPR 26#5) (Arm.r (.GPR 26#5) s) (Arm.w (.GPR 25#5) (Arm.r (.GPR 25#5) s) w))) := by simp
  have h26 : Arm.r (.GPR 26#5) s = Arm.r (.GPR 26#5) (Arm.w (.GPR 28#5) (Arm.r (.GPR 28#5) s)
      (Arm.w (.GPR 26#5) (Arm.r (.GPR 26#5) s) (Arm.w (.GPR 25#5) (Arm.r (.GPR 25#5) s) w))) := by simp
  have hav' := hav
  rw [h25] at hav'
  obtain ⟨s1, hrun1, hint1, -, hfr1, hmem1, hprog1, -⟩ :=
    casHead_spec hty fl (R.envOf (j0 + 1)) s hst.err
  obtain ⟨t1', hrunt, -, -, hfrt, -, hprogt, -⟩ := casHead_spec hty fl env0
    (Arm.w (.GPR 28#5) (Arm.r (.GPR 28#5) s) (Arm.w (.GPR 26#5)
      (Arm.r (.GPR 26#5) s) (Arm.w (.GPR 25#5) (Arm.r (.GPR 25#5) s) w))) (by simp [herrw])
  rw [hrunh, Option.some.injEq] at hrunt
  subst hrunt
  obtain ⟨hsw1, h27⟩ := casHead_congr hty fl (R.envOf (j0 + 1)) env0 hsw0 h25 h26 hav' hrun1 hrunh
  have hcond : Arm.ConditionHolds Cond.ne.bits s1 = Arm.ConditionHolds Cond.ne.bits t1 :=
    ConditionHolds_sameWorld hsw1 _
  have hrx : relaxLines R.far (casLoopLines ty.bits fl (.loop ps1.aloop) (.loop (ps1.aloop + 1))) =
      casLoopLines ty.bits fl (.loop ps1.aloop) (.loop (ps1.aloop + 1)) :=
    relaxLines_loop (by
      rcases hty with rfl | rfl | rfl | rfl <;>
        simp (config := {decide := true}) [casLoopLines, casLoopHead, casLoopCmp, Insn.condTarget?,
          CTy.bits])
  have hj7 : j0 + (relaxLines R.far (casLoopLines ty.bits fl (.loop ps1.aloop)
      (.loop (ps1.aloop + 1)))).length = j0 + 7 := by
    rw [hrx]; simp [casLoopLines, casLoopHead]
  have hdrop' : R.L.drop j0 = casLoopLines ty.bits fl (.loop ps1.aloop) (.loop (ps1.aloop + 1)) ++
      (relaxLines R.far (X' ++ x.2.1) ++ R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2)) := by
    rw [hdrop, hrx]
  have hat : ∀ q ln, (casLoopLines ty.bits fl (.loop ps1.aloop) (.loop (ps1.aloop + 1)))[q]? = some ln →
      R.L[j0 + q]? = some ln := by
    intro q ln hq
    have := congrArg (·[q]?) hdrop'
    simp only [List.getElem?_drop] at this
    rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hq).1]; exact hq
  have hL0 : R.L[j0]? = some (.label (.loop ps1.aloop)) := hat 0 _ rfl
  have hL1 : ∃ x t, R.L[j0 + 1]? = some (.ins x t) := ⟨_, _, hat 1 _ rfl⟩
  have hL2 : ∃ x t, R.L[j0 + 2]? = some (.ins x t) := ⟨_, _, hat 2 _ rfl⟩
  have hL3 : R.L[j0 + 3]? = some (.ins (.bcond .ne (.loop (ps1.aloop + 1))) none) := hat 3 _ rfl
  have hL4 : R.L[j0 + 4]? = some (.ins (.stlxr ty.bits (.x 24) (.x 28) (.x 25)) fl.trapCode) :=
    hat 4 _ rfl
  have hL5 : R.L[j0 + 5]? = some (.ins (.cbz true true (.x 24) (.loop ps1.aloop)) none) := hat 5 _ rfl
  have hL6 : R.L[j0 + 6]? = some (.label (.loop (ps1.aloop + 1))) := hat 6 _ rfl
  have hd1 : R.L.drop (j0 + 1) = casLoopHead ty.bits fl ++
      (.ins (.bcond .ne (.loop (ps1.aloop + 1))) none ::
        .ins (.stlxr ty.bits (.x 24) (.x 28) (.x 25)) fl.trapCode ::
        .ins (.cbz true true (.x 24) (.loop ps1.aloop)) none :: .label (.loop (ps1.aloop + 1)) ::
        (relaxLines R.far (X' ++ x.2.1) ++ R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2))) := by
    rw [← List.drop_drop, hdrop']; simp [casLoopLines, casLoopHead]
  have hpc1 : Arm.r .PC s = R.pcOf (j0 + 1) := by rw [hpc, RL.pcOf_succ_label hL0]
  have hatH : ∀ q ln, (casLoopHead ty.bits fl)[q]? = some ln →
      R.fa.lines.toList[j0 + 1 + q]? = some ln := by
    intro q ln hq
    have := congrArg (·[q]?) hd1
    simp only [List.getElem?_drop, RL.L] at this
    rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hq).1]; exact hq
  have hpcsI := iterN_execLines_pc (X := R.X) (H := R.H) hR.layout hR.lm hR.fit _ (j0 + 1) s s1 hatH
    (fun i t h => by obtain ⟨i', t', e, hh⟩ := casHead_ins _ fl _ h; cases e; exact hh)
    hst.prog (by rw [hpc1]; rfl) hst.err hint1 hrun1
  have hpcI1 : Arm.r .PC (iterN R.step 1 s) = R.pcOf (j0 + 2) :=
    (hpcsI 1 (by simp [casLoopHead])).trans (by congr 1)
  obtain ⟨hit1, hpcs1, hgood1, hgx1⟩ := run_insNR (Y := Y) hR hd1 (casHead_ins _ fl) hst.prog hpc1
    hst.err hint1 hrun1
  have hgx01 : ∀ i < 2, R.GoodXNY Y (iterN R.step i s) := fun i hi =>
    hgx1 (casHead_tail _ fl) (RL.good_of_sp hst.sp)
      (casHead_reads _ fl _ s fun q hq => .inr (.inr ⟨hav q hq, havY q hq⟩)) i
      (by simp [casLoopHead]; omega)
  simp only [casLoopHead, List.length_cons, List.length_nil] at hit1 hpcs1 hgood1
  have herr1 : Arm.r .ERR s1 = .None := by
    rw [hfr1 .ERR (by simp) (by simp) (by simp)]; exact hst.err
  have hprog1' : s1.program = R.fb.program R.base := by rw [hprog1]; exact hst.prog
  obtain ⟨a, jl, ha, hjl, hstep⟩ := step_branch hR hL3 (.inr (.inl ⟨.ne, rfl⟩)) (by simp) hprog1'
    (by rw [hpcs1]) herr1
  rw [brCond_bcond ha] at hstep
  have hpc7 : R.pcOf (j0 + 7) = R.pcOf (j0 + 6) := RL.pcOf_succ_label hL6
  have hjl' : R.pcOf jl = R.pcOf (j0 + 7) := by
    have e1 := labelOffsets_label hR.lm (show R.fa.lines.toList[jl]? = _ from hjl)
    have e2 := labelOffsets_label hR.lm (show R.fa.lines.toList[j0 + 6]? = _ from hL6)
    rw [e1, Option.some.injEq] at e2
    rw [hpc7]; simp only [RL.pcOf, RL.L]; rw [e2]
  obtain ⟨xb, tb, hb⟩ := hL1
  have hfrC : ∀ jj x t, j0 ≤ jj → jj < j0 + 7 → R.L[jj]? = some (.ins x t) → x.frLine = false :=
    fun jj x t h1 h2 hj => frLine_casLoopLines _ _ _ _ x t (RL.mem_of_drop hdrop' hj h1
      (by simp [casLoopLines, casLoopHead]; omega))
  have fin : ∀ (sF : Arm.ArmState) (nst : Nat), iterN R.step nst s = sF →
      Arm.r .PC sF = R.pcOf (j0 + 7) → SameWorld R.F sF w' →
      [regVal sF (.x 27)] = outs.take 1 → outs.length = 2 →
      (∀ f, f ≠ .PC → (∀ n ∈ [27, 24], f ≠ .GPR (rnum n)) → (∀ g, f ≠ .FLAG g) →
        Arm.r f sF = Arm.r f s) →
      (∀ a, R.F a → sF.mem a = s.mem a) → sF.program = s.program → ctl = .next →
      (∀ i < nst, R.GoodXNY Y (iterN R.step i s)) → R.Inside s nst (j0 + 1) (j0 + 7) → 0 < nst →
      ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k
          (#[Reg.x 25, .x 26, .x 28, .x 27, .x 24].map Loc.reg) :: its, m, w⟩) c'' ∧
        R.SegNA Y s j0 ps1 T (.run ⟨b, .op k
          (#[Reg.x 25, .x 26, .x 28, .x 27, .x 24].map Loc.reg) :: its, m, w⟩) c'' n ∧
        R.FRFree s n := by
    intro sF nst hitF hpcF hswF h27F hlen2 hfrF hmemF hprogF hctl hgoodF hinF hposF
    subst hctl
    refine ⟨nst, _, MStep.op (outs' := [regVal sF (.x 27), regVal sF (.x 24)]) (m2 := m) hvb hi hops
      hsz' hsem0 hlen ⟨by simp [hlen2], fun h => by simp [havocFrom, MInst.keptDefs] at h, fun n h => ?_⟩ ?_
      (MNext.next hk), ⟨?_, hgoodF, ?_⟩, ?_⟩
    · simp only [havocFrom, MInst.keptDefs, Option.some.injEq] at h
      subst h
      simpa using h27F
    · refine ⟨fun l _ => ?_, fun c hc => by simp [MInst.clobbers] at hc⟩
      simp [writeM, Operand.isDef, Operand.isEarly]
    · unfold RL.QWn
      rw [hWs, hitF, hj7]
      refine .inl ⟨hT0, vb, items, pre ++ [.op k (#[Reg.x 25, .x 26, .x 28, .x 27, .x 24].map Loc.reg)],
        c2, X', psm', ps2, x, hvb, hit, by rw [hsplit]; simp, hchk', hc2, hX2, hT2, htr, ?_, hpcF, ?_,
        hx, hsc⟩
      · rw [← List.drop_drop, hdrop']
        exact List.drop_left' (by simp [casLoopLines, casLoopHead])
      · refine stRel_after hR hst ?_ ?_ hswF ?_ hprogF
          ⟨?_, fun a ha => hmemF a (RL.FK_F ha), ?_⟩
        · refine store_regs hst [27, 24] (by simp) ?_ ?_ hfrF
          · intro n hn
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
            rcases hn with rfl | rfl <;> simp [writeM, upd, Operand.isDef, Operand.isLate]
          · intro r hr
            simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
            simp [writeM, upd, Operand.isDef, Operand.isLate, hr.1, hr.2]
        · intro l hl
          simp [writeM, upd, Operand.isDef, Operand.isLate, hl]
        · rw [hfrF .ERR (by simp) (by simp) (by simp)]; exact hst.err
        · simp only [spOf]; exact hfrF _ (by simp) (by simp [rnum]) (by simp)
        · exact hfrF _ (by simp) (by simp [rnum]) (by simp)
    · exact RL.segLen_straight_base hR (by simp [RL.Straight]) (fun _ => by rw [hWs, hj7]) hb hinF
        (by rw [hitF]; exact hpcF) hposF (by omega)
    · refine RL.frFree_of hR fun i hi => ?_
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact ⟨j0 + 1, xb, tb, hb, hpc1, hfrC _ _ _ (by omega) (by omega) hb⟩
      · obtain ⟨jj, x, t, h1, h2, h3, h4⟩ := hinF i hi0 hi
        exact ⟨jj, x, t, h3, h4, hfrC _ _ _ (by omega) h2 h3⟩
  have hfr1' : ∀ f, f ≠ .PC → (∀ n ∈ [27, 24], f ≠ .GPR (rnum n)) → (∀ g, f ≠ .FLAG g) →
      Arm.r f s1 = Arm.r f s := by
    intro f h1 h2 h3
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, rnum] at h2
    exact hfr1 f h1 (by simp [h2.1]) h3
  have hpc3 : Arm.r .PC s1 = R.pcOf (j0 + 3) := by rw [hpcs1]
  have hgx2 : R.NextOk s1 (R.step s1) → R.GoodXNY Y (iterN R.step 2 s) := fun hnx => by
    rw [hit1]
    exact RL.goodXNR_ofIns hR hL3 hpc3 rfl rfl (by rw [← hit1]; exact hgood1 2 (by omega) (by omega))
      herr1 hprog1' hnx (RL.readsIn_noLoad hR hL3 hpc3 rfl)
  obtain ⟨x2, t2, hL2'⟩ := hL2
  have hin12 : ∀ i, 0 < i → i < 3 → ∃ jj x t, j0 + 1 < jj ∧ jj < j0 + 7 ∧
      R.L[jj]? = some (.ins x t) ∧ Arm.r .PC (iterN R.step i s) = R.pcOf jj := by
    intro i h0 hi
    rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl
    · exact ⟨j0 + 2, _, _, by omega, by omega, hL2', hpcI1⟩
    · exact ⟨j0 + 3, _, _, by omega, by omega, hL3, by rw [hit1]; exact hpc3⟩
  by_cases hc : Arm.ConditionHolds Cond.ne.bits t1 = true
  · rw [if_pos hc] at hsem
    simp only [Option.some.injEq, Prod.mk.injEq] at hsem
    obtain ⟨rfl, rfl, rfl⟩ := hsem
    rw [hcond, if_pos hc, hjl'] at hstep
    refine fin (Arm.w .PC (R.pcOf (j0 + 7)) s1) 3 ?_ (by simp) (SameWorld.w_left (by simp [Masked]) hsw1)
      ?_ (by simp) ?_ ?_ (by simp [Arm.w_program, hprog1]) rfl (fun i hi => ?_) hin12 (by omega)
    rotate_right
    · rcases (by omega : i < 2 ∨ i = 2) with hi2 | rfl
      · exact hgx01 i hi2
      · exact hgx2 (by rw [hstep]; exact RL.nextOk_label hL6 (by rw [Arm.r_of_w_same, hpc7]))
    · rw [show 3 = 2 + 1 from rfl, iterN_add, hit1]; simp [iterN, hstep]
    · simp [regVal, rnum, h27]
    · intro f h1 h2 h3; rw [Arm.r_of_w_different h1]; exact hfr1' f h1 h2 h3
    · intro a _; simp [Arm.ArmState.mem_w_eq_mem, hmem1]
  · rw [if_neg hc] at hsem
    obtain ⟨-, -, hrun2, rfl, rfl⟩ := loopSem_inv hsem
    simp only [List.zip_nil_left, List.foldl_nil] at hrun2
    rw [hcond, if_neg hc] at hstep
    have herrt : Arm.r .ERR t1 = .None := by
      rw [hfrt .ERR (by simp) (by simp) (by simp)]; simp [herrw]
    obtain ⟨w2, hrunw2, -, hfrw2, -, -⟩ := stlxr_spec hty fl env0 t1 herrt
    rw [hrun2, Option.some.injEq] at hrunw2
    subst hrunw2
    have herr2 : Arm.r .ERR (Arm.w .PC (R.pcOf (j0 + 3 + 1)) s1) = .None := by simp [herr1]
    obtain ⟨s3, hrun3, h24, hfr3, hmem3, hprog3⟩ := stlxr_spec hty fl (R.envOf (j0 + 4))
      (Arm.w .PC (R.pcOf (j0 + 3 + 1)) s1) herr2
    have hd4 : R.L.drop (j0 + 4) = [.ins (.stlxr ty.bits (.x 24) (.x 28) (.x 25)) fl.trapCode] ++
        (.ins (.cbz true true (.x 24) (.loop ps1.aloop)) none :: .label (.loop (ps1.aloop + 1)) ::
          (relaxLines R.far (X' ++ x.2.1) ++ R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2))) := by
      rw [← List.drop_drop, hdrop']; simp [casLoopLines, casLoopHead]
    obtain ⟨hit3, hpcs3, -, hgx3⟩ := run_insNR (Y := Y) hR hd4 (by simp [Insn.hooked])
      (by simp [Arm.w_program, hprog1']) (by simp) herr2
      (fun q h0 h1 => by simp at h1; omega) hrun3
    simp only [List.length_cons, List.length_nil, Nat.zero_add, iterN] at hit3
    have herr3 : Arm.r .ERR s3 = .None := by
      rw [hfr3 .ERR (by simp) (by simp)]; exact herr2
    have hprog3' : s3.program = R.fb.program R.base := by
      rw [hprog3]; simp [Arm.w_program, hprog1']
    obtain ⟨a5, jl5, ha5, -, hstep5⟩ := step_branch hR hL5 (.inr (.inr (.inl ⟨true, true, .x 24, rfl⟩))) (by simp)
      hprog3' hpcs3 herr3
    have hbr : brCond a5 s3 = false := by
      rw [brCond_cbz (by decide) ha5]; simp [rnum, h24]
    rw [hbr] at hstep5
    simp only [Bool.false_eq_true, ite_false] at hstep5
    have h25s : Arm.r (.GPR 25#5) (Arm.w .PC (R.pcOf (j0 + 3 + 1)) s1) = Arm.r (.GPR 25#5) s := by
      rw [Arm.r_of_w_different (by simp)]; exact hfr1 _ (by simp) (by simp) (by simp)
    have hsw3 := stlxr_congr hty fl (R.envOf (j0 + 4)) env0
      (SameWorld.w_left (by simp [Masked]) hsw1)
      (by rw [h25s, hfrt _ (by simp) (by simp) (by simp)]; simp)
      (by rw [Arm.r_of_w_different (by simp), hfr1 _ (by simp) (by simp) (by simp),
        hfrt _ (by simp) (by simp) (by simp)]; simp) hrun3 hrun2
    have hi3 : iterN R.step 3 s = Arm.w .PC (R.pcOf (j0 + 3 + 1)) s1 := by
      rw [show 3 = 2 + 1 from rfl, iterN_add, hit1]
      simp only [iterN]
      rw [hstep]
    have hi4 : iterN R.step 4 s = s3 := by
      rw [show 4 = 2 + 1 + 1 from rfl, iterN_add, iterN_add, hit1]
      simp only [iterN]
      rw [hstep, hit3]
    refine fin (Arm.w .PC (R.pcOf (j0 + 7)) s3) 5 ?_ (by simp)
      (SameWorld.w_left (by simp [Masked]) hsw3) ?_ (by simp) ?_ ?_ ?_ rfl ?_ ?_ (by omega)
    · rw [show 5 = 4 + 1 from rfl, iterN_add, hi4]
      simp only [iterN]
      rw [hstep5, hpc7]
    · simp only [List.map_cons, List.map_nil, List.take_succ_cons, List.take_zero, regVal, rnum,
        List.cons.injEq, and_true]
      rw [Arm.r_of_w_different (by simp), hfr3 _ (by simp) (by simp), Arm.r_of_w_different (by simp),
        h27, hfrw2 _ (by simp) (by simp)]
      simp
    · intro f h1 h2 h3
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, rnum] at h2
      rw [Arm.r_of_w_different h1, hfr3 f h1 h2.2, Arm.r_of_w_different h1]
      exact hfr1 f h1 (by simp [h2.1]) h3
    · intro a ha
      simp only [Arm.ArmState.mem_w_eq_mem, hmem3]
      rw [mem_write_mem_bytes_ne _ _ _ _ _ (fun q hq e => hav q hq (by rw [← h25s, ← e]; exact ha))]
      simp [Arm.ArmState.mem_w_eq_mem, hmem1]
    · simp [Arm.w_program, hprog3, hprog1]
    · intro i hi
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · exact hgx01 0 (by omega)
      · exact hgx01 1 (by omega)
      · exact hgx2 (by rw [hstep]; exact RL.nextOk_succ hL3 rfl (Arm.r_of_w_same ..))
      · rw [hi3]
        exact hgx3 (fun i t h => by
            simp only [List.mem_singleton, Line.ins.injEq] at h
            obtain ⟨rfl, -⟩ := h; rfl)
          (R.good_succ hR hL3 (fun _ h => Insn.noConfusion h) (fun _ h => Insn.noConfusion h)
            (Arm.r_of_w_same ..)) (linesReads_noLoads fun y t h => by
              simp only [List.mem_singleton, Line.ins.injEq] at h
              obtain ⟨rfl, -⟩ := h; rfl) 0 (by simp)
      · rw [hi4]
        exact RL.goodXNR_ofIns hR hL5 hpcs3 rfl rfl
          (R.good_succ hR hL4 (fun _ h => Insn.noConfusion h) (fun _ h => Insn.noConfusion h) hpcs3)
          herr3 hprog3' (by rw [hstep5]; exact RL.nextOk_succ hL5 rfl (Arm.r_of_w_same ..))
          (RL.readsIn_noLoad hR hL5 hpcs3 rfl)
    · intro i h0 hi
      rcases (by omega : i < 3 ∨ i = 3 ∨ i = 4) with hi2 | rfl | rfl
      · exact hin12 i h0 hi2
      · exact ⟨j0 + 4, _, _, by omega, by omega, hL4, by rw [hi3, Arm.r_of_w_same]⟩
      · exact ⟨j0 + 5, _, _, by omega, by omega, hL5, by rw [hi4]; exact hpcs3⟩

/-- **An `atomic_rmw` loop on the machine, at a witness** (`realizes_rmwLoopNY`). -/
theorem realizes_rmwLoopNA {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {b k : Nat}
    {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {c' : MConf CV Arm.ArmState}
    {j0 : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j0 ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {ty : CTy}
    {op : AtomicRmwLoopOp} {fl : Clif.MemFlags} {ra ro rd r1 r2 : Reg}
    (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.atomicRmwLoop ty op fl ra ro rd r1 r2))
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c')
    (hsemY : ∀ ops, (MInst.atomicRmwLoop ty op fl ra ro rd r1 r2).operands = .ok ops →
      ∃ rY, csem Y R.ctx R.X (.atomicRmwLoop ty op fl ra ro rd r1 r2)
        (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = some rY) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      R.SegNA Y s j0 ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' n :=
  let ⟨n, c'', h1, h2, _⟩ := realizes_rmwLoopNAF hR hq hvb hi h hsemY
  ⟨n, c'', h1, h2⟩

/-- **An `atomic_cas` loop on the machine, at a witness** (`realizes_casLoopNY`). -/
theorem realizes_casLoopNA {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} {s : Arm.ArmState} {b k : Nat}
    {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {c' : MConf CV Arm.ArmState}
    {j0 : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j0 ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {ty : CTy}
    {fl : Clif.MemFlags} {ra re rx rd r1 : Reg}
    (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.atomicCasLoop ty fl ra re rx rd r1))
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c')
    (hsemY : ∀ ops, (MInst.atomicCasLoop ty fl ra re rx rd r1).operands = .ok ops →
      ∃ rY, csem Y R.ctx R.X (.atomicCasLoop ty fl ra re rx rd r1)
        (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = some rY) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      R.SegNA Y s j0 ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' n :=
  let ⟨n, c'', h1, h2, _⟩ := realizes_casLoopNAF hR hq hvb hi h hsemY
  ⟨n, c'', h1, h2⟩

end Backend.Proof
