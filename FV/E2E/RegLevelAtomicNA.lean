import FV.E2E.RegLevelCallNA
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
    (hS : RL.Straight c c'') (hW : (R.nextW j ps1 T c c'').1 = jt)
    (hb : R.L[jb]? = some (.ins xb tb)) (hin : R.Inside s n jb jt)
    (hpn : Arm.r .PC (iterN R.step n s) = R.pcOf jt) (hpos : 0 < n) (hne : jt ≠ j) :
    R.SegLen j ps1 T c c'' s n := by
  refine ⟨by rw [hW]; exact RL.firstArr_of_inside hR hb hin (Nat.le_refl _) hpn, ?_⟩
  unfold RL.EmptyW
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

set_option maxHeartbeats 4000000 in
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
      R.SegNA Y s j0 ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' n := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  have hok := ctlCheck_inst hck hvb hi
  simp only [ctlInstOk, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hok
  obtain ⟨va, rfl⟩ := isVregInt_iff h0
  obtain ⟨vo, rfl⟩ := isVregInt_iff h1
  obtain ⟨vd, rfl⟩ := isVregInt_iff h2
  obtain ⟨v1, rfl⟩ := isVregInt_iff h3
  obtain ⟨v2, rfl⟩ := isVregInt_iff h4
  obtain ⟨items, pre, regs, i', c1, c2, ls1, ls2, psm, ps2, cc, wh, ops, hc1o, rfl, hit, hsplit,
    hasg, hc1', hops, hstat, hchk', hc2, hl1, hl2, htr, hdrop, hpc, hst⟩ := qW_op hq hvb hi
  have hops' : ops = #[⟨va, .int, .use, .early, .fixed (.x 25)⟩, ⟨vo, .int, .use, .early, .fixed (.x 26)⟩,
      ⟨vd, .int, .def, .late, .fixed (.x 27)⟩, ⟨v1, .int, .def, .late, .fixed (.x 24)⟩,
      ⟨v2, .int, .def, .late, .fixed (.x 28)⟩] := by
    have e : (MInst.atomicRmwLoop ty op fl (.vreg va .int) (.vreg vo .int) (.vreg vd .int)
        (.vreg v1 .int) (.vreg v2 .int)).operands =
        .ok #[⟨va, .int, .use, .early, .fixed (.x 25)⟩, ⟨vo, .int, .use, .early, .fixed (.x 26)⟩,
          ⟨vd, .int, .def, .late, .fixed (.x 27)⟩, ⟨v1, .int, .def, .late, .fixed (.x 24)⟩,
          ⟨v2, .int, .def, .late, .fixed (.x 28)⟩] := rfl
    rw [e] at hops; injection hops with h; exact h.symm
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
  cases h with
  | @op b k allocs its m w vb'' i ops outs outs' w' ctl m2 c' hvb' hi' hops' hsz' hsem hlen hho hcl hn =>
  rw [hvb] at hvb'; cases hvb'
  rw [hi] at hi'; cases hi'
  rw [hops] at hops'; cases hops'
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
  have hdrop' := ftList_rmw hR hty ⟨_, rfl⟩ hdrop
  have hL0 : R.L[j0]? = some (.label (.loop ps1.aloop)) := by
    have := congrArg (·[0]?) hdrop'
    simpa [List.getElem?_drop, rmwLoopLines] using this
  have hd1 : R.L.drop (j0 + 1) = rmwLoopBody ty.bits op fl ++
      (.ins (.cbz true true (.x 24) (.loop ps1.aloop)) none :: (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T)) := by
    rw [← List.drop_drop, hdrop']; simp [rmwLoopLines]
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
  have hk : k + 1 < vb.insts.size := by
    cases hn with
    | next hk => exact hk
  have hfr2 : ∀ f, f ≠ .PC → (∀ n ∈ [27, 24, 28], f ≠ .GPR (rnum n)) → (∀ g, f ≠ .FLAG g) →
      Arm.r f (Arm.w .PC (R.pcOf (j0 + 1 + (rmwLoopBody ty.bits op fl).length + 1)) s1) =
        Arm.r f s := by
    intro f h1 h2 h3
    rw [Arm.r_of_w_different h1]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, rnum] at h2
    exact hfr1 f h1 (by simp [h2.1, h2.2.1, h2.2.2]) h3
  have hlenL : (rmwLoopLines ty.bits op fl (.loop ps1.aloop)).length =
      (rmwLoopBody ty.bits op fl).length + 2 := by simp [rmwLoopLines]
  have hWs : ∀ (m' : Loc → CV) (w'' : Arm.ArmState),
      R.nextW j0 ps1 T (.run ⟨b, .op k (#[Reg.x 25, .x 26, .x 27, .x 24, .x 28].map Loc.reg) :: its, m, w⟩)
        (.run ⟨b, its, m', w''⟩) = (j0 + (rmwLoopBody ty.bits op fl).length + 2,
          { ps1 with aloop := ps1.aloop + 1 }, T) := by
    intro m' w''
    rw [RL.nextW_straight, RL.straightW_eq hvb hc1o hl1o, relaxLines_rmwLoopLines hty, hlenL]
    rfl
  refine ⟨(rmwLoopBody ty.bits op fl).length + 1, _,
    MStep.op (outs' := [regVal (Arm.w .PC (R.pcOf (j0 + 1 + (rmwLoopBody ty.bits op fl).length + 1)) s1) (.x 27),
      regVal (Arm.w .PC (R.pcOf (j0 + 1 + (rmwLoopBody ty.bits op fl).length + 1)) s1) (.x 24),
      regVal (Arm.w .PC (R.pcOf (j0 + 1 + (rmwLoopBody ty.bits op fl).length + 1)) s1) (.x 28)])
      (m2 := m) hvb hi hops hsz' hsem0 hlen ⟨by simp, fun h => by simp [havocFrom, MInst.keptDefs] at h,
        fun n h => ?_⟩ ?_ (MNext.next hk), ?_, fun i hi => ?_, ?_⟩
  · simp only [havocFrom, MInst.keptDefs, Option.some.injEq] at h
    subst h
    simp [regVal, rnum, h27]
  · refine ⟨fun l _ => ?_, fun c hc => by simp [MInst.clobbers] at hc⟩
    simp [writeM, Operand.isDef, Operand.isEarly]
  · rw [hWs, hiter]
    refine ⟨vb, items, pre ++ [.op k (#[Reg.x 25, .x 26, .x 27, .x 24, .x 28].map Loc.reg)], c2, ls2,
      ps2, hvb, hit, by rw [hsplit]; simp, hchk', hc2, hl2, htr, ?_, ?_, ?_⟩
    · rw [show j0 + (rmwLoopBody ty.bits op fl).length + 2 =
        j0 + (rmwLoopLines ty.bits op fl (.loop ps1.aloop)).length by rw [hlenL]; omega,
        ← List.drop_drop, hdrop', List.drop_left]
    · simp only [Arm.r_of_w_same]
      congr 1
      omega
    · refine stRel_after hR hst ?_ ?_ (SameWorld.w_left (by simp [Masked]) hsw1) ?_ ?_ ⟨?_, fun a ha => ?_⟩
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
    refine RL.segLen_straight_base hR (by simp [RL.Straight]) (by rw [hWs])
      hb (fun i h0 hi => ?_) (by rw [hiter, Arm.r_of_w_same]; congr 1; omega) (by omega) (by omega)
    rcases Nat.lt_or_ge i (rmwLoopBody ty.bits op fl).length with hi1 | hi1
    · obtain ⟨ln, hln⟩ : ∃ ln, (rmwLoopBody ty.bits op fl)[i]? = some ln :=
        ⟨_, List.getElem?_eq_getElem hi1⟩
      obtain ⟨x, t, rfl, -⟩ := rmwBody_ins hty op fl _ (List.mem_of_getElem? hln)
      exact ⟨j0 + 1 + i, x, t, by omega, by omega, hatb i _ hln, hpcsI i (by omega)⟩
    · obtain rfl : i = (rmwLoopBody ty.bits op fl).length := by omega
      exact ⟨_, _, _, by omega, by omega, hLc, hpcsI _ (Nat.le_refl _)⟩

end Backend.Proof
