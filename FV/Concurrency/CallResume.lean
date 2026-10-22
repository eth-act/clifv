import FV.Concurrency.CallSeg
import FV.Concurrency.ThreadProgress

/-!
# Resuming the caller after a compiled callee returns (T2j follow-up, #473, calls)

The pieces that follow a compiled activation's precise Arm run through its whole straight-line
code, with the pc of every state (a linked machine dispatching on where a step goes needs it),
up to its return:

* `linesAt_pc`, `moves_privP`: through straight-line lines and through moves (`moves_privA`), the
  pc of every state is at a line (`R.pcOf`);
* `srcStep_of_mstep_eq`: a step of the allocated code at a related configuration is a thread step
  to the same configuration;
* `oneEv_op1`: **one step at a straight-line form with one Arm instruction** (`OneEvForm`, as
  `oneEv_op`): the Arm's step and the source step reading its bytes, related states after both;
* `rets_privP`: **the return** from a `rets` item: the epilogue and the `ret`, each step's events
  private (the `ldp` reads the fp/lr slot), at a line; the return address reached with `sp` as at
  entry, the memory and program kept;
* `cstep_ret_pushC`: the CLIF return of the bottom frame below suspended callers resumes the first
  of them.
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot VCodeThread Backend Backend.Proof AllocThread ThreadRefine
open Code VCodeEvents VCodeAddr

/-- **One step at a straight-line form with one Arm instruction** (`oneEv_op`'s first step): on a
nonempty precise run from related states, the first label's events are the source step's
(reading its bytes), and the states after both are related. -/
theorem oneEv_op1 {R : RL} (hR : R.Wf) {s : ArmState} {mon : Mon} {b k : Nat} {allocs : Array Loc}
    {its' : List RItem} {m : Loc → CV} {w : ArmState} {evs0 : List Ev} {c0 : MConf CV ArmState}
    (hq : Q R s (OpC b k allocs its' m w)) (hA : AInv R (OpC b k allocs its' m w))
    (hs0 : SrcStep R (OpC b k allocs its' m w) evs0 c0)
    (hform : ∀ vb i, R.vc.blocks[b]? = some vb → vb.insts[k]? = some i → OneEvForm R.F R.ctx i)
    {l : Lab} {ls'' : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm R.step (fun _ _ => True) (s, mon) (l :: ls'') t') :
    ∃ c' t1 φ, SrcStep R (OpC b k allocs its' m w) l.evs c' ∧
      PRun Policy.arm R.step (fun _ _ => True) (s, mon) [l] t1 ∧ t1.1 = R.step (patch l.evs s) ∧
      RelQ R t1 c' ∧ Img (PrivA R) l.evs (evTr [l]) φ := by
  cases hs0 with
  | @op _ _ _ _ _ _ vb i ops _ _ hvb hi hops hevs hfoot hst =>
  have hf := hform vb i hvb hi
  obtain ⟨regs, hal, hsz, hall, huses⟩ := q_regs hq hvb hi hops
  have hstr := q_stRel hq
  have herrw : Arm.r .ERR w = .None := by
    rw [← hstr.world.1 .ERR (by simp [Masked]), hstr.err]
  have halw : CheckSPAlignment w :=
    align_of_sp (show Arm.r (.GPR 31#5) w = Arm.r (.GPR 31#5) s from
      (hstr.world.1 (.GPR 31#5) (by simp [Masked])).symm) hstr.align
  have hnc : ∀ info, i ≠ .call info := by rintro info rfl; exact absurd hf.ctl (by simp [MInst.isCtl])
  have hnt : ∀ info ti, i ≠ .tryCall info ti := by rintro info ti rfl; exact absurd hf.ctl (by simp [MInst.isCtl])
  have hwf : csemWF R.ctx i (itemUses ops allocs m) = true := by
    rw [huses]; simp [csemWF, hf.form, hops, useVals_length ops regs hsz]
  have hsemM : ∀ M, R.sem i (itemUses ops allocs m) (setMem M w) =
      straightSem R.F R.ctx i (itemUses ops allocs m) (setMem M w) := fun M => by
    rw [R.sem_eq hnc hnt, csem_of_wf hf.ctl hwf (by rw [r_setMem]; exact herrw)
      (by rw [spAlign_setMem]; exact halw)]
  obtain ⟨ops', ic, x', t', a', hops', hic, hlc, hac, hci⟩ := hf.canon
  rw [hops] at hops'
  cases hops'
  have hss := fun M => straightSem_one (F := R.F) (uses := itemUses ops allocs m) (w := w) hops hic
    hlc hac hci M
  obtain ⟨hOS, hL⟩ := formOk_sound (F := R.F) (X := R.X) hf.form
  cases hst with
  | @op _ _ _ _ _ _ vb1 i1 ops1 outs outs' w' ctl m2 c' hvb1 hi1 hops1 hsz1 hsem hlen hho hcl hn =>
  rw [hvb] at hvb1; cases hvb1; rw [hi] at hi1; cases hi1; rw [hops] at hops1; cases hops1
  obtain rfl := csem_ctl hf.ctl (R.sem_csem hsem)
  cases hn with
  | next hk =>
  have hsem' := hsem
  rw [show patch evs0 w = setMem (applyR evs0 w.mem) w from rfl, hsemM, hss] at hsem'
  split at hsem'
  case isFalse => cases hsem'
  rename_i hC
  simp only [Option.some.injEq, Prod.mk.injEq] at hsem'
  obtain ⟨rfl, -, -⟩ := hsem'
  -- the Arm instruction at `s`
  have hav0 : ∀ e ∈ evs0, Avoids R.F e.n e.addr := by
    rw [hevs]
    exact cEvs_avoid (by rw [patch, r_setMem]; exact herrw)
      (fun _ => ⟨hwf, by rw [patch, spAlign_setMem]; exact halw⟩) (R.sem_csem hsem)
  obtain ⟨j, regs', i', ls1, T, s', c'', hal', hasg, hl1, hins, hdrop, hpc, -, -, -, -, -⟩ :=
    realizes_op_lines hR (q_patch hR hq hav0) hvb hi hops hsz1 hsem hlen hk hOS hL
      (csem_next_world' (R.sem_csem hsem) hnc (by rw [patch, r_setMem]; exact herrw))
  obtain rfl : regs' = regs := regs_inj (hal'.symm.trans hal)
  obtain ⟨x, t, hxl⟩ := hf.line ops regs' i' hops hsz hasg
  obtain rfl := lines_one_eq hl1 hxl
  have hj : R.fa.lines.toList[j]? = some (.ins x t) := by simpa using lines_at hdrop 0 _ rfl
  have hhk : x.hooked = false := by
    obtain ⟨x0, t0, e, hh⟩ := hins _ List.mem_cons_self; cases e; exact hh
  obtain ⟨a, ha, -, hev, hdec⟩ := stepEvs_line (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj hhk
    hstr.prog (by have := hpc; rw [patch, r_setMem] at this; exact this) hstr.err
  obtain ⟨hnostx, hevk⟩ := hf.arm ops regs' i' x t _ a hops hsz hasg (hxl {}) ha
  -- the Arm run
  cases hr with
  | @cons _ t1 _ _ _ hs hp _ hr' =>
  have hxf : l.xfail = false := by
    cases hs with
    | exec => rfl
    | xfail hc => rw [cls_of_decode hdec] at hc; exact absurd hc (hnostx _ _ _)
  obtain ⟨M, hM⟩ : ∃ M, l.evs = stepEvs (setMem M s) := by
    rcases hp with h | h
    · rw [hxf] at h; cases h
    · exact h
  have hl : l.evs = instEvs a (setMem M s) := by
    rw [hM, ArmPrecise.stepEvs_setMem, hev, ArmPrecise.instEvs_setMem]
  have hevq : ∀ M', instEvs a (setMem M' s) = cEvs R.F R.ctx i (itemUses ops allocs m) (setMem M' w) :=
    fun M' => by rw [huses]; exact hf.ev s w ops regs' i' x t _ a hstr.world hops hsz hall hasg (hxl {}) ha M'
  have hfix : l.evs = cEvs R.F R.ctx i (itemUses ops allocs m) (patch l.evs w) := by
    show l.evs = cEvs R.F R.ctx i (itemUses ops allocs m) (setMem (applyR l.evs w.mem) w)
    rw [← hevq, ArmPrecise.instEvs_setMem, hl, ArmPrecise.instEvs_setMem,
      reread_applyR_reread (len_instEvs a s) (ArmPrecise.n_instEvs a s)]
  -- the source step reading the Arm's bytes
  have hsem1 : R.sem i (itemUses ops allocs m) (patch l.evs w) =
      some (defVals ops (canonRegs ops) (exec_inst a' (setMem (applyR l.evs w.mem)
        (placeUses ops (canonRegs ops) (itemUses ops allocs m) w))),
        exec_inst a' (setMem (applyR l.evs w.mem) (placeUses ops (canonRegs ops) (itemUses ops allocs m) w)),
        .next) := by
    show R.sem i _ (setMem _ w) = _
    rw [hsemM, hss, ite_eq_left hC]
  have hlen1 : (defVals ops (canonRegs ops) (exec_inst a' (setMem (applyR l.evs w.mem)
      (placeUses ops (canonRegs ops) (itemUses ops allocs m) w)))).length =
      ((ops.zip allocs).toList.filter (·.1.isDef)).length := by
    rw [defVals_length _ _ _ (exec_inst a' (setMem (applyR evs0 w.mem)
      (placeUses ops (canonRegs ops) (itemUses ops allocs m) w)))]
    exact hlen
  have hav1 : ∀ e ∈ l.evs, Avoids R.F e.n e.addr := by
    rw [hfix]
    exact cEvs_avoid (by rw [patch, r_setMem]; exact herrw)
      (fun _ => ⟨hwf, by rw [patch, spAlign_setMem]; exact halw⟩) (R.sem_csem hsem1)
  have hq1 := q_patch hR hq hav1
  obtain ⟨j2, regs2, i2, ls2, T2, s2, c2, hal2, hasg2, hl2, hins2, hdrop2, hpc2, hrun2, hint2,
    ⟨m2', w2, rfl⟩, hm2, hq2⟩ := realizes_op_lines hR hq1 hvb hi hops hsz1 hsem1 hlen1 hk hOS hL
      (csem_next_world' (R.sem_csem hsem1) hnc (by rw [patch, r_setMem]; exact herrw))
  obtain rfl : regs2 = regs' := regs_inj (hal2.symm.trans hal)
  obtain ⟨x2, t2, hxl2⟩ := hf.line ops regs2 i2 hops hsz hasg2
  obtain rfl := lines_one_eq hl2 hxl2
  have hstr1 := q_stRel hq1
  have hhook2 : ∀ x t, Line.ins x t ∈ [Line.ins x2 t2] → x.hooked = false := fun x t h => by
    obtain ⟨x', t', e, hh⟩ := hins2 _ h; cases e; exact hh
  have hit : iterN R.step 1 (patch l.evs s) = s2 :=
    iterN_execLines hR.layout hR.lm hR.fit _ j2 _ s2 (lines_at hdrop2) hhook2 hstr1.prog hpc2
      hstr1.err hint2 hrun2
  obtain ⟨s1, mon1⟩ := t1
  have ht1 : s1 = R.step (patch l.evs s) := by
    cases hs with
    | exec => rfl
    | xfail => cases hxf
  subst ht1
  -- the item's image
  have hfoot1 : IFoot R.sem i (itemUses ops allocs m) (patch l.evs w) l.evs := by
    have hfo := straightSem_foot (F := R.F) (ctx := R.ctx) (i := i) (uses := itemUses ops allocs m)
      (w := patch l.evs w)
    have hce : cEvs R.F R.ctx i (itemUses ops allocs m) (patch l.evs w) =
        straightEvs R.ctx i (itemUses ops allocs m) (patch l.evs w) := by
      unfold cEvs; simp only [hf.ctl, Bool.false_eq_true, ite_false]
    rw [← hce, ← hfix] at hfo
    refine ⟨hfo.1, fun m' hm' => ?_⟩
    rw [show setMem m' (patch l.evs w) = setMem m' w from rfl, hsemM, show patch l.evs w =
      setMem (applyR l.evs w.mem) w from rfl, hsemM]
    exact hfo.2 m' hm'
  have hlen : l.evs.length ≤ 1 := by rw [hl]; exact len_instEvs a _
  refine ⟨_, (R.step (patch l.evs s), mon1), fun k => (0, k), .op hvb hi hops hfix hfoot1 hm2,
    PRun.cons hs hp trivial .nil, rfl,
    ⟨by show Q R (R.step (patch l.evs s)) _; rw [show R.step (patch l.evs s) = s2 from hit]; exact hq2,
      aInv_step hR hq1 (aInv_patch hA _) hm2⟩, ?_⟩
  have htr : evTr [l] = [l.evs] := by simp [evTr]
  rw [htr]
  refine ⟨fun k hk => by rw [evAt_single]; exact List.getElem?_eq_getElem hk,
    fun k k' h1 h2 => Or.inr ⟨rfl, h1⟩, fun p y hy hW hn => ?_, fun e he hF => ?_,
    .inl ⟨hlen, fun e he => ?_⟩, fun h => by omega⟩
  · obtain ⟨j', k'⟩ := p
    rcases j' with _ | j'
    · rw [evAt_single] at hy
      exact absurd rfl (hn k' (List.getElem?_eq_some_iff.mp hy).1)
    · simp [evAt] at hy
  · have he' : e ∈ instEvs a (setMem M s) := hl ▸ he
    have hn0 := (hevk _ e he').2 hF
    have := hav1 e he 0 hn0
    simpa [PrivA] using this
  · exact (hevk _ e (hl ▸ he)).1

end Concurrency.ArmAllocThread

namespace Concurrency.CallSeg

open Arm ArmFoot ArmThread Prog ClifThread ProgE2E Backend Backend.Proof VCodeThread PrepThread
  AllocThread ThreadRefine ArmAllocThread E2E ArmInstFoot CallThread

/-! ## The pc along straight-line code -/

/-- **The pc through straight-line lines**: at line `j + i` after `i` steps. -/
theorem linesAt_pc {R : RL} (hR : R.Wf) {j : Nat} {ls1 : List Line} {s s' : ArmState}
    (h : LinesAt R j ls1 s s') : ∀ i ≤ ls1.length, Arm.r .PC (iterN R.step i s) = R.pcOf (j + i) :=
  iterN_execLines_pc hR.layout hR.lm hR.fit ls1 j s s' h.at_ h.hook h.prog h.pc h.err h.inter h.run

/-- `ls` has no `ret` line. -/
def NoRet (ls : List Line) : Prop := ∀ x t, Line.ins x t ∈ ls → x ≠ .ret

/-- **A state at an instruction line other than `ret`.** -/
def AtNonRet (R : RL) (u : ArmState) : Prop :=
  ∃ j x t, R.fa.lines.toList[j]? = some (.ins x t) ∧ x ≠ .ret ∧ Arm.r .PC u = R.pcOf j

/-- **Through straight-line lines without `ret`, every state before the last line's step is at a
line other than `ret`.** -/
theorem linesAt_nonRet {R : RL} (hR : R.Wf) {j : Nat} {ls1 : List Line} {s s' : ArmState}
    (h : LinesAt R j ls1 s s') (hnr : NoRet ls1) : ∀ i < ls1.length, AtNonRet R (iterN R.step i s) := by
  intro i hi
  obtain ⟨x, t, -, hli, -, -, -, -⟩ := step_execLines (X := R.X) (H := R.H) hR.layout hR.lm hR.fit
    h.at_ h.hook h.prog h.pc h.err h.inter h.run i hi
  exact ⟨j + i, x, t, h.at_ i _ hli, hnr x t (List.mem_of_getElem? hli), linesAt_pc hR h i (by omega)⟩

/-- **Through a list of moves whose lines have no `ret`** (`moves_privA`): every state of the
run before its end is at a line other than `ret`. -/
theorem moves_privP {R : RL} (hR : R.Wf) {b : Nat} {w : ArmState} :
    ∀ (mvs : List (Loc × Loc)) (its : List RItem) (s : ArmState) (m : Loc → CV),
      Q R s (.run ⟨b, mvs.map (fun p => RItem.move p.1 p.2) ++ its, m, w⟩) →
      AInv R (.run ⟨b, mvs.map (fun p => RItem.move p.1 p.2) ++ its, m, w⟩) →
      (∀ p ∈ mvs, ∀ code ls1, R.fr.moveInsts p.1 p.2 = .ok code →
        codeLinesE R.ctx R.af code {} = .ok (ls1, {}) → NoRet ls1) →
      ∃ n, Q R (iterN R.step n s) (.run ⟨b, its, movesM mvs m, w⟩) ∧
        AInv R (.run ⟨b, its, movesM mvs m, w⟩) ∧
        ∀ i < n, ((∀ e ∈ stepEvs (iterN R.step i s), R.F e.addr) ∧ NoStx (iterN R.step i s)) ∧
          (iterN R.step i s).program = R.fb.program R.base ∧ AtNonRet R (iterN R.step i s)
  | [], its, s, m, hq, hA, _ => ⟨0, hq, hA, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | p :: mvs, its, s, m, hq, hA, hnr => by
    obtain ⟨j, ls1, s', code, hcode, hls1, hlat, hq1, hpriv⟩ := move_lines hR hq
    have hA1 := Backend.Proof.aInv_step hR hq hA (.move (src := p.1) (dst := p.2))
    have hit := hlat.iter hR
    rw [← hit] at hq1
    obtain ⟨n, hq2, hA2, hp2⟩ := moves_privP hR mvs its _ _ hq1 hA1
      fun p' hp' => hnr p' (List.mem_cons_of_mem _ hp')
    have hnr1 : NoRet ls1 := hnr p List.mem_cons_self code ls1 hcode (hls1 {})
    refine ⟨ls1.length + n, by rw [iterN_add]; exact hq2, hA2, fun i hi => ?_⟩
    by_cases h : i < ls1.length
    · exact ⟨hpriv i h, linesAt_program hR hlat i (by omega), linesAt_nonRet hR hlat hnr1 i h⟩
    · have := hp2 (i - ls1.length) (by omega)
      rw [← iterN_add, show ls1.length + (i - ls1.length) = i by omega] at this
      exact this

/-- **A step of the allocated code at a related configuration is a thread step to the same
configuration** (`ThreadProgress.srcStep_of_mstep`). -/
theorem srcStep_of_mstep_eq {R : RL} (hcov : ThreadProgress.CoveredCode R) (hX : TlsMemFree R.X)
    {s : ArmState} {c c' : MConf CV ArmState} (hq : Q R s c)
    (hs : MStep R.vc R.sem ckeep R.rf c c') : ∃ evs, SrcStep R c evs c' := by
  cases hs with
  | move => exact ⟨[], .move⟩
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsem hlen hho hclob
      hnext =>
    obtain ⟨hnc, hnt, hcv⟩ := hcov b vb k i hvb hi
    have hstr := q_stRel hq
    have herrw : Arm.r .ERR w = .None := by
      rw [← hstr.world.1 .ERR (by simp [Masked]), hstr.err]
    have halw : CheckSPAlignment w :=
      align_of_sp (show Arm.r (.GPR 31#5) w = Arm.r (.GPR 31#5) s from
        (hstr.world.1 (.GPR 31#5) (by simp [Masked])).symm) hstr.align
    obtain ⟨regs, -, hsz', -, huses⟩ := q_regs hq hvb hi hops
    have hst : i.isCtl = false →
        csemWF R.ctx i (itemUses ops allocs m) = true ∧ CheckSPAlignment w := by
      intro hctl
      have hfo : FormOk R.ctx i = true := by
        rcases hcv with h | h
        · rw [hctl] at h; cases h
        · exact h
      refine ⟨?_, halw⟩
      rw [huses]
      simp [csemWF, hfo, hops, useVals_length ops regs hsz']
    have hfoot := ifoot_csem (F := R.F) (ctx := R.ctx) (uses := itemUses ops allocs m) hX herrw
      hnc hnt hst
    have hsemC : csem R.F R.ctx R.X i (itemUses ops allocs m) w = some (outs, w', ctl) := by
      rw [← R.sem_eq hnc hnt]; exact hsem
    have hp := patch_of_agrees (ThreadProgress.agrees_cEvs herrw hfoot hsemC)
    refine ⟨cEvs R.F R.ctx i (itemUses ops allocs m) w, .op hvb hi hops ?_ ?_ ?_⟩
    · rw [hp]
    · rw [hp]
      unfold IFoot at hfoot ⊢
      simp only [R.sem_eq hnc hnt]
      exact hfoot
    · rw [hp]
      exact .op hvb hi hops hsz hsem hlen hho hclob hnext

/-! ## The return -/

/-- **The epilogue's `ldp x29, x30, [sp], #16`**: one plain read at `sp`, no exclusive. -/
theorem ldp_fplr_evs (env : Env) (s : ArmState) (hal : CheckSPAlignment s) :
    ∃ a, (Insn.ldp Reg.fp Reg.lr (.spPostIndexed 16)).toArmInst env = .ok a ∧ isExcl a = false ∧
      ∀ e ∈ instEvs a s, e.addr = spOf s ∧ e.k = .plainR := by
  refine ⟨_, by simp [csimp_rules, Reg.fp, Reg.lr, pure, Except.pure]; rfl, rfl, ?_⟩
  have hal' := spAligned hal
  intro e he
  simp [instEvs, pairEvs, LDST.reg_pair_constrain_unpredictable, hal, Arm.BitVec.lsb] at he
  subst he
  refine ⟨?_, rfl⟩
  simp only [read_gpr, spOf]
  bv_omega

theorem kinds_spAdj (n : Nat) : Code.kinds (spAdjLines false n) = [] := by
  have h := Code.kinds_epilogueLines n
  rw [epilogueLines_eq, Code.kinds_append] at h
  have h2 : Code.kinds [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none, .ins .ret none] =
      [.plainR] := rfl
  rw [h2] at h
  simpa using h

theorem noRet_spAdj (sub : Bool) (size : Nat) : NoRet (spAdjLines sub size) := by
  intro x t hln
  unfold spAdjLines at hln
  split at hln
  · simp at hln
  · split at hln
    · simp only [List.mem_singleton, Line.ins.injEq] at hln
      obtain ⟨rfl, -⟩ := hln; intro h; cases h
    · rw [List.mem_append, loadConst64_eq] at hln
      rcases hln with hln | hln
      · simp only [List.mem_cons] at hln
        rcases hln with hln | hln
        · simp only [Line.ins.injEq] at hln; obtain ⟨rfl, -⟩ := hln; intro h; cases h
        · obtain ⟨c, i, hc⟩ := movkLines_mem hln
          simp only [Line.ins.injEq] at hc; obtain ⟨rfl, -⟩ := hc; intro h; cases h
      · simp only [List.mem_singleton, Line.ins.injEq] at hln
        obtain ⟨rfl, -⟩ := hln; intro h; cases h

theorem noRet_prologue (size : Nat) : NoRet (prologueLines size) := by
  intro x t hln
  rw [prologueLines_eq, List.mem_append] at hln
  rcases hln with hln | hln
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Line.ins.injEq] at hln
    rcases hln with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> intro h <;> cases h
  · exact noRet_spAdj true size x t hln

/-- **The return from a `rets` item** (`ret_machine`, per step): the epilogue and the `ret`, each
step's events private (the `ldp` reads the fp/lr slot), no store exclusive, the program kept, at a
line; then the return address with no error, `sp` as at entry, the memory and the program kept. -/
theorem rets_privP {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    {s : ArmState} {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV}
    {w : ArmState} (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock}
    {us : List (Reg × Reg)} (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.rets us)) :
    ∃ n, (∀ i < n, ((∀ e ∈ stepEvs (iterN R.step i s), R.F e.addr) ∧ NoStx (iterN R.step i s)) ∧
        (iterN R.step i s).program = R.fb.program R.base ∧
        ∃ j, Arm.r .PC (iterN R.step i s) = R.pcOf j) ∧
      Arm.r .PC (iterN R.step n s) = ra ∧ Arm.r .ERR (iterN R.step n s) = .None ∧
      spv (iterN R.step n s) = spv R.s0 ∧ (iterN R.step n s).mem = s.mem ∧
      (iterN R.step n s).program = s.program ∧
      (∀ i, i + 1 < n → AtNonRet R (iterN R.step i s)) ∧ 0 < n ∧
      ∃ j t, R.fa.lines.toList[j]? = some (.ins .ret t) ∧
        Arm.r .PC (iterN R.step (n - 1) s) = R.pcOf j := by
  have hframe := lowerRFunc_frame hR.alloc
  have hst0 := hR.stack.frame
  have hsp0 := (spv R.s0).isLt
  have hs : R.af.frameSize < 2 ^ 64 := by have := hst0.1; omega
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, rfl, hit, hsplit,
    hasg, hc1', hops, hstat, hchk', hc2, h1, h2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  obtain ⟨us', rfl⟩ := assign_rets hasg
  obtain rfl : c1 = [.epilogueRet] := by
    rcases hc1' with ⟨-, -, h⟩ | ⟨_, h, -⟩ | ⟨_, -, h⟩
    · exact absurd rfl (h us')
    · cases h
    · exact h
  simp only [codeLinesE, ainstLines, hframe, ite_true, bind, Except.bind, pure, Except.pure,
    List.append_nil, Except.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  rw [epilogueLines_eq] at hdrop
  have hpl : ∀ ln ∈ spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none, .ins .ret none], ln.plain = true := by
    intro ln hln
    rcases List.mem_append.1 hln with hln | hln
    · obtain ⟨_, _, _, hp⟩ := spAdjLines_ins false _ ln hln; exact hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hln
      rcases hln with rfl | rfl <;> rfl
  rw [ftR_plain_append _ _ _ hpl (noTrap_next h2)] at hdrop
  obtain ⟨X, hX⟩ : ∃ X, X = relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T := ⟨_, rfl⟩
  have hdrop' : R.L.drop j0 = (spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]) ++ (.ins .ret none :: X) := by
    rw [hdrop, hX]; simp
  have hdropA : R.L.drop j0 = spAdjLines false R.af.frameSize ++
      (Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none :: .ins .ret none :: X) := by
    rw [hdrop, hX]; simp
  have hdrop0 : frameDrop R.af = R.af.frameSize + 16 := by simp [frameDrop, hframe]
  have hslot : spOf s + BitVec.ofNat 64 R.af.frameSize = spv R.s0 - 16#64 := by
    rw [hst.sp, RL.spB, hdrop0, BitVec.ofNat_add]; bv_omega
  have hal : (spOf s + BitVec.ofNat 64 R.af.frameSize).toNat % 16 = 0 := by
    have h16 : 16 ≤ (spv R.s0).toNat := by have := hst0.1; omega
    rw [hslot, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using h16)]
    have := hent.spAligned
    simp; omega
  obtain ⟨s1, hsteps, hsp1, hx29, hx30, ho1, hm1⟩ := epilogue_ok (R.envOf j0) hs s hal
  have hinsE : ∀ ln ∈ spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none], ∃ x, ln = .ins x none ∧
        x.hooked = false := fun ln h => by
    rcases List.mem_append.1 h with h | h
    · obtain ⟨x, e, hh, -⟩ := spAdjLines_ins false _ ln h; exact ⟨x, e, hh⟩
    · simp only [List.mem_singleton] at h; exact ⟨_, h, rfl⟩
  obtain ⟨hiter, hpc1, -, -⟩ := iterN_steps hR hdrop' hinsE hst.prog hpc hst.err hsteps
  obtain ⟨herr1, hprog1⟩ := hsteps.err
  have hlat : LinesAt R j0 (spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]) s s1 :=
    ⟨lines_at hdrop', fun x t h => by obtain ⟨x', e, hh⟩ := hinsE _ h; cases e; exact hh,
      hst.prog, by rw [hpc]; rfl, hst.err, stepsOk_interOk hsteps hst.err, hsteps.exec⟩
  -- the state at the `ldp`
  obtain ⟨s0, hsteps0, hsp0', -, -⟩ := spAdj_ok (R.envOf j0) false hs s
  obtain ⟨hiter0, -, -, -⟩ := iterN_steps hR hdropA
    (fun ln h => by obtain ⟨x, e, hh, -⟩ := spAdjLines_ins false _ ln h; exact ⟨x, e, hh⟩)
    hst.prog hpc hst.err hsteps0
  simp only [Bool.false_eq_true, ite_false] at hsp0'
  -- the `ret`
  have hj : R.fa.lines.toList[j0 + (spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length]? = some (Line.ins .ret none) := by
    have := congrArg (·[(spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length]?) hdrop'
    simpa [List.getElem?_drop, RL.L] using this
  obtain ⟨a, ha, hstep⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj rfl
    (by rw [hprog1, hst.prog]) hpc1 (by rw [herr1, hst.err])
  obtain ⟨a', ha', he'⟩ := exec_ret ⟨lineOffset R.fa.lines.toList (j0 + (spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length), (R.lm[·]?)⟩ s1
  rw [ha] at ha'; cases ha'
  have hfin : iterN R.step ((spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length + 1) s =
      Arm.w .PC (xreg 30 s1) s1 := by
    rw [iterN_one_succ, hiter]; exact hstep.trans he'
  have hfplr := hst.fplr hframe
  rw [← hslot] at hfplr
  have hstepEvs := step_execLines (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hlat.at_ hlat.hook
    hlat.prog hlat.pc hlat.err hlat.inter hlat.run
  refine ⟨(spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length + 1, fun i hi => ?_, ?_⟩
  · by_cases hiL : i < (spAdjLines false R.af.frameSize ++
        [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length
    · obtain ⟨x, t, a, hli, ha, hdec, hev, -⟩ := hstepEvs i hiL
      have hns : isExcl a = false → NoStx (iterN R.step i s) := fun hx rel rs rn hc => by
        rw [show R.step = ArmStepX R.X R.H R.fa from rfl, cls_of_decode hdec] at hc
        exact clsOf_ne_stx hx rel rs rn hc
      refine ⟨?_, linesAt_program hR hlat i (by omega), _, linesAt_pc hR hlat i (by omega)⟩
      rw [show R.step = ArmStepX R.X R.H R.fa from rfl, hev]
      by_cases hi0 : i < (spAdjLines false R.af.frameSize).length
      · have hmem : Line.ins x t ∈ spAdjLines false R.af.frameSize := by
          rw [List.getElem?_append_left hi0] at hli
          exact List.mem_of_getElem? hli
        have hk := kinds_mem_none (kinds_spAdj _) hmem
        rw [VCodeEvents.instEvs_none ha hk]
        exact ⟨fun e he => absurd he List.not_mem_nil, hns (isExcl_none ha hk)⟩
      · have hiE : i = (spAdjLines false R.af.frameSize).length := by simp at hiL; omega
        subst hiE
        rw [List.getElem?_append_right (Nat.le_refl _)] at hli
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq, Line.ins.injEq] at hli
        obtain ⟨rfl, -⟩ := hli
        have hs0 : iterN R.step (spAdjLines false R.af.frameSize).length s = s0 := hiter0
        have halS : CheckSPAlignment s0 := (checkSP_iff _).2 (by rw [hsp0']; exact hal)
        obtain ⟨a2, ha2, hx2, hevs2⟩ := ldp_fplr_evs ⟨lineOffset R.fa.lines.toList
          (j0 + (spAdjLines false R.af.frameSize).length), (R.lm[·]?)⟩ s0 halS
        rw [ha] at ha2
        cases ha2
        have hs0' : iterN (ArmStepX R.X R.H R.fa) (spAdjLines false R.af.frameSize).length s = s0 :=
          hiter0
        have hns0 : NoStx s0 := by rw [← hs0]; exact hns hx2
        rw [hs0']
        refine ⟨fun e he => ?_, hns0⟩
        obtain ⟨hadd, -⟩ := hevs2 e he
        rw [hadd, hsp0', hslot]
        have := RL.FK_F (fplr_inF hR hframe 0 (by omega))
        simpa using this
    · have hiE : i = (spAdjLines false R.af.frameSize ++
          [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]).length := by omega
      subst hiE
      rw [hiter]
      obtain ⟨a3, ha3, -, hev3, hdec3⟩ := stepEvs_line (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj
        rfl (by rw [hprog1, hst.prog]) hpc1 (by rw [herr1, hst.err])
      have hk : Code.insnKind Insn.ret = none := rfl
      refine ⟨⟨fun e he => ?_, fun rel rs rn hc => ?_⟩, by rw [hprog1, hst.prog], _, hpc1⟩
      · rw [hev3, VCodeEvents.instEvs_none ha3 hk] at he
        exact absurd he List.not_mem_nil
      · rw [cls_of_decode hdec3] at hc
        exact clsOf_ne_stx (isExcl_none ha3 hk) rel rs rn hc
  have hnrE : NoRet (spAdjLines false R.af.frameSize ++
      [Line.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)) none]) := by
    intro x t hln
    rcases List.mem_append.1 hln with hln | hln
    · exact noRet_spAdj false _ x t hln
    · simp only [List.mem_singleton, Line.ins.injEq] at hln
      obtain ⟨rfl, -⟩ := hln; intro h; cases h
  refine ⟨?_, ?_, ?_, ?_, ?_, fun i hi => linesAt_nonRet hR hlat hnrE i (by omega), by omega,
    _, none, hj, by rw [Nat.add_sub_cancel, hiter]; exact hpc1⟩ <;> rw [hfin]
  · rw [Arm.r_of_w_same, hx30, hfplr, BitVec.extractLsb'_append_eq_left, hent.lr]
  · rw [Arm.r_of_w_different (by simp), herr1, hst.err]
  · simp only [spv]
    rw [Arm.r_of_w_different (by simp)]
    show spOf s1 = spv R.s0
    rw [hsp1, hslot, BitVec.sub_add_cancel]
  · rw [Arm.ArmState.mem_w_eq_mem, hm1]
  · rw [Arm.w_program, hprog1]

end Concurrency.CallSeg
