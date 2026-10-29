import FV.Concurrency.CallSeg
import FV.Concurrency.ThreadProgress
import FV.Concurrency.FrameEvs

/-!
# Resuming the caller after a compiled callee returns (T2j follow-up, #473, calls)

The pieces that follow a compiled activation's precise Arm run through its whole straight-line
code, with the pc of every state (a linked machine dispatching on where a step goes needs it),
up to its return:

* `linesAt_pc`, `moves_privP`: through straight-line lines and through moves (`moves_privA`), the
  pc of every state is at a line (`R.pcOf`); `moves_privQA`: the same from `QA`, callee restores
  included (they run no line and continue a return tail, `RetTail`);
* `srcStep_of_mstep_eq`: a step of the allocated code at a related configuration is a thread step
  to the same configuration;
* `oneEv_op1`: **one step at a straight-line form with one Arm instruction** (`OneEvForm`, as
  `oneEv_op`): the Arm's step and the source step reading its bytes, related states after both;
* `rets_privP`: **the return** from a `rets` item: Cranelift's epilogue and the `ret`, each
  step's events private (the pops and the `ldp` read the clobber area and fp/lr,
  `FrameEvs.epilogue_evsIn`), at a line; the return address reached with `sp` and x29 as at
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
    .inl ⟨by show Q R (R.step (patch l.evs s)) _; rw [show R.step (patch l.evs s) = s2 from hit]; exact hq2,
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

/-- **Through straight-line lines without `ret`, every state before the last line's step is at a
line other than `ret`.** -/
theorem linesAt_nonRet {R : RL} (hR : R.Wf) {j : Nat} {ls1 : List Line} {s s' : ArmState}
    (h : LinesAt R j ls1 s s') (hnr : NoRet ls1) : ∀ i < ls1.length, AtNonRet R (iterN R.step i s) :=
  nonRet_execLines hR h.at_ h.hook h.prog h.pc h.err h.inter h.run hnr

/-- **Through a list of moves whose lines have no `ret`** (`moves_privA`; no callee restore among
them): every state of the run before its end is at a line other than `ret`. -/
theorem moves_privP {R : RL} (hR : R.Wf) {b : Nat} {w : ArmState} :
    ∀ (mvs : List (Loc × Loc)) (its : List RItem) (s : ArmState) (m : Loc → CV),
      Q R s (.run ⟨b, mvs.map (fun p => RItem.move p.1 p.2) ++ its, m, w⟩) →
      AInv R (.run ⟨b, mvs.map (fun p => RItem.move p.1 p.2) ++ its, m, w⟩) →
      (∀ p ∈ mvs, ∀ code ls1, R.fr.moveInsts p.1 p.2 = .ok code →
        codeLinesE R.ctx R.af code {} = .ok (ls1, {}) → NoRet ls1) →
      (∀ p ∈ mvs, p.1.isSave = false) →
      ∃ n, Q R (iterN R.step n s) (.run ⟨b, its, movesM mvs m, w⟩) ∧
        AInv R (.run ⟨b, its, movesM mvs m, w⟩) ∧
        ∀ i < n, ((∀ e ∈ stepEvs (iterN R.step i s), R.F e.addr) ∧ NoStx (iterN R.step i s)) ∧
          (iterN R.step i s).program = R.fb.program R.base ∧ AtNonRet R (iterN R.step i s)
  | [], its, s, m, hq, hA, _, _ => ⟨0, hq, hA, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | p :: mvs, its, s, m, hq, hA, hnr, hns => by
    obtain ⟨j, ls1, s', code, hcode, hls1, hlat, hq1, hpriv⟩ :=
      move_lines hR hq (hns p List.mem_cons_self)
    have hA1 := Backend.Proof.aInv_step hR hq hA (.move (src := p.1) (dst := p.2))
    have hit := hlat.iter hR
    rw [← hit] at hq1
    obtain ⟨n, hq2, hA2, hp2⟩ := moves_privP hR mvs its _ _ hq1 hA1
      (fun p' hp' => hnr p' (List.mem_cons_of_mem _ hp'))
      (fun p' hp' => hns p' (List.mem_cons_of_mem _ hp'))
    have hnr1 : NoRet ls1 := hnr p List.mem_cons_self code ls1 hcode (hls1 {})
    refine ⟨ls1.length + n, by rw [iterN_add]; exact hq2, hA2, fun i hi => ?_⟩
    by_cases h : i < ls1.length
    · exact ⟨hpriv i h, linesAt_program hR hlat i (by omega), linesAt_nonRet hR hlat hnr1 i h⟩
    · have := hp2 (i - ls1.length) (by omega)
      rw [← iterN_add, show ls1.length + (i - ls1.length) = i by omega] at this
      exact this

/-- **One move other than a callee restore, from `Q`**: its lines run (`move_lines`), every state
before their end private, on the program, at a line other than `ret`. -/
theorem move_privQ {R : RL} (hR : R.Wf) {s : ArmState} {b : Nat} {src dst : Loc}
    {its : List RItem} {m : Loc → CV} {w : ArmState}
    (hq : Q R s (.run ⟨b, .move src dst :: its, m, w⟩)) (hns : src.isSave = false)
    (hnr : ∀ code ls1, R.fr.moveInsts src dst = .ok code →
      codeLinesE R.ctx R.af code {} = .ok (ls1, {}) → NoRet ls1) :
    ∃ n, Q R (iterN R.step n s) (.run ⟨b, its, Backend.Proof.upd m dst (m src), w⟩) ∧
      ∀ i < n, ((∀ e ∈ stepEvs (iterN R.step i s), R.F e.addr) ∧ NoStx (iterN R.step i s)) ∧
        (iterN R.step i s).program = R.fb.program R.base ∧ AtNonRet R (iterN R.step i s) := by
  obtain ⟨j, ls1, s', code, hcode, hls1, hlat, hq1, hpriv⟩ := move_lines hR hq hns
  have hit := hlat.iter hR
  rw [← hit] at hq1
  have hnr1 : NoRet ls1 := hnr code ls1 hcode (hls1 {})
  exact ⟨ls1.length, hq1, fun i hi =>
    ⟨hpriv i hi, linesAt_program hR hlat i (by omega), linesAt_nonRet hR hlat hnr1 i hi⟩⟩

/-- **One move from `QA`** (`move_opR` per state): a callee restore runs no line and starts or
continues a return tail (`RetTail`, as `realizesQA`); every other move runs its lines
(`move_privQ`, from the machine's store in a return tail). -/
theorem move_privQA {R : RL} (hR : R.Wf) {s : ArmState} {b : Nat} {src dst : Loc}
    {its : List RItem} {m : Loc → CV} {w : ArmState}
    (hqa : QA R s (.run ⟨b, .move src dst :: its, m, w⟩))
    (hnr : ∀ code ls1, R.fr.moveInsts src dst = .ok code →
      codeLinesE R.ctx R.af code {} = .ok (ls1, {}) → NoRet ls1) :
    ∃ n, QA R (iterN R.step n s) (.run ⟨b, its, Backend.Proof.upd m dst (m src), w⟩) ∧
      ∀ i < n, ((∀ e ∈ stepEvs (iterN R.step i s), R.F e.addr) ∧ NoStx (iterN R.step i s)) ∧
        (iterN R.step i s).program = R.fb.program R.base ∧ AtNonRet R (iterN R.step i s) := by
  rcases hqa with ⟨hq, hA⟩ | hrt
  · cases hsS : src.isSave
    · obtain ⟨n, hq', hp⟩ := move_privQ hR hq hsS hnr
      exact ⟨n, .inl ⟨hq', aInv_step hR hq hA .move⟩, hp⟩
    · -- a callee restore: it starts a return tail
      obtain ⟨r, rfl⟩ : ∃ r, src = .save r := by
        cases src <;> simp [Loc.isSave] at hsS; exact ⟨_, rfl⟩
      obtain ⟨rfl, D, htl⟩ := restore_tail hR hq
      refine ⟨0, .inr ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
      simp only [RetTail]
      refine ⟨m, D ++ [r], q_restore rfl hq, fun l hl => ?_, htl⟩
      simp only [Backend.Proof.upd, hl r (by simp), ite_false]
  · simp only [RetTail] at hrt
    obtain ⟨mt, D, hq, hmD, vb, pend, k, a, rest, us, hvb, he, hk, htl⟩ := hrt
    rcases pend with _ | ⟨it, pend⟩
    · simp at he
    unfold retTailOk at htl
    split at htl
    · -- a restore: no line, the tail goes on with `r` restored
      rename_i r hr1 hr2
      simp only [Bool.and_eq_true] at htl
      obtain rfl := RItem.eq_restore hr1 hr2
      simp only [List.cons_append, List.cons.injEq, RItem.move.injEq] at he
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
      refine ⟨0, .inr ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
      simp only [RetTail]
      refine ⟨mt, D ++ [r], q_restore rfl hq, fun l hl => ?_, vb, pend, k, a, rest, us, hvb, rfl,
        hk, htl.2⟩
      simp only [Backend.Proof.upd, hl r (by simp), ite_false]
      exact hmD l (fun r' hr' => hl r' (List.mem_append_left _ hr'))
    · -- another move: its lines from the machine's store
      simp only [Bool.and_eq_true] at htl
      obtain ⟨hav, htl⟩ := htl
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [RItem.avoids, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false,
        Bool.or_eq_true, beq_iff_eq, not_or] at hav
      obtain ⟨⟨hx, -⟩, hD⟩ := hav
      obtain ⟨n, hq', hp⟩ := move_privQ hR hq hx hnr
      refine ⟨n, .inr ?_, hp⟩
      simp only [RetTail]
      refine ⟨Backend.Proof.upd mt dst (mt src), D, hq', fun l hl => ?_, vb, pend, k, a, rest, us,
        hvb, rfl, hk, htl⟩
      by_cases hly : l = dst
      · simp only [Backend.Proof.upd, hly, ite_true]
        exact hmD src (fun r hr e => (hD r hr).1 e)
      · simp only [Backend.Proof.upd, hly, ite_false]
        exact hmD l hl

/-- **Through a list of moves from `QA`, callee restores included** (`moves_privP` for return
tails, `move_privQA` per move). -/
theorem moves_privQA {R : RL} (hR : R.Wf) {b : Nat} {w : ArmState} :
    ∀ (mvs : List (Loc × Loc)) (its : List RItem) (s : ArmState) (m : Loc → CV),
      QA R s (.run ⟨b, mvs.map (fun p => RItem.move p.1 p.2) ++ its, m, w⟩) →
      (∀ p ∈ mvs, ∀ code ls1, R.fr.moveInsts p.1 p.2 = .ok code →
        codeLinesE R.ctx R.af code {} = .ok (ls1, {}) → NoRet ls1) →
      ∃ n, QA R (iterN R.step n s) (.run ⟨b, its, movesM mvs m, w⟩) ∧
        ∀ i < n, ((∀ e ∈ stepEvs (iterN R.step i s), R.F e.addr) ∧ NoStx (iterN R.step i s)) ∧
          (iterN R.step i s).program = R.fb.program R.base ∧ AtNonRet R (iterN R.step i s)
  | [], its, s, m, hqa, _ => ⟨0, hqa, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | p :: mvs, its, s, m, hqa, hnr => by
    obtain ⟨n1, hqa1, hp1⟩ := move_privQA hR hqa (hnr p List.mem_cons_self)
    obtain ⟨n2, hqa2, hp2⟩ := moves_privQA hR mvs its _ _ hqa1
      (fun p' hp' => hnr p' (List.mem_cons_of_mem _ hp'))
    refine ⟨n1 + n2, by rw [iterN_add]; exact hqa2, fun i hi => ?_⟩
    by_cases h : i < n1
    · exact hp1 i h
    · have := hp2 (i - n1) (by omega)
      rw [← iterN_add, show n1 + (i - n1) = i by omega] at this
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

theorem noRet_pushLines (int : Bool) (rs : List Reg) : NoRet (pushLines int rs) := by
  intro x t hln
  obtain ⟨y, e, r, r', hy⟩ := pushLines_mem hln
  simp only [Line.ins.injEq] at e
  obtain ⟨rfl, -⟩ := e
  rcases hy with rfl | rfl | rfl | rfl <;> intro h <;> cases h

theorem noRet_popLines (int : Bool) (rs : List Reg) : NoRet (popLines int rs) := by
  intro x t hln
  obtain ⟨y, e, r, r', hy⟩ := popLines_mem hln
  simp only [Line.ins.injEq] at e
  obtain ⟨rfl, -⟩ := e
  rcases hy with rfl | rfl | rfl | rfl <;> intro h <;> cases h

/-- The stack probes (#581): `sub sp`, `stur wzr` and `add sp`, no `ret`. -/
theorem noRet_probeLines (total : Nat) : NoRet (probeLines total) := by
  intro x t hln
  rcases probeLines_mem hln with h | h | ⟨n, h⟩ <;>
    (simp only [Line.ins.injEq] at h; obtain ⟨rfl, -⟩ := h; intro h; cases h)

/-- The prologue has no `ret` (with the stack probes, #581: `calls` is the new argument of
`prologueLines`). -/
theorem noRet_prologue (saves : List Reg) (size : Nat) (calls : Bool) :
    NoRet (prologueLines saves size calls) := by
  intro x t hln
  rw [prologueLines_eq] at hln
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hln
  rcases hln with (h | h) | h | h | h | h
  · simp only [Line.ins.injEq] at h; obtain ⟨rfl, -⟩ := h; intro h; cases h
  · simp only [Line.ins.injEq] at h; obtain ⟨rfl, -⟩ := h; intro h; cases h
  · exact noRet_probeLines _ x t h
  · exact noRet_pushLines _ _ x t h
  · exact noRet_pushLines _ _ x t h
  · exact noRet_spAdj true _ x t h

theorem noRet_epiLines (saves : List Reg) (size : Nat) : NoRet (epiLines saves size) := by
  intro x t hln
  simp only [epiLines, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hln
  rcases hln with h | h | h | h
  · exact noRet_spAdj false _ x t h
  · exact noRet_popLines _ _ x t h
  · exact noRet_popLines _ _ x t h
  · simp only [Line.ins.injEq] at h; obtain ⟨rfl, -⟩ := h; intro h; cases h

/-- **The return from a `rets` item** (`ret_machine`, per step): Cranelift's epilogue and the
`ret`, each step's events private (the pops and the `ldp` read the clobber area and fp/lr), no
store exclusive, the program kept, at a line; then the return address with no error, `sp` as at
entry, the memory and the program kept, x29 as at entry (the `ldp` of fp/lr). -/
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
      (iterN R.step n s).program = s.program ∧ xreg 29 (iterN R.step n s) = xreg 29 R.s0 ∧
      (∀ i, i + 1 < n → AtNonRet R (iterN R.step i s)) ∧ 0 < n ∧
      ∃ j t, R.fa.lines.toList[j]? = some (.ins .ret t) ∧
        Arm.r .PC (iterN R.step (n - 1) s) = R.pcOf j := by
  obtain ⟨hframe, hfs, -, hsv, -, hcb, -, -, -⟩ := RL.frame_facts hR
  have hst0 := hR.stack.frame
  have hsp0 := (spv R.s0).isLt
  have hs : R.af.frameSize < 2 ^ 64 := by have := hst0.1; omega
  have hcb' : clobberBytes R.af.saves ≤ R.af.frameSize := by rw [hfs]; exact hcb
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
  rw [epilogueLines_epi] at hdrop
  have hpl : ∀ ln ∈ epiLines R.af.saves R.af.frameSize ++ [Line.ins .ret none], ln.plain = true := by
    intro ln hln
    rcases List.mem_append.1 hln with hln | hln
    · obtain ⟨_, _, _, hp, -⟩ := epiLines_ins _ _ ln hln; exact hp
    · simp only [List.mem_singleton] at hln; subst hln; rfl
  rw [ftR_plain_append _ _ _ hpl (noTrap_next h2)] at hdrop
  have hdrop' : R.L.drop j0 = epiLines R.af.saves R.af.frameSize ++
      (.ins .ret none :: (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T)) := by
    rw [hdrop]; simp
  -- `sp + size - clobberBytes` is the bottom of the clobber area, `sp + size` the fp/lr slot
  have hdrop0 : frameDrop R.af = R.af.frameSize + 16 := by simp [frameDrop, hframe]
  have hslot : spOf s + BitVec.ofNat 64 R.af.frameSize = spv R.s0 - 16#64 := by
    rw [hst.sp, RL.spB, hdrop0, BitVec.ofNat_add]; bv_omega
  have hB : spOf s + BitVec.ofNat 64 (R.af.frameSize - clobberBytes R.af.saves) = R.topB := by
    obtain ⟨d, hd⟩ : ∃ d, R.af.frameSize = d + clobberBytes R.af.saves :=
      ⟨_, (Nat.sub_add_cancel hcb').symm⟩
    rw [hst.sp, RL.spB, RL.topB, RL.topN, hdrop0, hd, Nat.add_sub_cancel,
      show d + clobberBytes R.af.saves + 16 = d + (16 + clobberBytes R.af.saves) by omega,
      BitVec.ofNat_add, BitVec.ofNat_add]
    bv_omega
  have htopcb : R.topB + BitVec.ofNat 64 (clobberBytes R.af.saves) = spv R.s0 - 16#64 := by
    rw [RL.topB, RL.topN, BitVec.ofNat_add]; bv_omega
  have hal : (spOf s + BitVec.ofNat 64 (R.af.frameSize - clobberBytes R.af.saves)).toNat % 16 = 0 := by
    rw [hB]
    have := hent.spAligned
    have := clobberBytes_mod R.af.saves
    have h16 : 16 + clobberBytes R.af.saves ≤ (spv R.s0).toNat := by have := hst0.1; omega
    have hm : (16 + clobberBytes R.af.saves) % 2 ^ 64 = 16 + clobberBytes R.af.saves :=
      Nat.mod_eq_of_lt (by omega)
    simp only [RL.topB, RL.topN]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, hm]; exact h16),
      BitVec.toNat_ofNat, hm]
    omega
  obtain ⟨s1, hsteps, hsp1, hx29, hx30, -, hm1, -⟩ := epilogue_ok (R.envOf j0) hs hsv hcb' s hal
  have hev := epilogue_evsIn (R.envOf j0) hs hsv hcb' s hal
  have hplain : ∀ k ∈ Code.kinds (epiLines R.af.saves R.af.frameSize), k = .plainR ∨ k = .plainW := by
    intro k hk
    have hk' : k ∈ Code.kinds (epilogueLines R.af.saves R.af.frameSize) := by
      rw [epilogueLines_epi, Code.kinds_append]; exact List.mem_append_left _ hk
    rw [Code.kinds_epilogueLines] at hk'
    exact .inl (List.eq_of_mem_replicate hk')
  obtain ⟨hiter, hpc1, -, -⟩ := iterN_steps hR hdrop'
    (fun ln h => by obtain ⟨x, e, hh, -, -⟩ := epiLines_ins _ _ ln h; exact ⟨x, e, hh⟩)
    hst.prog hpc hst.err hsteps
  obtain ⟨herr1, hprog1⟩ := hsteps.err
  have hlat : LinesAt R j0 (epiLines R.af.saves R.af.frameSize) s s1 :=
    ⟨lines_at hdrop', fun x t h => by obtain ⟨x', e, hh, -, -⟩ := epiLines_ins _ _ _ h; cases e; exact hh,
      hst.prog, by rw [hpc]; rfl, hst.err, stepsOk_interOk hsteps hst.err, hsteps.exec⟩
  -- the `ret`
  have hj : R.fa.lines.toList[j0 + (epiLines R.af.saves R.af.frameSize).length]? =
      some (Line.ins .ret none) := by
    have := congrArg (·[(epiLines R.af.saves R.af.frameSize).length]?) hdrop'
    simpa [List.getElem?_drop, RL.L] using this
  obtain ⟨a, ha, hstep⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj rfl
    (by rw [hprog1, hst.prog]) hpc1 (by rw [herr1, hst.err])
  obtain ⟨a', ha', he'⟩ := exec_ret ⟨lineOffset R.fa.lines.toList
    (j0 + (epiLines R.af.saves R.af.frameSize).length), (R.lm[·]?)⟩ s1
  rw [ha] at ha'; cases ha'
  have hfin : iterN R.step ((epiLines R.af.saves R.af.frameSize).length + 1) s =
      Arm.w .PC (xreg 30 s1) s1 := by
    rw [iterN_one_succ, hiter]; exact hstep.trans he'
  -- fp/lr as the prologue left them
  have hbytes := read_mem_bytes_bytes R.topN R.topB s R.sP (hst.fplr hframe)
  obtain ⟨sP, -, hsP, hP16, -⟩ := RL.sP_steps hR hent
  rw [hsP] at hbytes
  have hfplr : Arm.read_mem_bytes 16 (spOf s + BitVec.ofNat 64 R.af.frameSize) s =
      xreg 30 R.s0 ++ xreg 29 R.s0 := by
    rw [hslot, ← htopcb, read_sub (n := 16) (o := clobberBytes R.af.saves) hbytes
      (by simp only [RL.topN]; omega), htopcb]
    exact hP16
  have hstepEvs := step_execLines (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hlat.at_ hlat.hook
    hlat.prog hlat.pc hlat.err hlat.inter hlat.run
  refine ⟨(epiLines R.af.saves R.af.frameSize).length + 1, fun i hi => ?_, ?_⟩
  · by_cases hiL : i < (epiLines R.af.saves R.af.frameSize).length
    · obtain ⟨x, t, a, hli, ha, hdec, -, -⟩ := hstepEvs i hiL
      refine ⟨⟨fun e he => ?_, fun rel rs rn hc => ?_⟩, linesAt_program hR hlat i (by omega), _,
        linesAt_pc hR hlat i (by omega)⟩
      · have hm : e ∈ (segEvs R.step (epiLines R.af.saves R.af.frameSize).length s).flatten :=
          List.mem_flatten.2 ⟨_, stepEvs_mem_segEvs hiL, he⟩
        rw [hlat.seg hR] at hm
        obtain ⟨k, hk, hk'⟩ := hev e hm
        rw [hk', hB]
        exact RL.FK_F (fplr_inF hR hframe k (by simp only [RL.topN]; omega))
      · rw [show R.step = ArmStepX R.X R.H R.fa from rfl, cls_of_decode hdec] at hc
        exact clsOf_ne_stx (noExcl_of_kinds hplain (List.mem_of_getElem? hli) ha) rel rs rn hc
    · have hiE : i = (epiLines R.af.saves R.af.frameSize).length := by omega
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_,
    fun i hi => linesAt_nonRet hR hlat (noRet_epiLines _ _) i (by omega), by omega,
    _, none, hj, by rw [Nat.add_sub_cancel, hiter]; exact hpc1⟩ <;> rw [hfin]
  · rw [Arm.r_of_w_same, hx30, hfplr, BitVec.extractLsb'_append_eq_left, hent.lr]
  · rw [Arm.r_of_w_different (by simp), herr1, hst.err]
  · simp only [spv]
    rw [Arm.r_of_w_different (by simp)]
    show spOf s1 = spv R.s0
    rw [hsp1, hslot, BitVec.sub_add_cancel]
  · rw [Arm.ArmState.mem_w_eq_mem, hm1]
  · rw [Arm.w_program, hprog1]
  · show Arm.r (.GPR 29#5) _ = _
    rw [Arm.r_of_w_different (by simp)]
    show xreg 29 s1 = _
    rw [hx29, hfplr, BitVec.extractLsb'_append_eq_right]

/-! ## Steps of a linked machine -/

/-- **A thread step of `f` is one of `g`** when they agree on the state with every memory. -/
theorem tstep_transfer {P : Policy} {f g : ArmState → ArmState} {x : ArmState} {mon : Mon}
    {l : Lab} {t : ArmState × Mon} (h : ∀ m, f (setMem m x) = g (setMem m x))
    (hs : TStep P f (x, mon) l t) : TStep P g (x, mon) l t := by
  cases hs with
  | @exec _ _ evs hk hag hfp hsucc =>
    have hfp' : Footprint g x evs := fun m hm' => by
      rw [← h m, ← h (applyR evs x.mem)]; exact hfp m hm'
    have hstep := TStep.exec (f := g) (P := P) (mon := mon) hk hag hfp' hsucc
    rw [← h] at hstep
    exact hstep
  | xfail hc hfail herr hsp => exact .xfail hc hfail herr hsp

/-- **One precise step reading the thread's own bytes at private addresses** (`prun_privF`'s
step, for any machine): the machine's state, the label the step's events, no failed store
exclusive, no `relXW`. -/
theorem tstep_priv1 {R : RL} {f : ArmState → ArmState} {x : ArmState} {mon : Mon} {l : Lab}
    {t : ArmState × Mon} (hs : TStep Policy.arm f (x, mon) l t) (hp : ArmPrecise.Precise x l)
    (ho : OkPriv R x l) (hpv : ∀ e ∈ stepEvs x, R.F e.addr) (hx : NoStx x) :
    t.1 = f x ∧ l.evs = stepEvs x ∧ l.xfail = false ∧ ∀ e ∈ l.evs, e.k ≠ .relXW := by
  have hxf : l.xfail = false := by
    cases hs with
    | exec => rfl
    | xfail hc => exact absurd hc (hx _ _ _)
  have hag : Agrees l.evs x.mem := by
    intro e he hRd
    rcases hp with h' | ⟨M, hM⟩
    · rw [hxf] at h'; cases h'
    · have he' := he
      rw [hM, ArmPrecise.stepEvs_setMem] at he'
      obtain ⟨e0, he0, -, ha, -⟩ := mem_reread he'
      exact ho e he hRd (privA_addr.2 (ha ▸ hpv e0 he0))
  have hk : ∀ e ∈ l.evs, e.k ≠ .relXW := by
    cases hs with
    | exec hk' =>
      intro e he hke
      have := hk'.1 e he
      rw [hke] at this
      cases hc : cls x <;> rw [hc] at this <;> simp [Cls.kind, AKind.dir] at this
      exact hx _ _ _ hc
    | xfail => intro e he; exact absurd he List.not_mem_nil
  obtain ⟨h1, h2, -⟩ := tstep_own hs hp hag hxf
  exact ⟨h1, h2, hxf, hk⟩

/-- Runs of a source step relation compose. -/
theorem SRun.append' {C : Type} {S : C → List Ev → C → Prop} :
    ∀ {a b c : C} {tr1 tr2 : List (List Ev)}, SRun S a tr1 b → SRun S b tr2 c →
      SRun S a (tr1 ++ tr2) c
  | _, _, _, _, _, .nil, h2 => h2
  | _, _, _, _, _, .cons h r, h2 => .cons h (SRun.append' r h2)

/-- **The moves at the head of the items, as the allocated code's thread run** (no events). -/
theorem srun_moves {R : RL} {b : Nat} {w : ArmState} :
    ∀ (mvs : List (Loc × Loc)) (its : List RItem) (m : Loc → CV),
      SRun (SrcStep R) (.run ⟨b, mvs.map (fun p => RItem.move p.1 p.2) ++ its, m, w⟩)
        (mvs.map fun _ => []) (.run ⟨b, its, movesM mvs m, w⟩)
  | [], _, _ => .nil
  | _ :: mvs, its, _ => .cons .move (srun_moves mvs its _)

/-- **A step of the allocated code at an instruction without events** is a thread step without
events to the same configuration. -/
theorem srcStep_of_mstep_nil {R : RL} (hcov : ThreadProgress.CoveredCode R) (hX : TlsMemFree R.X)
    {s : ArmState} {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV}
    {w : ArmState} {c' : MConf CV ArmState} (hq : Q R s (OpC b k allocs its m w))
    (hn : ∀ vb i, R.vc.blocks[b]? = some vb → vb.insts[k]? = some i → Code.akinds i = [])
    (hs : MStep R.vc R.sem ckeep R.rf (OpC b k allocs its m w) c') :
    SrcStep R (OpC b k allocs its m w) [] c' := by
  obtain ⟨evs, h⟩ := srcStep_of_mstep_eq hcov hX hq hs
  have he : evs = [] := by
    cases h with
    | op hvb hi hops hevs => rw [hevs]; exact VCodeEvents.cEvs_nil (hn _ _ hvb hi) _ _
  rw [he] at h
  exact h

/-- **The events of a precise step at an `ldar` line** (64 bits, address `x q`): one `acqR`
event of 8 bytes at the address register's value, on every memory. -/
theorem ldar_evs_line {R : RL} (hR : R.Wf) {s : ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.fa.lines.toList[j]? = some (.ins x t))
    (hh : x.hooked = false) (hprog : s.program = R.fb.program R.base)
    (hpc : Arm.r .PC s = R.pcOf j) (herr : Arm.r .ERR s = .None) {p q : Nat}
    (hp : p ≤ 30) (hq : q ≤ 30)
    (hx : ∀ env, x.armFields env = Insn.armFields.exclFields 64 1 1 31 (.x p) (.x q)) (M : Memory) :
    NoStx s ∧ ∃ e, stepEvs (setMem M s) = [e] ∧ e.k = .acqR ∧ e.n = 8 ∧
      e.addr = read_gpr 64 (BitVec.ofNat 5 q) s := by
  obtain ⟨a, ha, -, hev, hdec⟩ := stepEvs_line (X := R.X) (H := R.H) (s := setMem M s) hR.layout
    hR.lm hR.fit hj hh (by rw [setMem_program]; exact hprog) (by rw [r_setMem]; exact hpc)
    (by rw [r_setMem]; exact herr)
  obtain ⟨sz, rn', rt', rfl, hrn, -, hsz⟩ := toArmInst_excl (hx _) ha
  simp only [Reg.encSP, hq, ite_true, pure, Except.pure, Except.ok.injEq] at hrn
  subst hrn
  have hsz' : sz = 3#2 := by rcases hsz with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ <;> first | omega | exact h
  subst hsz'
  have hq31 : BitVec.ofNat 5 q ≠ 31#5 := ofNat5_ne31 (by omega)
  refine ⟨fun rel rs rn h => ?_, ?_⟩
  · have hdec' := hdec
    rw [decodeAt_setMem] at hdec'
    rw [cls_of_decode hdec'] at h
    simp [clsOf, exclCls] at h
  · rw [hev]
    simp only [instEvs, exclEvs, hq31, false_and, ite_false, exclKind,
      show BitVec.ofNat 1 1 = 1#1 from rfl, ite_true]
    refine ⟨_, rfl, rfl, rfl, ?_⟩
    simp only [read_gpr, r_setMem]

end Concurrency.CallSeg

namespace Concurrency.ClifCStepTerm

open Prog ClifThread

/-- **A return to a suspended caller**: the bottom frame's `return` resumes the first caller with
the returned values, without events. -/
theorem cstep_ret_pop {env : Clif.Env} {p : Clif.Program} {s : Clif.State}
    (hb : s.frame.body = []) {xs : List Clif.ValueId} (hT : s.frame.term = .ret xs)
    {vals : List Clif.Val} (hg : s.frame.getMany xs = .ok vals) {u : Unit}
    (hc : Clif.checkTys s!"return values of %{s.frame.func.name}" vals
      (Clif.AbiParam.tys s.frame.func.sig.returns) = .ok u)
    {caller : Clif.Frame} {results : List Clif.ValueId}
    {cs : List (Clif.Frame × List Clif.ValueId)} (hcs : s.callers = (caller, results) :: cs)
    {regs : Clif.Regs} (hr : caller.regs.setMany results vals = some regs) :
    CStep env p (.run s) []
      (.run ⟨{ caller with regs := regs }, cs, (s.mem.free (s.frame.slots.map (·.2))).leave⟩) := by
  refine ⟨⟨by rw [evShape_term hb]; simp, fun _ h => nomatch h⟩, ⟨s.mem.bytes, trivial⟩,
    fun B _ => ⟨.run ⟨{ caller with regs := regs }, cs,
      ClifCStep.withB (s.mem.free (s.frame.slots.map (·.2))).leave B⟩, ?_, rfl⟩⟩
  have hbB : (withBytes s B).frame.body = [] := hb
  rw [Clif.step_term env p _ hbB]
  show res (Clif.stepTerm env p (withBytes s B) s.frame.term) = _
  rw [hT]
  simp only [Clif.stepTerm]
  show res (Clif.StepResult.ofRes (s.frame.getMany xs) _) = _
  rw [hg]
  show res (Clif.returnValues (withBytes s B) vals (withBytes s B).mem) = _
  simp only [Clif.returnValues]
  rw [show (withBytes s B).frame = s.frame from rfl,
    show (withBytes s B).callers = s.callers from rfl, hc, hcs]
  simp only [Clif.StepResult.ofRes_ok, hr, res, withBytes, withB_free, withB_leave]
  rfl

end Concurrency.ClifCStepTerm
