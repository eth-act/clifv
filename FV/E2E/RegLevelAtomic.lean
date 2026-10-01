import FV.E2E.RegLevelJT
import FV.Backend.Proof.LoopRun

/-!
# The LL/SC loops on the machine (M6)

`atomicRmwLoop` is emitted as `l: ldaxr x27, [x25]; …; stlxr w24, …, [x25]; cbnz x24, l`
(`rmwLoopLines`), `atomicCasLoop` as `again: ldaxr x27, [x25]; cmp …; b.ne out;
stlxr w24, x28, [x25]; cbnz x24, again; out:` (`casLoopLines`). Their operands are fixed to
x24–x28 (`ctlInstOk`: int vregs; the checker: the fixed allocations). In the single-threaded Arm
model (`docs/decisions/arm-model.md`) the exclusive store succeeds and writes 0 to w24, so the
`cbnz` back edge is not taken: the machine runs the body once (`LoopRun`), as `csem`'s `loopSem`
does on the world, and falls through to the next item (`realizes_rmwLoop`, `realizes_casLoop`).
The scratch defs (x24, x28) are havocked to the machine's values (`HavocOuts`,
`MInst.keptDefs`). The loop labels take no bytes; a `b` after the `cbnz` cannot jump to the loop
label again (labels are defined once, `labelOffsets`), so `fallthrough` leaves the lines alone.
-/

namespace Backend.Proof

open Backend E2E

/-! ## Fall-through over the loop lines -/

theorem ftStep_keep {ln : Line} {n1 n2 : Option Line} (h1 : ∀ x t, ln ≠ .ins (.b x) t)
    (h2 : ∀ c, ln = .ins c none → c.condTarget? = none ∨ ∀ e, n1 ≠ some (.ins (.b e) none)) :
    ftStep ln n1 n2 = ([ln], 1) := by
  unfold ftStep
  repeat' split
  all_goals simp_all

/-- Lines that are not `b` and not conditional branches pass `fallthrough` unchanged. -/
theorem ftList_prefix : ∀ (P Z : List Line),
    (∀ ln ∈ P, (∀ x t, ln ≠ .ins (.b x) t) ∧ ∀ c, ln = .ins c none → c.condTarget? = none) →
    ftList (P ++ Z) = P ++ ftList Z
  | [], _, _ => rfl
  | ln :: P, Z, h => by
    rw [List.cons_append, ftList_pass (ftStep_keep (h ln (by simp)).1
      (fun c e => .inl ((h ln (by simp)).2 c e))), ftList_prefix P Z (fun x hx => h x (by simp [hx]))]
    rfl

/-- A `cbz`/`b.cond` before a `b`: kept, or inverted over the `b` when the line after the `b`
defines its target. -/
theorem ftStep_ins_cases (c : Insn) (hc : ∀ x, c ≠ .b x) (n1 n2 : Option Line) :
    ftStep (.ins c none) n1 n2 = ([.ins c none], 1) ∨
      ∃ e l, n1 = some (.ins (.b e) none) ∧ n2 = some (.label l) ∧ c.condTarget? = some l ∧
        ftStep (.ins c none) n1 n2 = ([.ins (c.invertTo e) none], 2) := by
  unfold ftStep
  repeat' split
  all_goals simp_all

/-- A label is defined once: two lines defining it with an instruction between them would get
two offsets. -/
theorem label_once {R : RL} (hR : R.Wf) {j0 : Nat} {l : Lbl} {P T : List Line}
    (hd : R.L.drop j0 = .label l :: (P ++ .label l :: T)) {q : Nat} {i : Insn}
    {t : Option Clif.TrapCode} (hq : P[q]? = some (.ins i t)) : False := by
  have hat : ∀ k ln, (Line.label l :: (P ++ .label l :: T))[k]? = some ln → R.L[j0 + k]? = some ln := by
    intro k ln hk
    have := congrArg (·[k]?) hd
    simp only [List.getElem?_drop] at this
    rw [this]; exact hk
  have h0 := hat 0 _ rfl
  have hql : q < P.length := (List.getElem?_eq_some_iff.1 hq).1
  have h1 := hat (1 + P.length) (.label l) (by
    rw [show 1 + P.length = P.length + 1 by omega, List.getElem?_cons_succ,
      List.getElem?_append_right (by omega)]
    simp)
  have h2 := hat (1 + q) (.ins i t) (by
    rw [show 1 + q = q + 1 by omega, List.getElem?_cons_succ, List.getElem?_append_left hql]
    exact hq)
  have e0 := labelOffsets_label hR.lm (show R.fa.lines.toList[j0]? = some (.label l) from h0)
  have e1 := labelOffsets_label hR.lm (show R.fa.lines.toList[j0 + (1 + P.length)]? = some (.label l)
    from h1)
  rw [e0] at e1
  have e := Option.some.inj e1
  have m1 := lineOffset_mono R.fa.lines.toList (show j0 ≤ j0 + (1 + q) by omega)
  have s1 := lineOffset_succ R.fa.lines.toList (j0 + (1 + q)) _ h2
  have m2 := lineOffset_mono R.fa.lines.toList (show j0 + (1 + q) + 1 ≤ j0 + (1 + P.length) by omega)
  simp only [Line.size] at s1
  omega

/-- The lines of an `atomic_rmw` loop pass `fallthrough` unchanged. -/
theorem ftList_rmw {R : RL} (hR : R.Wf) {j0 : Nat} {ty : CTy} (hty : AtomTy ty)
    {op : AtomicRmwLoopOp} {fl : Clif.MemFlags} {l : Lbl} {Z T : List Line}
    (hd : R.L.drop j0 = ftList (rmwLoopLines ty.bits op fl l ++ Z) ++ T) :
    R.L.drop j0 = rmwLoopLines ty.bits op fl l ++ (ftList Z ++ T) := by
  have hb : rmwLoopLines ty.bits op fl l ++ Z =
      (.label l :: rmwLoopBody ty.bits op fl) ++ (.ins (.cbz true true (.x 24) l) none :: Z) := by
    simp [rmwLoopLines]
  have hP : ∀ ln ∈ Line.label l :: rmwLoopBody ty.bits op fl,
      (∀ x t, ln ≠ .ins (.b x) t) ∧ ∀ c, ln = .ins c none → c.condTarget? = none := by
    rcases hty with rfl | rfl | rfl | rfl <;> cases op <;>
      simp (config := {decide := true}) [rmwLoopBody, rmwLoopMid, rmwLoopStored, rmwLoopSext,
        rmwLoopCmp, CTy.bits, Insn.condTarget?]
  rw [hb, ftList_prefix _ _ hP] at hd
  rcases ftStep_ins_cases (.cbz true true (.x 24) l) (fun x h => by cases h) Z[0]? Z[1]? with
    hk | ⟨e, l', h0, h1, hct, hk⟩
  · rw [ftList_pass hk] at hd
    rw [hd]; simp [rmwLoopLines]
  · exfalso
    simp only [Insn.condTarget?, Option.some.injEq] at hct
    subst hct
    obtain ⟨Z', rfl⟩ : ∃ Z', Z = .ins (.b e) none :: .label l :: Z' := by
      rcases Z with _ | ⟨a, _ | ⟨b, Z'⟩⟩ <;> simp at h0 h1
      subst h0 h1; exact ⟨Z', rfl⟩
    rw [ftList_cons, hk] at hd
    simp only [List.drop, List.singleton_append] at hd
    rw [ftList_pass (ftStep_keep (fun x t h => by cases h) (fun c h => by cases h))] at hd
    have hbody : ∃ i t, (rmwLoopBody ty.bits op fl)[0]? = some (.ins i t) :=
      ⟨.ldaxr ty.bits (.x 27) (.x 25), fl.trapCode, by simp [rmwLoopBody]⟩
    obtain ⟨i, t, hi⟩ := hbody
    refine label_once hR (j0 := j0) (l := l) (P := rmwLoopBody ty.bits op fl ++
      [.ins ((Insn.cbz true true (.x 24) l).invertTo e) none]) (T := ftList Z' ++ T)
      (q := 0) (i := i) (t := t) ?_ ?_
    · rw [hd]; simp
    · rw [List.getElem?_append_left (by simp [rmwLoopBody])]; exact hi

/-- The lines of an `atomic_cas` loop pass `fallthrough` unchanged. -/
theorem ftList_cas {ty : CTy} (hty : AtomTy ty) (fl : Clif.MemFlags) (a o : Lbl) (Z : List Line) :
    ftList (casLoopLines ty.bits fl a o ++ Z) = casLoopLines ty.bits fl a o ++ ftList Z := by
  rcases hty with rfl | rfl | rfl | rfl
  all_goals
    simp only [casLoopLines, casLoopHead, casLoopCmp, CTy.bits, List.cons_append, List.nil_append]
    repeat rw [ftList_pass (ftStep_keep (by simp) (by intro c hc; first
      | (exfalso; cases hc; done)
      | exact .inl (by cases hc; rfl)
      | exact .inr (by intro e; simp)))]

/-! ## Straight lines and labels on the machine -/

/-- Instruction lines placed at line `j` run on the machine as `execLines` runs them. -/
theorem run_ins {R : RL} (hR : R.Wf) {j : Nat} {ls T : List Line} {s s' : Arm.ArmState}
    (hd : R.L.drop j = ls ++ T) (hins : ∀ ln ∈ ls, ∃ i t, ln = .ins i t ∧ i.hooked = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (hint : LinesInterOk (R.envOf j) ls s)
    (hrun : execLines (R.envOf j) ls s = some s') :
    iterN R.step ls.length s = s' ∧ Arm.r .PC s' = R.pcOf (j + ls.length) := by
  have hat : ∀ k ln, ls[k]? = some ln → R.fa.lines.toList[j + k]? = some ln := by
    intro k ln hk
    have := congrArg (·[k]?) hd
    simp only [List.getElem?_drop, RL.L] at this
    rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk).1]
    exact hk
  have hins' : ∀ ln ∈ ls, ∃ i t, ln = .ins i t := fun ln h => by
    obtain ⟨i, t, e, -⟩ := hins ln h; exact ⟨i, t, e⟩
  refine ⟨iterN_execLines hR.layout hR.lm hR.fit ls j s s' hat
      (fun i t h => by obtain ⟨i', t', e, hh⟩ := hins _ h; cases e; exact hh)
      hprog (by rw [hpc]; rfl) herr hint hrun, ?_⟩
  rw [execLines_pc hrun, hpc]
  simp only [RL.pcOf, RL.L]
  rw [lineOffset_drop_ins (by simpa [RL.L] using hd) hins', BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

theorem RL.pcOf_succ_label {R : RL} {j : Nat} {l : Lbl} (hj : R.L[j]? = some (.label l)) :
    R.pcOf (j + 1) = R.pcOf j := by
  simp only [RL.pcOf]
  rw [lineOffset_succ _ _ _ hj]
  simp [Line.size]

/-! ## The store after a loop -/

/-- A state that keeps the frame (`FrameKeep`) and the program, with the world `w'`, represents
a store that holds its registers and agrees with the old store elsewhere. -/
theorem stRel_after {R : RL} (hR : R.Wf) {s s' : Arm.ArmState} {m m' : Loc → CV}
    {w w' : Arm.ArmState} (hst : StRel R s m w)
    (hreg : ∀ r, r.allocatable = true → m' (.reg r) = regVal s' r)
    (hoth : ∀ l, (∀ r, l ≠ .reg r) → m' l = m l) (hw : SameWorld R.F s' w')
    (herr : Arm.r .ERR s' = .None) (hprog : s'.program = s.program) (hK : FrameKeep R.F s s') :
    StRel R s' m' w' := by
  have hfr := R.frameOk hR
  refine ⟨fun l hl hL => ?_, hw, herr, by rw [hprog]; exact hst.prog, hK.1.trans hst.sp,
    align_of_sp hK.1 hst.align, fun hframe => ?_,
    code_keep hR.prog0 hst.code fun a ha => hK.2 a (.inr (.inr ha))⟩
  · cases l with
    | reg r => rw [hreg r (hl r rfl)]; rfl
    | stack k c =>
      rw [hoth _ (fun r h => by cases h), hst.store _ hl hL,
        locVal_frame_keep hfr hst.sp hK hL (fun r h => by cases h)]
    | save r =>
      rw [hoth _ (fun r h => by cases h), hst.store _ hl hL,
        locVal_frame_keep hfr hst.sp hK hL (fun r h => by cases h)]
  · rw [← hst.fplr hframe]
    exact read_mem_bytes_congr _ _ (fun k hk => hK.2 _ (fplr_inF hR hframe k hk))

/-! ## `csem` of the loops, taken apart -/

theorem loopSem_inv {F : BitVec 64 → Prop} {ty : CTy} {a : CV} {body : List Line}
    {regs : List Reg} {uses : List CV} {defs : List Reg} {w : Arm.ArmState} {outs : List CV}
    {w' : Arm.ArmState} {c : Ctl} (h : loopSem F ty a body regs uses defs w = some (outs, w', c)) :
    AtomTy ty ∧ Avoids F ty.bytes (lo64 a) ∧
      execLines env0 body ((regs.zip uses).foldl (fun s p => setReg s p.1 p.2) w) = some w' ∧
      outs = defs.map (regVal w') ∧ c = .next := by
  unfold loopSem at h
  split at h
  · rename_i hc
    split at h
    · rename_i t' ht
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨hc.1, hc.2.1, ht, rfl, rfl⟩
      · cases h
    · cases h
  · cases h

theorem regs5 {regs : Array Reg} (h : regs.size = 5) : ∃ a b c d e, regs = #[a, b, c, d, e] := by
  rcases regs with ⟨_ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨a, b, c, d, e, rfl⟩

theorem fixed_reg {c : CheckCtx} {ops : Array Operand} {regs : Array Reg} {o : Operand} {q p : Reg}
    (hloc : ∀ x ∈ (ops.zip (regs.map Loc.reg)).toList, c.locOk x.2 x.1.cls = true ∧
      ∀ r, x.1.con = .fixed r → x.2 = .reg r)
    (hm : (o, Loc.reg q) ∈ (ops.zip (regs.map Loc.reg)).toList) (hc : o.con = .fixed p) : q = p := by
  have := (hloc _ hm).2 p hc
  injection this

/-- A store that holds the machine's values at the loop's def registers `ds` and the old
store's elsewhere agrees with the machine after the loop on the allocatable registers. -/
theorem store_regs {R : RL} {s s' : Arm.ArmState} {m m' : Loc → CV} {w : Arm.ArmState}
    (hst : StRel R s m w) (ds : List Nat) (hds : ∀ n ∈ ds, n < 32)
    (hd : ∀ n ∈ ds, m' (.reg (.x n)) = regVal s' (.x n))
    (ho : ∀ r, (∀ n ∈ ds, r ≠ .x n) → m' (.reg r) = m (.reg r))
    (hfr : ∀ f, f ≠ .PC → (∀ n ∈ ds, f ≠ .GPR (rnum n)) → (∀ g, f ≠ .FLAG g) →
      Arm.r f s' = Arm.r f s) :
    ∀ r, r.allocatable = true → m' (.reg r) = regVal s' r := by
  intro r hr
  by_cases hin : ∃ n ∈ ds, r = .x n
  · obtain ⟨n, hn, rfl⟩ := hin
    exact hd n hn
  · rw [ho r (fun n hn e => hin ⟨n, hn, e⟩), hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial]
    simp only [locVal]
    rcases allocatable_cases hr with ⟨n, rfl, hn, -⟩ | ⟨n, rfl, -⟩
    · simp only [regVal]
      rw [hfr _ (by simp) (fun n' hn' e => by
        injection e with e
        simp only [rnum] at e
        exact hin ⟨n', hn', by rw [(ofNat5_eq_iff (by omega) (hds n' hn')).1 e]⟩) (by simp)]
    · simp only [regVal]
      rw [hfr _ (by simp) (fun n' hn' e => by cases e) (by simp)]

theorem rmwBody_ins {ty : CTy} (hty : AtomTy ty) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags) :
    ∀ ln ∈ rmwLoopBody ty.bits op fl, ∃ i t, ln = .ins i t ∧ i.hooked = false := by
  rcases hty with rfl | rfl | rfl | rfl <;> cases op <;>
    simp (config := {decide := true}) [rmwLoopBody, rmwLoopMid, rmwLoopStored, rmwLoopSext,
      rmwLoopCmp, CTy.bits, Insn.hooked]

/-! ## `atomic_rmw` -/

set_option maxHeartbeats 4000000 in
/-- **An `atomic_rmw` loop on the machine**: from `Q` at an `atomicRmwLoop` item, the machine
runs the loop body once and the `cbnz` falls through (status 0), reaching `Q` at the next item
(the scratch defs havocked to the machine's values). -/
theorem realizes_rmwLoop {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {c' : MConf CV Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {ty : CTy}
    {op : AtomicRmwLoopOp} {fl : Clif.MemFlags} {ra ro rd r1 r2 : Reg}
    (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.atomicRmwLoop ty op fl ra ro rd r1 r2))
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c') :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' := by
  have hck := (lowerRFunc_ok hR.alloc).2.2.2
  have hok := ctlCheck_inst hck hvb hi
  simp only [ctlInstOk, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hok
  obtain ⟨va, rfl⟩ := isVregInt_iff h0
  obtain ⟨vo, rfl⟩ := isVregInt_iff h1
  obtain ⟨vd, rfl⟩ := isVregInt_iff h2
  obtain ⟨v1, rfl⟩ := isVregInt_iff h3
  obtain ⟨v2, rfl⟩ := isVregInt_iff h4
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, rfl, hit, hsplit,
    hasg, hc1', hops, hstat, hchk', hc2, hl1, hl2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
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
  have hl1' := codeLinesE_single hl1
  simp only [MInst.lines, bne_self_eq_false, Bool.or_false, Bool.and_false, Bool.false_eq_true,
    ite_false, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1'
  obtain ⟨rfl, rfl⟩ := hl1'
  -- the step of the allocated code
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
  simp only [RL.sem, csem, herrw, ite_true] at hsem
  obtain ⟨hty, hav, hrunw, rfl, rfl⟩ := loopSem_inv hsem
  simp only [List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, setReg_x,
    lo64_regVal_x, rnum] at hrunw hav
  have hsw0 : SameWorld R.F s (Arm.w (.GPR 26#5) (Arm.r (.GPR 26#5) s)
      (Arm.w (.GPR 25#5) (Arm.r (.GPR 25#5) s) w)) :=
    SameWorld.w_right (by simp [Masked]) (SameWorld.w_right (by simp [Masked]) hst.world)
  have h25 : Arm.r (.GPR 25#5) s = Arm.r (.GPR 25#5) (Arm.w (.GPR 26#5) (Arm.r (.GPR 26#5) s)
      (Arm.w (.GPR 25#5) (Arm.r (.GPR 25#5) s) w)) := by simp
  have h26 : Arm.r (.GPR 26#5) s = Arm.r (.GPR 26#5) (Arm.w (.GPR 26#5) (Arm.r (.GPR 26#5) s)
      (Arm.w (.GPR 25#5) (Arm.r (.GPR 25#5) s) w)) := by simp
  have hav' := hav
  rw [h25] at hav'
  -- the machine's run of the body, and its agreement with `csem`'s
  obtain ⟨s1, hrun1, hint1, -, h24, hfr1, hmem1, hprog1⟩ :=
    rmwBody_spec hty op fl (R.envOf (j0 + 1)) s hst.err
  obtain ⟨hsw1, h27⟩ := rmwBody_congr hty op fl (R.envOf (j0 + 1)) env0 hsw0 h25 h26 hav' hrun1 hrunw
  -- the lines
  have hdrop' := ftList_rmw hR hty hdrop
  have hL0 : R.L[j0]? = some (.label (.loop ps1.aloop)) := by
    have := congrArg (·[0]?) hdrop'
    simpa [List.getElem?_drop, rmwLoopLines] using this
  have hd1 : R.L.drop (j0 + 1) = rmwLoopBody ty.bits op fl ++
      (.ins (.cbz true true (.x 24) (.loop ps1.aloop)) none :: (ftList (ls2 ++ nxtOf R.af b) ++ T)) := by
    rw [← List.drop_drop, hdrop']; simp [rmwLoopLines]
  have hpc1 : Arm.r .PC s = R.pcOf (j0 + 1) := by rw [hpc, RL.pcOf_succ_label hL0]
  obtain ⟨hit1, hpcs1⟩ := run_ins hR hd1 (rmwBody_ins hty op fl) hst.prog hpc1 hst.err hint1 hrun1
  have herr1 : Arm.r .ERR s1 = .None := by
    rw [hfr1 .ERR (by simp) (by simp) (by simp)]; exact hst.err
  have hprog1' : s1.program = R.fb.program R.base := by rw [hprog1]; exact hst.prog
  have hLc : R.L[j0 + 1 + (rmwLoopBody ty.bits op fl).length]? =
      some (.ins (.cbz true true (.x 24) (.loop ps1.aloop)) none) := by
    have := congrArg (·[(rmwLoopBody ty.bits op fl).length]?) hd1
    simp only [List.getElem?_drop] at this
    rw [this]; simp
  obtain ⟨a, jl, ha, -, hstep⟩ := step_branch hR hLc (.inr (.inr (.inl ⟨true, true, .x 24, rfl⟩)))
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
  -- the step with the machine's scratch values, and `Q` at the next item
  have hfr2 : ∀ f, f ≠ .PC → (∀ n ∈ [27, 24, 28], f ≠ .GPR (rnum n)) → (∀ g, f ≠ .FLAG g) →
      Arm.r f (Arm.w .PC (R.pcOf (j0 + 1 + (rmwLoopBody ty.bits op fl).length + 1)) s1) =
        Arm.r f s := by
    intro f h1 h2 h3
    rw [Arm.r_of_w_different h1]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, rnum] at h2
    exact hfr1 f h1 (by simp [h2.1, h2.2.1, h2.2.2]) h3
  refine ⟨(rmwLoopBody ty.bits op fl).length + 1, _,
    MStep.op (outs' := [regVal (Arm.w .PC (R.pcOf (j0 + 1 + (rmwLoopBody ty.bits op fl).length + 1)) s1) (.x 27),
      regVal (Arm.w .PC (R.pcOf (j0 + 1 + (rmwLoopBody ty.bits op fl).length + 1)) s1) (.x 24),
      regVal (Arm.w .PC (R.pcOf (j0 + 1 + (rmwLoopBody ty.bits op fl).length + 1)) s1) (.x 28)])
      (m2 := m) hvb hi hops hsz' hsem0 hlen ⟨by simp, fun h => by simp [MInst.keptDefs] at h,
        fun n h => ?_⟩ ?_ (MNext.next hk), ?_⟩
  · simp only [MInst.keptDefs, Option.some.injEq] at h
    subst h
    simp [regVal, rnum, h27]
  · refine ⟨fun l _ => ?_, fun c hc => by simp [MInst.clobbers] at hc⟩
    simp [writeM, Operand.isDef, Operand.isEarly]
  rw [hiter]
  refine ⟨j0 + (rmwLoopLines ty.bits op fl (.loop ps1.aloop)).length, vb, items,
    pre ++ [.op k (#[Reg.x 25, .x 26, .x 27, .x 24, .x 28].map Loc.reg)], c2, ls2, _, ps2, T,
    hvb, hit, by rw [hsplit]; simp, hchk', hc2, hl2, htr, ?_, ?_, ?_⟩
  · rw [← List.drop_drop, hdrop', List.drop_left]
  · simp only [Arm.r_of_w_same]
    congr 1
    simp [rmwLoopLines]; omega
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
      rw [← e]; exact ha

end Backend.Proof

