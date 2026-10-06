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
    {op : AtomicRmwLoopOp} {fl : Clif.MemFlags} {l : Lbl} (hl : ∃ n, l = .loop n) {Z T : List Line}
    (hd : R.L.drop j0 = relaxLines R.far (ftList (rmwLoopLines ty.bits op fl l ++ Z)) ++ T) :
    R.L.drop j0 = rmwLoopLines ty.bits op fl l ++ (relaxLines R.far (ftList Z) ++ T) := by
  have hb : rmwLoopLines ty.bits op fl l ++ Z =
      (.label l :: rmwLoopBody ty.bits op fl) ++ (.ins (.cbz true true (.x 24) l) none :: Z) := by
    simp [rmwLoopLines]
  have hP : ∀ ln ∈ Line.label l :: rmwLoopBody ty.bits op fl,
      (∀ x t, ln ≠ .ins (.b x) t) ∧ ∀ c, ln = .ins c none → c.condTarget? = none := by
    rcases hty with rfl | rfl | rfl | rfl <;> cases op <;>
      simp (config := {decide := true}) [rmwLoopBody, rmwLoopMid, rmwLoopStored, rmwLoopSext,
        rmwLoopCmp, CTy.bits, Insn.condTarget?]
  have hPn : relaxLines R.far (Line.label l :: rmwLoopBody ty.bits op fl) =
      Line.label l :: rmwLoopBody ty.bits op fl :=
    relaxLines_of_none fun ln h => relaxable_none (hP ln h).2
  have hcb : ∀ f : Lbl → Bool, relaxLine f (.ins (.cbz true true (.x 24) l) none) =
      [.ins (.cbz true true (.x 24) l) none] := by
    obtain ⟨n, rfl⟩ := hl; intro f; rfl
  rw [hb, ftList_prefix _ _ hP, relaxLines_append, hPn] at hd
  rcases ftStep_ins_cases (.cbz true true (.x 24) l) (fun x h => by cases h) Z[0]? Z[1]? with
    hk | ⟨e, l', h0, h1, hct, hk⟩
  · rw [ftList_pass hk, relaxLines_cons, hcb] at hd
    rw [hd]; simp [rmwLoopLines]
  · exfalso
    simp only [Insn.condTarget?, Option.some.injEq] at hct
    subst hct
    obtain ⟨Z', rfl⟩ : ∃ Z', Z = .ins (.b e) none :: .label l :: Z' := by
      rcases Z with _ | ⟨a, _ | ⟨b, Z'⟩⟩ <;> simp at h0 h1
      subst h0 h1; exact ⟨Z', rfl⟩
    rw [ftList_cons, hk] at hd
    simp only [List.drop, List.singleton_append] at hd
    rw [ftList_pass (ftStep_keep (fun x t h => by cases h) (fun c h => by cases h)), relaxLines_cons,
      relaxLines_cons, relaxLine_label] at hd
    have hbody : ∃ i t, (rmwLoopBody ty.bits op fl)[0]? = some (.ins i t) :=
      ⟨.ldaxr ty.bits (.x 27) (.x 25), fl.trapCode, by simp [rmwLoopBody]⟩
    obtain ⟨i, t, hi⟩ := hbody
    refine label_once hR (j0 := j0) (l := l) (P := rmwLoopBody ty.bits op fl ++
      relaxLine R.far (.ins ((Insn.cbz true true (.x 24) l).invertTo e) none))
      (T := relaxLines R.far (ftList Z') ++ T)
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
    iterN R.step ls.length s = s' ∧ Arm.r .PC s' = R.pcOf (j + ls.length) ∧
      ∀ i, 0 < i → i ≤ ls.length → R.Good (iterN R.step i s) := by
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
      hprog (by rw [hpc]; rfl) herr hint hrun, ?_,
    R.good_execLines hR hat (fun i t h => by obtain ⟨i', t', e, hh⟩ := hins _ h; cases e; exact hh)
      hprog hpc herr hint hrun⟩
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
    (herr : Arm.r .ERR s' = .None) (hprog : s'.program = s.program) (hK : FrameKeep R.FK s s') :
    StRel R s' m' w' := by
  have hfr := R.frameOkK hR
  refine ⟨fun l hl hL => ?_, hw, herr, by rw [hprog]; exact hst.prog, hK.1.trans hst.sp,
    align_of_sp hK.1 hst.align, fun hframe => ?_,
    code_keep hR.prog0 hst.code fun a ha => hK.2 a (.inl (.inr (.inr ha))),
    fun a ha => (hK.2 a (.inr ha)).trans (hst.gkeep a ha)⟩
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
      outs = (defs.take 1).map (regVal w') ++ (defs.drop 1).map (fun _ => ofX 0) ∧ c = .next := by
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
      Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.Good (iterN R.step i s) := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
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
  simp only [RL.sem, csemV, csem, herrw, ite_true] at hsem
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
  have hdrop' := ftList_rmw hR hty ⟨_, rfl⟩ hdrop
  have hL0 : R.L[j0]? = some (.label (.loop ps1.aloop)) := by
    have := congrArg (·[0]?) hdrop'
    simpa [List.getElem?_drop, rmwLoopLines] using this
  have hd1 : R.L.drop (j0 + 1) = rmwLoopBody ty.bits op fl ++
      (.ins (.cbz true true (.x 24) (.loop ps1.aloop)) none :: (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T)) := by
    rw [← List.drop_drop, hdrop']; simp [rmwLoopLines]
  have hpc1 : Arm.r .PC s = R.pcOf (j0 + 1) := by rw [hpc, RL.pcOf_succ_label hL0]
  obtain ⟨hit1, hpcs1, hgood1⟩ := run_ins hR hd1 (rmwBody_ins hty op fl) hst.prog hpc1 hst.err hint1 hrun1
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
      (m2 := m) hvb hi hops hsz' hsem0 hlen ⟨by simp, fun h => by simp [havocFrom, MInst.keptDefs] at h,
        fun n h => ?_⟩ ?_ (MNext.next hk), ?_, fun i hi => ?_⟩
  · simp only [havocFrom, MInst.keptDefs, Option.some.injEq] at h
    subst h
    simp [regVal, rnum, h27]
  rotate_right
  · rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact RL.good_of_sp hst.sp
    · exact hgood1 i hi0 (by omega)
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
      rw [← e]; exact RL.FK_F ha

/-! ## `atomic_cas` -/

theorem casHead_ins (bits : Nat) (fl : Clif.MemFlags) :
    ∀ ln ∈ casLoopHead bits fl, ∃ i t, ln = .ins i t ∧ i.hooked = false := by
  intro ln hln
  simp only [casLoopHead, List.mem_cons, List.not_mem_nil, or_false] at hln
  rcases hln with rfl | rfl
  · exact ⟨_, _, rfl, rfl⟩
  · refine ⟨_, _, rfl, ?_⟩
    unfold casLoopCmp; split <;> rfl

set_option maxHeartbeats 8000000 in
/-- **An `atomic_cas` loop on the machine**: from `Q` at an `atomicCasLoop` item, the machine
runs the head; if the values differ, `b.ne` jumps to the exit label, else the `stlxr` stores and
the `cbnz` falls through (status 0); it reaches `Q` at the next item (the scratch def havocked
to the machine's value). -/
theorem realizes_casLoop {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {c' : MConf CV Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {ty : CTy}
    {fl : Clif.MemFlags} {ra re rx rd r1 : Reg}
    (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.atomicCasLoop ty fl ra re rx rd r1))
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c') :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.Good (iterN R.step i s) := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  have hok := ctlCheck_inst hck hvb hi
  simp only [ctlInstOk, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hok
  obtain ⟨va, rfl⟩ := isVregInt_iff h0
  obtain ⟨ve, rfl⟩ := isVregInt_iff h1
  obtain ⟨vx, rfl⟩ := isVregInt_iff h2
  obtain ⟨vd, rfl⟩ := isVregInt_iff h3
  obtain ⟨v1, rfl⟩ := isVregInt_iff h4
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, rfl, hit, hsplit,
    hasg, hc1', hops, hstat, hchk', hc2, hl1, hl2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  have hops' : ops = #[⟨va, .int, .use, .early, .fixed (.x 25)⟩, ⟨ve, .int, .use, .early, .fixed (.x 26)⟩,
      ⟨vx, .int, .use, .early, .fixed (.x 28)⟩, ⟨vd, .int, .def, .late, .fixed (.x 27)⟩,
      ⟨v1, .int, .def, .late, .fixed (.x 24)⟩] := by
    have e : (MInst.atomicCasLoop ty fl (.vreg va .int) (.vreg ve .int) (.vreg vx .int)
        (.vreg vd .int) (.vreg v1 .int)).operands =
        .ok #[⟨va, .int, .use, .early, .fixed (.x 25)⟩, ⟨ve, .int, .use, .early, .fixed (.x 26)⟩,
          ⟨vx, .int, .use, .early, .fixed (.x 28)⟩, ⟨vd, .int, .def, .late, .fixed (.x 27)⟩,
          ⟨v1, .int, .def, .late, .fixed (.x 24)⟩] := rfl
    rw [e] at hops; injection hops with h; exact h.symm
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
  have hl1' := codeLinesE_single hl1
  simp only [MInst.lines, bne_self_eq_false, Bool.or_false, Bool.false_eq_true,
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
  have hsw0 : SameWorld R.F s (Arm.w (.GPR 28#5) (Arm.r (.GPR 28#5) s) (Arm.w (.GPR 26#5)
      (Arm.r (.GPR 26#5) s) (Arm.w (.GPR 25#5) (Arm.r (.GPR 25#5) s) w))) :=
    SameWorld.w_right (by simp [Masked]) (SameWorld.w_right (by simp [Masked])
      (SameWorld.w_right (by simp [Masked]) hst.world))
  have h25 : Arm.r (.GPR 25#5) s = Arm.r (.GPR 25#5) (Arm.w (.GPR 28#5) (Arm.r (.GPR 28#5) s)
      (Arm.w (.GPR 26#5) (Arm.r (.GPR 26#5) s) (Arm.w (.GPR 25#5) (Arm.r (.GPR 25#5) s) w))) := by simp
  have h26 : Arm.r (.GPR 26#5) s = Arm.r (.GPR 26#5) (Arm.w (.GPR 28#5) (Arm.r (.GPR 28#5) s)
      (Arm.w (.GPR 26#5) (Arm.r (.GPR 26#5) s) (Arm.w (.GPR 25#5) (Arm.r (.GPR 25#5) s) w))) := by simp
  have h28 : Arm.r (.GPR 28#5) s = Arm.r (.GPR 28#5) (Arm.w (.GPR 28#5) (Arm.r (.GPR 28#5) s)
      (Arm.w (.GPR 26#5) (Arm.r (.GPR 26#5) s) (Arm.w (.GPR 25#5) (Arm.r (.GPR 25#5) s) w))) := by simp
  have hav' := hav
  rw [h25] at hav'
  -- the head, on the machine and in `csem`
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
  -- the lines
  have hdrop' : R.L.drop j0 = casLoopLines ty.bits fl (.loop ps1.aloop) (.loop (ps1.aloop + 1)) ++
      (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T) := by
    rw [hdrop, ftList_cas hty, relaxLines_append, relaxLines_loop (by
      rcases hty with rfl | rfl | rfl | rfl <;>
        simp (config := {decide := true}) [casLoopLines, casLoopHead, casLoopCmp, Insn.condTarget?,
          CTy.bits]), List.append_assoc]
  have hat : ∀ q ln, (casLoopLines ty.bits fl (.loop ps1.aloop) (.loop (ps1.aloop + 1)))[q]? = some ln →
      R.L[j0 + q]? = some ln := by
    intro q ln hq
    have := congrArg (·[q]?) hdrop'
    simp only [List.getElem?_drop] at this
    rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hq).1]; exact hq
  have hL0 : R.L[j0]? = some (.label (.loop ps1.aloop)) := hat 0 _ rfl
  have hL3 : R.L[j0 + 3]? = some (.ins (.bcond .ne (.loop (ps1.aloop + 1))) none) := hat 3 _ rfl
  have hL4 : R.L[j0 + 4]? = some (.ins (.stlxr ty.bits (.x 24) (.x 28) (.x 25)) fl.trapCode) :=
    hat 4 _ rfl
  have hL5 : R.L[j0 + 5]? = some (.ins (.cbz true true (.x 24) (.loop ps1.aloop)) none) := hat 5 _ rfl
  have hL6 : R.L[j0 + 6]? = some (.label (.loop (ps1.aloop + 1))) := hat 6 _ rfl
  have hd1 : R.L.drop (j0 + 1) = casLoopHead ty.bits fl ++
      (.ins (.bcond .ne (.loop (ps1.aloop + 1))) none ::
        .ins (.stlxr ty.bits (.x 24) (.x 28) (.x 25)) fl.trapCode ::
        .ins (.cbz true true (.x 24) (.loop ps1.aloop)) none :: .label (.loop (ps1.aloop + 1)) ::
        (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T)) := by
    rw [← List.drop_drop, hdrop']; simp [casLoopLines, casLoopHead]
  have hpc1 : Arm.r .PC s = R.pcOf (j0 + 1) := by rw [hpc, RL.pcOf_succ_label hL0]
  obtain ⟨hit1, hpcs1, hgood1⟩ := run_ins hR hd1 (casHead_ins _ fl) hst.prog hpc1 hst.err hint1 hrun1
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
  -- `Q` at the next item, from a machine state after the loop
  have fin : ∀ (sF : Arm.ArmState) (nst : Nat), iterN R.step nst s = sF →
      Arm.r .PC sF = R.pcOf (j0 + 7) → SameWorld R.F sF w' →
      [regVal sF (.x 27)] = outs.take 1 → outs.length = 2 →
      (∀ f, f ≠ .PC → (∀ n ∈ [27, 24], f ≠ .GPR (rnum n)) → (∀ g, f ≠ .FLAG g) →
        Arm.r f sF = Arm.r f s) →
      (∀ a, R.F a → sF.mem a = s.mem a) → sF.program = s.program → ctl = .next →
      (∀ i < nst, R.Good (iterN R.step i s)) →
      ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k
          (#[Reg.x 25, .x 26, .x 28, .x 27, .x 24].map Loc.reg) :: its, m, w⟩) c'' ∧
        Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.Good (iterN R.step i s) := by
    intro sF nst hitF hpcF hswF h27F hlen2 hfrF hmemF hprogF hctl hgoodF
    subst hctl
    have hk : k + 1 < vb.insts.size := by
      cases hn with
      | next hk => exact hk
    refine ⟨nst, _, MStep.op (outs' := [regVal sF (.x 27), regVal sF (.x 24)]) (m2 := m) hvb hi hops
      hsz' hsem0 hlen ⟨by simp [hlen2], fun h => by simp [havocFrom, MInst.keptDefs] at h, fun n h => ?_⟩ ?_
      (MNext.next hk), ?_, hgoodF⟩
    · simp only [havocFrom, MInst.keptDefs, Option.some.injEq] at h
      subst h
      simpa using h27F
    · refine ⟨fun l _ => ?_, fun c hc => by simp [MInst.clobbers] at hc⟩
      simp [writeM, Operand.isDef, Operand.isEarly]
    rw [hitF]
    refine ⟨j0 + 7, vb, items, pre ++ [.op k (#[Reg.x 25, .x 26, .x 28, .x 27, .x 24].map Loc.reg)],
      c2, ls2, _, ps2, T, hvb, hit, by rw [hsplit]; simp, hchk', hc2, hl2, htr, ?_, hpcF, ?_⟩
    · rw [← List.drop_drop, hdrop']
      exact List.drop_left' (by simp [casLoopLines, casLoopHead])
    · refine stRel_after hR hst ?_ ?_ hswF ?_ hprogF ⟨?_, fun a ha => hmemF a (RL.FK_F ha)⟩
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
  have hfr1' : ∀ f, f ≠ .PC → (∀ n ∈ [27, 24], f ≠ .GPR (rnum n)) → (∀ g, f ≠ .FLAG g) →
      Arm.r f s1 = Arm.r f s := by
    intro f h1 h2 h3
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, rnum] at h2
    exact hfr1 f h1 (by simp [h2.1]) h3
  by_cases hc : Arm.ConditionHolds Cond.ne.bits t1 = true
  · -- the values differ: `b.ne` to the exit
    rw [if_pos hc] at hsem
    simp only [Option.some.injEq, Prod.mk.injEq] at hsem
    obtain ⟨rfl, rfl, rfl⟩ := hsem
    rw [hcond, if_pos hc, hjl'] at hstep
    refine fin (Arm.w .PC (R.pcOf (j0 + 7)) s1) 3 ?_ (by simp) (SameWorld.w_left (by simp [Masked]) hsw1)
      ?_ (by simp) ?_ ?_ (by simp [Arm.w_program, hprog1]) rfl (fun i hi => ?_)
    rotate_right
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact RL.good_of_sp hst.sp
      · exact hgood1 i hi0 (by omega)
    · rw [show 3 = 2 + 1 from rfl, iterN_add, hit1]; simp [iterN, hstep]
    · simp [regVal, rnum, h27]
    · intro f h1 h2 h3; rw [Arm.r_of_w_different h1]; exact hfr1' f h1 h2 h3
    · intro a _; simp [Arm.ArmState.mem_w_eq_mem, hmem1]
  · -- equal values: the `stlxr`, then the `cbnz` falls through
    rw [if_neg hc] at hsem
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
          (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T)) := by
      rw [← List.drop_drop, hdrop']; simp [casLoopLines, casLoopHead]
    obtain ⟨hit3, hpcs3, -⟩ := run_ins hR hd4 (by simp [Insn.hooked])
      (by simp [Arm.w_program, hprog1']) (by simp) herr2
      (fun q h0 h1 => by simp at h1; omega) hrun3
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
    refine fin (Arm.w .PC (R.pcOf (j0 + 7)) s3) 5 ?_ (by simp)
      (SameWorld.w_left (by simp [Masked]) hsw3) ?_ (by simp) ?_ ?_ ?_ rfl (fun i hi => ?_)
    rotate_right
    · have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · exact RL.good_of_sp hst.sp
      · exact hgood1 1 (by omega) (by omega)
      · exact hgood1 2 (by omega) (by omega)
      · rw [show 3 = 2 + 1 from rfl, iterN_add, hit1]
        simp only [iterN]
        rw [hstep]
        exact R.good_succ hR hL3 (fun _ h => Insn.noConfusion h) (fun _ h => Insn.noConfusion h)
          (Arm.r_of_w_same ..)
      · rw [show 4 = 2 + 1 + 1 from rfl, iterN_add, iterN_add, hit1]
        simp only [iterN]
        simp only [List.length_cons, List.length_nil, Nat.zero_add, iterN] at hit3
        rw [hstep, hit3]
        exact R.good_succ hR hL4 (fun _ h => Insn.noConfusion h) (fun _ h => Insn.noConfusion h) hpcs3
    · rw [show 5 = 2 + 1 + 1 + 1 from rfl, iterN_add, iterN_add, iterN_add, hit1]
      simp only [iterN]
      simp only [List.length_cons, List.length_nil, Nat.zero_add, iterN] at hit3
      rw [hstep, hit3, hstep5, hpc7]
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

end Backend.Proof


