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

end Backend.Proof
