import FV.E2E.RegLevelJT

/-!
# Traps on the machine (M6)

A VCode run that halts at `udf code` or at a taken `trapIf _ code` is realised by an Arm run
that stops at a trap site of the function with that code (`TrapAt`): `udf` sits at a trap
site itself (`FnAsm.layout_traps`); a taken `trapIf` branches to its deferred trap label, whose
line in the trap section (`trapLines`) is followed by `udf` with the code.
-/

namespace Backend.Proof

open Backend E2E

theorem trapLines_get : ∀ (ts : List (Lbl × Clif.TrapCode)) (n : Nat) (p : Lbl × Clif.TrapCode),
    ts[n]? = some p → (trapLines ts)[2 * n]? = some (.label p.1) ∧
      (trapLines ts)[2 * n + 1]? = some (.ins (.udf 0xc11f) (some p.2))
  | [], _, _, h => by simp at h
  | q :: ts, 0, p, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [trapLines]
  | q :: ts, n + 1, p, h => by
    simp only [List.getElem?_cons_succ] at h
    have := trapLines_get ts n p h
    simp only [trapLines, List.flatMap_cons] at this ⊢
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, show 2 * n + 2 + 1 = 2 * n + 1 + 2 by omega]
    simpa using this

/-- A `udf` line at the pc is a trap site. -/
theorem trapAt_line {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {code : Clif.TrapCode}
    (hj : R.L[j]? = some (.ins (.udf 0xc11f) (some code))) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) : TrapAt R.fb R.base code s := by
  refine ⟨herr, ⟨lineOffset R.L j, code⟩, ?_, rfl, hpc⟩
  exact ((FnAsm.layout_traps hR.layout).2 _).mpr ⟨j, _, hj, rfl⟩

/-- `udf` on the machine: the error is set, the pc and the program are kept. -/
theorem exec_udf_insn (env : Env) (s : Arm.ArmState) :
    ∃ a, (Insn.udf 0xc11f).toArmInst env = .ok a ∧
      Arm.r .ERR (Arm.exec_inst a s) ≠ .None ∧ Arm.r .PC (Arm.exec_inst a s) = Arm.r .PC s ∧
      (Arm.exec_inst a s).program = s.program := by
  refine ⟨_, by simp [csimp_rules, pure, Except.pure]; rfl, ?_⟩
  simp [csimp_rules, Arm.exec_inst, Arm.Reserved.exec_reserved, Arm.Reserved.exec_udf, Arm.w_program]

/-- An error state at a `udf` line stays put: the machine's step at a non-hooked line is
`Arm.stepi`, which leaves an error state unchanged. -/
theorem RL.step_udf_err {R : RL} (hR : R.Wf) {v : Arm.ArmState} {j : Nat}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins (.udf 0xc11f) t))
    (hpc : Arm.r .PC v = R.pcOf j) (hprog : v.program = R.fb.program R.base)
    (herr : Arm.r .ERR v ≠ .None) : R.step v = v := by
  obtain ⟨_, w, hw, hk⟩ := FnAsm.layout_word hR.layout hR.lm hj rfl
  have hne : R.fb.words.toList ≠ [] := by
    intro h
    have : R.fb.words.size = 0 := by simpa using congrArg List.length h
    simp [this] at hk
  have hb : progBase v = R.base := progBase_eq (by rw [hprog]; rfl) hne
  have hsum := layout_sum hR.layout
  have hfit := hR.fit
  have hins : insnAt R.fa (progBase v) (Arm.r .PC v) = some (.udf 0xc11f) := by
    rw [hb, hpc]; exact insnAt_line (by omega) hj
  unfold RL.step ArmStepX
  simp only [hins]
  unfold Arm.stepi
  dsimp only
  split
  · rename_i h; exact absurd h herr
  · rfl

/-- From the step at a `udf` line on, every state errs. -/
theorem RL.udf_stuck {R : RL} (hR : R.Wf) {u : Arm.ArmState} {j : Nat}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins (.udf 0xc11f) t))
    (hpc : Arm.r .PC u = R.pcOf j) (hprog : u.program = R.fb.program R.base)
    (herr : Arm.r .ERR u = .None) : ∀ m, Arm.r .ERR (iterN R.step (m + 1) u) ≠ .None := by
  obtain ⟨a, ha, hst⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj rfl hprog hpc
    herr
  obtain ⟨a', ha', he, hp, hpr⟩ := exec_udf_insn ⟨lineOffset R.fa.lines.toList j, (R.lm[·]?)⟩ u
  rw [ha] at ha'; cases ha'
  have hv : ∀ m, iterN R.step m (R.step u) = R.step u := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [iterN_add]
      simp only [iterN]
      rw [ih]
      exact RL.step_udf_err hR hj (by rw [show R.step u = _ from hst, hp, hpc])
        (by rw [show R.step u = _ from hst, hpr, hprog]) (by rw [show R.step u = _ from hst]; exact he)
  intro m
  rw [show m + 1 = 1 + m by omega, iterN_add]
  simp only [iterN]
  rw [hv m, show R.step u = _ from hst]
  exact he

/-- **`udf` on the machine**: `Q` at a `udf code` item is a trap site with `code`, and every
state after its step errs. -/
theorem trap_udf {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {code : Clif.TrapCode}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.udf code)) :
    TrapAt R.fb R.base code s ∧ ∀ m, Arm.r .ERR (iterN R.step (m + 1) s) ≠ .None := by
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, rfl, hit, hsplit,
    hasg, hc1', hops, hstat, hchk', hc2, h1, h2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  obtain ⟨rfl, rfl⟩ := assign_none (fun f => rfl) hasg
  obtain rfl : c1 = [.inst (.udf code)] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  have hl1 := codeLinesE_single h1
  simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
  obtain ⟨rfl, -⟩ := hl1
  have hZ : ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  rw [ftR_plain_append _ _ _ (by simp [Line.plain]) hZ] at hdrop
  have hj := drop_get (Z := []) (by simpa using hdrop)
  exact ⟨trapAt_line hR hj hpc hst.err, RL.udf_stuck hR hj hpc hst.prog hst.err⟩

/-- **A taken `trapIf` on the machine**: one branch to the deferred trap label, whose next
line is the trap site; every state after the trap site's step errs. -/
theorem trap_trapIf {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {kk : CondBrKind}
    {code : Clif.TrapCode} (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.trapIf kk code)) {ops : Array Operand}
    (hops : (MInst.trapIf kk code).operands = .ok ops)
    (hholds : kk.holds (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = true) :
    ∃ n, TrapAt R.fb R.base code (iterN R.step n s) ∧ (∀ i < n, R.GoodX (iterN R.step i s)) ∧
      ∀ m, Arm.r .ERR (iterN R.step (n + m + 1) s) ≠ .None := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops', rfl, hit, hsplit,
    hasg, hc1', hops', hstat, hchk', hc2, h1, h2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  rw [hops] at hops'; cases hops'
  have hkk : ∀ r sz, kk = .zero r sz ∨ kk = .notZero r sz → r.isVregInt = true := by
    intro r sz hr
    have := ctlCheck_inst hck hvb hi
    rcases hr with rfl | rfl <;> simpa [ctlInstOk] using this
  obtain ⟨k', rfl, hkr⟩ := kind_alloc hkk (mk := fun k => MInst.trapIf k code) rfl
    (fun f => rfl) (fun f => rfl) hops hstat hasg m
  obtain rfl : c1 = [.inst (.trapIf k' code)] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  have hl1 := codeLinesE_single h1
  simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
  obtain ⟨rfl, hpsm⟩ := hl1
  -- the branch (relaxed or not) to the trap label is taken
  have hZ : ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  have hdrop' : R.L.drop j0 = relaxLine R.far (.ins (k'.insn (.trap ps1.traps.size)) none) ++
      (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T) := by
    rw [hdrop, List.singleton_append, ftList_kind_trap k' ps1.traps.size _ hZ, relaxLines_cons,
      List.append_assoc]
  have hform : (∃ c, k'.insn (.trap ps1.traps.size) = .bcond c (.trap ps1.traps.size)) ∨
      (∃ nz w r, k'.insn (.trap ps1.traps.size) = .cbz nz w r (.trap ps1.traps.size)) ∨
      (∃ nz r bit, k'.insn (.trap ps1.traps.size) = .tbz nz r bit (.trap ps1.traps.size)) := by
    cases k' <;> simp [CondBrKind.insn]
  obtain ⟨nst, jl, hnst, hjt, -, -, -, hgx⟩ := reach_rcbX hR hdrop' hform (by simp) true
    (fun env a ha => by rw [kind_brCond hst hkr _ ha, hholds])
    (fun hct env a ha => by rw [kind_brCond_inv hst hkr _ _ hct ha, hholds])
    (by rw [hst.prog]) hpc hst.err hst.sp
  have hjl := hjt rfl
  -- the trap section entry of this trap
  have hpre : psm.traps.toList <+: R.psF.traps.toList :=
    (codeLinesE_traps h2).trans htr
  have hn : R.psF.traps.toList[ps1.traps.size]? = some (.trap ps1.traps.size, code) := by
    obtain ⟨t, ht⟩ := hpre
    rw [← ht, ← hpsm]
    simp
  obtain ⟨body, psF', hb, hL, -⟩ := emit_block hR.emit
  rw [relaxLines_append, relaxLines_trapLines,
    show emitFar ⟨R.fa.k, R.af.slotBase⟩ R.af = R.far from rfl] at hL
  obtain ⟨body', hb'⟩ := hR.psF
  have hk : R.ctx = ⟨R.fa.k, R.af.slotBase⟩ := rfl
  rw [hk, hb] at hb'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hb'
  obtain ⟨-, rfl⟩ := hb'
  obtain ⟨hlab, hudf⟩ := trapLines_get _ _ _ hn
  have hlab' : R.L[(relaxLines R.far (ftList body)).length + 2 * ps1.traps.size]? = some (.label (.trap ps1.traps.size)) := by
    simp only [RL.L, hL]; rw [List.getElem?_append_right (by omega)]; simpa using hlab
  have hudf' : R.L[(relaxLines R.far (ftList body)).length + 2 * ps1.traps.size + 1]? =
      some (.ins (.udf 0xc11f) (some code)) := by
    simp only [RL.L, hL]; rw [List.getElem?_append_right (by omega)]
    simpa [Nat.add_assoc] using hudf
  -- the branch reaches the label's offset, which is the trap site's
  have hoff : R.pcOf jl = R.pcOf ((relaxLines R.far (ftList body)).length + 2 * ps1.traps.size + 1) := by
    have e1 := labelOffsets_label hR.lm hjl
    have e2 := labelOffsets_label hR.lm hlab'
    simp only [RL.pcOf]
    rw [lineOffset_succ _ _ _ hlab']
    simp only [RL.L] at e1 e2 ⊢
    rw [e1] at e2
    simp only [Option.some.injEq] at e2
    rw [e2]; simp [Line.size]
  have hpcF : Arm.r .PC (iterN R.step nst s) =
      R.pcOf ((relaxLines R.far (ftList body)).length + 2 * ps1.traps.size + 1) := by
    rw [hnst, Arm.r_of_w_same, hoff]
  have herrF : Arm.r .ERR (iterN R.step nst s) = .None := by
    rw [hnst, Arm.r_of_w_different (by simp)]; exact hst.err
  have hprogF : (iterN R.step nst s).program = R.fb.program R.base := by
    rw [hnst, Arm.w_program, hst.prog]
  refine ⟨nst, trapAt_line hR hudf' hpcF herrF, hgx, fun m => ?_⟩
  rw [show nst + m + 1 = nst + (m + 1) by omega, iterN_add]
  exact RL.udf_stuck hR hudf' hpcF hprogF herrF m

end Backend.Proof
