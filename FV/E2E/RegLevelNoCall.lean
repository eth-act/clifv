module

public import FV.E2E.RegLevelGoodX

@[expose] public section

/-!
# Call states of an activation's run (SEM1 #537, step 2k)

`RL.CallSt R u`: the pc of `u` is a call line (`bl`/`blr`) of the activation (`CallPc`).
`RL.NoCallAt R u` is its negation, `RL.GoodXN` is `GoodX` with `NoCallAt`. The `realizes_*N`
variants (files `*N.lean`, docs/plans/uninit.md §5.5) state `GoodXN` at every state of a segment
of a non-call item and, for a `call`/`try_call`, exactly one `CallSt` state. Every `bl`/`blr` is
hooked (`Insn.not_call_of_hooked`), so an unhooked line is no call line (`RL.noCallAt_of_line`).
-/

namespace Backend.Proof

open Backend E2E

/-- **`u` is at a call line** (`bl`, `blr`) of the activation. -/
def RL.CallSt (R : RL) (u : Arm.ArmState) : Prop := CallPc R.fa R.base (Arm.r .PC u)

/-- **`u` is at no call line** of the activation. -/
def RL.NoCallAt (R : RL) (u : Arm.ArmState) : Prop := ¬ R.CallSt u

/-- **The per-state facts with no call** (non-call items' segments). -/
def RL.GoodXN (R : RL) (u : Arm.ArmState) : Prop := R.GoodX u ∧ R.NoCallAt u

theorem RL.callSt_iff {R : RL} {u : Arm.ArmState} :
    R.CallSt u ↔ ∃ x, R.AtLine u x ∧ ((∃ n, x = .bl n) ∨ ∃ r, x = .blr r) := by
  constructor
  · rintro ⟨j, x, t, hj, hc, hpc⟩
    exact ⟨x, ⟨j, t, hj, hpc⟩, hc⟩
  · rintro ⟨x, ⟨j, t, hj, hpc⟩, hc⟩
    exact ⟨j, x, t, hj, hc, hpc⟩

/-- **At a line that is no `bl`/`blr`, no call state.** -/
theorem RL.noCallAt_of_noCall {R : RL} (hR : R.Wf) {u : Arm.ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    (hx : (∀ n, x ≠ .bl n) ∧ ∀ r, x ≠ .blr r) : R.NoCallAt u := by
  intro hc
  obtain ⟨x', hat, hc⟩ := RL.callSt_iff.1 hc
  rw [RL.atLine_iff hR hj hpc] at hat
  subst hat
  rcases hc with ⟨n, rfl⟩ | ⟨r, rfl⟩
  · exact hx.1 n rfl
  · exact hx.2 r rfl

/-- **At an unhooked line, no call state.** -/
theorem RL.noCallAt_of_line {R : RL} (hR : R.Wf) {u : Arm.ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    (hx : x.hooked = false) : R.NoCallAt u :=
  RL.noCallAt_of_noCall hR hj hpc (Insn.not_call_of_hooked hx)

/-- **At a `bl`/`blr` line, a call state.** -/
theorem RL.callSt_of_line {R : RL} {u : Arm.ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    (hx : (∃ n, x = .bl n) ∨ ∃ r, x = .blr r) : R.CallSt u :=
  RL.callSt_iff.2 ⟨x, ⟨j, t, hj, hpc⟩, hx⟩

/-- `GoodXN` at a `GoodX` state whose line is unhooked. -/
theorem RL.goodXN_of_line {R : RL} (hR : R.Wf) {u : Arm.ArmState} (hg : R.GoodX u) {j : Nat}
    {x : Insn} {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t))
    (hpc : Arm.r .PC u = R.pcOf j) (hx : x.hooked = false) : R.GoodXN u :=
  ⟨hg, RL.noCallAt_of_line hR hj hpc hx⟩

/-- **The states of a straight-line run** of unhooked lines: `GoodXN` (`RL.goodX_execLinesG`). -/
theorem RL.goodXN_execLinesG {R : RL} (hR : R.Wf) {ls : List Line} {j : Nat} {s s' : Arm.ArmState}
    (hat : ∀ k ln, ls[k]? = some ln → R.fa.lines.toList[j + k]? = some ln)
    (hhook : ∀ i t, Line.ins i t ∈ ls → i.hooked = false)
    (htail : ∀ i t, Line.ins i t ∈ ls → i.tlsTail = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (h0 : R.Good s) (hinter : InterOk (R.envOf j) ls s)
    (hrun : execLines (R.envOf j) ls s = some s')
    (hrd : LinesReads (R.envOf j) ls s R.ReadOk) :
    ∀ i < ls.length, R.GoodXN (iterN R.step i s) := by
  intro i hi
  refine ⟨RL.goodX_execLinesG hR hat hhook htail hprog hpc herr h0 hinter hrun hrd i hi, ?_⟩
  have hpcs := iterN_execLines_pc (X := R.X) (H := R.H) hR.layout hR.lm hR.fit ls j s s' hat hhook
    hprog hpc herr hinter hrun
  obtain ⟨ln, hln⟩ : ∃ ln, ls[i]? = some ln := ⟨ls[i], List.getElem?_eq_getElem hi⟩
  have hmem := List.mem_of_getElem? hln
  obtain ⟨x, t, rfl⟩ := execLines_ins hrun _ hmem
  exact RL.noCallAt_of_line hR (hat i _ hln) (hpcs i (by omega)) (hhook x t hmem)

/-- `RL.goodXN_execLinesG` from the body's `sp`. -/
theorem RL.goodXN_execLines {R : RL} (hR : R.Wf) {ls : List Line} {j : Nat} {s s' : Arm.ArmState}
    (hat : ∀ k ln, ls[k]? = some ln → R.fa.lines.toList[j + k]? = some ln)
    (hhook : ∀ i t, Line.ins i t ∈ ls → i.hooked = false)
    (htail : ∀ i t, Line.ins i t ∈ ls → i.tlsTail = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (hsp : spOf s = R.spB) (hinter : InterOk (R.envOf j) ls s)
    (hrun : execLines (R.envOf j) ls s = some s')
    (hrd : LinesReads (R.envOf j) ls s R.ReadOk) :
    ∀ i < ls.length, R.GoodXN (iterN R.step i s) :=
  RL.goodXN_execLinesG hR hat hhook htail hprog hpc herr (.inr hsp) hinter hrun hrd

end Backend.Proof
