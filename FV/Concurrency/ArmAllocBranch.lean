import FV.Concurrency.ArmAllocLoopMem
import FV.E2E.RegLevelGoto
import FV.E2E.EmitLabels

/-!
# Layer 4b with the block-ending branches (T2, #311)

The scope of `ArmAllocLoopMem.arm_alloc_refines_loop` extended by the block-ending branches
(`jump`, `condBr`, `testBitAndBranch`), so that functions with more than one block are covered:

* `reach_bE`, `reach_rcbE`, `reach_cbE`: the machine runs a block's final lines (the emission
  plan's, after `MachBuffer`'s branch simplification, #553) to a line representing the successor
  (`RepL`), with the facts layer 4b needs of the steps (`NoEvSteps`: the branch lines `b`, `b.cond`,
  `cbz`, `tbz` and the relaxation's inverted short branch have no event and are no store
  exclusive); no step only when the final lines are empty, at the line after them;
* **the ranks** (`QR`, `RkC`): a `Q` witness of a configuration has a rank, from the line after
  the segment of the block whose code the machine runs (`segEnd`), the configuration's remaining
  items and the number of forwarding blocks entered without a machine step (`QEd`). The
  realizations without an Arm step decrease it: an item without lines stays in its segment with
  one item less; a removed branch (`MachBuffer` removes a `b` to a label at the next line) goes
  to a block whose label line is after the segment (`qe_entry_rk`); a forwarding block's `jump`
  (`QE.fwd`) enters its successor at the same line, one forwarding step less. A rank bounded by
  the configuration alone does not exist: a forwarding block `st: jump b` whose `b` was removed
  and a block `b: jump st` kept as `b st` give `Q` at `b` (entered through `st`) and at `st` at the
  same state, with the zero-step source steps `b → st → b`. The forwarding steps of a witness are
  bounded by the number of blocks (`qed_short`: the forwarding successors are a function, so a
  longer chain repeats a block, `pigeon`);
* `RConf`, `SrcStepR`, `RelQR`, `DoneR`, `μR`: **layer 4b with branches runs on configurations
  paired with a rank** (`RelQR`: `RelQ` and the rank of a witness at the Arm state); `μR` is the
  rank;
* `realizes_gotoE`: `Backend.Proof.realizes_goto` with these facts and the rank;
* `goto_op(R)`: **the per-item obligation at a branch item** (`OpOutR`, `OpOutNR`);
* `isOut_μR`, `opOutR_of`: the other items' obligations (`OpOutG`, measure `MConf.measure`) with
  the rank: they stay in their block (`SameB`, every step but those of `GotoForm`, `csem_goto`),
  so a step without an Arm step has one item less in the same segment;
* `MemScopeB`, `itemSim_br`: the scope `MemScopeL` with the branches, and its per-item obligation
  with moves, under `OkPriv`;
* **`arm_alloc_refines_br`**: `arm_alloc_refines_loop`'s conclusion for the functions of
  `MemScopeB` (the ranks dropped, `SRun.fst`).
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot ArmPrecise Backend Backend.Proof AllocThread ThreadRefine
  VCodeThread Code VCodeEvents

/-! ## The branch lines on the machine -/

/-- The single-core steps `i < n` from `s` have no event and are no store exclusive. -/
def NoEvSteps (R : RL) (n : Nat) (s : ArmState) : Prop :=
  ∀ i < n, stepEvs (iterN R.step i s) = [] ∧ NoStx (iterN R.step i s)

/-- The branch instructions (any target, the relaxation's `.skip` too). -/
def BrInsn (x : Insn) : Prop :=
  (∃ l, x = .b l) ∨ (∃ c l, x = .bcond c l) ∨ (∃ nz w r l, x = .cbz nz w r l) ∨
    (∃ nz r bit l, x = .tbz nz r bit l)

/-- A branch line: no event, no store exclusive. -/
theorem br_noEv {R : RL} (hR : R.Wf) {j : Nat} {x : Insn} (hj : R.L[j]? = some (.ins x none))
    (hx : BrInsn x) {u : ArmState} (hprog : u.program = R.fb.program R.base)
    (hpc : Arm.r .PC u = R.pcOf j) (herr : Arm.r .ERR u = .None) : stepEvs u = [] ∧ NoStx u := by
  have hh : x.hooked = false ∧ insnKind x = none := by
    rcases hx with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
      exact ⟨rfl, rfl⟩
  exact line_noEv hR hj hh.1 hh.2 hprog hpc herr

theorem brInsn_of {bc : Insn} {t : Lbl}
    (hbc : (∃ c, bc = .bcond c t) ∨ (∃ nz w r, bc = .cbz nz w r t) ∨ (∃ nz r bit, bc = .tbz nz r bit t)) :
    BrInsn bc := by
  rcases hbc with ⟨c, rfl⟩ | ⟨nz, w, r, rfl⟩ | ⟨nz, r, bit, rfl⟩
  · exact .inr (.inl ⟨_, _, rfl⟩)
  · exact .inr (.inr (.inl ⟨_, _, _, _, rfl⟩))
  · exact .inr (.inr (.inr ⟨_, _, _, _, rfl⟩))

/-- A branch instruction is unhooked and not a `ret`. -/
theorem brInsn_hooked {x : Insn} (hx : BrInsn x) : x.hooked = false ∧ x ≠ .ret := by
  rcases hx with ⟨l, rfl⟩ | ⟨c, l, rfl⟩ | ⟨nz, w, r, l, rfl⟩ | ⟨nz, r, bit, l, rfl⟩ <;>
    exact ⟨rfl, by simp⟩

/-- **`reach_rcb` with the steps' facts**, at least one step; every state before the last step is
at an unhooked line other than `ret`. -/
theorem reach_rcbE {R : RL} (hR : R.Wf) {s : ArmState} {j0 : Nat} {bc : Insn} {t : Lbl}
    {T : List Line} (hdrop : R.L.drop j0 = relaxLine R.far (.ins bc none) ++ T)
    (hbc : (∃ c, bc = .bcond c t) ∨ (∃ nz w r, bc = .cbz nz w r t) ∨ (∃ nz r bit, bc = .tbz nz r bit t))
    (ht : t ≠ .skip) (cond : Bool) (hc : ∀ env a, bc.toArmInst env = .ok a → brCond a s = cond)
    (hcs : bc.condTarget? = some t → ∀ env a, (bc.invertTo .skip).toArmInst env = .ok a →
      brCond a s = !cond)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) :
    ∃ n jl, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      (cond = true → R.L[jl]? = some (.label t)) ∧
      (cond = false → jl = j0 + (relaxLine R.far (.ins bc none)).length) ∧
      NoEvSteps R n s ∧ 0 < n ∧ ∀ i < n, AtNonRet R (iterN R.step i s) := by
  have hform : bc = .b t ∨ (∃ c, bc = .bcond c t) ∨ (∃ nz w r, bc = .cbz nz w r t) ∨
      (∃ nz r bit, bc = .tbz nz r bit t) := .inr hbc
  rcases relaxLine_cases R.far bc with h | ⟨t', ht', h⟩
  · rw [h] at hdrop
    have hj := drop_get (Z := []) (by simpa using hdrop)
    obtain ⟨a, jl, ha, hjl, hstep⟩ := step_branch hR hj hform ht hprog hpc herr
    have h1 : NoEvSteps R 1 s := fun i hi => by
      obtain rfl : i = 0 := by omega
      exact br_noEv hR hj (brInsn_of hbc) hprog hpc herr
    have hAT : ∀ i < 1, AtNonRet R (iterN R.step i s) := fun i hi => by
      obtain rfl : i = 0 := by omega
      exact ⟨j0, bc, none, hj, (brInsn_hooked (brInsn_of hbc)).2,
        (brInsn_hooked (brInsn_of hbc)).1, hpc⟩
    rw [hc _ _ ha] at hstep
    cases cond
    · exact ⟨1, j0 + 1, by simp only [iterN]; rw [hstep]; rfl, by simp, by simp [h], h1,
        Nat.one_pos, hAT⟩
    · exact ⟨1, jl, by simp only [iterN]; rw [hstep]; rfl, fun _ => hjl, by simp, h1, Nat.one_pos,
        hAT⟩
  · have hct := relaxTarget_condTarget ht'
    obtain rfl : t' = t := by
      rcases hbc with ⟨c, rfl⟩ | ⟨nz, w, r, rfl⟩ | ⟨nz, r, bit, rfl⟩ <;>
        simp only [Insn.condTarget?] at hct
      · split at hct <;> simp_all
      · simp_all
      · simp_all
    rw [h] at hdrop
    have hj0 := drop_get (Z := [_]) (by simpa using hdrop)
    have hj1 := drop_succ2 hdrop
    obtain ⟨a, ha, hstep⟩ := step_skip hR hj0 hj1 (invertTo_form hbc) hprog hpc herr
    have hn0 := br_noEv hR hj0 (brInsn_of (t := .skip) (invertTo_form hbc)) hprog hpc herr
    have hAT0 : AtNonRet R s := ⟨j0, bc.invertTo .skip, none, hj0,
      (brInsn_hooked (brInsn_of (t := .skip) (invertTo_form hbc))).2,
      (brInsn_hooked (brInsn_of (t := .skip) (invertTo_form hbc))).1, hpc⟩
    rw [hcs hct _ _ ha] at hstep
    cases cond
    · exact ⟨1, j0 + 2, by simp only [iterN]; rw [hstep]; rfl, by simp, by simp [h],
        fun i hi => by
          obtain rfl : i = 0 := by omega
          exact hn0, Nat.one_pos, fun i hi => by
            obtain rfl : i = 0 := by omega
            exact hAT0⟩
    · have hprog1 : (Arm.w .PC (R.pcOf (j0 + 1)) s).program = R.fb.program R.base := by
        rw [Arm.w_program, hprog]
      have herr1 : Arm.r .ERR (Arm.w .PC (R.pcOf (j0 + 1)) s) = .None := by
        rw [Arm.r_of_w_different (by simp), herr]
      obtain ⟨a', jl, ha', hjl, hstep'⟩ := step_branch hR hj1 (.inl rfl) ht hprog1
        (Arm.r_of_w_same ..) herr1
      have hn1 := br_noEv hR hj1 (.inl ⟨_, rfl⟩) hprog1 (Arm.r_of_w_same ..) herr1
      rw [brCond_b ha'] at hstep'
      simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hstep
      refine ⟨2, jl, ?_, fun _ => hjl, by simp, fun i hi => ?_, by omega, fun i hi => ?_⟩
      · simp only [iterN]
        rw [hstep, hstep', Arm.w_of_w_shadow]
        rfl
      · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · exact hn0
        · simp only [iterN]
          rw [hstep]
          exact hn1
      · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · exact hAT0
        · simp only [iterN]
          rw [hstep]
          exact ⟨j0 + 1, .b t', none, hj1, (brInsn_hooked (x := .b t') (.inl ⟨t', rfl⟩)).2,
            (brInsn_hooked (x := .b t') (.inl ⟨t', rfl⟩)).1, Arm.r_of_w_same ..⟩

/-- The state after `n` steps that changed only the pc, then `n'` more, with the steps' facts. -/
theorem reach_thenE {R : RL} {s : ArmState} {n n' : Nat} {v v' : BitVec 64}
    (hn : iterN R.step n s = Arm.w .PC v s)
    (hn' : iterN R.step n' (Arm.w .PC v s) = Arm.w .PC v' (Arm.w .PC v s))
    (he : NoEvSteps R n s) (he' : NoEvSteps R n' (Arm.w .PC v s))
    (ha : ∀ i < n, AtNonRet R (iterN R.step i s))
    (ha' : ∀ i < n', AtNonRet R (iterN R.step i (Arm.w .PC v s))) :
    iterN R.step (n + n') s = Arm.w .PC v' s ∧ NoEvSteps R (n + n') s ∧
      ∀ i < n + n', AtNonRet R (iterN R.step i s) := by
  refine ⟨by rw [iterN_add, hn, hn', Arm.w_of_w_shadow], fun i hi => ?_, fun i hi => ?_⟩
  · rcases Nat.lt_or_ge i n with h | h
    · exact he i h
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [iterN_add, hn]
      exact he' k (by omega)
  · rcases Nat.lt_or_ge i n with h | h
    · exact ha i h
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [iterN_add, hn]
      exact ha' k (by omega)

/-- **A `jump x`'s final lines with the steps' facts** (`reach_jumpX`): the machine reaches a
line representing `x`, by its `b` (no event, no store exclusive, at a line other than `ret`) or
at once when `MachBuffer` removed the branch, at the line after the final lines. The statement
before #553 took the `fallthrough` lines (`ftList`, removed). -/
theorem reach_bE {R : RL} (hR : R.Wf) {s : ArmState} {j0 : Nat} {x : Label}
    {o : List Line} {nxt : Nat}
    (hdrop : R.L.drop j0 = relaxLines R.far o ++ R.L.drop (rix R.far (planLines R.fa.k R.af) nxt))
    (ho : (∃ l', o = [.ins (.b l') none] ∧
        RepLbl (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) x l') ∨
      (o = [] ∧ planRep R.fa.k R.af x nxt = true))
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) :
    ∃ n jl, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      RepL R.af (planOwn R.fa.k R.af) R.L x jl ∧ NoEvSteps R n s ∧
      (n = 0 → jl = rix R.far (planLines R.fa.k R.af) nxt) ∧
      ∀ i < n, AtNonRet R (iterN R.step i s) := by
  rcases ho with ⟨l', rfl, hl⟩ | ⟨rfl, hr⟩
  · obtain ⟨hsk, jl, hjl, hrep⟩ := repLbl_line hR hl
    have hj : R.L[j0]? = some (.ins (.b l') none) := by
      have := congrArg (·[0]?) hdrop
      rw [relaxLines_cons, relaxLine_of_none rfl] at this
      simpa [List.getElem?_drop] using this
    obtain ⟨a, jl', ha, hjl', hstep⟩ := step_branch hR hj (.inl rfl) hsk hprog hpc herr
    obtain rfl : jl' = jl := labelOffsets_uniq hR.lm hjl' hjl
    refine ⟨1, jl', ?_, hrep, fun i hi => ?_, fun h => absurd h (by omega), fun i hi => ?_⟩
    · simp only [iterN]; rw [hstep, brCond_b ha]; rfl
    · obtain rfl : i = 0 := by omega
      exact br_noEv hR hj (.inl ⟨_, rfl⟩) hprog hpc herr
    · obtain rfl : i = 0 := by omega
      exact ⟨j0, .b l', none, hj, (brInsn_hooked (x := .b l') (.inl ⟨l', rfl⟩)).2,
        (brInsn_hooked (x := .b l') (.inl ⟨l', rfl⟩)).1, hpc⟩
  · have hrep := rep_nxt hR hr
    simp only [relaxLines, List.flatMap_nil, List.nil_append] at hdrop
    obtain rfl := drop_idx hdrop hrep.lt
    exact ⟨0, _, by simp only [iterN]; rw [← hpc, Arm.w_irrelevant], hrep, fun i hi => by omega,
      fun _ => rfl, fun i hi => by omega⟩

/-- **A conditional branch's final lines with the steps' facts** (`reach_condX`; `ci` the
branch, whose condition holds iff `cond`): the machine reaches a line representing the successor
`cond` picks; no step only when the final lines are empty, at the line after them. The statement
before #553 took the `fallthrough` lines (`ftList`, removed). -/
theorem reach_cbE {R : RL} (hR : R.Wf) {s : ArmState} {j0 : Nat} {s1 s2 : Label}
    {ci : Insn} {o : List Line} {nxt : Nat}
    (hdrop : R.L.drop j0 = relaxLines R.far o ++ R.L.drop (rix R.far (planLines R.fa.k R.af) nxt))
    (hco : CondOut (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) s1 s2 ci o nxt)
    (hci : (∃ c t, ci = .bcond c t) ∨ (∃ nz w r t, ci = .cbz nz w r t) ∨
      (∃ nz r bit t, ci = .tbz nz r bit t))
    (cond : Bool)
    (hcT : ∀ l env a, (ci.setTarget l).toArmInst env = .ok a → brCond a s = cond)
    (hcF : ci.condTarget?.isSome = true → ∀ l env a, (ci.invertTo l).toArmInst env = .ok a →
      brCond a s = !cond)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j0)
    (herr : Arm.r .ERR s = .None) :
    ∃ n jl, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      RepL R.af (planOwn R.fa.k R.af) R.L (if cond then s1 else s2) jl ∧ NoEvSteps R n s ∧
      (n = 0 → jl = rix R.far (planLines R.fa.k R.af) nxt) ∧
      ∀ i < n, AtNonRet R (iterN R.step i s) := by
  rcases hco with ⟨c, t', e', rfl, hct, rfl, hl1, hl2⟩ | ⟨c, t', rfl, hct, hc⟩ | ⟨rfl, hr1, hr2⟩
  · -- `b.c t'; b e'`
    obtain ⟨hsk1, jt, hjt, hrep1⟩ := repLbl_line hR hl1
    rw [relaxLines_cons, List.append_assoc] at hdrop
    obtain ⟨n, jl, hn, hjT, hjF, hne, hpos, hAt⟩ := reach_rcbE hR hdrop (setTarget_form hci t') hsk1
      cond (hcT t') (fun hct' env a ha => by
        rw [setTarget_invertTo hci] at ha
        exact hcF (condTarget_setTarget_isSome hci hct') _ env a ha) hprog hpc herr
    cases cond
    · -- the fall-through `b e'`
      have hd1 : R.L.drop jl = relaxLines R.far [.ins (.b e') none] ++
          R.L.drop (rix R.far (planLines R.fa.k R.af) nxt) := by
        rw [hjF rfl, ← List.drop_drop, hdrop, List.drop_left]
      have hs1 : (Arm.w .PC (R.pcOf jl) s).program = R.fb.program R.base := by
        rw [Arm.w_program, hprog]
      obtain ⟨n', jl', hn', hrep', hne', -, hAt'⟩ := reach_bE hR hd1 (.inl ⟨e', rfl, hl2⟩) hs1
        (Arm.r_of_w_same ..) (by rw [Arm.r_of_w_different (by simp), herr])
      obtain ⟨hN, hE, hA⟩ := reach_thenE hn hn' hne hne' hAt hAt'
      exact ⟨n + n', jl', hN, by simpa using hrep', hE, fun h => absurd h (by omega), hA⟩
    · obtain rfl : jl = jt := labelOffsets_uniq hR.lm (hjT rfl) hjt
      exact ⟨n, jl, hn, by simpa using hrep1, hne, fun h => absurd h (by omega), hAt⟩
  · -- one branch
    rcases hc with ⟨rfl, hl1, hr2⟩ | ⟨rfl, hl2, hr1⟩
    · obtain ⟨hsk1, jt, hjt, hrep1⟩ := repLbl_line hR hl1
      rw [relaxLines_cons] at hdrop
      simp only [relaxLines, List.flatMap_nil, List.append_nil] at hdrop
      obtain ⟨n, jl, hn, hjT, hjF, hne, hpos, hAt⟩ := reach_rcbE hR hdrop (setTarget_form hci t')
        hsk1 cond (hcT t') (fun hct' env a ha => by
          rw [setTarget_invertTo hci] at ha
          exact hcF (condTarget_setTarget_isSome hci hct') _ env a ha) hprog hpc herr
      cases cond
      · have hrep2 := rep_nxt hR hr2
        have hd : R.L.drop jl = R.L.drop (rix R.far (planLines R.fa.k R.af) nxt) := by
          rw [hjF rfl, ← List.drop_drop, hdrop, List.drop_left]
        obtain rfl := drop_idx hd hrep2.lt
        exact ⟨n, _, hn, by simpa using hrep2, hne, fun h => absurd h (by omega), hAt⟩
      · obtain rfl : jl = jt := labelOffsets_uniq hR.lm (hjT rfl) hjt
        exact ⟨n, jl, hn, by simpa using hrep1, hne, fun h => absurd h (by omega), hAt⟩
    · obtain ⟨hsk2, jt, hjt, hrep2⟩ := repLbl_line hR hl2
      rw [relaxLines_cons] at hdrop
      simp only [relaxLines, List.flatMap_nil, List.append_nil] at hdrop
      obtain ⟨n, jl, hn, hjT, hjF, hne, hpos, hAt⟩ := reach_rcbE hR hdrop (invertTo_form' hci t')
        hsk2 (!cond) (hcF (condTarget_invertTo_isSome hci hct) t') (fun _ env a ha => by
          rw [invertTo_invertTo hci] at ha
          rw [Bool.not_not]
          exact hcT _ env a ha) hprog hpc herr
      cases cond
      · obtain rfl : jl = jt := labelOffsets_uniq hR.lm (hjT rfl) hjt
        exact ⟨n, jl, hn, by simpa using hrep2, hne, fun h => absurd h (by omega), hAt⟩
      · have hrep1 := rep_nxt hR hr1
        have hd : R.L.drop jl = R.L.drop (rix R.far (planLines R.fa.k R.af) nxt) := by
          rw [hjF rfl, ← List.drop_drop, hdrop, List.drop_left]
        obtain rfl := drop_idx hd hrep1.lt
        exact ⟨n, _, hn, by simpa using hrep1, hne, fun h => absurd h (by omega), hAt⟩
  · -- no lines: both successors next
    simp only [relaxLines, List.flatMap_nil, List.nil_append] at hdrop
    have hrep1 := rep_nxt hR hr1
    obtain rfl := drop_idx hdrop hrep1.lt
    refine ⟨0, _, by simp only [iterN]; rw [← hpc, Arm.w_irrelevant], ?_, fun i hi => by omega,
      fun _ => rfl, fun i hi => by omega⟩
    cases cond
    · simpa using rep_nxt hR hr2
    · simpa using hrep1

/-! ## The ranks of the `Q` witnesses -/

/-- The line after block `b`'s segment in the final lines (`segX`; `0` if `b` has none). -/
def segEnd (R : RL) (b : Nat) : Nat :=
  match segX R.fa.k R.af b with
  | some x => rix R.far (planLines R.fa.k R.af) x.2.2
  | none => 0

/-- An upper bound of the blocks' item counts. -/
def itemBound (R : RL) : Nat := (R.rf.blocks.toList.map Array.size).sum + 1

/-- The rank's unit per line: above every item count plus every number of forwarding steps of a
short witness (`qed_short`). -/
def rankK (R : RL) : Nat := itemBound R + R.vc.blocks.size

/-- **The rank of `n` items of block `b`**: the lines from the end of `b`'s segment on, then the
items (`+ 1`: positive). -/
def rk (R : RL) (b n : Nat) : Nat := (R.L.length + 1 - segEnd R b) * rankK R + n + 1

/-- The item count of block `b`. -/
def blkSize (R : RL) (b : Nat) : Nat := (R.rf.blocks[b]?.map Array.size).getD 0

/-- The successor of a forwarding block (`succOf … 0`). -/
def fwdNext (R : RL) (b : Nat) : Nat := (succOf R.vc b 0).getD 0

/-- **Block `b` forwards** (`QE.fwd`'s conditions but the successor's `QE`): its items are one
`op` of its only instruction, a `jump` to `fwdNext b`. -/
def FwdE (R : RL) (b : Nat) : Prop :=
  ∃ vb x items allocs regs i vbx, R.vc.blocks[b]? = some vb ∧ R.af.fwd? vb.label = some x ∧
    R.rf.blocks[b]? = some items ∧ items.toList = [.op 0 allocs] ∧ allocs = regs.map Loc.reg ∧
    vb.insts = #[i] ∧ i.assign regs = .ok (.jump x) ∧ succOf R.vc b 0 = some (fwdNext R b) ∧
    R.vc.blocks[fwdNext R b]? = some vbx ∧ vbx.label = x

/-- **`QE` in `d` forwarding steps**: blocks `b`, `fwdNext b`, … forward (`FwdE`), and `Qs` holds
at the first item of the block reached after `d` steps. -/
def QEd (R : RL) (s : ArmState) (m : Loc → CV) (w : ArmState) (b d : Nat) : Prop :=
  (∀ i < d, FwdE R (iterN (fwdNext R) i b)) ∧
    ∃ items, R.rf.blocks[iterN (fwdNext R) d b]? = some items ∧
      Qs R s (iterN (fwdNext R) d b) items.toList m w

/-- **`Q` with a rank** at the configuration `⟨b, its, m, w⟩`: `Qs` (rank `rk b |its|`), or the
block's entry through `d` forwarding blocks (rank `rk` of the block reached, all its items, plus
`d`). -/
def QR (R : RL) (s : ArmState) (b : Nat) (its : List RItem) (m : Loc → CV) (w : ArmState)
    (r : Nat) : Prop :=
  (Qs R s b its m w ∧ r = rk R b its.length) ∨
    ∃ items d, R.rf.blocks[b]? = some items ∧ its = items.toList ∧ QEd R s m w b d ∧
      r = rk R (iterN (fwdNext R) d b) (blkSize R (iterN (fwdNext R) d b)) + d

/-- **The rank of a configuration at an Arm state** (any store: a return tail relates the
machine to another store, `RetTail`); every rank of a configuration that is not running. -/
def RkC (R : RL) (s : ArmState) : MConf CV ArmState → Nat → Prop
  | .run ⟨b, its, _, w⟩, r => ∃ mt, QR R s b its mt w r
  | _, _ => True

theorem iterN_succ_in {S : Type} (f : S → S) (n : Nat) (s : S) :
    iterN f (n + 1) s = iterN f n (f s) := rfl

theorem fwdNext_of {R : RL} {b bx : Nat} (h : succOf R.vc b 0 = some bx) : fwdNext R b = bx := by
  simp [fwdNext, h]

/-- `QEd` is `QE`. -/
theorem QEd.qe {R : RL} {s : ArmState} {m : Loc → CV} {w : ArmState} :
    ∀ (d : Nat) {b : Nat}, QEd R s m w b d → QE R s m w b
  | 0, b, ⟨_, items, hit, hq⟩ => .std hit hq
  | d + 1, b, ⟨hall, items, hit, hq⟩ => by
    obtain ⟨vb, x, its, allocs, regs, i, vbx, hvb, hx, hits, hil, hal, hins, hasg, hsucc, hvbx,
      hlx⟩ : FwdE R b := hall 0 (by omega)
    exact .fwd hvb hx hits hil hal hins hasg hsucc hvbx hlx
      (QEd.qe d ⟨fun i hi => hall (i + 1) (by omega), items, hit, hq⟩)

/-- `QE` is `QEd` for some number of forwarding steps. -/
theorem QE.qed {R : RL} {s : ArmState} {m : Loc → CV} {w : ArmState} {b : Nat}
    (h : QE R s m w b) : ∃ d, QEd R s m w b d := by
  induction h with
  | std hit hq => exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero _), _, hit, hq⟩
  | @fwd b bx vb vbx x items allocs regs i hvb hx hit hil hal hins hasg hsucc hvbx hlx _ ih =>
    obtain ⟨d, hall, its, hits, hq⟩ := ih
    have hfn := fwdNext_of hsucc
    refine ⟨d + 1, fun k hk => ?_, its, ?_, ?_⟩
    · rcases k with _ | k
      · exact (⟨vb, x, items, allocs, regs, i, vbx, hvb, hx, hit, hil, hal, hins, hasg,
          by rw [hfn]; exact hsucc, by rw [hfn]; exact hvbx, hlx⟩ : FwdE R b)
      · show FwdE R (iterN (fwdNext R) k (fwdNext R b))
        rw [hfn]; exact hall k (by omega)
    · show R.rf.blocks[iterN (fwdNext R) d (fwdNext R b)]? = some its
      rw [hfn]; exact hits
    · show Qs R s (iterN (fwdNext R) d (fwdNext R b)) its.toList m w
      rw [hfn]; exact hq

/-- `Qs` holds for any store the state represents (`StRel` is its only store condition). -/
theorem Qs.store {R : RL} {s : ArmState} {b : Nat} {its : List RItem} {mt m : Loc → CV}
    {w : ArmState} (h : Qs R s b its mt w) (hst : StRel R s m w) : Qs R s b its m w := by
  obtain ⟨j, vb, items, pre, code, X, ps1, psm, ps2, x, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    -, h12, h13⟩ := h
  exact ⟨j, vb, items, pre, code, X, ps1, psm, ps2, x, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    hst, h12, h13⟩

theorem QR.store {R : RL} {s : ArmState} {b : Nat} {its : List RItem} {mt m : Loc → CV}
    {w : ArmState} {r : Nat} (h : QR R s b its mt w r) (hst : StRel R s m w) :
    QR R s b its m w r := by
  rcases h with ⟨hq, hr⟩ | ⟨items, d, hit, hits, ⟨hall, its', hits', hq⟩, hr⟩
  · exact .inl ⟨Qs.store hq hst, hr⟩
  · exact .inr ⟨items, d, hit, hits, ⟨hall, its', hits', Qs.store hq hst⟩, hr⟩

/-- A ranked `Q` is `Q`. -/
theorem QR.q {R : RL} {s : ArmState} {b : Nat} {its : List RItem} {m : Loc → CV}
    {w : ArmState} {r : Nat} (h : QR R s b its m w r) : Q R s (.run ⟨b, its, m, w⟩) := by
  rcases h with ⟨hq, -⟩ | ⟨items, d, hit, hits, hqe, -⟩
  · exact .inl hq
  · exact .inr ⟨items, hit, hits, hqe.qe d⟩

/-- Every `Q` witness has a rank. -/
theorem Q.qr {R : RL} {s : ArmState} {b : Nat} {its : List RItem} {m : Loc → CV}
    {w : ArmState} (h : Q R s (.run ⟨b, its, m, w⟩)) : ∃ r, QR R s b its m w r := by
  rcases h with hq | ⟨items, hit, hits, hqe⟩
  · exact ⟨_, .inl ⟨hq, rfl⟩⟩
  · obtain ⟨d, hd⟩ := QE.qed hqe
    exact ⟨_, .inr ⟨items, d, hit, hits, hd, rfl⟩⟩

theorem RkC.of_q {R : RL} {s : ArmState} {c : MConf CV ArmState} (h : Q R s c) :
    ∃ r, RkC R s c r := by
  match c, h with
  | .run ⟨b, its, m, w⟩, h =>
    obtain ⟨r, hr⟩ := Q.qr h
    exact ⟨r, m, hr⟩
  | .ret .., _ => exact ⟨0, trivial⟩
  | .halt _, _ => exact ⟨0, trivial⟩

theorem RkC.of_relQ {R : RL} {t : ArmState × Mon} {c : MConf CV ArmState} (h : RelQ R t c) :
    ∃ r, RkC R t.1 c r := by
  match c, h with
  | .run ⟨b, its, m, w⟩, h =>
    obtain ⟨mt, hq⟩ := RelQ.q h
    obtain ⟨r, hr⟩ := Q.qr hq
    exact ⟨r, mt, hr⟩
  | .ret .., _ => exact ⟨0, trivial⟩
  | .halt _, _ => exact ⟨0, trivial⟩

theorem rk_pos (R : RL) (b n : Nat) : 0 < rk R b n := by simp only [rk]; omega

theorem QR.pos {R : RL} {s : ArmState} {b : Nat} {its : List RItem} {m : Loc → CV}
    {w : ArmState} {r : Nat} (h : QR R s b its m w r) : 0 < r := by
  rcases h with ⟨-, rfl⟩ | ⟨_, d, _, _, _, rfl⟩
  · exact rk_pos ..
  · have := rk_pos R (iterN (fwdNext R) d b) (blkSize R (iterN (fwdNext R) d b)); omega

/-! ## The block labels are distinct -/

/-- `labelOffsets` defines every label once. -/
theorem labelOffsets_go_nodup : ∀ {L : List Line} {off : Nat} {m0 m : Std.HashMap Lbl Nat},
    labelOffsets.go L off m0 = .ok m →
      (E2E.EmitLabels.defs L).Nodup ∧ ∀ l ∈ E2E.EmitLabels.defs L, m0.contains l = false
  | [], _, _, _, _ => ⟨List.nodup_nil, fun _ h => by simp at h⟩
  | ln :: L, off, m0, m, h => by
    cases ln with
    | label l =>
      simp only [labelOffsets.go] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · rename_i hc
        obtain ⟨ih1, ih2⟩ := labelOffsets_go_nodup h
        have hl : l ∉ E2E.EmitLabels.defs L := fun hm => by
          have := ih2 l hm
          simp [Std.HashMap.contains_insert] at this
        refine ⟨by simpa [E2E.EmitLabels.lineDef] using ⟨hl, ih1⟩, fun x hx => ?_⟩
        simp only [E2E.EmitLabels.defs_cons, E2E.EmitLabels.lineDef, Option.toList_some,
          List.singleton_append, List.mem_cons] at hx
        rcases hx with rfl | hx
        · simpa using hc
        · have := ih2 x hx
          rw [Std.HashMap.contains_insert, Bool.or_eq_false_iff] at this
          exact this.2
    | ins i t =>
      simp only [labelOffsets.go] at h
      simpa [E2E.EmitLabels.lineDef] using labelOffsets_go_nodup h
    | word a b =>
      simp only [labelOffsets.go] at h
      simpa [E2E.EmitLabels.lineDef] using labelOffsets_go_nodup h

theorem nodup_idx {α : Type} {l : List α} (h : l.Nodup) {i j : Nat} {x : α} (hi : l[i]? = some x)
    (hj : l[j]? = some x) : i = j := by
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.1 hi
  obtain ⟨hj', e⟩ := List.getElem?_eq_some_iff.1 hj
  exact (List.Nodup.getElem_inj h).1 e.symm

/-! ## Short forwarding chains -/

/-- **Pigeonhole**: `N + 1` values below `N` repeat. -/
theorem pigeon : ∀ (N : Nat) (f : Nat → Nat), (∀ i ≤ N, f i < N) →
    ∃ a c, a < c ∧ c ≤ N ∧ f a = f c
  | 0, f, h => absurd (h 0 (Nat.le_refl 0)) (Nat.not_lt_zero _)
  | N + 1, f, h => by
    by_cases hc : ∃ a, a ≤ N ∧ f a = f (N + 1)
    · obtain ⟨a, ha, he⟩ := hc
      exact ⟨a, N + 1, by omega, Nat.le_refl _, he⟩
    · have hc' : ∀ a, a ≤ N → f a ≠ f (N + 1) := fun a ha he => hc ⟨a, ha, he⟩
      have hN1 := h (N + 1) (Nat.le_refl _)
      obtain ⟨a, c, hac, hcN, he⟩ := pigeon N (fun i => if f i = N then f (N + 1) else f i)
        (fun i hi => by
          have h1 := h i (by omega)
          have h3 := hc' i hi
          by_cases hfi : f i = N
          · rw [if_pos hfi]; omega
          · rw [if_neg hfi]; omega)
      refine ⟨a, c, hac, by omega, ?_⟩
      have ha' := hc' a (by omega)
      have hc'' := hc' c hcN
      by_cases h1 : f a = N <;> by_cases h2 : f c = N
      · omega
      · rw [if_pos h1, if_neg h2] at he; exact absurd he.symm hc''
      · rw [if_neg h1, if_pos h2] at he; exact absurd he ha'
      · rwa [if_neg h1, if_neg h2] at he

/-- **A short forwarding chain**: `QEd` holds in fewer steps than there are blocks, reaching the
same block. -/
theorem qed_short {R : RL} {s : ArmState} {m : Loc → CV} {w : ArmState} :
    ∀ (d : Nat) {b : Nat}, QEd R s m w b d →
      ∃ d', d' < R.vc.blocks.size ∧ QEd R s m w b d' ∧
        iterN (fwdNext R) d' b = iterN (fwdNext R) d b := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
  intro b hq
  by_cases hd : d < R.vc.blocks.size
  · exact ⟨d, hd, hq, rfl⟩
  obtain ⟨hall, items, hit, hqs⟩ := hq
  have hlt : ∀ i ≤ R.vc.blocks.size, iterN (fwdNext R) i b < R.vc.blocks.size := by
    intro i hi
    rcases Nat.lt_or_ge i d with h | h
    · obtain ⟨vb, -, -, -, -, -, -, hvb, -⟩ := hall i h
      exact (Array.getElem?_eq_some_iff.1 hvb).1
    · obtain rfl : i = d := by omega
      obtain ⟨_, vb, _, _, _, _, _, _, _, _, hvb, -⟩ := hqs
      exact (Array.getElem?_eq_some_iff.1 hvb).1
  obtain ⟨a, c, hac, hcN, he⟩ := pigeon _ _ hlt
  have hcd : c ≤ d := by omega
  -- the chain repeats between `a` and `c`: drop that loop
  have hshift : iterN (fwdNext R) (d - (c - a)) b = iterN (fwdNext R) d b := by
    have e1 : d - (c - a) = a + (d - c) := by omega
    have e2 : d = c + (d - c) := by omega
    rw [e1, iterN_add, he, ← iterN_add, ← e2]
  obtain ⟨d', hd', hq', he'⟩ := ih (d - (c - a)) (by omega) (b := b)
    ⟨fun i hi => hall i (by omega), items, by rw [hshift]; exact hit, by rw [hshift]; exact hqs⟩
  exact ⟨d', hd', hq', he'.trans hshift⟩

/-! ## Entering a block, with a rank -/

/-- **A block's label line is before the end of its segment.** -/
theorem lt_segEnd {R : RL} (hR : R.Wf) {t : Nat} {vb : VBlock} {items : Array RItem}
    (hvb : R.vc.blocks[t]? = some vb) (hit : R.rf.blocks[t]? = some items) {jl : Nat}
    (hjl : R.L[jl]? = some (.label (.block vb.label))) : jl < segEnd R t := by
  obtain ⟨⟨-, -, -, hbl⟩, -⟩ := lowerRFunc_ok hR.alloc
  obtain ⟨code, -, haf⟩ := hbl t vb items hvb hit
  obtain ⟨p, hp, hL, hseg⟩ := emit_seg hR.emit
  obtain ⟨i, sg, o, -, -, -, -, hs, ho', hidx, hlab, -⟩ := hseg t _ _ haf
  obtain ⟨A, hA, hX⟩ := segX_get hp hs ho'
  rw [hidx] at hX
  have hPL : planLines R.fa.k R.af = p.lines := by simp [planLines, hp]
  have hRL : R.L = relaxLines R.far p.lines := hL
  have hlbl : p.lines[A.length]? = some (.label (.block vb.label)) := by
    rw [hA, ← hlab, List.append_assoc, List.cons_append]; exact getElem?_mid _ _ _
  have r1 := relax_label (F := R.far) hlbl
  rw [← hRL] at r1
  have hj : jl = rix R.far p.lines A.length := labelOffsets_uniq hR.lm hjl r1.1
  have hm := rix_mono R.far p.lines
    (show A.length + 1 ≤ A.length + 1 + sg.body.length + o.length by omega)
  simp only [segEnd, hX, hPL]
  have := r1.2
  omega

/-- **Entering a block at a line representing it, with a rank** (`qe_entry`): `QEd` in some
number of forwarding steps, reaching a block whose segment ends after the line. -/
theorem qe_entry_rk {R : RL} (hR : R.Wf) {s : ArmState} {m : Loc → CV} {w : ArmState}
    (hst : StRel R s m w) {l : Label} {jl : Nat}
    (hrep : RepL R.af (planOwn R.fa.k R.af) R.L l jl) (hpc : Arm.r .PC s = R.pcOf jl) :
    ∀ {t : Nat} {vb : VBlock} {items : Array RItem}, t ≠ 0 → R.vc.blocks[t]? = some vb →
      vb.label = l → R.rf.blocks[t]? = some items →
      ∃ d, QEd R s m w t d ∧ jl < segEnd R (iterN (fwdNext R) d t) := by
  revert hpc
  induction hrep with
  | here ho hL =>
    intro hpc t vb items ht hvb hl hit
    subst hl
    exact ⟨0, ⟨fun i hi => absurd hi (Nat.not_lt_zero _), items, hit,
      qs_entry hR ht hvb hit ho hL hpc hst⟩, lt_segEnd hR hvb hit hL⟩
  | @skip l j l' ho hL _ ih =>
    intro hpc t vb items ht hvb hl hit
    have hpc' : Arm.r .PC s = R.pcOf (j + 1) := by
      rw [hpc]
      simp only [RL.pcOf]
      rw [lineOffset_succ _ _ _ hL]
      simp [Line.size]
    obtain ⟨d, hd, hlt⟩ := ih hpc' ht hvb hl hit
    exact ⟨d, hd, by omega⟩
  | @fwd l x j hx _ ih =>
    intro hpc t vb items ht hvb hl hit
    obtain ⟨b', vb', items', allocs, regs, i, bx, vbx, itx, hvb', hl', hit', -, hil, hal, hins,
      hasg, hsucc, hvbx, hlx, hitx, hbx0⟩ := RL.fwd_block hR hx
    obtain rfl : t = b' := RL.label_inj hR hvb hit hvb' hit' (hl.trans hl'.symm)
    rw [hvb] at hvb'
    cases hvb'
    rw [hit] at hit'
    cases hit'
    have hfn := fwdNext_of hsucc
    obtain ⟨d, ⟨hall, its, hits, hqs⟩, hlt⟩ := ih hpc hbx0 hvbx hlx hitx
    have hit1 : iterN (fwdNext R) (d + 1) t = iterN (fwdNext R) d bx := by
      rw [iterN_succ_in, hfn]
    refine ⟨d + 1, ⟨fun k hk => ?_, its, by rw [hit1]; exact hits, by rw [hit1]; exact hqs⟩,
      by rw [hit1]; exact hlt⟩
    rcases k with _ | k
    · exact (⟨vb, x, items, allocs, regs, i, vbx, hvb, by rw [hl]; exact hx, hit, hil, hal, hins,
        hasg, by rw [hfn]; exact hsucc, by rw [hfn]; exact hvbx, hlx⟩ : FwdE R t)
    · rw [iterN_succ_in, hfn]
      exact hall k (by omega)

theorem le_sum_of_mem' : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.sum
  | _ :: _, _, .head _ => by simp
  | _ :: _, _, .tail _ h => by have := le_sum_of_mem' h; simp; omega

theorem size_lt_itemBound {R : RL} {t : Nat} {items : Array RItem}
    (h : R.rf.blocks[t]? = some items) : items.size < itemBound R := by
  have hm : items.size ∈ R.rf.blocks.toList.map Array.size :=
    List.mem_map.2 ⟨items, Array.mem_toList_iff.2 (Array.mem_of_getElem? h), rfl⟩
  have := le_sum_of_mem' hm
  simp only [itemBound]
  omega

theorem blkSize_lt (R : RL) (t : Nat) : blkSize R t < itemBound R := by
  unfold blkSize
  cases h : R.rf.blocks[t]? with
  | none => simp [itemBound]
  | some items => simpa using size_lt_itemBound h

/-- **A removed branch decreases the rank**: from the line after block `b`'s segment, a block
`st` it represents is entered with a rank below `rk b 1`. -/
theorem rank_entry {R : RL} (hR : R.Wf) {s : ArmState} {m : Loc → CV} {w : ArmState}
    (hst : StRel R s m w) {b st : Nat} {vs : VBlock} {items : Array RItem} (hst0 : st ≠ 0)
    (hvs : R.vc.blocks[st]? = some vs) (hit : R.rf.blocks[st]? = some items) {jl : Nat}
    (hrep : RepL R.af (planOwn R.fa.k R.af) R.L vs.label jl) (hpc : Arm.r .PC s = R.pcOf jl)
    (hend : jl = segEnd R b) :
    ∃ r', r' < rk R b 1 ∧ QR R s st items.toList m w r' := by
  obtain ⟨d, hqe, hlt⟩ := qe_entry_rk hR hst hrep hpc hst0 hvs rfl hit
  obtain ⟨d', hd', hqe', hy⟩ := qed_short d hqe
  rw [← hy] at hlt
  refine ⟨_, ?_, .inr ⟨items, d', hit, rfl, hqe', rfl⟩⟩
  have hL := hrep.lt
  have hbs := blkSize_lt R (iterN (fwdNext R) d' st)
  have hm : (R.L.length + 1 - segEnd R (iterN (fwdNext R) d' st)) * rankK R ≤
      (R.L.length - jl) * rankK R := Nat.mul_le_mul_right _ (by omega)
  have he : (R.L.length + 1 - segEnd R b) * rankK R = (R.L.length - jl) * rankK R + rankK R := by
    rw [← hend, show R.L.length + 1 - jl = (R.L.length - jl) + 1 by omega, Nat.succ_mul]
  have hK : rankK R = itemBound R + R.vc.blocks.size := rfl
  simp only [rk]
  omega

/-! ## `Qs` at the last item, with its segment -/

/-- **`qs_term` with the block's segment** (`segX b = some x`, for the rank). -/
theorem qs_termX {R : RL} (hR : R.Wf) {s : ArmState} {b : Nat} {it : RItem} {m : Loc → CV}
    {w : ArmState} (hq : Qs R s b [it] m w) :
    ∃ j vb items pre c1 X ps1 psm ps2, ∃ x : Seg × List Line × Nat, R.vc.blocks[b]? = some vb ∧
      R.rf.blocks[b]? = some items ∧ items.toList = pre ++ [it] ∧ ItemsChecked R vb [it] ∧
      itemCode R.fr vb it = .ok c1 ∧ codeLinesE R.ctx R.af c1.dropLast ps1 = .ok (X, psm) ∧
      codeLinesE R.ctx R.af c1.getLast?.toList psm = .ok (x.1.term, ps2) ∧
      ps2.traps.toList <+: R.psF.traps.toList ∧
      R.L.drop j = relaxLines R.far (X ++ x.2.1) ++
        R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2) ∧
      Arm.r .PC s = R.pcOf j ∧ StRel R s m w ∧
      termOk (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) c1.getLast? x.1.term
        x.2.1 x.2.2 = true ∧ segX R.fa.k R.af b = some x := by
  obtain ⟨j, vb, items, pre, code, X, ps1, psm, ps2, x, hvb, hit, hsplit, hchk, hcode, hX, hT, htr,
    hdrop, hpc, hst, hx, hsc⟩ := hq
  obtain ⟨c1, c2, h1, h2, rfl⟩ := itemsCode_cons hcode
  obtain rfl : c2 = [] := by simpa [itemsCode, pure, Except.pure] using h2.symm
  rw [List.append_nil] at hX hT
  refine ⟨j, vb, items, pre, c1, X, ps1, psm, ps2, x, hvb, hit, hsplit, hchk, h1, hX, hT, htr,
    hdrop, hpc, hst, ?_, hx⟩
  have hne : c1 ≠ [] := by
    obtain ⟨cc, k, a, out, -, -, hrun⟩ := hchk
    obtain ⟨c0, ins, _, hc0, -⟩ := hR.check
    obtain ⟨preds, hcfg⟩ := hc0.cfg
    have := itemsCode_ne_nil hcfg hvb hrun (by simp) hcode
    simpa using this
  obtain ⟨y, hy⟩ : ∃ y, c1.getLast? = some y := ⟨_, List.getLast?_eq_getLast hne⟩
  obtain ⟨x', hx', hok⟩ := hsc
  rw [hx] at hx'
  cases hx'
  obtain ⟨p, hp, -⟩ := hR.psF
  obtain ⟨-, hidx⟩ := segX_mem hp hx
  unfold segTermOk at hok
  rw [hidx] at hok
  obtain ⟨⟨-, -, -, hbl⟩, -⟩ := lowerRFunc_ok hR.alloc
  obtain ⟨codeF, hcF, haf⟩ := hbl b vb items hvb hit
  rw [hsplit] at hcF
  obtain ⟨ca, cb, -, hcb, rfl⟩ := itemsCode_append hcF
  change itemsCode R.fr vb [it] = .ok cb at hcb
  rw [hcode, List.append_nil] at hcb
  cases hcb
  rw [haf] at hok
  rw [hy]
  have hb : (((if b = 0 then [AInst.prologue] else []) ++ (ca ++ c1)).toArray).back? = some y := by
    rw [Array.back?_eq_getElem?]
    simp only [List.size_toArray, List.getElem?_toArray]
    rw [← List.getLast?_eq_getElem?, ← List.append_assoc, List.getLast?_append, hy]
    rfl
  simpa [hb] using hok

/-! ## Block-ending branches -/

/-- The block-ending branches. -/
def BrForm (i : MInst) : Prop :=
  (∃ l, i = .jump l) ∨ (∃ t e kk, i = .condBr t e kk) ∨
    (∃ kd t e rn bit, i = .testBitAndBranch kd t e rn bit)

/-- The instructions whose step may go to another block. -/
def GotoForm (i : MInst) : Prop :=
  BrForm i ∨ (∃ info ti, i = .tryCall info ti) ∨ ∃ a ts c d e, i = .jtSequence a ts c d e

/-- `csem` goes to another block only at a `GotoForm`. -/
theorem csem_goto {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst} {uses : List CV}
    {w : ArmState} {outs : List CV} {w' : ArmState} {j : Nat}
    (h : csem F ctx X i uses w = some (outs, w', .goto j)) : GotoForm i := by
  cases hc : i.isCtl
  · cases csem_ctl hc h
  · cases i
    all_goals first
      | exact .inl (.inl ⟨_, rfl⟩)
      | exact .inl (.inr (.inl ⟨_, _, _, rfl⟩))
      | exact .inl (.inr (.inr ⟨_, _, _, _, _, rfl⟩))
      | exact .inr (.inl ⟨_, _, rfl⟩)
      | exact .inr (.inr ⟨_, _, _, _, _, rfl⟩)
      | (simp [MInst.isCtl] at hc; done)
      | skip
    all_goals exfalso
    all_goals simp only [csem, loopSem] at h
    all_goals (repeat' split at h) <;> simp_all

/-- **`Backend.Proof.realizes_goto` with the steps' facts and the rank**: from a ranked `Q` at a
branch item, the machine reaches `Q` at the successor in `n` steps without events or store
exclusives; with no step only with a lower rank at the successor (a forwarding block's `jump`, or
final lines that `MachBuffer` removed). -/
theorem realizes_gotoE {R : RL} (hR : R.Wf) {s : ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : ArmState} {c' : MConf CV ArmState} {r : Nat}
    (hq : QR R s b (.op k allocs :: its) m w r) {vb : VBlock} {i : MInst}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hbr : BrForm i)
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c') :
    ∃ n, Q R (iterN R.step n s) c' ∧ NoEvSteps R n s ∧
      (n = 0 → ∃ r', r' < r ∧ RkC R s c' r') ∧ ∀ i < n, AtNonRet R (iterN R.step i s) := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  obtain ⟨c, ins, _, hc, -⟩ := hR.check
  obtain ⟨preds, hcfg⟩ := hc.cfg
  obtain ⟨t0, ts, hback, hss, hlab⟩ := cfg_block hcfg hvb
  -- the witness: `Qs` at the item, or a forwarding block entered
  have hcase : (Qs R s b (.op k allocs :: its) m w ∧ r = rk R b (its.length + 1)) ∨
      ∃ d items, R.rf.blocks[b]? = some items ∧ RItem.op k allocs :: its = items.toList ∧
        QEd R s m w b (d + 1) ∧
        r = rk R (iterN (fwdNext R) (d + 1) b) (blkSize R (iterN (fwdNext R) (d + 1) b)) +
          (d + 1) := by
    rcases hq with ⟨hqs, hr⟩ | ⟨items, d, hit, hits, hqe, hr⟩
    · exact .inl ⟨hqs, by simpa using hr⟩
    · rcases d with _ | d
      · obtain ⟨-, items', hit', hqs⟩ := hqe
        change R.rf.blocks[b]? = some items' at hit'
        have e : items' = items := Option.some.inj (hit'.symm.trans hit)
        rw [e] at hqs
        refine .inl ⟨by rw [hits]; exact hqs, ?_⟩
        rw [hr]
        have hsz : items.size = its.length + 1 := by
          have := congrArg List.length hits; simp at this; omega
        simp [blkSize, hit, hsz, iterN]
      · exact .inr ⟨d, items, hit, hits, hqe, hr⟩
  rcases hcase with ⟨hqs, hr⟩ | ⟨d, items, hit, hits, ⟨hall, its', hits', hqs'⟩, hr⟩
  rotate_left
  · -- a forwarding block: its `jump` takes no machine step, one forwarding step less
    obtain ⟨vbf, x, itemsf, allocsf, regsf, if_, vbx, hvbf, -, hitf, hil, hal, hins, hasgf, hsuccf,
      -, -⟩ : FwdE R b := hall 0 (by omega)
    rw [hvb] at hvbf
    cases hvbf
    rw [hit] at hitf
    cases hitf
    rw [hil] at hits
    simp only [List.cons.injEq, RItem.op.injEq] at hits
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hits
    have hi1 := hi
    rw [hins] at hi1
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hi1
    subst hi1
    obtain ⟨rfl, -⟩ := assign_jump hasgf
    cases h with
    | @op b k allocs its m w vb' i ops outs outs' w' ctl m2 c' hvb' hi' hops' hsz hsem hlen hho hcl
      hn =>
    rw [hvb] at hvb'
    cases hvb'
    rw [hi] at hi'
    cases hi'
    simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
    obtain ⟨rfl, rfl, rfl⟩ := hsem
    obtain rfl : outs' = [] := List.eq_nil_of_length_eq_zero hho.1
    have hm2 : m2 = m := by
      funext l'
      refine (hcl.1 l' (by simp [MInst.clobbers])).trans ?_
      simp [Proof.writeM]
    subst m2
    cases hn with
    | @goto _ st items' hk1 hsucc hitems =>
    rw [hsuccf] at hsucc
    cases hsucc
    rw [iterN_succ_in] at hits' hqs' hr
    have hqe : QEd R s m w (fwdNext R b) d :=
      ⟨fun i hi => hall (i + 1) (by omega), its', hits', hqs'⟩
    have hqr : QR R s (fwdNext R b) items'.toList m w
        (rk R (iterN (fwdNext R) d (fwdNext R b)) (blkSize R (iterN (fwdNext R) d (fwdNext R b))) +
          d) := .inr ⟨items', d, hitems, rfl, hqe, rfl⟩
    refine ⟨0, ?_, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ => ⟨rk R (iterN (fwdNext R) d
      (fwdNext R b)) (blkSize R (iterN (fwdNext R) d (fwdNext R b))) + d, by omega, m, hqr⟩,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    simpa [iterN, Proof.writeM] using hqr.q
  obtain ⟨_, vb0, _, _, code, _, _, _, _, _, hvb0, -, -, hchk0, hcode, -⟩ := id hqs
  rw [hvb] at hvb0; cases hvb0
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
  rw [hi] at hi0; cases hi0
  obtain ⟨cc, wh, i2, ops2, hi2, hops2, hstat, -⟩ := op_checked hchk0
  rw [hi] at hi2; cases hi2
  cases h with
  | @op b k allocs its m w vb' i ops outs outs' w' ctl m2 c' hvb' hi' hops' hsz hsem hlen hho hcl hn =>
  rw [hvb] at hvb'; cases hvb'
  rw [hi] at hi'; cases hi'
  rw [hops2] at hops'; cases hops'
  -- the semantics: no defs, same world, `goto j`
  generalize hU : (((ops2.zip (regs.map Loc.reg)).toList.filter (·.1.isUse)).map (m ·.2)) = U at hsem
  have hsem' : outs = [] ∧ w' = w ∧ ∃ j, ctl = .goto j ∧ (∀ l, i = .jump l → j = 0) ∧
      (∀ t e kk, i = .condBr t e kk → j = if kk.holds U w then 0 else 1) ∧
      (∀ kd t e rn bit, i = .testBitAndBranch kd t e rn bit →
        ∃ a, U = [a] ∧ j = if ((lo64 a).getLsbD bit == (kd == .nz)) then 0 else 1) := by
    rcases hbr with ⟨l, rfl⟩ | ⟨t, e, kk, rfl⟩ | ⟨kd, t, e, rn, bit, rfl⟩
    · simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
      obtain ⟨rfl, rfl, rfl⟩ := hsem
      refine ⟨rfl, rfl, 0, rfl, fun _ _ => rfl, ?_, ?_⟩
      · intro _ _ _ h; cases h
      · intro _ _ _ _ _ h; cases h
    · simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
      obtain ⟨rfl, rfl, rfl⟩ := hsem
      refine ⟨rfl, rfl, _, rfl, ?_, ?_, ?_⟩
      · intro _ h; cases h
      · intro t' e' kk' h; cases h; rfl
      · intro _ _ _ _ _ h; cases h
    · simp only [RL.sem, csemV, csem] at hsem
      split at hsem
      · rename_i a
        simp only [Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        refine ⟨rfl, rfl, _, rfl, ?_, ?_, ?_⟩
        · intro _ h; cases h
        · intro _ _ _ h; cases h
        intro kd' t' e' rn' bit' h
        cases h
        exact ⟨a, rfl, rfl⟩
      · cases hsem
  obtain ⟨rfl, hw', j, rfl, hj0, hjc, hjt⟩ := hsem'
  obtain rfl : outs' = [] := List.eq_nil_of_length_eq_zero hho.1
  subst w'
  -- the store is unchanged
  have hm2 : m2 = m := by
    funext l
    refine (hcl.1 l ?_).trans ?_
    · rcases hbr with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ <;> simp [MInst.clobbers]
    · simp [Proof.writeM]
  subst m2
  cases hn with
  | @goto _ st items' hk1 hsucc hitems =>
  have hwm : Proof.writeM m ((((ops2.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip
      ([] : List CV)).filter (·.1.1.isLate)) = m := by simp [Proof.writeM]
  rw [hwm]
  -- the successor's label
  have hti : t0 = i := by
    rw [Array.back?_eq_getElem?, show vb.insts.size - 1 = k by omega, hi] at hback
    cases hback; rfl
  subst hti
  have hsucc' := hsucc
  simp only [succOf, hcfg, hss, Option.bind_some] at hsucc'
  obtain ⟨vs, hvs, hlj⟩ := hlab j st hsucc'
  have hst0 : st ≠ 0 := ctlCheck_succ hck hsucc
  -- the block's last item: its final lines and the branch check's verdict on them
  obtain rfl : its = [] := hchk0.tail_nil (by omega)
  obtain ⟨j0, vb0, items, pre, c1', X, ps1, psm, ps2, x, hvb0, hit, hsplit, -, hc1'', hX, -, htr,
    hdrop, hpc, hst, hterm, hx⟩ := qs_termX hR hqs
  rw [hvb] at hvb0; cases hvb0
  rw [hc1] at hc1''; cases hc1''
  have hone : ∀ a, c1 = [a] → X = [] ∧ R.L.drop j0 = relaxLines R.far x.2.1 ++
      R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2) := by
    intro a ha
    subst ha
    simp only [List.dropLast_singleton, codeLinesE, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hX
    obtain ⟨rfl, rfl⟩ := hX
    exact ⟨rfl, by simpa using hdrop⟩
  -- the machine reaches a line representing the successor
  have hreach : ∃ n jl, iterN R.step n s = Arm.w .PC (R.pcOf jl) s ∧
      RepL R.af (planOwn R.fa.k R.af) R.L vs.label jl ∧ NoEvSteps R n s ∧
      (n = 0 → jl = rix R.far (planLines R.fa.k R.af) x.2.2) ∧
      ∀ i < n, AtNonRet R (iterN R.step i s) := by
    rcases hbr with ⟨l, rfl⟩ | ⟨t, e, kk, rfl⟩ | ⟨kd, t, e, rn, bit, rfl⟩
    · obtain ⟨rfl, rfl⟩ := assign_none (fun f => rfl) hasg
      obtain rfl : c1 = [.inst _] := by
        rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
        · exact h
        · cases h
        · cases h
      obtain ⟨-, hd⟩ := hone _ rfl
      simp only [List.getLast?_singleton] at hterm
      rw [hj0 l rfl] at hlj
      simp only [MInst.targets, List.getElem?_cons_zero, Option.some.injEq] at hlj
      rw [← hlj]
      exact reach_bE hR hd (termOk_jump hterm) (by rw [hst.prog]) hpc hst.err
    · have hkk : ∀ r sz, kk = .zero r sz ∨ kk = .notZero r sz → r.isVregInt = true := by
        intro r sz hr
        have := ctlCheck_inst hck hvb hi
        rcases hr with rfl | rfl <;> simpa [ctlInstOk] using this
      obtain ⟨k', rfl, hkr⟩ := kind_alloc hkk (mk := fun k => MInst.condBr t e k) rfl
        (fun f => rfl) (fun f => rfl) hops2 hstat hasg m
      obtain rfl : c1 = [.inst _] := by
        rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
        · exact h
        · cases h
        · cases h
      obtain ⟨-, hd⟩ := hone _ rfl
      simp only [List.getLast?_singleton] at hterm
      have hci : (∃ c t', k'.insn (.block t) = .bcond c t') ∨
          (∃ nz w r t', k'.insn (.block t) = .cbz nz w r t') ∨
          (∃ nz r bit t', k'.insn (.block t) = .tbz nz r bit t') := by
        cases k' <;> simp [CondBrKind.insn]
      have hset : ∀ l, (k'.insn (.block t)).setTarget l = k'.insn l := by
        intro l; cases k' <;> rfl
      have hct : (k'.insn (.block t)).condTarget?.isSome = true →
          (k'.insn (.block t)).condTarget? = some (.block t) := by
        intro h
        cases k' <;> simp_all [CondBrKind.insn, Insn.condTarget?]
      obtain ⟨n, jl, hn, hrep, hne, h0, hAt⟩ := reach_cbE hR hd (termOk_condBr hterm) hci
        (kk.holds _ w)
        (fun l env a ha => kind_brCond hst hkr l (by rwa [hset] at ha))
        (fun hs l env a ha => kind_brCond_inv hst hkr (.block t) l (hct hs) ha)
        (by rw [hst.prog]) hpc hst.err
      refine ⟨n, jl, hn, ?_, hne, h0, hAt⟩
      rw [hU] at hrep
      rw [hjc t e kk rfl] at hlj
      simp only [MInst.targets] at hlj
      cases hcond : kk.holds U w <;> simp only [hcond] at hlj hrep <;> simp at hlj <;> rw [← hlj] <;>
        simpa using hrep
    · obtain ⟨nr, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
      obtain ⟨r', rfl, rfl⟩ := assign_one (n := nr) (sp := OpSpec.use)
        (mk := fun r => MInst.testBitAndBranch kd t e r bit) (fun f => by simp [MInst.visitOperands])
        hasg
      have hops' : ops2 = #[⟨nr, .int, .use, .early, .reg⟩] := by
        have e : (MInst.testBitAndBranch kd t e (.vreg nr .int) bit).operands =
            .ok #[⟨nr, .int, .use, .early, .reg⟩] := rfl
        rw [e] at hops2
        injection hops2 with h
        exact h.symm
      subst hops'
      obtain ⟨⟨n', rfl, hn', -⟩, -⟩ := (allocOk_of_checkStatic hstat).fits
        (⟨nr, .int, .use, .early, .reg⟩, r') (by simp)
      obtain rfl : c1 = [.inst _] := by
        rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
        · exact h
        · cases h
        · cases h
      obtain ⟨-, hd⟩ := hone _ rfl
      simp only [List.getLast?_singleton] at hterm
      have hal := ((checkStatic_facts hstat).2.1 (⟨nr, .int, .use, .early, .reg⟩, .reg (.x n'))
        (by simp)).1
      simp only [CheckCtx.locOk, Bool.and_eq_true] at hal
      have hm : m (.reg (.x n')) = (Arm.r (.GPR (rnum n')) s).setWidth 128 := by
        rw [hst.store (.reg (.x n')) (fun r e => by cases e; exact hal.2) trivial]; rfl
      obtain ⟨n, jl, hn, hrep, hne, h0, hAt⟩ := reach_cbE hR hd (termOk_tbz hterm)
        (.inr (.inr ⟨_, _, _, _, rfl⟩))
        ((Arm.r (.GPR (rnum n')) s).getLsbD bit == (kd == .nz))
        (fun l env a ha => brCond_tbz (by omega) ha s)
        (fun _ l env a ha => by
          simp only [Insn.invertTo] at ha
          rw [brCond_tbz (by omega) ha s, beq_not_right])
        (by rw [hst.prog]) hpc hst.err
      refine ⟨n, jl, hn, ?_, hne, h0, hAt⟩
      obtain ⟨a, hUa, hja⟩ := hjt kd t e _ bit rfl
      have ha : a = m (.reg (.x n')) := by
        rw [← hU] at hUa
        simp [Operand.isUse] at hUa
        exact hUa.symm
      subst ha
      rw [hja] at hlj
      simp only [MInst.targets, hm, lo64_regX] at hlj
      cases hcond : ((Arm.r (.GPR (rnum n')) s).getLsbD bit == (kd == .nz)) <;>
        simp only [hcond] at hlj hrep <;> simp at hlj <;> rw [← hlj] <;> simpa using hrep
  obtain ⟨n, jl, hn, hrep, hne, h0, hAt⟩ := hreach
  refine ⟨n, ?_, hne, fun hn0 => ?_, hAt⟩
  · rw [hn]
    exact q_entry hR hst0 hvs hitems hrep (Arm.r_of_w_same ..) (hst.pc _)
  · subst hn0
    have hs' : Arm.w .PC (R.pcOf jl) s = s := hn.symm
    have hend : jl = segEnd R b := by simp only [segEnd, hx]; exact h0 rfl
    obtain ⟨r', hr', hqr⟩ := rank_entry hR (hst.pc (R.pcOf jl)) hst0 hvs hitems hrep
      (Arm.r_of_w_same ..) hend
    rw [hs'] at hqr
    exact ⟨r', by rw [hr]; exact hr', m, hqr⟩

/-! ## Configurations with a rank -/

/-- **A configuration of the allocated code with a rank** (layer 4b with branches): the rank of
a `Q` witness at the related Arm state (`RelQR`), which every realization without an Arm step
decreases. -/
abbrev RConf := MConf CV ArmState × Nat

/-- The allocated code's thread step, the ranks free. -/
abbrev SrcStepR (R : RL) (c : RConf) (evs : List Ev) (c' : RConf) : Prop := SrcStep R c.1 evs c'.1

/-- **The relation of layer 4b with branches**: `RelQ`, and the rank is one of the configuration
at the Arm state (`RkC`). -/
abbrev RelQR (R : RL) (t : ArmState × Mon) (c : RConf) : Prop := RelQ R t c.1 ∧ RkC R t.1 c.1 c.2

/-- `Done` of the configuration. -/
abbrev DoneR (R : RL) (c : RConf) : Prop := Done R c.1

/-- **The measure of layer 4b with branches**: the rank. The measure before #553 (the block's
index and its remaining items) was a function of the configuration only; with `MachBuffer`'s
branch simplification a zero-step cycle of configurations exists (module doc), so the measure is
the rank of the `Q` witness, carried with the configuration. -/
abbrev μR (_R : RL) (c : RConf) : Nat := c.2

theorem RelQR.of {R : RL} {t : ArmState × Mon} {c : MConf CV ArmState} (hq : Q R t.1 c)
    (hA : AInv R c) : ∃ r, RelQR R t (c, r) := by
  obtain ⟨r, hr⟩ := RkC.of_q hq
  exact ⟨r, RelQ.of hq hA, hr⟩

/-- A run of the configurations with ranks is one of the configurations. -/
theorem SRun.fst {R : RL} : ∀ {c c' : RConf} {tr : List (List Ev)},
    SRun (SrcStepR R) c tr c' → SRun (SrcStep R) c.1 tr c'.1
  | _, _, _, .nil => .nil
  | _, _, _, .cons hs hr => .cons hs (SRun.fst hr)

theorem prun_take_zero {P : Policy} {f : ArmState → ArmState} {ok : ArmState → Lab → Prop}
    {t t1 : ArmState × Mon} {ls : List Lab} (h : PRun P f ok t (ls.take 0) t1) : t1 = t := by
  rw [List.take_zero] at h
  cases h
  rfl

/-- The successor `c'` stays in `c`'s block or ends the function. -/
def SameB (c c' : MConf CV ArmState) : Prop :=
  ∀ s, c = .run s → ∀ s', c' = .run s' → s'.b = s.b

/-- **No `GotoForm` at the head of `c`**: its step stays in its block (`sameB_step`). -/
def NoGotoAt (R : RL) (c : MConf CV ArmState) : Prop :=
  ∀ b its m w, c = .run ⟨b, its, m, w⟩ → ∀ k allocs its', its = .op k allocs :: its' →
    ∀ vb i, R.vc.blocks[b]? = some vb → vb.insts[k]? = some i → ¬ GotoForm i

/-- **The steps that stay in their block**: every step but those of a `GotoForm` instruction. -/
theorem sameB_step {R : RL} {b : Nat} {its : List RItem} {m : Loc → CV} {w : ArmState}
    {evs : List Ev} {c' : MConf CV ArmState} (h : SrcStep R (.run ⟨b, its, m, w⟩) evs c')
    (hng : ∀ k allocs its', its = .op k allocs :: its' → ∀ vb i, R.vc.blocks[b]? = some vb →
      vb.insts[k]? = some i → ¬ GotoForm i) :
    SameB (.run ⟨b, its, m, w⟩) c' := by
  intro s hs s' hs'
  injection hs with hs
  subst hs
  cases h with
  | move => cases hs'; rfl
  | @op _ k allocs its' _ _ vb i ops _ _ hvb hi hops hevs hfoot hst =>
    cases hst with
    | @op _ _ _ _ _ _ vb1 i1 ops1 outs outs' w' ctl m2 c'' hvb1 hi1 hops1 hsz hsem hlen hho hcl hn =>
      rw [hvb] at hvb1; cases hvb1; rw [hi] at hi1; cases hi1
      cases hn with
      | next _ => cases hs'; rfl
      | goto _ _ _ => exact absurd (csem_goto (R.sem_csem hsem)) (hng k allocs its' rfl vb i hvb hi)
      | ret _ => cases hs'
      | halt => cases hs'

/-- **A step staying in its block without an Arm step decreases the rank**: one item less in the
same segment (a forwarding block's only item is a `jump`, a `GotoForm`). -/
theorem RkC.lt_of_step {R : RL} {t : ArmState × Mon} {c c' : MConf CV ArmState} {evs : List Ev}
    {r : Nat} (hk : RkC R t.1 c r) (hng : NoGotoAt R c) (hs : SrcStep R c evs c')
    (hm : c'.measure < c.measure) (hR' : RelQ R t c') : ∃ r', r' < r ∧ RkC R t.1 c' r' := by
  match c, c', hk, hng, hs, hm, hR' with
  | .run ⟨b, its, m, w⟩, .run ⟨b', its', m', w'⟩, ⟨mt, hk⟩, hng, hs, hm, hR' =>
    have hb : b = b' := (sameB_step hs (hng b its m w rfl) _ rfl _ rfl).symm
    subst hb
    simp only [MConf.measure] at hm
    obtain ⟨mt', hq'⟩ := RelQ.q hR'
    -- the source's rank: `rk b |its|` (a forwarding witness has a `GotoForm` item)
    have hr : r = rk R b its.length ∧ ∃ items pre, R.rf.blocks[b]? = some items ∧
        items.toList = pre ++ its := by
      rcases hk with ⟨hqs, hr⟩ | ⟨items, d, hit, hits, hqe, hr⟩
      · obtain ⟨_, _, items, pre, _, _, _, _, _, _, _, hit, hsplit, -⟩ := hqs
        exact ⟨hr, items, pre, hit, hsplit⟩
      · rcases d with _ | d
        · obtain ⟨-, items', hit', -⟩ := hqe
          change R.rf.blocks[b]? = some items' at hit'
          have e : items' = items := Option.some.inj (hit'.symm.trans hit)
          subst e
          refine ⟨?_, items', [], hit, hits.symm⟩
          rw [hr]
          have hsz : items'.size = its.length := by
            have := congrArg List.length hits; simp at this; omega
          simp [blkSize, hit, hsz, iterN]
        · exfalso
          obtain ⟨vbf, x, itemsf, allocsf, regsf, if_, vbx, hvbf, -, hitf, hil, -, hins, hasg, -⟩ :
            FwdE R b := hqe.1 0 (by omega)
          rw [hit] at hitf
          cases hitf
          rw [hil] at hits
          obtain ⟨rfl, -⟩ := assign_jump hasg
          exact hng b its m w rfl 0 allocsf [] hits vbf _ hvbf (by rw [hins]; rfl)
            (.inl (.inl ⟨_, rfl⟩))
    obtain ⟨rfl, items, pre, hit, hsplit⟩ := hr
    -- the successor: `Qs` (fewer items than the block's), rank `rk b |its'|`
    have hqs' : Qs R t.1 b its' mt' w' := by
      rcases hq' with hqs' | ⟨items', hit', hits', -⟩
      · exact hqs'
      · exfalso
        rw [hit] at hit'
        cases hit'
        have : items.toList.length = pre.length + its.length := by rw [hsplit]; simp
        rw [← hits'] at this
        omega
    exact ⟨rk R b its'.length, by simp only [rk]; omega, mt', .inl ⟨hqs', rfl⟩⟩
  | .run _, .ret .., ⟨mt, hk⟩, _, _, _, _ => exact ⟨0, QR.pos hk, trivial⟩
  | .run _, .halt _, ⟨mt, hk⟩, _, _, _, _ => exact ⟨0, QR.pos hk, trivial⟩
  | .ret .., _, _, _, _, hm, _ => simp [MConf.measure] at hm
  | .halt _, _, _, _, _, hm, _ => simp [MConf.measure] at hm

/-- **From `MConf.measure` to the rank**, at the configurations whose steps stay in their block. -/
theorem isOut_μR {R : RL} {ok : ArmState → Lab → Prop} {t : ArmState × Mon}
    {c : MConf CV ArmState} {r : Nat} {ls : List Lab} (hng : NoGotoAt R c)
    (hk : RkC R t.1 c r)
    (h : ItemSimOut Policy.arm R.step ok (SrcStep R) (RelQ R) (PrivA R) (fun c => c.measure) t c ls) :
    ItemSimOut Policy.arm R.step ok (SrcStepR R) (RelQR R) (PrivA R) (μR R) t (c, r) ls := by
  obtain ⟨n, evs, c', t1, φ, hn, hpos, hs, hr1, hR1, hi⟩ := h
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    obtain rfl := prun_take_zero hr1
    have hm : c'.measure < c.measure := hpos.resolve_left (Nat.lt_irrefl 0)
    obtain ⟨r', hr', hk'⟩ := RkC.lt_of_step hk hng hs hm hR1
    exact ⟨0, evs, (c', r'), t1, φ, hn, .inr hr', hs, hr1, ⟨hR1, hk'⟩, hi⟩
  · obtain ⟨r', hk'⟩ := RkC.of_relQ hR1
    exact ⟨n, evs, (c', r'), t1, φ, hn, .inl h0, hs, hr1, ⟨hR1, hk'⟩, hi⟩

/-- A step returning without events: no Arm step, the rank `0` at the return. -/
theorem itemSimOut_retR {R : RL} {ok : ArmState → Lab → Prop} {t : ArmState × Mon}
    {c : MConf CV ArmState} {r : Nat} {vals : List CV} {m' : Loc → CV} {w' : ArmState}
    {ls : List Lab} (hs : SrcStep R c [] (.ret vals m' w')) (hr : 0 < r) :
    ItemSimOut Policy.arm R.step ok (SrcStepR R) (RelQR R) (PrivA R) (μR R) t (c, r) ls :=
  ⟨0, [], (.ret vals m' w', 0), t, fun _ => (0, 0), Nat.zero_le _, .inr hr, hs,
    by rw [List.take_zero]; exact .nil, ⟨relQ_ret, trivial⟩, img_nil (by simp) _⟩

/-- The rank at a running configuration is positive. -/
theorem RkC.pos {R : RL} {s : ArmState} {b : Nat} {its : List RItem} {m : Loc → CV}
    {w : ArmState} {r : Nat} (h : RkC R s (.run ⟨b, its, m, w⟩) r) : 0 < r := by
  obtain ⟨mt, h⟩ := h
  exact h.pos

/-- The conclusion of `ItemSim` at one ranked configuration. -/
abbrev OpOutR (R : RL) (ok : ArmState → Lab → Prop) (t : ArmState × Mon) (c : RConf)
    (ls : List Lab) : Prop :=
  DoneR R c ∨ ItemSimOut Policy.arm R.step ok (SrcStepR R) (RelQR R) (PrivA R) (μR R) t c ls ∨
    (∃ evs c' φ, SrcStepR R c evs c' ∧ Img (PrivA R) evs (evTr ls) φ) ∨ PrivW (PrivA R) (evTr ls)

/-- The conclusion of `ItemSim` at one ranked configuration, runs ending inside the item at a line
other than `ret` (`OpOutN` with the rank). -/
abbrev OpOutNR (R : RL) (ok : ArmState → Lab → Prop) (t : ArmState × Mon) (c : RConf)
    (ls : List Lab) (t' : ArmState × Mon) : Prop :=
  DoneR R c ∨ ItemSimOut Policy.arm R.step ok (SrcStepR R) (RelQR R) (PrivA R) (μR R) t c ls ∨
    ((∃ evs c' φ, SrcStepR R c evs c' ∧ Img (PrivA R) evs (evTr ls) φ) ∧ AtNonRet R t'.1) ∨
    (PrivW (PrivA R) (evTr ls) ∧ AtNonRet R t'.1)

theorem OpOutNR.out {R : RL} {ok : ArmState → Lab → Prop} {t : ArmState × Mon} {c : RConf}
    {ls : List Lab} {t' : ArmState × Mon} (h : OpOutNR R ok t c ls t') : OpOutR R ok t c ls :=
  h.imp_right (Or.imp_right (Or.imp And.left And.left))

/-- A source step without the rank is one with any rank. -/
theorem srcImg_rank {R : RL} {c : MConf CV ArmState} {r : Nat} {ls : List Lab}
    (h : ∃ evs c' φ, SrcStep R c evs c' ∧ Img (PrivA R) evs (evTr ls) φ) :
    ∃ evs c' φ, SrcStepR R (c, r) evs c' ∧ Img (PrivA R) evs (evTr ls) φ := by
  obtain ⟨evs, c', φ, hs, hi⟩ := h
  exact ⟨evs, (c', 0), φ, hs, hi⟩

/-- **`OpOutG` with the rank**, at the configurations whose steps stay in their block. -/
theorem opOutR_of {R : RL} {ok : ArmState → Lab → Prop} {t : ArmState × Mon}
    {c : MConf CV ArmState} {r : Nat} {ls : List Lab} (hng : NoGotoAt R c) (hk : RkC R t.1 c r)
    (h : OpOutG R ok t c ls) : OpOutR R ok t (c, r) ls := by
  rcases h with h | h | h | h
  · exact .inl h
  · exact .inr (.inl (isOut_μR hng hk h))
  · exact .inr (.inr (.inl (srcImg_rank h)))
  · exact .inr (.inr (.inr h))

/-- **`OpOutN` with the rank**, at the configurations whose steps stay in their block. -/
theorem opOutNR_of {R : RL} {ok : ArmState → Lab → Prop} {t : ArmState × Mon}
    {c : MConf CV ArmState} {r : Nat} {ls : List Lab} {t' : ArmState × Mon}
    (hng : NoGotoAt R c) (hk : RkC R t.1 c r)
    (h : OpOutN R ok (fun c => c.measure) t c ls t') : OpOutNR R ok t (c, r) ls t' := by
  rcases h with h | h | ⟨h, hn⟩ | h
  · exact .inl h
  · exact .inr (.inl (isOut_μR hng hk h))
  · exact .inr (.inr (.inl ⟨srcImg_rank h, hn⟩))
  · exact .inr (.inr (.inr h))

/-- **The per-item obligation at a block-ending branch** (module doc): the Arm runs the branch
lines (no event, no store exclusive) to a line representing the successor, where `Q` holds; the
source step has no event; with no Arm step the rank decreases; a run ending inside the branch
(before reaching the successor) is at a line other than `ret`. -/
theorem goto_opR {R : RL} (hR : R.Wf) {ok : ArmState → Lab → Prop} {s : ArmState} {mon : Mon}
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : ArmState} {r : Nat}
    {evs0 : List Ev} {c0 : MConf CV ArmState}
    (hq : Q R s (OpC b k allocs its m w)) (hA : AInv R (OpC b k allocs its m w))
    (hk : RkC R s (OpC b k allocs its m w) r)
    (hs0 : SrcStep R (OpC b k allocs its m w) evs0 c0)
    (hform : ∀ vb i, R.vc.blocks[b]? = some vb → vb.insts[k]? = some i → BrForm i)
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm R.step ok (s, mon) ls t') :
    OpOutNR R ok (s, mon) (OpC b k allocs its m w, r) ls t' := by
  have hs0' := hs0
  cases hs0' with
  | @op _ _ _ _ _ _ vb i ops _ _ hvb hi hops hevs hfoot hst =>
  have hbr := hform vb i hvb hi
  have hak : akinds i = [] := by
    rcases hbr with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ <;> rfl
  have he : evs0 = [] := hevs.trans (cEvs_nil hak _ _)
  subst he
  rw [patch_nil] at hst
  obtain ⟨mt, hqr⟩ := hk
  obtain ⟨n, hq', hne, hμ, hAt⟩ := realizes_gotoE hR (hqr.store (q_stRel hq)) hvb hi hbr hst
  have hA' := aInv_step hR hq hA hst
  by_cases hN : n ≤ ls.length
  · obtain ⟨⟨s1, mon1⟩, r1, -⟩ := PRun.split (ls.take n) (ls.drop n)
      (by rw [List.take_append_drop]; exact hr)
    have hlen1 : (ls.take n).length = n := by simp; omega
    obtain ⟨hs1, hev1, -⟩ := prun_nil r1 fun i hi => hne i (by omega)
    rw [hlen1] at hs1
    simp only at hs1
    subst hs1
    have hrk : ∃ r', (0 < n ∨ r' < r) ∧ RkC R (iterN R.step n s) c0 r' := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        obtain ⟨r', hr', hk'⟩ := hμ rfl
        exact ⟨r', .inr hr', hk'⟩
      · obtain ⟨r', hk'⟩ := RkC.of_q hq'
        exact ⟨r', .inl h0, hk'⟩
    obtain ⟨r', hpos, hk'⟩ := hrk
    exact .inr (.inl ⟨n, [], (c0, r'), _, fun _ => (0, 0), hN, hpos, hs0, r1,
      ⟨.inl ⟨hq', hA'⟩, hk'⟩, img_nil hev1 _⟩)
  · obtain ⟨hs', hev, -⟩ := prun_nil hr fun i hi => hne i (by omega)
    refine .inr (.inr (.inr ⟨privW_of_nil hev, ?_⟩))
    rw [hs']
    exact hAt ls.length (by omega)

/-- **The per-item obligation at a block-ending branch** (module doc): the Arm runs the branch
lines (no event, no store exclusive) to a line representing the successor, where `Q` holds; the
source step has no event; with no Arm step the rank decreases. -/
theorem goto_op {R : RL} (hR : R.Wf) {ok : ArmState → Lab → Prop} {s : ArmState} {mon : Mon}
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : ArmState} {r : Nat}
    {evs0 : List Ev} {c0 : MConf CV ArmState}
    (hq : Q R s (OpC b k allocs its m w)) (hA : AInv R (OpC b k allocs its m w))
    (hk : RkC R s (OpC b k allocs its m w) r)
    (hs0 : SrcStep R (OpC b k allocs its m w) evs0 c0)
    (hform : ∀ vb i, R.vc.blocks[b]? = some vb → vb.insts[k]? = some i → BrForm i)
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm R.step ok (s, mon) ls t') :
    OpOutR R ok (s, mon) (OpC b k allocs its m w, r) ls :=
  (goto_opR hR hq hA hk hs0 hform hr).out

/-! ## The other items -/

/-- `OpOut` (runs under any condition) gives `OpOutG` under `OkPriv`. -/
theorem opOut_okPriv {R : RL} {s : ArmState} {mon : Mon} {c : MConf CV ArmState}
    (h : ∀ ls t', PRun Policy.arm R.step (fun _ _ => True) (s, mon) ls t' → OpOut R (s, mon) c ls)
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm R.step (OkPriv R) (s, mon) ls t') :
    OpOutG R (OkPriv R) (s, mon) c ls := by
  rcases h ls t' (PRun.mono (fun _ _ _ => trivial) hr) with
    h | ⟨n, evs, c', t1, φ, hn, hpos, hs, hr1, hR1, hi'⟩ | h | h
  · exact .inl h
  · obtain ⟨t1', r1, -⟩ := PRun.split (ls.take n) (ls.drop n)
      (by rw [List.take_append_drop]; exact hr)
    obtain rfl := PRun.det (PRun.mono (fun _ _ _ => trivial) r1) hr1
    exact .inr (.inl ⟨n, evs, c', t1', φ, hn, hpos, hs, r1, hR1, hi'⟩)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

/-- The memory forms and LL/SC loops do not leave their block. -/
theorem noGoto_memFormL {ctx : FnCtx} {i : MInst} (h : MemFormL ctx i) : ¬ GotoForm i := by
  intro hg
  rcases hg with (⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩) | ⟨_, _, rfl⟩ |
      ⟨_, _, _, _, _, rfl⟩ <;>
    simp [MemFormL, MemForm, NoEvForm, MInst.isCtl] at h

/-- A move item stays in its block. -/
theorem noGotoAt_move {R : RL} {b : Nat} {src dst : Loc} {its : List RItem} {m : Loc → CV}
    {w : ArmState} : NoGotoAt R (MvC b src dst its m w) := by
  intro _ _ _ _ e _ _ _ e'
  injection e with e
  injection e with _ e
  subst e
  cases e'

/-- An `op` item whose instruction is no `GotoForm` stays in its block. -/
theorem noGotoAt_op {R : RL} {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV}
    {w : ArmState} {vb : VBlock} {i : MInst} (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some i) (hg : ¬ GotoForm i) : NoGotoAt R (OpC b k allocs its m w) := by
  intro b' its' m' w' e k' allocs' its'' e' vb' i' h1 h2
  injection e with e
  injection e with e1 e2
  subst e1 e2
  injection e' with e'
  injection e' with e3
  subst e3
  rw [hvb] at h1; cases h1; rw [hi] at h2; cases h2
  exact hg

/-! ## The scope with branches -/

/-- **The scope of `arm_alloc_refines_br`**: every instruction is a memory form, an LL/SC loop
(`MemFormL`) or a block-ending branch (`BrForm`). -/
def MemScopeB (R : RL) : Prop :=
  ∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst), R.vc.blocks[b]? = some vb →
    vb.insts[k]? = some i → MemFormL R.ctx i ∨ BrForm i

theorem memScopeB_of_memScopeL {R : RL} (h : MemScopeL R) : MemScopeB R :=
  fun b vb k i hb hi => .inl (h b vb k i hb hi)

/-- **The per-item obligation of the scope with branches, with moves**, on ranked
configurations (`μR`). The statement before #553 was on configurations with a measure of the
configuration only, which `MachBuffer`'s layout falsifies (module doc). -/
theorem itemSim_br {R : RL} (hR : R.Wf) (hsc : MemScopeB R) :
    ItemSim Policy.arm R.step (OkPriv R) (SrcStepR R) (RelQR R) (DoneR R) (μR R) (PrivA R) := by
  rintro ⟨s, mon⟩ ⟨c, r⟩ ⟨hqa, hk⟩ ls t' hr
  match c, hqa, hk with
  | .ret vals m w, _, _ => exact .inl (.inl ⟨vals, m, w, rfl⟩)
  | .halt w, _, _ => exact .inl (.inr (.inl ⟨w, rfl⟩))
  | .run ⟨b, its, m, w⟩, hqa, hk =>
  by_cases hS : ∃ evs c', SrcStep R (.run ⟨b, its, m, w⟩) evs c'
  case neg => exact .inl (.inr (.inr fun evs c' h => hS ⟨evs, c', h⟩))
  obtain ⟨evs0, c0, hs0⟩ := hS
  cases hs0 with
  | @move _ src dst its' =>
    rcases move_op hR hqa hr with h | h
    · exact .inr (.inl (isOut_μR noGotoAt_move hk h))
    · exact .inr (.inr (.inr h))
  | @op _ k allocs its' _ _ vb i ops _ _ hvb hi hops hevs hfoot hst =>
    have hs : SrcStep R (OpC b k allocs its' m w) _ _ := .op hvb hi hops hevs hfoot hst
    rcases RelQ.op' hqa hs with ⟨hq, hA⟩ | ⟨rfl, vals, m', w', rfl⟩
    case inr => exact .inr (.inl (itemSimOut_retR hs (RkC.pos hk)))
    have uniq : ∀ vb' i', R.vc.blocks[b]? = some vb' → vb'.insts[k]? = some i' → i' = i :=
      fun vb' i' h1 h2 => by rw [hvb] at h1; cases h1; rw [hi] at h2; cases h2; rfl
    rcases hsc b vb k i hvb hi with hl | hbr
    · refine opOutR_of (noGotoAt_op hvb hi (noGoto_memFormL hl)) hk ?_
      rcases hl with (h | h | ⟨ty, rt, rn, fl, rfl, hfo⟩ | ⟨ty, rt, rn, fl, rfl, hfo⟩) | hl | hl
      · exact opOut_okPriv (fun ls t' hr => noev_op hR hq hA hs
          (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ h) hr) hr
      · exact opOut_okPriv (fun ls t' hr => fence_op hR hq hA hs
          (fun vb' i' h1 h2 => (uniq vb' i' h1 h2).trans h) hr) hr
      · exact opOut_okPriv (fun ls t' hr => oneEv_op hR hq hA hs
          (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ ldar_form hfo) hr) hr
      · exact opOut_okPriv (fun ls t' hr => oneEv_op hR hq hA hs
          (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ stlr_form hfo) hr) hr
      · exact rmw_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ hl) hr
      · exact cas_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ hl) hr
    · exact goto_op hR hq hA hk hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ hbr) hr

/-- **Layer 4b with the block-ending branches** (module doc): every precise Arm run under
`OkPriv` from a `Q`-related state realizes a run of the allocated code (`MTRun`) with `Refines`
(equal kinds, the addresses outside the world private, the atomic updates monitor pairs), up to the
allocated code's return, trap or undefined behaviour (`Done`), for functions whose instructions
are event-free, `fence`, `ldar`, `stlr`, LL/SC loops or block-ending branches (`MemScopeB`),
whatever their moves. -/
theorem arm_alloc_refines_br {R : RL} (hR : R.Wf) (hsc : MemScopeB R)
    {s : ArmState} {mon : Mon} {c : MConf CV ArmState} (hq : Q R s c) (hA : AInv R c)
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm R.step (OkPriv R) (s, mon) ls t') :
    ∃ n trS cE ψ, n ≤ ls.length ∧ MTRun R.vc R.rf R.sem ckeep (cEvs R.F R.ctx) c trS cE ∧
      Refines (· = ·) (PrivA R) (MonPair (evTr (ls.take n))) (PrepThread.conv trS)
        (PrepThread.conv (evTr (ls.take n))) ψ ∧ (n = ls.length ∨ Done R cE) := by
  obtain ⟨r, hrel⟩ := RelQR.of (t := (s, mon)) hq hA
  obtain ⟨n, trS, cE, ψ, hn, hs, href, hend⟩ :=
    refines_of_itemSim (itemSim_br hR hsc) hr hrel
  exact ⟨n, trS, cE.1, ψ, hn, mtrun_of_srun (SRun.fst hs), href, hend⟩

end Concurrency.ArmAllocThread
