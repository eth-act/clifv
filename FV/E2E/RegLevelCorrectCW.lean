import FV.E2E.RegLevelCorrectCY
import FV.E2E.RegLevelTryNA
import FV.E2E.RegLevelAtomicNA
import FV.E2E.RegLevelCallNA
import FV.E2E.RegLevelTlsNA
import FV.E2E.RegLevelMoveNA
import FV.E2E.RegLevelNextNA
import FV.E2E.RegLevelOpNA
import FV.E2E.RegLevelPoolNA

/-!
# The guarded realisation at a witness (SEM1 #537, item (3), route (a))

`realizes_allCY` started from `QW` at a witness `(j, ps1, T)`: every case ends at the witness
`RL.nextW` computes, at the first arrival there (`RL.SegLenA`: `RL.SegLen` when the step stays in
the activation, no step when it returns or traps). Two activations of one compiled function
started at one witness, at configurations of the same blocks and items, with agreeing pcs, then
cut their segments at the same index (`RL.segLen_eq_same`).

* `MConf.ShapeEq`, `MStep.shapeEq`: two steps from one configuration reach the same block and
  items (the semantics is a function; only havocked defs differ);
* `realizes_zeroNA`: the items with no lines (`args`, `emitIsland`);
* `QWA`: `QA` at a witness (`QW ∧ AInv`, or a return tail whose restores emit no code, at the
  witness of its next item's lines);
* `realizes_stepCW`: every step from `QW ∧ AInv` but a callee restore;
* **`realizes_allCW`**: the dispatcher, from `QWA`.
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.Driver

/-- **Two configurations at the same block and items** (or both returned, or both halted). -/
def _root_.Backend.MConf.ShapeEq {V W : Type} : MConf V W → MConf V W → Prop
  | .run ⟨b, its, _, _⟩, .run ⟨b', its', _, _⟩ => b = b' ∧ its = its'
  | .ret .., .ret .. => True
  | .halt _, .halt _ => True
  | _, _ => False

section
variable {V W : Type} {vc : VCode} {rf : RFunc} {sem : ISem V W} {keep : Reg → V → V}

/-- **Two steps from one configuration reach the same block and items.** -/
theorem MStep.shapeEq {c c' c'' : MConf V W} (h : MStep vc sem keep rf c c')
    (h' : MStep vc sem keep rf c c'') : MConf.ShapeEq c' c'' := by
  cases h with
  | move => cases h' with | move => exact ⟨rfl, rfl⟩
  | op hvb hi hops hsz hsem hlen hho hcl hn =>
    cases h' with
    | op hvb' hi' hops' hsz' hsem' hlen' hho' hcl' hn' =>
      rw [hvb] at hvb'; cases hvb'
      rw [hi] at hi'; cases hi'
      rw [hops] at hops'; cases hops'
      rw [hsem] at hsem'
      simp only [Option.some.injEq, Prod.mk.injEq] at hsem'
      obtain ⟨rfl, rfl, rfl⟩ := hsem'
      cases hn with
      | next => cases hn' with | next => exact ⟨rfl, rfl⟩
      | goto _ hs1 hi1 =>
        cases hn' with
        | goto _ hs2 hi2 =>
          rw [hs1] at hs2; cases hs2
          rw [hi1] at hi2; cases hi2
          exact ⟨rfl, rfl⟩
      | ret => cases hn' with | ret => trivial
      | halt => cases hn' with | halt => trivial

end

/-- **The segment length at a witness**: `RL.SegLen` when the step stays in the activation; no
step when it returns or halts. -/
def RL.SegLenA (R : RL) (j : Nat) (ps1 : PState) (T : List Line)
    (c c'' : MConf CV Arm.ArmState) (s : Arm.ArmState) (n : Nat) : Prop :=
  match c'' with
  | .run _ => R.SegLen j ps1 T c c'' s n
  | _ => n = 0

/-- `RL.SegLen` is `RL.SegLenA` when the step stays in the activation. -/
theorem RL.segLenA_of_run {R : RL} {j : Nat} {ps1 : PState} {T : List Line}
    {c c'' : MConf CV Arm.ArmState} {s : Arm.ArmState} {n : Nat} (hr : ∃ x, c'' = .run x)
    (h : R.SegLen j ps1 T c c'' s n) : R.SegLenA j ps1 T c c'' s n := by
  obtain ⟨x, rfl⟩ := hr
  exact h

/-- **An instruction step stays in the activation** unless the instruction is a `rets`, or a
`udf`/`trapIf` that halts. -/
theorem RL.mstep_run {R : RL} {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV}
    {w : Arm.ArmState} {c'' : MConf CV Arm.ArmState}
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'') {vb : VBlock}
    {i : MInst} (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    (hnr : ∀ us, i ≠ .rets us)
    (hnh : (∃ cd, i = .udf cd) ∨ (∃ kk cd, i = .trapIf kk cd) → ∀ w'', c'' ≠ .halt w'') :
    ∃ x, c'' = .run x := by
  cases h with
  | op hvb' hi' hops hsz hsem hlen hho hcl hn =>
    rw [hvb] at hvb'; cases hvb'
    rw [hi] at hi'; cases hi'
    cases hn with
    | next => exact ⟨_, rfl⟩
    | goto => exact ⟨_, rfl⟩
    | ret h => exact absurd h (hnr _)
    | halt =>
      obtain ⟨-, hform⟩ := csem_halt (R.sem_csem hsem)
      rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
      · exact absurd rfl (hnh (.inl ⟨cd, rfl⟩) _)
      · exact absurd rfl (hnh (.inr ⟨kk, cd, rfl⟩) _)

/-- **The items with no lines** (`args`, `emitIsland`), at a witness: no step, the next item at
the straight witness (the same line). -/
theorem realizes_zeroNA {R : RL} {Y : BitVec 64 → Prop} {s : Arm.ArmState} {b k : Nat}
    {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {j : Nat}
    {ps1 : PState} {T : List Line} (hq : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    (hz : (∃ ds, i = .args ds) ∨ ∃ nb, i = .emitIsland nb) {m' : Loc → CV} {w' : Arm.ArmState}
    (hst : StRel R s m' w') :
    R.SegNA Y s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) (.run ⟨b, its, m', w'⟩) 0 := by
  obtain ⟨items, pre, regs, i', c1, c2, ls1, ls2, psm, ps2, cc, wh, ops, hc1o, rfl, hit, hsplit,
    hasg, hc1', hops, hstat, hchk', hc2, h1, h2, htr, hdrop, hpc, -⟩ := qW_op hq hvb hi
  have hl : ls1 = [] ∧ psm = ps1 := by
    rcases hz with ⟨ds, rfl⟩ | ⟨nb, rfl⟩
    · obtain ⟨ds', rfl⟩ := assign_args hasg
      obtain rfl : c1 = [] := by
        rcases hc1' with ⟨-, h, -⟩ | ⟨_, _, rfl⟩ | ⟨us, h, -⟩
        · exact absurd rfl (h ds')
        · rfl
        · cases h
      simp only [codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h1
      exact ⟨h1.1.symm, h1.2.symm⟩
    · obtain ⟨rfl, rfl⟩ := assign_none (fun f => rfl) hasg
      obtain rfl : c1 = [.inst (.emitIsland nb)] := by
        rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
        · exact h
        · cases h
        · cases h
      have hl1 := codeLinesE_single h1
      simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
      exact ⟨hl1.1.symm, hl1.2.symm⟩
  obtain ⟨rfl, hps⟩ := hl
  subst hps
  have hr0 : (relaxLines R.far ([] : List Line)).length = 0 := by simp [relaxLines]
  have hW : R.nextW j psm T (.run ⟨b, .op k (regs.map Loc.reg) :: its, m, w⟩)
      (.run ⟨b, its, m', w'⟩) = (j, psm, T) := by
    rw [RL.nextW_straight, RL.straightW_eq hvb hc1o h1, hr0, Nat.add_zero]
  have hQ := qW_next (ls1 := []) (j0 := j) hvb hit hsplit hchk' hc2 h2 htr hdrop (by simp)
    (by rw [hr0, Nat.add_zero]; exact hpc) hst
  rw [hr0, Nat.add_zero] at hQ
  refine ⟨?_, fun i h => absurd h (Nat.not_lt_zero _), ⟨?_, fun i h0 h => absurd h (by omega)⟩, ?_⟩
  · rw [hW]; exact hQ
  · rw [hW]; exact hpc
  · rw [RL.segLen_straight_iff, RL.straightW_eq hvb hc1o h1, hr0, Nat.add_zero]
    exact ⟨fun _ => rfl, fun _ => rfl⟩

/-! ## `QA` at a witness -/

/-- **A return tail at the witness `(j, ps1, T)`** (`RetTail` with `QW`): the store `m` is the
machine's store `mt` (related by `QW`) but at the restored registers `D`. -/
def RetTailW (R : RL) (s : Arm.ArmState) (j : Nat) (ps1 : PState) (T : List Line) :
    MConf CV Arm.ArmState → Prop
  | .run ⟨b, its, m, w⟩ => ∃ mt D, QW R s j ps1 T (.run ⟨b, its, mt, w⟩) ∧
      (∀ l, (∀ r ∈ D, l ≠ .reg r) → m l = mt l) ∧ TailOk R b D its
  | _ => False

/-- **`QA` at the witness `(j, ps1, T)`**: `QW ∧ AInv`, or a return tail. -/
def QWA (R : RL) (s : Arm.ArmState) (j : Nat) (ps1 : PState) (T : List Line)
    (c : MConf CV Arm.ArmState) : Prop :=
  (QW R s j ps1 T c ∧ AInv R c) ∨ RetTailW R s j ps1 T c

/-- `QWA` is `QA` at a witness. -/
theorem QWA.qa {R : RL} {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    {c : MConf CV Arm.ArmState} (h : QWA R s j ps1 T c) : QA R s c := by
  rcases h with ⟨hq, hA⟩ | h
  · exact .inl ⟨hq.q, hA⟩
  · cases c with
    | run st =>
      obtain ⟨b, its, m, w⟩ := st
      obtain ⟨mt, D, hq, hm, ht⟩ := h
      exact .inr ⟨mt, D, hq.q, hm, ht⟩
    | ret => exact h.elim
    | halt => exact h.elim

/-- The witness after a straight step does not depend on the stores and worlds. -/
theorem RL.nextW_straight_congr {R : RL} {j : Nat} {ps1 : PState} {T : List Line} {b : Nat}
    {it : RItem} {its : List RItem} {m1 m2 m3 m4 : Loc → CV} {w1 w2 w3 w4 : Arm.ArmState} :
    R.nextW j ps1 T (.run ⟨b, it :: its, m1, w1⟩) (.run ⟨b, its, m2, w2⟩) =
      R.nextW j ps1 T (.run ⟨b, it :: its, m3, w3⟩) (.run ⟨b, its, m4, w4⟩) := by
  rw [RL.nextW_straight, RL.nextW_straight]

/-- The segment length of a straight step does not depend on the stores and worlds. -/
theorem RL.segLen_straight_congr {R : RL} {j : Nat} {ps1 : PState} {T : List Line} {b : Nat}
    {it : RItem} {its : List RItem} {m1 m2 m3 m4 : Loc → CV} {w1 w2 w3 w4 : Arm.ArmState}
    {s : Arm.ArmState} {n : Nat}
    (h : R.SegLen j ps1 T (.run ⟨b, it :: its, m1, w1⟩) (.run ⟨b, its, m2, w2⟩) s n) :
    R.SegLen j ps1 T (.run ⟨b, it :: its, m3, w3⟩) (.run ⟨b, its, m4, w4⟩) s n := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [RL.nextW_straight_congr (m3 := m1) (w3 := w1) (m4 := m2) (w4 := w2)]; exact h1
  · rw [RL.segLen_straight_iff] at h2 ⊢; exact h2

/-- **A callee restore at a witness takes no step**: the witness stays, at its first arrival. -/
theorem RL.segLen_restore {R : RL} {s : Arm.ArmState} {b : Nat} {r : Reg} {dst : Loc}
    {its : List RItem} {m m' : Loc → CV} {w : Arm.ArmState} {j : Nat} {ps1 : PState}
    {T : List Line} (hq : QW R s j ps1 T (.run ⟨b, .move (.save r) dst :: its, m, w⟩)) :
    R.SegLen j ps1 T (.run ⟨b, .move (.save r) dst :: its, m, w⟩) (.run ⟨b, its, m', w⟩) s 0 ∧
      R.nextW j ps1 T (.run ⟨b, .move (.save r) dst :: its, m, w⟩) (.run ⟨b, its, m', w⟩) =
        (j, ps1, T) := by
  have hW := nextW_move_save (m' := m') (w' := w) hq (.inl rfl)
  refine ⟨⟨⟨?_, fun i h0 h => by omega⟩, ?_⟩, hW⟩
  · rw [hW]; exact hq.pc
  · rw [RL.segLen_straight_iff, ← RL.nextW_straight (m := m) (m' := m') (w := w) (w' := w), hW]
    exact ⟨fun _ => rfl, fun _ => rfl⟩


set_option maxHeartbeats 4000000 in
/-- **One step of the allocated code at a witness from `QW ∧ AInv`** that is not a callee
restore (`realizes_allCW`'s non-restore case): the segment of the step ends at the next witness,
at its first arrival (`RL.SegLenA`), at a configuration of the same block and items as the given
step's. -/
theorem realizes_stepCW {R : RL} (hR : R.Wf) {P : Arm.ArmState → Prop}
    (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hC : CalleeOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    {c c' : MConf CV Arm.ArmState} (hq : QW R s j ps1 T c) (hA : AInv R c) (hP : P s)
    (hG : MStep R.vc (R.semG Ok) ckeep R.rf c c')
    (hns : ∀ b src dst its m w, c = .run ⟨b, .move src dst :: its, m, w⟩ → src.isSave = false) :
    ∃ n c'', MStep R.vc (R.semG Ok) ckeep R.rf c c'' ∧ MConf.ShapeEq c'' c' ∧ AInv R c'' ∧
      QW R (iterN R.step n s) (R.nextW j ps1 T c c'').1 (R.nextW j ps1 T c c'').2.1
        (R.nextW j ps1 T c c'').2.2 c'' ∧
      (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.WReadsIn Ok (iterN R.step i s)) ∧
      countIn R.CallSt R.step s n = opCalls R.vc c ∧ R.SegLenA j ps1 T c c'' s n := by
  have lift : ∀ c'', MStep R.vc R.sem ckeep R.rf c c'' → MStep R.vc (R.semG Ok) ckeep R.rf c c'' :=
    fun c'' h'' => MStep.guardLift h'' hG RL.semG_le
  have fin1 : ∀ Y, (∀ a, R.F a → Y a) → ((∀ a, Y a) ∨ ∃ w, Ok w Y) →
      ∀ n c'', MStep R.vc R.sem ckeep R.rf c c'' →
      QW R (iterN R.step n s) (R.nextW j ps1 T c c'').1 (R.nextW j ps1 T c c'').2.1
        (R.nextW j ps1 T c c'').2.2 c'' →
      (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.ReadsInY Y (iterN R.step i s)) →
      countIn R.CallSt R.step s n = opCalls R.vc c → R.SegLenA j ps1 T c c'' s n →
      ∃ n c'', MStep R.vc (R.semG Ok) ckeep R.rf c c'' ∧ MConf.ShapeEq c'' c' ∧ AInv R c'' ∧
        QW R (iterN R.step n s) (R.nextW j ps1 T c c'').1 (R.nextW j ps1 T c c'').2.1
          (R.nextW j ps1 T c c'').2.2 c'' ∧
        (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.WReadsIn Ok (iterN R.step i s)) ∧
        countIn R.CallSt R.step s n = opCalls R.vc c ∧ R.SegLenA j ps1 T c c'' s n :=
    fun Y hYF hYO n c'' hm hq' ht hc hs => ⟨n, c'', lift c'' hm, MStep.shapeEq (lift c'' hm) hG,
      aInv_step hR hq.q hA hm, hq', fun i hi => ⟨(ht i hi).1, Y, hYF, hYO, (ht i hi).2⟩, hc, hs⟩
  have fin : ∀ Y, (∀ a, R.F a → Y a) → ((∀ a, Y a) ∨ ∃ w, Ok w Y) →
      ∀ n c'', MStep R.vc R.sem ckeep R.rf c c'' →
      QW R (iterN R.step n s) (R.nextW j ps1 T c c'').1 (R.nextW j ps1 T c c'').2.1
        (R.nextW j ps1 T c c'').2.2 c'' →
      (∀ i < n, R.GoodXNY Y (iterN R.step i s)) → opCalls R.vc c = 0 →
      R.SegLenA j ps1 T c c'' s n →
      ∃ n c'', MStep R.vc (R.semG Ok) ckeep R.rf c c'' ∧ MConf.ShapeEq c'' c' ∧ AInv R c'' ∧
        QW R (iterN R.step n s) (R.nextW j ps1 T c c'').1 (R.nextW j ps1 T c c'').2.1
          (R.nextW j ps1 T c c'').2.2 c'' ∧
        (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.WReadsIn Ok (iterN R.step i s)) ∧
        countIn R.CallSt R.step s n = opCalls R.vc c ∧ R.SegLenA j ps1 T c c'' s n :=
    fun Y hYF hYO n c'' hm hq' ht h0 hs => fin1 Y hYF hYO n c'' hm hq'
      (fun i hi => ⟨(ht i hi).1.1, (ht i hi).2⟩)
      (by rw [h0]; exact countIn_zero_of fun i hi => (ht i hi).1.2) hs
  have finT := fin (fun _ => True) (fun _ _ => trivial) (.inl fun _ => trivial)
  have fin1T := fin1 (fun _ => True) (fun _ _ => trivial) (.inl fun _ => trivial)
  have nil : ∀ i < 0, R.GoodXNY (fun _ => True) (iterN R.step i s) :=
    fun _ h => absurd h (Nat.not_lt_zero _)
  have hck := (lowerRFunc_ok hR.alloc).2.2
  cases hG with
  | move =>
    obtain ⟨n, hq', ht, hs⟩ := realizes_moveNA (Y := fun _ => True) hR hq (hns _ _ _ _ _ _ rfl)
    exact finT n _ MStep.move hq' ht rfl hs
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsemG hlen hho hcl hn =>
    obtain ⟨hguard, hsem⟩ := RL.semG_inv hsemG
    have hoc : opCalls R.vc (.run ⟨b, .op k allocs :: its, m, w⟩) = if i.isCallI then 1 else 0 := by
      simp only [opCalls, hvb, hi]
    have hoc0 : i.isCallI = false → opCalls R.vc (.run ⟨b, .op k allocs :: its, m, w⟩) = 0 :=
      fun h => by rw [hoc, h]; rfl
    have hstep : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c' :=
      MStep.op hvb hi hops hsz hsem hlen hho hcl hn
    have toA : ∀ {c'' : MConf CV Arm.ArmState} {n : Nat},
        MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' →
        (∀ us, i ≠ .rets us) →
        ((∃ cd, i = .udf cd) ∨ (∃ kk cd, i = .trapIf kk cd) → ∀ w'', c'' ≠ .halt w'') →
        R.SegLen j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' s n →
        R.SegLenA j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' s n :=
      fun hm hnr hnh hs => RL.segLenA_of_run (RL.mstep_run hm hvb hi hnr hnh) hs
    have herrw : Arm.r .ERR w = .None := by
      have hst := q_stRel hq.q
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    obtain ⟨Y, hYF, hOk, hwr⟩ := hguard
    have hYO : (∀ a, Y a) ∨ ∃ w, Ok w Y := .inr ⟨w, hOk⟩
    cases hct : i.isCtl
    · rcases (hcov b vb k i hvb hi).resolve_left (by simp [hct]) with hfo | hpl
      rotate_left
      · -- the literal-pool load (#565)
        obtain ⟨sz, d, v, fl, rfl, -⟩ := isPoolLoad_form hpl
        obtain ⟨-, rfl⟩ := pool_world hsem
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht, hs⟩ := realizes_poolLoadNA (Y := fun _ => True) hR hq hvb hi
            hpl hops hsz hsem hlen hk
          exact finT n c'' hm hq' ht (hoc0 rfl)
            (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      -- a covered straight-line form
      obtain ⟨hOS, hL⟩ := formOk_sound (F := R.F) (X := R.X) hfo
      obtain rfl := csem_ctl hct (R.sem_csem hsem)
      have hwi : i.wReads = true := by
        simp [MInst.wReads, hct]
      obtain ⟨rY, hsemY⟩ := hwr hwi
      cases hn with
      | next hk =>
        have hnc : ∀ info, i ≠ .call info := by rintro info rfl; simp [MInst.isCtl] at hct
        obtain ⟨n, c'', hm, hq', ht, hs⟩ := realizes_op_nextNA hR hYF hq hvb hi hops hsz hsem hsemY
          hlen hk hOS hL
          (fun ha hasg hl hw he hal hs env => formOk_reads hfo hops ha hasg hl hw he hal hs env)
          (csem_next_world' (R.sem_csem hsem) hnc herrw)
        refine fin Y hYF hYO n c'' hm hq' ht
          (hoc0 (by cases i <;> first | rfl | simp [MInst.isCtl] at hct))
          (toA hm (fun us h => by subst h; simp [MInst.isCtl] at hct)
            (fun h => by rcases h with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> simp [MInst.isCtl] at hct) hs)
    · cases i <;> simp only [MInst.isCtl, reduceCtorEq] at hct
      case call info =>
        have hc : ctl = .next := by
          have hsem := R.sem_csem hsem
          simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
          obtain ⟨_, -, -, -, h⟩ := hsem; exact h.symm
        subst hc
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht, ⟨i0, hi0, hc0, hnc⟩, hs⟩ := realizes_callNA (Y := fun _ => True)
            hR hC hP hq hvb hi hops hsz hsem hlen hk
          exact fin1T n c'' hm hq' ht (by rw [hoc]; exact countIn_one_of hi0 hc0 hnc)
            (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      case args ds =>
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          have hQ := realizes_args hR hq.q hA hvb hi hstep
          obtain ⟨hq', -, hs⟩ := realizes_zeroNA (Y := fun _ => True) hq hvb hi (.inl ⟨ds, rfl⟩)
            (q_stRel hQ)
          exact finT 0 _ hstep hq' nil (hoc0 rfl) hs
      case rets us =>
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        cases hn with
        | ret _ => exact finT 0 _ hstep trivial nil (hoc0 rfl) rfl
      case loadExtNameGot rd nm =>
        obtain ⟨d, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht, hs⟩ := realizes_symAddrNA (Y := fun _ => True) hR hq hvb hi
            (.inl ⟨d, nm, rfl⟩) hops hsz hsem hlen hk
          exact finT n c'' hm hq' ht (hoc0 rfl)
            (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      case loadExtNameNear rd nm off =>
        obtain ⟨d, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht, hs⟩ := realizes_symAddrNA (Y := fun _ => True) hR hq hvb hi
            (.inr ⟨d, nm, off, rfl⟩) hops hsz hsem hlen hk
          exact finT n c'' hm hq' ht (hoc0 rfl)
            (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      case jump l =>
        obtain ⟨n, hq', ht, hs⟩ := realizes_gotoNA (Y := fun _ => True) hR hq hvb hi
          (.inl ⟨l, rfl⟩) hstep
        exact finT n c' hstep hq' ht (hoc0 rfl)
          (toA hstep (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      case condBr t e kk =>
        obtain ⟨n, hq', ht, hs⟩ := realizes_gotoNA (Y := fun _ => True) hR hq hvb hi
          (.inr (.inl ⟨t, e, kk, rfl⟩)) hstep
        exact finT n c' hstep hq' ht (hoc0 rfl)
          (toA hstep (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      case testBitAndBranch kd t e rn bit =>
        obtain ⟨n, hq', ht, hs⟩ := realizes_gotoNA (Y := fun _ => True) hR hq hvb hi
          (.inr (.inr ⟨kd, t, e, rn, bit, rfl⟩)) hstep
        exact finT n c' hstep hq' ht (hoc0 rfl)
          (toA hstep (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      case trapIf kk code =>
        by_cases hh : ∃ w'', c' = .halt w''
        · obtain ⟨w'', rfl⟩ := hh
          exact finT 0 _ hstep trivial nil (hoc0 rfl) rfl
        · obtain ⟨n, hq', ht, hs⟩ := realizes_trapIf_nextNA (Y := fun _ => True) hR hq hvb hi hstep
            (fun w'' e => hh ⟨w'', e⟩)
          exact finT n c' hstep hq' ht (hoc0 rfl)
            (toA hstep (fun _ h => by cases h) (fun _ w'' e => hh ⟨w'', e⟩) hs)
      case udf code =>
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        cases hn with
        | halt => exact finT 0 _ hstep trivial nil (hoc0 rfl) rfl
      case emitIsland nb =>
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          have hQ := realizes_island hq.q hvb hi hstep
          obtain ⟨hq', -, hs⟩ := realizes_zeroNA (Y := fun _ => True) hq hvb hi (.inr ⟨nb, rfl⟩)
            (q_stRel hQ)
          exact finT 0 _ hstep hq' nil (hoc0 rfl) hs
      case jtSequence d ts ridx t1 t2 =>
        obtain ⟨n, c'', hm, hq', ht, hs⟩ := realizes_jtNA (Y := fun _ => True) hR hq hvb hi hstep
        exact finT n c'' hm hq' ht (hoc0 rfl)
          (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      case atomicRmwLoop ty op fl ra ro rd r1 r2 =>
        obtain ⟨n, c'', hm, hq', ht, hs⟩ := realizes_rmwLoopNA hR hq hvb hi hstep fun ops' hops' => by
          rw [hops] at hops'; cases hops'; exact hwr rfl
        exact fin Y hYF hYO n c'' hm hq' ht (hoc0 rfl)
          (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      case atomicCasLoop ty fl ra re rx rd r1 =>
        obtain ⟨n, c'', hm, hq', ht, hs⟩ := realizes_casLoopNA hR hq hvb hi hstep fun ops' hops' => by
          rw [hops] at hops'; cases hops'; exact hwr rfl
        exact fin Y hYF hYO n c'' hm hq' ht (hoc0 rfl)
          (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      case tryCall info ti =>
        have hc : ctl = .goto ti.handlers.length := by
          have hsem := R.sem_csem hsem
          simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
          obtain ⟨_, -, -, -, h⟩ := hsem; exact h.symm
        subst hc
        cases hn with
        | goto hk1 hsucc hitems =>
          obtain ⟨n, c'', hm, hq', ht, ⟨i0, hi0, hc0, hnc⟩, hs⟩ := realizes_tryCallNA (Y := fun _ => True)
            hR hC (hT (hasTryCall_of_mem hvb hi)) hP hq hvb hi hops hsz hsem hlen hk1 hsucc hitems rfl
          exact fin1T n c'' hm hq' ht (by rw [hoc]; exact countIn_one_of hi0 hc0 hnc)
            (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      case elfTlsGetAddr nm rd tmp =>
        have hv := ctlCheck_inst hck hvb hi
        simp only [ctlInstOk, Bool.and_eq_true] at hv
        obtain ⟨d, rfl⟩ := isVregInt_iff hv.1
        obtain ⟨t, rfl⟩ := isVregInt_iff hv.2
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht, hs⟩ := realizes_tlsNA (Y := fun _ => True) hR
            (hTls (hasTls_of_mem hvb hi)) hq hvb hi hops hsz hsem hlen hk
          exact finT n c'' hm hq' ht (hoc0 rfl)
            (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)

set_option maxHeartbeats 1000000 in
/-- **`realizesQA` at a witness**: from the realisation from `QW ∧ AInv` of every step but a
callee restore (`hstep`), the realisation at a witness of the moves (no restore) with no call
state (`hmove`), and the `Rets` steps' ending the run, the step ends at `QWA` at the next
witness, at its first arrival (`RL.SegLenA`). A callee restore takes no step (the witness
stays); the moves of a return tail are realised on the machine's store. `Ex` is an extra fact of
each segment, holding of the empty one. -/
theorem realizesQWA {R : RL} (hR : R.Wf) {sem : ISem CV Arm.ArmState}
    {Tr : Arm.ArmState → Prop} {Ex : Arm.ArmState → Nat → Prop} (hEx0 : ∀ s, Ex s 0)
    (hrets : ∀ b k a its m w c' vb us, R.vc.blocks[b]? = some vb → vb.insts[k]? = some (.rets us) →
      MStep R.vc sem ckeep R.rf (.run ⟨b, .op k a :: its, m, w⟩) c' → ∃ vals m' w', c' = .ret vals m' w')
    (hmove : ∀ s j ps1 T b src dst its m w, QW R s j ps1 T (.run ⟨b, .move src dst :: its, m, w⟩) →
      src.isSave = false → ∃ n, QW R (iterN R.step n s)
          (R.nextW j ps1 T (.run ⟨b, .move src dst :: its, m, w⟩)
            (.run ⟨b, its, upd m dst (m src), w⟩)).1
          (R.nextW j ps1 T (.run ⟨b, .move src dst :: its, m, w⟩)
            (.run ⟨b, its, upd m dst (m src), w⟩)).2.1
          (R.nextW j ps1 T (.run ⟨b, .move src dst :: its, m, w⟩)
            (.run ⟨b, its, upd m dst (m src), w⟩)).2.2
          (.run ⟨b, its, upd m dst (m src), w⟩) ∧
        (∀ i < n, Tr (iterN R.step i s)) ∧ countIn R.CallSt R.step s n = 0 ∧
        R.SegLen j ps1 T (.run ⟨b, .move src dst :: its, m, w⟩)
          (.run ⟨b, its, upd m dst (m src), w⟩) s n ∧ Ex s n)
    {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line} {c c' : MConf CV Arm.ArmState}
    (hstep : QW R s j ps1 T c → AInv R c →
      (∀ b src dst its m w, c = .run ⟨b, .move src dst :: its, m, w⟩ → src.isSave = false) →
      ∃ n c'', MStep R.vc sem ckeep R.rf c c'' ∧ MConf.ShapeEq c'' c' ∧ AInv R c'' ∧
        QW R (iterN R.step n s) (R.nextW j ps1 T c c'').1 (R.nextW j ps1 T c c'').2.1
          (R.nextW j ps1 T c c'').2.2 c'' ∧
        (∀ i < n, Tr (iterN R.step i s)) ∧ countIn R.CallSt R.step s n = opCalls R.vc c ∧
        R.SegLenA j ps1 T c c'' s n ∧ Ex s n)
    (hq : QWA R s j ps1 T c) (hG : MStep R.vc sem ckeep R.rf c c') :
    ∃ n c'', MStep R.vc sem ckeep R.rf c c'' ∧ MConf.ShapeEq c'' c' ∧
      QWA R (iterN R.step n s) (R.nextW j ps1 T c c'').1 (R.nextW j ps1 T c c'').2.1
        (R.nextW j ps1 T c c'').2.2 c'' ∧
      (∀ i < n, Tr (iterN R.step i s)) ∧ countIn R.CallSt R.step s n = opCalls R.vc c ∧
      R.SegLenA j ps1 T c c'' s n ∧ Ex s n := by
  have nil : ∀ i < 0, Tr (iterN R.step i s) := fun _ h => absurd h (Nat.not_lt_zero _)
  rcases hq with ⟨hq, hA⟩ | hrt
  · by_cases hres : ∃ b r dst its m w, c = .run ⟨b, .move (.save r) dst :: its, m, w⟩
    · obtain ⟨b, r, dst, its, m, w, rfl⟩ := hres
      obtain ⟨rfl, D, htl⟩ := restore_tail hR hq.q
      obtain ⟨hs, hW⟩ := RL.segLen_restore (m' := upd m (.reg r) (m (.save r))) hq
      refine ⟨0, _, .move, MStep.shapeEq MStep.move hG, ?_, nil, rfl,
        RL.segLenA_of_run ⟨_, rfl⟩ hs, hEx0 s⟩
      rw [hW]
      right
      simp only [RetTailW]
      refine ⟨m, D ++ [r], qW_restore rfl hq, fun l hl => ?_, htl⟩
      simp only [upd, hl r (by simp), ite_false]
    · obtain ⟨n, c'', hm, hsh, hA', hq', ht, hc, hs, hx⟩ := hstep hq hA fun b src dst its m w e => by
        cases src with
        | save r => exact absurd ⟨b, r, dst, its, m, w, e⟩ hres
        | _ => rfl
      exact ⟨n, c'', hm, hsh, .inl ⟨hq', hA'⟩, ht, hc, hs, hx⟩
  · rcases c with ⟨b, its, m, w⟩ | ⟨vals, m, w⟩ | w
    · simp only [RetTailW] at hrt
      obtain ⟨mt, D, hq, hmD, vb, pend, k, a, rest, us, hvb, rfl, hk, htl⟩ := hrt
      rcases pend with _ | ⟨it, pend⟩
      · obtain ⟨vals, m', w', rfl⟩ := hrets b k a rest m w c' vb us hvb hk hG
        exact ⟨0, _, hG, MStep.shapeEq hG hG, .inl ⟨trivial, trivial⟩, nil,
          by simp [opCalls, hvb, hk, MInst.isCallI, countIn], rfl, hEx0 s⟩
      · simp only [List.cons_append] at hG hq ⊢
        unfold retTailOk at htl
        split at htl
        · rename_i r hr1 hr2
          simp only [Bool.and_eq_true] at htl
          obtain rfl := RItem.eq_restore hr1 hr2
          obtain ⟨hs, hW⟩ := RL.segLen_restore (m' := upd mt (.reg r) (mt (.save r))) hq
          refine ⟨0, _, .move, MStep.shapeEq MStep.move hG, ?_, nil, rfl,
            RL.segLenA_of_run ⟨_, rfl⟩ (RL.segLen_straight_congr hs), hEx0 s⟩
          rw [RL.nextW_straight_congr (m3 := mt) (w3 := w) (m4 := upd mt (.reg r) (mt (.save r)))
            (w4 := w), hW]
          right
          simp only [RetTailW]
          refine ⟨mt, D ++ [r], qW_restore rfl hq, fun l hl => ?_, vb, pend, k, a, rest, us, hvb, rfl,
            hk, htl.2⟩
          simp only [upd, hl r (by simp), ite_false]
          exact hmD l (fun r' hr' => hl r' (List.mem_append_left _ hr'))
        · simp only [Bool.and_eq_true] at htl
          obtain ⟨hav, htl⟩ := htl
          cases it with
          | op _ _ => simp [RItem.avoids] at hav
          | move x y =>
            simp only [RItem.avoids, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false,
              Bool.or_eq_true, beq_iff_eq, not_or] at hav
            obtain ⟨⟨hxs, -⟩, hD⟩ := hav
            obtain ⟨n, hq', ht, hc0, hs, hx⟩ := hmove s j ps1 T b x y _ mt w hq hxs
            refine ⟨n, _, .move, MStep.shapeEq MStep.move hG, ?_, ht, by rw [hc0]; rfl,
              RL.segLenA_of_run ⟨_, rfl⟩ (RL.segLen_straight_congr hs), hx⟩
            rw [RL.nextW_straight_congr (m3 := mt) (w3 := w) (m4 := upd mt y (mt x)) (w4 := w)]
            right
            simp only [RetTailW]
            refine ⟨upd mt y (mt x), D, hq', fun l hl => ?_, vb, pend, k, a, rest, us, hvb, rfl, hk,
              htl⟩
            by_cases hly : l = y
            · simp only [upd, hly, ite_true]
              exact hmD x (fun r hr e => (hD r hr).1 e)
            · simp only [upd, hly, ite_false]
              exact hmD l hl
    · simp only [RetTailW] at hrt
    · simp only [RetTailW] at hrt

/-- **The machine realises the allocated code at a witness** (`realizes_allCY` from `QWA`): the
segment of the step ends at `QWA` at the next witness, at its first arrival (`RL.SegLenA`), at a
configuration of the same block and items as the given step's (`realizesQWA` on
`realizes_stepCW`). -/
theorem realizes_allCW {R : RL} (hR : R.Wf) {P : Arm.ArmState → Prop}
    (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hC : CalleeOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    {c c' : MConf CV Arm.ArmState} (hq : QWA R s j ps1 T c) (hP : P s)
    (hG : MStep R.vc (R.semG Ok) ckeep R.rf c c') :
    ∃ n c'', MStep R.vc (R.semG Ok) ckeep R.rf c c'' ∧ MConf.ShapeEq c'' c' ∧
      QWA R (iterN R.step n s) (R.nextW j ps1 T c c'').1 (R.nextW j ps1 T c c'').2.1
        (R.nextW j ps1 T c c'').2.2 c'' ∧
      (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.WReadsIn Ok (iterN R.step i s)) ∧
      countIn R.CallSt R.step s n = opCalls R.vc c ∧ R.SegLenA j ps1 T c c'' s n := by
  obtain ⟨n, c'', hm, hsh, hq', ht, hc, hs, -⟩ :=
    realizesQWA (Tr := fun u => R.GoodX u ∧ R.WReadsIn Ok u) (Ex := fun _ _ => True) hR
      (fun _ => trivial) (fun _ _ _ _ _ _ _ _ _ hvb hi h => rets_mstepG hvb hi h)
      (fun s j ps1 T b src dst its m w hq hs =>
        let ⟨n, h1, h2, h3⟩ := realizes_moveNA (Y := fun _ => True) hR hq hs
        ⟨n, h1, fun i hi => ⟨(h2 i hi).1.1, fun _ => True, fun _ _ => trivial,
          .inl fun _ => trivial, (h2 i hi).2⟩, countIn_zero_of fun i hi => (h2 i hi).1.2, h3,
          trivial⟩)
      (fun hq hA hns =>
        let ⟨n, c'', h1, h2, h3, h4, h5, h6, h7⟩ :=
          realizes_stepCW hR Ok hC hT hTls hcov hq hA hP hG hns
        ⟨n, c'', h1, h2, h3, h4, h5, h6, h7, trivial⟩) hq hG
  exact ⟨n, c'', hm, hsh, hq', ht, hc, hs⟩

/-- **A chain of realised segments** from `s` at witness `W` and configuration `c`: the
segment lengths and the configurations reached, in order, each segment cut at its first arrival
(`RL.SegLenA`), ending at the next witness, its states satisfying `Tr`. Ends at `u`, witness
`W'`, configuration `c'`. -/
inductive RL.SegChain (R : RL) (Tr : Arm.ArmState → Prop) (s : Arm.ArmState)
    (W : Nat × PState × List Line) (c : MConf CV Arm.ArmState) :
    List (Nat × MConf CV Arm.ArmState) → Arm.ArmState → Nat × PState × List Line →
      MConf CV Arm.ArmState → Prop
  | nil : RL.SegChain R Tr s W c [] s W c
  | snoc {l : List (Nat × MConf CV Arm.ArmState)} {u : Arm.ArmState}
      {W1 : Nat × PState × List Line} {c1 c2 : MConf CV Arm.ArmState} {n : Nat} :
      RL.SegChain R Tr s W c l u W1 c1 → R.SegLenA W1.1 W1.2.1 W1.2.2 c1 c2 u n →
      (∀ i < n, Tr (iterN R.step i u)) →
      RL.SegChain R Tr s W c (l ++ [(n, c2)]) (iterN R.step n u)
        (R.nextW W1.1 W1.2.1 W1.2.2 c1 c2) c2

/-- **The chain's end is its start after the sum of the segment lengths.** -/
theorem RL.SegChain.iter {R : RL} {Tr : Arm.ArmState → Prop} {s : Arm.ArmState}
    {W : Nat × PState × List Line}
    {c : MConf CV Arm.ArmState} {l : List (Nat × MConf CV Arm.ArmState)} {u : Arm.ArmState}
    {W' : Nat × PState × List Line} {c' : MConf CV Arm.ArmState}
    (h : R.SegChain Tr s W c l u W' c') : u = iterN R.step (l.map Prod.fst).sum s := by
  induction h with
  | nil => rfl
  | snoc _ _ _ ih =>
    rw [ih, List.map_append, List.sum_append, ← iterN_add]
    simp [Nat.add_comm]

/-- **Every state of the chain's run before its end satisfies `Tr`.** -/
theorem RL.SegChain.trace {R : RL} {Tr : Arm.ArmState → Prop} {s : Arm.ArmState}
    {W : Nat × PState × List Line}
    {c : MConf CV Arm.ArmState} {l : List (Nat × MConf CV Arm.ArmState)} {u : Arm.ArmState}
    {W' : Nat × PState × List Line} {c' : MConf CV Arm.ArmState}
    (h : R.SegChain Tr s W c l u W' c') : ∀ i < (l.map Prod.fst).sum, Tr (iterN R.step i s) := by
  induction h with
  | nil => intro i hi; simp at hi
  | @snoc l u W1 c1 c2 n hch _ ht ih =>
    have hu := hch.iter
    rw [List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    refine trace_add ih ?_
    rw [← hu]
    exact ht

/-- **`realizes_allC_spY` exporting the segmentation**: under `Q` = "a chain of realised
segments from `(s₀, W₀, c₀)` reaches the state at a witness at which `QWA` holds", with the body
`sp` at the contract's states. -/
theorem realizes_allC_spW {R : RL} (hR : R.Wf) {P : Arm.ArmState → Prop}
    (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hC : CalleeOkGP (fun u => P u ∧ spOf u = R.spB) R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H
      R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGP (fun u => P u ∧ spOf u = R.spB) R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H
        R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) (s₀ : Arm.ArmState) (W₀ : Nat × PState × List Line)
    (c₀ : MConf CV Arm.ArmState) :
    RealizesCP R.vc R.rf (R.semG Ok) ckeep R.step
      (fun u c => ∃ l W, R.SegChain (fun u => R.Good u ∧ R.WReadsIn Ok u) s₀ W₀ c₀ l u W c ∧
        QWA R u W.1 W.2.1 W.2.2 c)
      (fun u => R.GoodX u ∧ R.WReadsIn Ok u) R.CallSt P := by
  intro s c c' ⟨l, W, hch, hq⟩ hP h
  have hsp : spOf s = R.spB := by
    cases c with
    | run st =>
      obtain ⟨b, its, m, w⟩ := st
      obtain ⟨mt, hq'⟩ := qa_q hq.qa
      exact (q_stRel hq').sp
    | _ => cases h
  obtain ⟨n, c'', hm, -, hq', ht, hcnt, hs⟩ := realizes_allCW hR Ok hC hT hTls hcov hq ⟨hP, hsp⟩ h
  exact ⟨n, c'', hm, ⟨_, _, .snoc hch hs fun i hi => ⟨(ht i hi).1.good, (ht i hi).2⟩, hq'⟩, ht, hcnt⟩

end Backend.Proof
