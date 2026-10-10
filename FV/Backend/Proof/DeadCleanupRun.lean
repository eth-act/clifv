import FV.Backend.Proof.DeadCleanupLive
import FV.Backend.Proof.DeadCleanupSem

namespace Backend.DeadCleanup
open Backend.Proof

/-- A jump is a block terminator. Conditional traps may still stop earlier. -/
def GotoAtEnd {V W : Type} (sem : ISem V W) (ms : List MInst) : Prop :=
  ∀ pre i post us w outs w' j, ms = pre ++ i :: post →
    sem i us w = some (outs, w', .goto j) → post = []

/-- Observable outcomes of straight-line runs. A jump additionally preserves
all live-out values needed for the parallel edge copy. Instruction indices may
change when preceding producers are removed. -/
def SameEnd {V W : Type} (exit : List Nat) : SeqEnd V W → SeqEnd V W → Prop
  | .fall a w, .fall b w' => w = w' ∧ Agree exit a b
  | .stop _ i ops a w outs w' ctl, .stop _ i' ops' b wb outsb wb' ctlb =>
      i = i' ∧ ops = ops' ∧ w = wb ∧ outs = outsb ∧ w' = wb' ∧ ctl = ctlb ∧
      vuses ops a = vuses ops b ∧
      (∀ j, ctl = .goto j → Agree exit (vdefUpd ops outs a) (vdefUpd ops outs b))
  | _, _ => False

private theorem SameEnd_succ {V W : Type} {live : List Nat} {a b : SeqEnd V W}
    (h : SameEnd live a b) : SameEnd live a.succ b.succ := by
  cases a <;> cases b <;> exact h

/-- Removing dead pure producers preserves successful block runs. This generic
lemma requires exact world purity; concrete register bookkeeping is handled by
an adapter when this is composed with the machine-code theorem. -/
theorem scan_run {V W : Type} (sem : ISem V W)
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (nregs : Nat) (ms : List MInst) (exit : List Nat)
    (hg : GotoAtEnd sem ms) {a b : Nat → V} {w : W} {result : SeqEnd V W}
    (ha : Agree (scan nregs ms exit).2 a b)
    (hr : seqRun sem ms a w = some result) :
    ∃ result', seqRun sem (scan nregs ms exit).1 b w = some result' ∧
      SameEnd exit result result' := by
  induction ms generalizing a b w result with
  | nil =>
    simp only [seqRun, Option.some.injEq] at hr
    subst result
    exact ⟨.fall b w, rfl, rfl, ha⟩
  | cons i ms ih =>
    have hgt : GotoAtEnd sem ms := by
      intro pre m post us w outs w' j hm hs
      apply hg (i :: pre) m post us w outs w' j
      · simp only [List.cons_append, hm]
      · exact hs
    cases hop : i.operands with
    | error e => simp [seqRun, hop] at hr
    | ok ops =>
      cases hs : sem i (vuses ops a) w with
      | none => simp [seqRun, hop, hs] at hr
      | some r =>
        obtain ⟨outs, w', ctl⟩ := r
        by_cases hl : outs.length = (ops.toList.filter Operand.isDef).length
        · by_cases hd : discard i (scan nregs ms exit).2 = true
          · have hworld := hp i _ _ _ _ _ (discard_pure hd) hs
            obtain ⟨rfl, rfl⟩ := hworld
            simp only [scan, hd, ↓reduceIte] at ha ⊢
            have hau : Agree (scan nregs ms exit).2 (vdefUpd ops outs a) b := by
              intro n hn
              exact (discard_updates_agree hd hop a outs n hn).symm.trans (ha n hn)
            simp only [seqRun, hop, hs, hl, ↓reduceIte, Option.map_eq_some_iff] at hr
            obtain ⟨r, hrun, rfl⟩ := hr
            obtain ⟨r', hrun', he⟩ := ih hgt hau hrun
            exact ⟨r', hrun', by cases r <;> cases r' <;> exact he⟩
          · have hd' : discard i (scan nregs ms exit).2 = false := by
              cases h : discard i (scan nregs ms exit).2 <;> simp_all
            simp only [scan, hd', Bool.false_eq_true, ↓reduceIte] at ha ⊢
            have hu : vuses ops a = vuses ops b := retained_uses ha hop
            have hau : Agree (scan nregs ms exit).2
                (vdefUpd ops outs a) (vdefUpd ops outs b) :=
              retained_updates_agree hop ha outs hl
            have hsb : sem i (vuses ops b) w = some (outs, w', ctl) := by rw [← hu]; exact hs
            cases ctl with
            | next =>
              simp only [seqRun, hop, hs, hl, ↓reduceIte, Option.map_eq_some_iff] at hr
              obtain ⟨r, hrun, rfl⟩ := hr
              obtain ⟨r', hrun', he⟩ := ih hgt hau hrun
              refine ⟨r'.succ, ?_, SameEnd_succ he⟩
              simp [seqRun, hop, hsb, hl, hrun']
            | goto j =>
              have hm : ms = [] := hg [] i ms _ _ _ _ j rfl hs
              subst ms
              simp only [seqRun, hop, hs, hl, ↓reduceIte, Option.some.injEq] at hr
              subst result
              refine ⟨.stop 0 i ops b w outs w' (.goto j), ?_,
                rfl, rfl, rfl, rfl, rfl, rfl, hu, ?_⟩
              · simp [seqRun, hop, hsb, hl]
              · intro _ _; exact hau
            | ret =>
              simp only [seqRun, hop, hs, hl, ↓reduceIte, Option.some.injEq] at hr
              subst result
              refine ⟨.stop 0 i ops b w outs w' .ret, ?_,
                rfl, rfl, rfl, rfl, rfl, rfl, hu, ?_⟩
              · simp [seqRun, hop, hsb, hl]
              · intro j hj; cases hj
            | halt =>
              simp only [seqRun, hop, hs, hl, ↓reduceIte, Option.some.injEq] at hr
              subst result
              refine ⟨.stop 0 i ops b w outs w' .halt, ?_,
                rfl, rfl, rfl, rfl, rfl, rfl, hu, ?_⟩
              · simp [seqRun, hop, hsb, hl]
              · intro j hj; cases hj
        · simp [seqRun, hop, hs, hl] at hr

/-! Non-vacuity: execute a real dead producer, a live producer and an ABI
return. Both runs have the same return inputs and world. -/
example (w : Arm.ArmState) : ∃ r r',
    seqRun (mspec 0) [deadMvn, liveBic, liveReturn] (fun _ => 0#128) w = some r ∧
    seqRun (mspec 0) [liveBic, liveReturn] (fun _ => 0#128) w = some r' ∧
    SameEnd [] r r' := by
  have hg : GotoAtEnd (mspec 0) [deadMvn, liveBic, liveReturn] := by
    intro pre i post us w outs w' j he hs
    have hi : i ∈ [deadMvn, liveBic, liveReturn] := by
      rw [he]
      simp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · have hc := (mspec_pure (by decide : pureForm deadMvn = true) hs).2
      cases hc
    · have hc := (mspec_pure (by decide : pureForm liveBic = true) hs).2
      cases hc
    · simp [mspec, ispec, liveReturn] at hs
  have hr : ∃ r, seqRun (mspec 0) [deadMvn, liveBic, liveReturn]
      (fun _ => 0#128) w = some r := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ := hr
  obtain ⟨r', hr', he⟩ := scan_run (mspec 0)
    (fun _ _ _ _ _ _ hp hs => mspec_pure hp hs) 4
    [deadMvn, liveBic, liveReturn] [] hg (fun _ _ => rfl) hr
  exact ⟨r, r', hr, hr', he⟩

end Backend.DeadCleanup
