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

private theorem dropCmp_vdefUpd {V : Type} {m : MInst} {kept : List MInst}
    (h : dropCmp m kept = true) {ops : Array Operand} (hop : m.operands = .ok ops)
    (outs : List V) (ρ : Nat → V) : vdefUpd ops outs ρ = ρ := by
  simp only [vdefUpd, dropCmp_noDef h hop, List.zip_nil_left, List.filter_nil]
  rfl

/-- `scan_run` from a cleaned world that may differ from the original one while a dropped
compare's flags wait to be overwritten by the next retained compare. -/
private theorem scan_run_pend {V W : Type} (sem : ISem V W)
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hcmp : CmpOverwrite sem)
    (nregs : Nat) (ms : List MInst) (exit : List Nat)
    (hg : GotoAtEnd sem ms) {a b : Nat → V} {w wb : W} {result : SeqEnd V W}
    (ha : Agree (scan nregs ms exit).2 a b)
    (hw : wb = w ∨ ((∃ K rest, (scan nregs ms exit).1 = K :: rest ∧ cmpForm K = true) ∧
      ∀ K us r, cmpForm K = true → sem K us w = some r → sem K us wb = some r))
    (hr : seqRun sem ms a w = some result) :
    ∃ result', seqRun sem (scan nregs ms exit).1 b wb = some result' ∧
      SameEnd exit result result' := by
  induction ms generalizing a b w wb result with
  | nil =>
    simp only [seqRun, Option.some.injEq] at hr
    subst result
    rcases hw with rfl | ⟨⟨K, rest, hK, -⟩, -⟩
    · exact ⟨.fall b wb, rfl, rfl, ha⟩
    · simp [scan] at hK
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
            simp only [scan, hd, Bool.true_or, ↓reduceIte] at ha hw ⊢
            have hau : Agree (scan nregs ms exit).2 (vdefUpd ops outs a) b := by
              intro n hn
              exact (discard_updates_agree hd hop a outs n hn).symm.trans (ha n hn)
            simp only [seqRun, hop, hs, hl, ↓reduceIte, Option.map_eq_some_iff] at hr
            obtain ⟨r, hrun, rfl⟩ := hr
            obtain ⟨r', hrun', he⟩ := ih hgt hau hw hrun
            exact ⟨r', hrun', by cases r <;> cases r' <;> exact he⟩
          · have hd' : discard i (scan nregs ms exit).2 = false := by
              cases h : discard i (scan nregs ms exit).2 <;> simp_all
            by_cases hdc : dropCmp i (scan nregs ms exit).1 = true
            · obtain ⟨hc, hov⟩ := hcmp _ _ _ _ _ _ (dropCmp_cmp hdc) hs
              subst hc
              simp only [scan, hd', hdc, Bool.false_or, ↓reduceIte] at ha hw ⊢
              have hau : Agree (scan nregs ms exit).2 (vdefUpd ops outs a) b := by
                rw [dropCmp_vdefUpd hdc hop]
                exact ha
              simp only [seqRun, hop, hs, hl, ↓reduceIte, Option.map_eq_some_iff] at hr
              obtain ⟨r, hrun, rfl⟩ := hr
              have hw' : wb = w' ∨ ((∃ K rest, (scan nregs ms exit).1 = K :: rest ∧
                  cmpForm K = true) ∧
                  ∀ K us r, cmpForm K = true → sem K us w' = some r → sem K us wb = some r) := by
                refine .inr ⟨dropCmp_head hdc, ?_⟩
                intro K us r hK h
                have h1 := hov K us r hK h
                rcases hw with rfl | ⟨-, h0⟩
                · exact h1
                · exact h0 K us r hK h1
              obtain ⟨r', hrun', he⟩ := ih hgt hau hw' hrun
              exact ⟨r', hrun', by cases r <;> cases r' <;> exact he⟩
            · have hdc' : dropCmp i (scan nregs ms exit).1 = false := by
                cases h : dropCmp i (scan nregs ms exit).1 <;> simp_all
              simp only [scan, hd', hdc', Bool.false_or, Bool.false_eq_true, ↓reduceIte]
                at ha hw ⊢
              have hu : vuses ops a = vuses ops b := retained_uses ha hop
              have hau : Agree (scan nregs ms exit).2
                  (vdefUpd ops outs a) (vdefUpd ops outs b) :=
                retained_updates_agree hop ha outs hl
              -- the retained instruction runs from the cleaned world to the same result
              have hsw : sem i (vuses ops a) wb = some (outs, w', ctl) := by
                rcases hw with rfl | ⟨⟨K, rest, hK, hKc⟩, hov⟩
                · exact hs
                · have hiK : i = K := (List.cons.inj hK).1
                  subst hiK
                  exact hov _ _ _ hKc hs
              have hsb : sem i (vuses ops b) wb = some (outs, w', ctl) := by
                rw [← hu]; exact hsw
              -- a stopping instruction is not a compare, so the worlds agree there
              have hstop : ctl ≠ .next → wb = w := by
                intro hn
                rcases hw with h | ⟨⟨K, rest, hK, hKc⟩, -⟩
                · exact h
                · have hiK : i = K := (List.cons.inj hK).1
                  subst hiK
                  exact absurd (hcmp _ _ _ _ _ _ hKc hs).1 hn
              cases ctl with
              | next =>
                simp only [seqRun, hop, hs, hl, ↓reduceIte, Option.map_eq_some_iff] at hr
                obtain ⟨r, hrun, rfl⟩ := hr
                obtain ⟨r', hrun', he⟩ := ih hgt hau (.inl rfl) hrun
                refine ⟨r'.succ, ?_, SameEnd_succ he⟩
                simp [seqRun, hop, hsb, hl, hrun']
              | goto j =>
                obtain rfl := hstop (by intro h; cases h)
                have hm : ms = [] := hg [] i ms _ _ _ _ j rfl hs
                subst ms
                simp only [seqRun, hop, hs, hl, ↓reduceIte, Option.some.injEq] at hr
                subst result
                refine ⟨.stop 0 i ops b wb outs w' (.goto j), ?_,
                  rfl, rfl, rfl, rfl, rfl, rfl, hu, ?_⟩
                · simp [seqRun, hop, hsb, hl]
                · intro _ _; exact hau
              | ret =>
                obtain rfl := hstop (by intro h; cases h)
                simp only [seqRun, hop, hs, hl, ↓reduceIte, Option.some.injEq] at hr
                subst result
                refine ⟨.stop 0 i ops b wb outs w' .ret, ?_,
                  rfl, rfl, rfl, rfl, rfl, rfl, hu, ?_⟩
                · simp [seqRun, hop, hsb, hl]
                · intro j hj; cases hj
              | halt =>
                obtain rfl := hstop (by intro h; cases h)
                simp only [seqRun, hop, hs, hl, ↓reduceIte, Option.some.injEq] at hr
                subst result
                refine ⟨.stop 0 i ops b wb outs w' .halt, ?_,
                  rfl, rfl, rfl, rfl, rfl, rfl, hu, ?_⟩
                · simp [seqRun, hop, hsb, hl]
                · intro j hj; cases hj
        · simp [seqRun, hop, hs, hl] at hr

/-- Removing dead pure producers, and compares whose flags the next retained compare
overwrites, preserves successful block runs. This generic lemma requires exact world
purity; concrete register bookkeeping is handled by an adapter when this is composed with
the machine-code theorem. -/
theorem scan_run {V W : Type} (sem : ISem V W)
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hcmp : CmpOverwrite sem)
    (nregs : Nat) (ms : List MInst) (exit : List Nat)
    (hg : GotoAtEnd sem ms) {a b : Nat → V} {w : W} {result : SeqEnd V W}
    (ha : Agree (scan nregs ms exit).2 a b)
    (hr : seqRun sem ms a w = some result) :
    ∃ result', seqRun sem (scan nregs ms exit).1 b w = some result' ∧
      SameEnd exit result result' :=
  scan_run_pend sem hp hcmp nregs ms exit hg ha (.inl rfl) hr

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
    (fun _ _ _ _ _ _ hp hs => mspec_pure hp hs) (mspec_cmpOverwrite 0) 4
    [deadMvn, liveBic, liveReturn] [] hg (fun _ _ => rfl) hr
  exact ⟨r, r', hr, hr', he⟩

end Backend.DeadCleanup
