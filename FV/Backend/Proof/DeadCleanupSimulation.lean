import FV.Backend.Proof.DeadCleanupEdges
import FV.Backend.Proof.IselContract
import FV.Backend.Proof.PrepareComplete

namespace Backend.DeadCleanup
open Backend.Proof

section
variable {V W : Type}

/-- The unconsumed cleaned suffix agrees on the registers its original suffix
can still read. Removed producers are matched by zero steps. After a dropped compare
(`pend`) the worlds may differ (`FlagsPend`) while the retained suffix runs flag-free
producers, until a retained compare of the same block overwrites the difference. -/
inductive Rel (vc : VCode) (sem : ISem V W) : VConf V W → VConf V W → Prop
  | run {b k k' a c w vb} (hb : vc.blocks[b]? = some vb)
      (hsuffix : (cleanBlock vc 0 vb).insts.toList.drop k' =
        (scan vc.classes.size (vb.insts.toList.drop k) (exitLive vc 0 vb)).1)
      (ha : Agree (scan vc.classes.size (vb.insts.toList.drop k) (exitLive vc 0 vb)).2 a c) :
      Rel vc sem (.run ⟨b, k, a, w⟩) (.run ⟨b, k', c, w⟩)
  | pend {b k k' a c w w' vb} (hb : vc.blocks[b]? = some vb)
      (hsuffix : (cleanBlock vc 0 vb).insts.toList.drop k' =
        (scan vc.classes.size (vb.insts.toList.drop k) (exitLive vc 0 vb)).1)
      (ha : Agree (scan vc.classes.size (vb.insts.toList.drop k) (exitLive vc 0 vb)).2 a c)
      (hdead : flagsDead ((cleanBlock vc 0 vb).insts.toList.drop k') = true)
      (hov : FlagsPend sem w w') :
      Rel vc sem (.run ⟨b, k, a, w⟩) (.run ⟨b, k', c, w'⟩)
  | ret (vals : List V) (w : W) : Rel vc sem (.ret vals w) (.ret vals w)
  | halt (w : W) : Rel vc sem (.halt w) (.halt w)

private theorem scan_nonempty {nregs : Nat} {ms : List MInst} {exit : List Nat}
    {t : MInst} (ht : ms.getLast? = some t) (hp : pureForm t = false) :
    (scan nregs ms exit).1 ≠ [] := by
  obtain ⟨pre, rfl⟩ := List.getLast?_eq_some_iff.mp ht
  have hh := scan_last nregs pre t exit hp
  intro he
  simp [he] at hh

private theorem suffix_nonempty {vc : VCode} {vb : VBlock} {k : Nat}
    (ht : ∃ t, vb.insts.back? = some t ∧ t.isTerminator = true)
    (hk : k < vb.insts.size) :
    (scan vc.classes.size (vb.insts.toList.drop k) (exitLive vc 0 vb)).1 ≠ [] := by
  obtain ⟨t, hb, hterm⟩ := ht
  have hp : pureForm t = false := by
    cases h : pureForm t
    · rfl
    · have := pureForm_notTerminator h; simp_all
  apply scan_nonempty (t := t) _ hp
  simpa [List.getLast?_drop, Nat.not_le.mpr hk] using hb

/-- The data both run-time constructors share; `WRel` relates the worlds. -/
private theorem rel_run_cases {vc : VCode} {sem : ISem V W} {b k : Nat} {a : Nat → V} {w : W}
    {c' : VConf V W}
    (hr : Rel vc sem (.run ⟨b, k, a, w⟩) c') :
    ∃ k' c wc vb, c' = .run ⟨b, k', c, wc⟩ ∧ vc.blocks[b]? = some vb ∧
      (cleanBlock vc 0 vb).insts.toList.drop k' =
        (scan vc.classes.size (vb.insts.toList.drop k) (exitLive vc 0 vb)).1 ∧
      Agree (scan vc.classes.size (vb.insts.toList.drop k) (exitLive vc 0 vb)).2 a c ∧
      (wc = w ∨ (flagsDead ((cleanBlock vc 0 vb).insts.toList.drop k') = true ∧
        FlagsPend sem w wc)) := by
  cases hr with
  | run hb hsuffix ha => exact ⟨_, _, _, _, rfl, hb, hsuffix, ha, .inl rfl⟩
  | pend hb hsuffix ha hdead hov => exact ⟨_, _, _, _, rfl, hb, hsuffix, ha, .inr ⟨hdead, hov⟩⟩

/-- Rebuild the relation from the shared data. -/
private theorem rel_of_cases {vc : VCode} {sem : ISem V W} {b k k' a c w wc vb}
    (hb : vc.blocks[b]? = some vb)
    (hsuffix : (cleanBlock vc 0 vb).insts.toList.drop k' =
      (scan vc.classes.size (vb.insts.toList.drop k) (exitLive vc 0 vb)).1)
    (ha : Agree (scan vc.classes.size (vb.insts.toList.drop k) (exitLive vc 0 vb)).2 a c)
    (hw : wc = w ∨ (flagsDead ((cleanBlock vc 0 vb).insts.toList.drop k') = true ∧
      FlagsPend sem w wc)) :
    Rel vc sem (.run ⟨b, k, a, w⟩) (.run ⟨b, k', c, wc⟩) := by
  rcases hw with rfl | ⟨hdead, hov⟩
  · exact .run hb hsuffix ha
  · exact .pend hb hsuffix ha hdead hov

private theorem writeV_nil (ρ : Nat → V) : writeV ρ [] = ρ := rfl

/-- One original step is matched by zero or one cleaned step. -/
theorem step_sim {vc : VCode} {sem : ISem V W}
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hcmp : CmpOverwrite sem)
    (ht : ∀ vb ∈ vc.blocks.toList, ∃ t, vb.insts.back? = some t ∧ t.isTerminator = true)
    {v v1 c : VConf V W} (hr : Rel vc sem v c) (hv : VStep vc sem v v1) :
    ∃ c1, Star (VStep (clean vc) sem) c c1 ∧ Rel vc sem v1 c1 := by
  cases hv with
  | @step b k a w vb i ops outs w' ctl v1 hb hi hop hs hl hn =>
    obtain ⟨k', c, wc, vb', rfl, hb', hsuffix, ha, hw⟩ := rel_run_cases hr
    rw [hb] at hb'; cases hb'
    have hik := (Array.getElem?_eq_some_iff.mp hi).1
    have hdrop : vb.insts.toList.drop k = i :: vb.insts.toList.drop (k + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hik)]
      have he := (Array.getElem?_eq_some_iff.mp hi).2
      simp only [Array.getElem_toList]
      rw [he]
    let tail := vb.insts.toList.drop (k + 1)
    let live := (scan vc.classes.size tail (exitLive vc 0 vb)).2
    let kept := (scan vc.classes.size tail (exitLive vc 0 vb)).1
    by_cases hd : discard i live = true
    · have hworld := hp _ _ _ _ _ _ (discard_pure hd) hs
      obtain ⟨hw', hc⟩ := hworld
      subst w' ctl
      cases hn with
      | next hk =>
        dsimp only [live, tail] at hd
        simp only [hdrop, scan, hd, Bool.true_or, ↓reduceIte] at ha hsuffix
        refine ⟨.run ⟨b, k', c, wc⟩, .refl _, rel_of_cases hb hsuffix ?_ hw⟩
        intro n hn
        exact (discard_updates_agree hd hop a outs n hn).symm.trans (ha n hn)
    · have hd0 : discard i live = false := by
        cases he : discard i live <;> simp_all
      by_cases hdc : dropCmp i kept = true
      · -- a dropped compare: the worlds now differ until a retained compare
        obtain ⟨hc, hov⟩ := hcmp.1 _ _ _ _ _ _ (dropCmp_cmp hdc) hs
        subst ctl
        have hnd := dropCmp_noDef hdc hop
        cases hn with
        | next hk =>
          dsimp only [live, kept, tail] at hd0 hdc
          simp only [hdrop, scan, hd0, hdc, Bool.false_or, ↓reduceIte] at ha hsuffix
          refine ⟨.run ⟨b, k', c, wc⟩, .refl _, ?_⟩
          simp only [hnd, List.zip_nil_left, List.filter_nil, writeV_nil]
          refine .pend hb hsuffix ha (by rw [hsuffix]; exact dropCmp_dead hdc) ?_
          rcases hw with rfl | ⟨-, hov0⟩
          · exact hov
          · exact hov.trans hov0
      · have hdc0 : dropCmp i kept = false := by
          cases he : dropCmp i kept <;> simp_all
        dsimp only [live, kept, tail] at hd0 hdc0
        simp only [hdrop, scan, hd0, hdc0, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
          at ha hsuffix
        have hhead : (cleanBlock vc 0 vb).insts[k']? = some i := by
          have he := congrArg (·[0]?) hsuffix
          simpa using he
        have htail : (cleanBlock vc 0 vb).insts.toList.drop (k' + 1) =
            (scan vc.classes.size tail (exitLive vc 0 vb)).1 := by
          have he := congrArg (List.drop 1) hsuffix
          simpa [List.drop_drop, Nat.add_comm] using he
        have hu : vuses ops a = vuses ops c := retained_uses ha hop
        -- the cleaned step: the same values; with pending flags, a retained compare reaches
        -- the original world, a flag-free producer keeps both worlds
        obtain ⟨wc', hsc, hw'⟩ : ∃ wc', sem i (vuses ops c) wc = some (outs, wc', ctl) ∧
            (wc' = w' ∨ (ctl = .next ∧
              flagsDead ((cleanBlock vc 0 vb).insts.toList.drop (k' + 1)) = true ∧
              FlagsPend sem w' wc')) := by
          rw [← hu]
          rcases hw with rfl | ⟨hdead, hov⟩
          · exact ⟨w', hs, .inl rfl⟩
          · rw [hsuffix] at hdead
            rcases flagsDead_cons hdead with hK | ⟨-, hff, hdead'⟩
            · exact ⟨w', hov.1 i _ _ hK hs, .inl rfl⟩
            · obtain ⟨rfl, rfl⟩ := hp _ _ _ _ _ _ (pureForm_of_flagFree hff) hs
              exact ⟨wc, hov.2 i _ outs .next (by simp [hff]) hs,
                .inr ⟨rfl, by rw [htail]; exact hdead', hov⟩⟩
        have hstop : ctl ≠ .next → wc' = w' := fun hn => by
          rcases hw' with h | h
          · exact h
          · exact absurd h.1 hn
        have hau : Agree live (vdefUpd ops outs a) (vdefUpd ops outs c) :=
          retained_updates_agree hop ha outs hl
        have hclean := clean_block hb
        cases hn with
        | next hk =>
          have hne := suffix_nonempty (vc := vc)
            (ht vb (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hb))) hk
          have hkl : k' + 1 < (cleanBlock vc 0 vb).insts.size := by
            apply Nat.lt_of_not_ge
            intro hh
            have hnil : (cleanBlock vc 0 vb).insts.toList.drop (k' + 1) = [] :=
              List.drop_eq_nil_of_le (by simpa using hh)
            exact hne (htail.symm.trans hnil)
          have hw'' : wc' = w' ∨ (flagsDead ((cleanBlock vc 0 vb).insts.toList.drop (k' + 1))
              = true ∧ FlagsPend sem w' wc') := by
            rcases hw' with h | h
            · exact .inl h
            · exact .inr h.2
          refine ⟨.run ⟨b, k' + 1, vdefUpd ops outs c, wc'⟩,
            .step (VStep.step hclean hhead hop hsc hl (VNext.next hkl)) (.refl _),
            rel_of_cases hb htail hau hw''⟩
        | @goto j s a' hk hsucc hedge =>
          have hempty : tail = [] := List.drop_eq_nil_of_le (by simp only [Array.length_toList]; omega)
          have hau' : Agree (exitLive vc 0 vb) (vdefUpd ops outs a) (vdefUpd ops outs c) := by
            simpa [live, hempty, scan] using hau
          have hks : k' + 1 = (cleanBlock vc 0 vb).insts.size := by
            have hbound := (Array.getElem?_eq_some_iff.mp hhead).1
            have hnil : (cleanBlock vc 0 vb).insts.toList.drop (k' + 1) = [] := by
              simpa [hempty, scan] using htail
            have := List.length_eq_zero_iff.mpr hnil
            simp only [List.length_drop, Array.length_toList] at this
            omega
          obtain ⟨sb, hsb⟩ : ∃ sb, vc.blocks[s]? = some sb := by
            cases he : vc.blocks[s]? with
            | none => simp [edgeEnv, hb, he, bind, Option.bind] at hedge
            | some sb => exact ⟨sb, rfl⟩
          obtain ⟨c', hedge', hag⟩ := clean_edge hb hsb hau' hedge
          have hsuc' : succOf (clean vc) b j = some s := by
            simpa [succOf, clean_cfg vc ht] using hsucc
          have hentry := scan_entry_agree
            (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hsb)) hag
          rcases hw' with rfl | h
          · refine ⟨.run ⟨s, 0, c', wc'⟩,
              .step (VStep.step hclean hhead hop hsc hl (VNext.goto hks hsuc' hedge')) (.refl _),
              .run hsb ?_ hentry⟩
            simp [cleanBlock]
          · cases h.1
        | ret he =>
          have e := hstop (by intro h; cases h); subst wc'
          refine ⟨.ret (vuses ops c) w',
            .step (VStep.step hclean hhead hop hsc hl (VNext.ret he)) (.refl _), ?_⟩
          rw [← hu]
          exact .ret _ _
        | halt =>
          have e := hstop (by intro h; cases h); subst wc'
          exact ⟨.halt w', .step (VStep.step hclean hhead hop hsc hl VNext.halt) (.refl _), .halt _⟩

/-- Whole finite runs preserve the simulation relation, including loop edges. -/
theorem star_sim {vc : VCode} {sem : ISem V W}
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hcmp : CmpOverwrite sem)
    (ht : ∀ vb ∈ vc.blocks.toList, ∃ t, vb.insts.back? = some t ∧ t.isTerminator = true)
    {v v1 c : VConf V W} (hr : Rel vc sem v c) (hv : Star (VStep vc sem) v v1) :
    ∃ c1, Star (VStep (clean vc) sem) c c1 ∧ Rel vc sem v1 c1 := by
  induction hv generalizing c with
  | refl => exact ⟨c, .refl _, hr⟩
  | step h _ ih =>
    obtain ⟨c1, hs, hr1⟩ := step_sim hp hcmp ht hr h
    obtain ⟨c2, hs2, hr2⟩ := ih hr1
    exact ⟨c2, hs.trans hs2, hr2⟩

/-- At an effectful observation (not a pure producer, not a compare, not a `jump`), both runs
read identical operand values in the same world. -/
theorem rel_kept {vc : VCode} {sem : ISem V W} {b k : Nat} {a : Nat → V} {w : W}
    {c : VConf V W} {vb : VBlock} {i : MInst} {ops : Array Operand}
    (hr : Rel vc sem (.run ⟨b, k, a, w⟩) c) (hb : vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some i) (hop : i.operands = .ok ops)
    (hp : pureForm i = false) (hc : cmpForm i = false) (hj : isJump i = false) :
    ∃ k' a', c = .run ⟨b, k', a', w⟩ ∧
      (clean vc).blocks[b]? = some (cleanBlock vc 0 vb) ∧
      (cleanBlock vc 0 vb).insts[k']? = some i ∧ vuses ops a = vuses ops a' := by
  obtain ⟨k', a', wc, vb', rfl, hb', hsuffix, ha, hw⟩ := rel_run_cases hr
  rw [hb] at hb'; cases hb'
  have hik := (Array.getElem?_eq_some_iff.mp hi).1
  have hdrop : vb.insts.toList.drop k = i :: vb.insts.toList.drop (k + 1) := by
    rw [List.drop_eq_getElem_cons (by simpa using hik)]
    have he := (Array.getElem?_eq_some_iff.mp hi).2
    simp only [Array.getElem_toList]
    rw [he]
  simp only [hdrop, scan, discard, hp, dropCmp, hc, Bool.false_and, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte] at ha hsuffix
  have hwc : wc = w := by
    rcases hw with h | ⟨hdead, -⟩
    · exact h
    · rw [hsuffix] at hdead
      rcases flagsDead_cons hdead with hK | ⟨-, hff, -⟩
      · rw [hc] at hK; cases hK
      · rw [pureForm_of_flagFree hff] at hp; cases hp
  subst hwc
  have hhead : (cleanBlock vc 0 vb).insts[k']? = some i := by
    have he := congrArg (·[0]?) hsuffix
    simpa using he
  exact ⟨k', a', rfl, clean_block hb, hhead, retained_uses ha hop⟩

end
end Backend.DeadCleanup
