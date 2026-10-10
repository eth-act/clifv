import FV.Backend.Proof.DeadCleanupEdges
import FV.Backend.Proof.IselContract

namespace Backend.DeadCleanup
open Backend.Proof

section
variable {V W : Type}

/-- The unconsumed cleaned suffix agrees on the registers its original suffix
can still read. Removed producers are matched by zero steps. -/
inductive Rel (vc : VCode) : VConf V W → VConf V W → Prop
  | run {b k k' a c w vb} (hb : vc.blocks[b]? = some vb)
      (hsuffix : (cleanBlock vc 0 vb).insts.toList.drop k' =
        (scan vc.classes.size (vb.insts.toList.drop k) (exitLive vc 0 vb)).1)
      (ha : Agree (scan vc.classes.size (vb.insts.toList.drop k) (exitLive vc 0 vb)).2 a c) :
      Rel vc (.run ⟨b, k, a, w⟩) (.run ⟨b, k', c, w⟩)
  | ret (vals : List V) (w : W) : Rel vc (.ret vals w) (.ret vals w)
  | halt (w : W) : Rel vc (.halt w) (.halt w)

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

/-- One original step is matched by zero or one cleaned step. -/
theorem step_sim {vc : VCode} {sem : ISem V W}
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (ht : ∀ vb ∈ vc.blocks.toList, ∃ t, vb.insts.back? = some t ∧ t.isTerminator = true)
    {v v1 c : VConf V W} (hr : Rel vc v c) (hv : VStep vc sem v v1) :
    ∃ c1, Star (VStep (clean vc) sem) c c1 ∧ Rel vc v1 c1 := by
  cases hv with
  | @step b k a w vb i ops outs w' ctl v1 hb hi hop hs hl hn =>
    cases hr with
    | @run _ _ k' _ c _ vb' hb' hsuffix ha =>
      rw [hb] at hb'; cases hb'
      have hik := (Array.getElem?_eq_some_iff.mp hi).1
      have hdrop : vb.insts.toList.drop k = i :: vb.insts.toList.drop (k + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hik)]
        have he := (Array.getElem?_eq_some_iff.mp hi).2
        simp only [Array.getElem_toList]
        rw [he]
      let tail := vb.insts.toList.drop (k + 1)
      let live := (scan vc.classes.size tail (exitLive vc 0 vb)).2
      by_cases hd : discard i live = true
      · have hworld := hp _ _ _ _ _ _ (discard_pure hd) hs
        obtain ⟨hw, hc⟩ := hworld
        subst w' ctl
        cases hn with
        | next hk =>
          dsimp only [live, tail] at hd
          simp only [hdrop, scan, hd, ↓reduceIte] at ha hsuffix
          refine ⟨.run ⟨b, k', c, w⟩, .refl _, .run hb hsuffix ?_⟩
          intro n hn
          exact (discard_updates_agree hd hop a outs n hn).symm.trans (ha n hn)
      · have hd' : discard i live = false := by
          cases he : discard i live <;> simp_all
        dsimp only [live, tail] at hd'
        simp only [hdrop, scan, hd', Bool.false_eq_true, ↓reduceIte] at ha hsuffix
        have hhead : (cleanBlock vc 0 vb).insts[k']? = some i := by
          have he := congrArg (·[0]?) hsuffix
          simpa using he
        have htail : (cleanBlock vc 0 vb).insts.toList.drop (k' + 1) =
            (scan vc.classes.size tail (exitLive vc 0 vb)).1 := by
          have he := congrArg (List.drop 1) hsuffix
          simpa [List.drop_drop, Nat.add_comm] using he
        have hu : vuses ops a = vuses ops c := retained_uses ha hop
        have hsc : sem i (vuses ops c) w = some (outs, w', ctl) := by rw [← hu]; exact hs
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
          refine ⟨.run ⟨b, k' + 1, vdefUpd ops outs c, w'⟩,
            .step (VStep.step hclean hhead hop hsc hl (VNext.next hkl)) (.refl _),
            .run hb htail hau⟩
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
          refine ⟨.run ⟨s, 0, c', w'⟩,
            .step (VStep.step hclean hhead hop hsc hl (VNext.goto hks hsuc' hedge')) (.refl _),
            .run hsb ?_ ?_⟩
          · simp [cleanBlock]
          · exact scan_entry_agree (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hsb)) hag
        | ret he =>
          refine ⟨.ret (vuses ops c) w',
            .step (VStep.step hclean hhead hop hsc hl (VNext.ret he)) (.refl _), ?_⟩
          rw [← hu]
          exact .ret _ _
        | halt =>
          exact ⟨.halt w', .step (VStep.step hclean hhead hop hsc hl VNext.halt) (.refl _), .halt _⟩

/-- Whole finite runs preserve the simulation relation, including loop edges. -/
theorem star_sim {vc : VCode} {sem : ISem V W}
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (ht : ∀ vb ∈ vc.blocks.toList, ∃ t, vb.insts.back? = some t ∧ t.isTerminator = true)
    {v v1 c : VConf V W} (hr : Rel vc v c) (hv : Star (VStep vc sem) v v1) :
    ∃ c1, Star (VStep (clean vc) sem) c c1 ∧ Rel vc v1 c1 := by
  induction hv generalizing c with
  | refl => exact ⟨c, .refl _, hr⟩
  | step h _ ih =>
    obtain ⟨c1, hs, hr1⟩ := step_sim hp ht hr h
    obtain ⟨c2, hs2, hr2⟩ := ih hr1
    exact ⟨c2, hs.trans hs2, hr2⟩

/-- At an effectful observation, both runs read identical operand values. -/
theorem rel_kept {vc : VCode} {b k : Nat} {a : Nat → V} {w : W} {c : VConf V W}
    {vb : VBlock} {i : MInst} {ops : Array Operand}
    (hr : Rel vc (.run ⟨b, k, a, w⟩) c) (hb : vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some i) (hop : i.operands = .ok ops)
    (hp : pureForm i = false) :
    ∃ k' a', c = .run ⟨b, k', a', w⟩ ∧
      (clean vc).blocks[b]? = some (cleanBlock vc 0 vb) ∧
      (cleanBlock vc 0 vb).insts[k']? = some i ∧ vuses ops a = vuses ops a' := by
  cases hr with
  | @run _ _ k' _ a' _ vb' hb' hsuffix ha =>
    rw [hb] at hb'; cases hb'
    have hik := (Array.getElem?_eq_some_iff.mp hi).1
    have hdrop : vb.insts.toList.drop k = i :: vb.insts.toList.drop (k + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hik)]
      have he := (Array.getElem?_eq_some_iff.mp hi).2
      simp only [Array.getElem_toList]
      rw [he]
    simp only [hdrop, scan, discard, hp, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte] at ha hsuffix
    have hhead : (cleanBlock vc 0 vb).insts[k']? = some i := by
      have he := congrArg (·[0]?) hsuffix
      simpa using he
    exact ⟨k', a', rfl, clean_block hb, hhead, retained_uses ha hop⟩

end
end Backend.DeadCleanup
