import FV.Backend.Proof.DeadCleanupLive

namespace Backend.DeadCleanup

/-- Every entry-live register was either live on exit or read in the block. -/
theorem scan_live_subset (nregs : Nat) (ms : List MInst) (exit : List Nat) :
    ∀ n ∈ (scan nregs ms exit).2, n ∈ exit ++ ms.flatMap (uses nregs) := by
  induction ms with
  | nil => simp [scan]
  | cons m ms ih =>
    intro n hn
    simp only [scan] at hn
    split at hn
    · have hi := ih n hn
      simpa only [List.flatMap_cons, List.mem_append] using
        (show n ∈ exit ∨ n ∈ uses nregs m ∨ n ∈ ms.flatMap (uses nregs) from
          (List.mem_append.mp hi).elim Or.inl (fun h => Or.inr (Or.inr h)))
    · rcases List.mem_append.mp hn with hu | ht
      · simp only [List.flatMap_cons, List.mem_append]
        exact Or.inr (Or.inl hu)
      · have hi := ih n (List.mem_filter.mp ht).1
        simp only [List.flatMap_cons, List.mem_append]
        exact (List.mem_append.mp hi).elim Or.inl (fun h => Or.inr (Or.inr h))

/-- Every entry-live register was either live on exit or read by a retained instruction. -/
theorem scan_live_kept (nregs : Nat) (ms : List MInst) (exit : List Nat) :
    ∀ n ∈ (scan nregs ms exit).2, n ∈ exit ++ (scan nregs ms exit).1.flatMap (uses nregs) := by
  induction ms with
  | nil => simp [scan]
  | cons m ms ih =>
    intro n hn
    simp only [scan] at hn ⊢
    split at hn
    · rename_i hd
      simp only [hd, ↓reduceIte]
      exact ih n hn
    · rename_i hd
      simp only [hd, ↓reduceIte, Bool.false_eq_true, List.flatMap_cons, List.mem_append] at hn ⊢
      rcases hn with hu | ht
      · exact .inr (.inl hu)
      · rcases List.mem_append.mp (ih n (List.mem_filter.mp ht).1) with he | hk
        · exact .inl he
        · exact .inr (.inr hk)

/-- A smaller live set kills at least as much: `discard` only asks that no def is live. -/
theorem discard_mono {m : MInst} {live live' : List Nat} (hl : ∀ n ∈ live', n ∈ live)
    (h : discard m live = true) : discard m live' = true := by
  simp only [discard, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h ⊢
  refine ⟨h.1, fun n hn => ?_⟩
  have hn' := h.2 n hn
  cases hc : live'.contains n
  · rfl
  · have := hl n (List.contains_iff_mem.mp hc)
    rw [List.contains_iff_mem.mpr this] at hn'
    cases hn'

/-- **The scan is monotone in its boundary**: a smaller live-out set keeps a sublist of the
code, leaves a smaller live-in set, and keeps the flags dead where they were dead. -/
theorem scan_mono (nregs : Nat) {L L' : List Nat} (hL : ∀ n ∈ L', n ∈ L) :
    ∀ ms : List MInst,
      (scan nregs ms L').1.Sublist (scan nregs ms L).1 ∧
      (∀ n ∈ (scan nregs ms L').2, n ∈ (scan nregs ms L).2) ∧
      (flagsDead (scan nregs ms L).1 = true → flagsDead (scan nregs ms L').1 = true)
  | [] => ⟨by simp [scan], by simpa [scan] using hL, fun h => by simp [scan] at h⟩
  | m :: ms => by
    have ih := scan_mono nregs hL ms
    rcases h1 : scan nregs ms L with ⟨k1, l1⟩
    rcases h2 : scan nregs ms L' with ⟨k2, l2⟩
    rw [h1, h2] at ih
    obtain ⟨hk, hl, hf⟩ := ih
    simp only [scan, h1, h2]
    have hd : (discard m l1 || dropCmp m k1) = true → (discard m l2 || dropCmp m k2) = true := by
      intro h
      rcases Bool.or_eq_true_iff.mp h with h | h
      · simp [discard_mono hl h]
      · have hc := dropCmp_cmp h
        have he := dropCmp_defs h
        simp [hc, he, hf (dropCmp_dead h)]
    by_cases d1 : (discard m l1 || dropCmp m k1) = true
    · simp only [d1, hd d1, ↓reduceIte]
      exact ⟨hk, hl, hf⟩
    · by_cases d2 : (discard m l2 || dropCmp m k2) = true
      · simp only [d1, d2, ↓reduceIte, Bool.false_eq_true]
        have hnd : ∀ n ∈ l2, (defs m).contains n = false := by
          intro n hn
          rcases Bool.or_eq_true_iff.mp d2 with h | h
          · cases hc : (defs m).contains n
            · rfl
            · exact absurd hn (discard_dead h n (List.contains_iff_mem.mp hc))
          · simp [dropCmp_defs h]
        refine ⟨hk.trans (List.sublist_cons_self m k1), fun n hn => ?_, fun h => ?_⟩
        · exact List.mem_append_right _
            (List.mem_filter.mpr ⟨hl n hn, by simp only [hnd n hn, Bool.not_false]⟩)
        · rcases Bool.or_eq_true_iff.mp d2 with hd2 | hd2
          · have hnc := pureForm_of_cmp (m := m)
            have hp := discard_pure hd2
            rcases flagsDead_cons h with hc | ⟨-, -, hk1⟩
            · rw [hnc hc] at hp; cases hp
            · exact hf hk1
          · exact dropCmp_dead hd2
      · simp only [d1, d2, ↓reduceIte, Bool.false_eq_true]
        refine ⟨hk.cons_cons m, fun n hn => ?_, fun h => ?_⟩
        · rcases List.mem_append.mp hn with hu | ht
          · exact List.mem_append_left _ hu
          · exact List.mem_append_right _
              (List.mem_filter.mpr ⟨hl n (List.mem_filter.mp ht).1, (List.mem_filter.mp ht).2⟩)
        · rcases flagsDead_cons h with hc | ⟨hc, hff, hk1⟩
          · simp [flagsDead, hc]
          · simp [flagsDead, hff, hf hk1]

/-- The boundary is a subset of the reads of the code. -/
theorem exitLive_allUses {vc : VCode} {idx : Nat} {other : VBlock} {n : Nat}
    (hn : n ∈ exitLive vc idx other) : n ∈ allUses vc := by
  simp only [exitLive, keptUses, List.mem_flatMap, List.mem_append] at hn
  obtain ⟨b, hb, hn⟩ := hn
  refine List.mem_flatMap.mpr ⟨b, hb, ?_⟩
  rcases hn with ha | ⟨i, hi, hu⟩
  · exact List.mem_append_left _ ha
  · exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨i, (scan_sublist _ _ _).subset hi, hu⟩)

/-- Every branch argument is live at all block boundaries. -/
theorem branchArgs_exit {vc : VCode} {b : VBlock} (hb : b ∈ vc.blocks.toList)
    {n : Nat} (hn : n ∈ regNums b.branchArgs.toList) (idx : Nat) (other : VBlock) :
    n ∈ exitLive vc idx other :=
  List.mem_flatMap.mpr ⟨b, hb, List.mem_append_left _ hn⟩

/-- A read of an instruction the cleanup keeps is live at all block boundaries, including its
own boundary on a self-loop: the cleanup keeps a sublist of what the first round keeps
(`scan_mono`), whose reads make up the boundary. -/
theorem kept_uses_exit {vc : VCode} {b : VBlock} (hb : b ∈ vc.blocks.toList) (idx : Nat)
    (other : VBlock) {n : Nat}
    (hn : n ∈ (scan vc.classes.size b.insts.toList (exitLive vc idx other)).1.flatMap
      (uses vc.classes.size)) :
    n ∈ exitLive vc idx other := by
  obtain ⟨i, hi, hu⟩ := List.mem_flatMap.mp hn
  have hsub := (scan_mono (L := allUses vc) (L' := exitLive vc idx other) vc.classes.size
    (fun _ h => exitLive_allUses h) b.insts.toList).1
  exact List.mem_flatMap.mpr ⟨b, hb, List.mem_append_right _
    (List.mem_flatMap.mpr ⟨i, hsub.subset hi, hu⟩)⟩

/-- **The boundary is closed**: what is live at the head of a block's cleaned code is live at
every boundary. -/
theorem live_closed {vc : VCode} {b : VBlock} (hb : b ∈ vc.blocks.toList) (idx : Nat)
    (other : VBlock) :
    ∀ n ∈ (scan vc.classes.size b.insts.toList (exitLive vc idx other)).2,
      n ∈ exitLive vc idx other := by
  intro n hn
  rcases List.mem_append.mp (scan_live_kept _ _ _ n hn) with he | hu
  · exact he
  · exact kept_uses_exit hb idx other hu

/-- Agreement on boundary-live registers suffices at a block's entry. -/
theorem scan_entry_agree {V : Type} {vc : VCode} {idx : Nat} {b : VBlock}
    (hb : b ∈ vc.blocks.toList) {a c : Nat → V}
    (ha : Agree (exitLive vc idx b) a c) :
    Agree (scan vc.classes.size b.insts.toList (exitLive vc idx b)).2 a c :=
  fun n hn => ha n (live_closed hb idx b n hn)

/-- Whitelisted producers cannot be block terminators. -/
theorem pureForm_notTerminator {m : MInst} (hp : pureForm m = true) :
    m.isTerminator = false := by
  cases m <;> simp [pureForm, MInst.isTerminator, MInst.isBranch, MInst.isRet] at *

/-- Compares cannot be block terminators. -/
theorem cmpForm_of_terminator {m : MInst} (h : m.isTerminator = true) : cmpForm m = false := by
  cases hc : cmpForm m
  · rfl
  · unfold cmpForm at hc
    split at hc <;> simp_all [MInst.isTerminator, MInst.isBranch, MInst.isRet]

/-- A successful CFG's final terminator survives cleanup. -/
theorem cleanBlock_back (vc : VCode) (idx : Nat) (b : VBlock) {t : MInst}
    (ht : b.insts.back? = some t) (hterm : t.isTerminator = true) :
    (cleanBlock vc idx b).insts.back? = some t := by
  have hp : pureForm t = false := by
    cases h : pureForm t
    · rfl
    · have := pureForm_notTerminator h
      simp_all
  have ht' : b.insts.toList.getLast? = some t := by simpa using ht
  obtain ⟨pre, he⟩ := List.getLast?_eq_some_iff.mp ht'
  simpa [cleanBlock, he] using
    scan_last vc.classes.size pre t (exitLive vc idx b) hp

/-! Non-vacuity: real instructions exercise live boundary and final return
preservation. The loop's input is live on its own boundary. -/
example : ∃ vc : VCode, 1 ∈ exitLive vc 0 vc.blocks[0]! ∧
    (clean vc).blocks[0]!.insts.back? = some liveReturn := by
  refine ⟨⟨"cleanup_flow", #[⟨0, #[deadMvn, liveBic, liveReturn], #[], #[]⟩],
    #[.int, .int, .int, .int], 0, 0, #[], #[], none⟩, ?_, ?_⟩ <;> decide

end Backend.DeadCleanup
