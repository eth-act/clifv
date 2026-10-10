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

/-- Reading in any block makes a register live at all block boundaries,
including its own boundary on a self-loop. -/
theorem blockUses_exit {vc : VCode} {b : VBlock} (hb : b ∈ vc.blocks.toList)
    {n : Nat} (hn : n ∈ blockUses vc.classes.size b) (idx : Nat) (other : VBlock) :
    n ∈ exitLive vc idx other := List.mem_flatMap.mpr ⟨b, hb, hn⟩

/-- Agreement on boundary-live registers suffices at a block's entry. -/
theorem scan_entry_agree {V : Type} {vc : VCode} {idx : Nat} {b : VBlock}
    (hb : b ∈ vc.blocks.toList) {a c : Nat → V}
    (ha : Agree (exitLive vc idx b) a c) :
    Agree (scan vc.classes.size b.insts.toList (exitLive vc idx b)).2 a c := by
  intro n hn
  apply ha n
  rcases List.mem_append.mp (scan_live_subset _ _ _ n hn) with he | hu
  · exact he
  · exact blockUses_exit hb (List.mem_append_right _ hu) idx b

/-- Whitelisted producers cannot be block terminators. -/
theorem pureForm_notTerminator {m : MInst} (hp : pureForm m = true) :
    m.isTerminator = false := by
  cases m <;> simp [pureForm, MInst.isTerminator, MInst.isBranch, MInst.isRet] at *

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
  simpa [cleanBlock, he] using scan_last vc.classes.size pre t (exitLive vc idx b) hp

/-! Non-vacuity: real instructions exercise live boundary and final return
preservation. The loop's input is live on its own boundary. -/
example : ∃ vc : VCode, 1 ∈ exitLive vc 0 vc.blocks[0]! ∧
    (clean vc).blocks[0]!.insts.back? = some liveReturn := by
  refine ⟨⟨"cleanup_flow", #[⟨0, #[deadMvn, liveBic, liveReturn], #[], #[]⟩],
    #[.int, .int, .int, .int], 0, 0, #[]⟩, ?_, ?_⟩ <;> decide

end Backend.DeadCleanup
