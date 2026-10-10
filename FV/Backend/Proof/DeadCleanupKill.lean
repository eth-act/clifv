import FV.Backend.Proof.DeadCleanupPrepare
import FV.Backend.Proof.KillPrep

namespace Backend.DeadCleanup
open Backend.Proof Backend.Proof.Spill

/-- The pass never deletes an instruction with an unstored definition. -/
theorem pure_unstored {i : MInst} (hp : pureForm i = true) : unstored i = [] := by
  have ht := pureForm_notTerminator hp
  have hk := (pureForm_keptDefs hp).1
  unfold unstored
  cases ho : i.operands with
  | error e => rfl
  | ok ops =>
    simp only [ho, storedDefs, ht, Bool.false_eq_true, ite_false, hk]
    apply List.filter_eq_nil_iff.mpr
    intro n hn
    simp [hn]

/-- Deleting pure instructions preserves the killed-register list exactly. -/
theorem scan_unstored (nregs : Nat) (ms : List MInst) (live : List Nat) :
    (scan nregs ms live).1.flatMap unstored = ms.flatMap unstored := by
  induction ms with
  | nil => rfl
  | cons i ms ih =>
    simp only [scan]
    split
    · rename_i hd
      rw [List.flatMap_cons, pure_unstored (discard_pure hd), List.nil_append]
      exact ih
    · simpa using congrArg (unstored i ++ ·) ih

theorem clean_killedOf (vc : VCode) : killedOf (clean vc) = killedOf vc := by
  simp only [killedOf, clean_blocks_map, Array.toList_map, List.flatMap_map]
  change ((vc.blocks.toList.map fun vb => (cleanBlock vc 0 vb).insts.toList.flatMap unstored).flatten) = _
  apply congrArg List.flatten
  apply List.map_congr_left
  intro vb hb
  simpa [cleanBlock] using scan_unstored vc.classes.size vb.insts.toList (exitLive vc 0 vb)

theorem clean_termEdgeDefs {vc : VCode} {ss ps : Array (Array Nat)}
    (hcfg : vc.cfg = .ok (ss, ps)) {b : Nat} {vb : VBlock}
    (hb : vc.blocks[b]? = some vb) (j : Nat) :
    termEdgeDefs (cleanBlock vc 0 vb) j = termEdgeDefs vb j := by
  obtain ⟨t, ts, ht, hterm, _⟩ := (Prep.cfg_spec hcfg).blk b vb hb
  simp only [termEdgeDefs, cleanBlock_back vc 0 vb ht hterm, ht]

theorem clean_entryStored {vc : VCode} {ss ps : Array (Array Nat)}
    (hcfg : vc.cfg = .ok (ss, ps)) (s : Nat) :
    entryStored (clean vc) ss ps s = entryStored vc ss ps s := by
  have hlookup (b : Nat) :
      (match (clean vc).blocks[b]?, ss[b]? with
       | some vb, some succ =>
         match succ.toList.idxOf? s with
         | some j => (termEdgeDefs vb j).map (fun (x : Operand × Loc) => x.1.vreg)
         | none => []
       | _, _ => []) =
      (match vc.blocks[b]?, ss[b]? with
       | some vb, some succ =>
         match succ.toList.idxOf? s with
         | some j => (termEdgeDefs vb j).map (fun (x : Operand × Loc) => x.1.vreg)
         | none => []
       | _, _ => []) := by
    rw [clean_blocks_map]
    simp only [Array.getElem?_map]
    cases hb : vc.blocks[b]? with
    | none => rfl
    | some vb =>
      simp only [Option.map_some]
      cases ss[b]? with
      | none => rfl
      | some succ =>
        simp only
        cases hj : succ.toList.idxOf? s with
        | none => rfl
        | some j => exact congrArg (List.map (·.1.vreg)) (clean_termEdgeDefs hcfg hb j)
  by_cases hex : ∃ b, ps[s]? = some #[b]
  · obtain ⟨b, hp⟩ := hex
    rw [KillPrep.entryStored_one hp, KillPrep.entryStored_one hp]
    exact hlookup b
  · rw [KillPrep.entryStored_ne (fun b hb => hex ⟨b, hb⟩),
      KillPrep.entryStored_ne (fun b hb => hex ⟨b, hb⟩)]

theorem clean_killFree {vc : VCode} {ss ps : Array (Array Nat)}
    (hcfg : vc.cfg = .ok (ss, ps)) (hk : killFreeB vc = true) :
    killFreeB (clean vc) = true := by
  simp only [killFreeB, clean_cfg vc (terminated_of_cfg hcfg), hcfg,
    clean_killedOf, Bool.and_eq_true] at hk ⊢
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true] at hk ⊢
    intro vb hb
    rw [List.all_eq_true]
    intro i hi
    exact clean_insts (P := fun i => (useVregs i).all (fun v => !(killedOf vc).contains v) = true)
      (fun b hb j hj => List.all_eq_true.mp (hk.1 b hb) j hj) vb hb i hi
  · have hsize : (clean vc).blocks.size = vc.blocks.size := by simp [clean]
    simp only [hsize, List.all_eq_true]
    intro b hb
    rw [clean_blocks_map]
    simp only [Array.getElem?_map]
    cases hblock : vc.blocks[b]? with
    | none => rfl
    | some vb =>
      have h := List.all_eq_true.mp hk.2 b hb
      rw [hblock] at h
      simp only [Option.map_some, cleanBlock, List.all_eq_true] at h ⊢
      intro a ha
      have hi := h a ha
      rw [clean_entryStored hcfg]
      cases he : (killedOf vc).contains a.homeNum with
      | false => simp [he]
      | true =>
        simp only [he, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hi ⊢
        refine ⟨hi.1, ?_⟩
        apply List.all_eq_true.mpr
        intro i hm
        exact List.all_eq_true.mp hi.2 i ((scan_sublist vc.classes.size vb.insts.toList (exitLive vc 0 vb)).subset hm)

/-- Invalid CFGs are unchanged; valid CFGs retain the same kill-free facts. -/
theorem prune_killFree {vc : VCode} (hk : killFreeB vc = true) :
    killFreeB (prune vc) = true := by
  unfold prune
  cases hcfg : vc.cfg with
  | error e => exact hk
  | ok p => exact clean_killFree hcfg hk

end Backend.DeadCleanup
