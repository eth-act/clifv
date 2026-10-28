import FV.Backend.Proof.CleanupStageFacts
import FV.Backend.Proof.DeadCleanupKill
import FV.Backend.Proof.DeadCleanupEdgesOk
import FV.Backend.Proof.DeadCleanupClasses

/-!
# The spill allocator's syntactic facts through the cleanup stage

The skip of unused instructions is a deleting block map (`DelMap`: each block keeps a sublist of
its instructions, its label, parameters, branch arguments and last instruction). The facts the
spill allocator's completeness uses on the lowering's output survive such a map, and so the whole
production cleanup stage (`cleanupStage f vc = prune (skipStage f vc)`):

* `DelMap.lowOk`, `skipStage_lowOk`, `cleanupStage_lowOk` (`LowOk`, the edge interface);
* `DelMap.classes`, `skipStage_classes`, `cleanupStage_classes` (`ClassesOkM`);
* `DelMap.killFree`, `skipStage_killFree`, `cleanupStage_killFree` (`killFreeB`: the killed vregs
  of the kept code are killed in `vc`, its reads are reads of `vc`, and the block entry stores
  only depend on the kept last instructions).
-/

namespace Backend.Proof.Driver
open Backend Backend.DeadCleanup Backend.Proof.Spill

variable {T : VBlock → VBlock}

theorem DelMap.lowOk (hT : DelMap T) {vc : VCode} (hv : LowOk vc) : LowOk (mapBlocks T vc) := by
  refine ⟨by simpa [mapBlocks] using hv.nonempty, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b vb hb
    obtain ⟨old, hb0, rfl⟩ := mapBlocks_block hb
    rw [hT.map.label]
    exact hv.labels b old hb0
  · intro vb hb
    obtain ⟨old, hb0, rfl⟩ := mapBlocks_block hb
    rw [hT.map.params]
    exact hv.entry old hb0
  · intro b vb t hb ht
    obtain ⟨old, hb0, rfl⟩ := mapBlocks_block hb
    rw [hT.map.back] at ht
    exact hv.noEntry b old t hb0 ht
  · intro b vb hb hne
    obtain ⟨old, hb0, rfl⟩ := mapBlocks_block hb
    rw [hT.map.branchArgs] at hne ⊢
    obtain ⟨l, tb, ht, htb, hsz, harg, hn⟩ := hv.args b old hb0 hne
    refine ⟨l, T tb, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hT.map.back]; exact ht
    · rw [mapBlocks_getElem?, htb]; rfl
    · rw [hT.map.params]; exact hsz
    · intro k a p ha hp
      rw [hT.map.params] at hp
      exact harg k a p ha hp
    · rw [hT.map.params]; exact hn
  · intro b vb t l tb hb hargs ht hl htb
    obtain ⟨old, hb0, rfl⟩ := mapBlocks_block hb
    obtain ⟨oldtb, htb0, rfl⟩ := mapBlocks_block htb
    rw [hT.map.branchArgs] at hargs
    rw [hT.map.back] at ht
    rw [hT.map.params]
    exact hv.noArgs b old t l oldtb hb0 hargs ht hl htb0
  · intro b vb info ti hb ht
    obtain ⟨old, hb0, rfl⟩ := mapBlocks_block hb
    rw [hT.map.back] at ht
    rw [hT.map.branchArgs]
    exact hv.tryArgs b old info ti hb0 ht
  · intro b vb info ti j l hb ht hl b' vb' t' j' hb' ht' hl'
    obtain ⟨old, hb0, rfl⟩ := mapBlocks_block hb
    obtain ⟨old', hb0', rfl⟩ := mapBlocks_block hb'
    rw [hT.map.back] at ht ht'
    exact hv.tryUniq b old info ti j l hb0 ht hl b' old' t' j' hb0' ht' hl'

theorem DelMap.classes (hT : DelMap T) {vc : VCode} (h : ClassesOkM vc) :
    ClassesOkM (mapBlocks T vc) := by
  have hc : (mapBlocks T vc).classes = vc.classes := (mapBlocks_metadata T vc).2.1
  refine ⟨?_, ?_⟩
  · rw [hc]
    exact hT.insts vc h.1
  · intro vb hb r hr
    simp only [mapBlocks, Array.toList_map, List.mem_map] at hb
    obtain ⟨old, hold, rfl⟩ := hb
    rw [hT.map.params, hT.map.branchArgs] at hr
    rw [hc]
    exact h.2 old hold r hr

/-- The kept code kills only vregs `vc` kills. -/
theorem DelMap.killedOf_sub (hT : DelMap T) (vc : VCode) :
    ∀ v ∈ killedOf (mapBlocks T vc), v ∈ killedOf vc := by
  intro v hv
  simp only [killedOf, mapBlocks, Array.toList_map, List.flatMap_map, List.mem_flatMap] at hv ⊢
  obtain ⟨vb, hvb, i, hi, hu⟩ := hv
  exact ⟨vb, hvb, i, (hT.sub vb).subset hi, hu⟩

theorem DelMap.entryStored_eq (hT : DelMap T) (vc : VCode) (succs preds : Array (Array Nat))
    (s : Nat) : Spill.entryStored (mapBlocks T vc) succs preds s =
      Spill.entryStored vc succs preds s := by
  have ht : ∀ vb j, termEdgeDefs (T vb) j = termEdgeDefs vb j := by
    intro vb j
    unfold termEdgeDefs
    rw [hT.map.back]
  have hlookup (b : Nat) :
      (match (mapBlocks T vc).blocks[b]?, succs[b]? with
       | some vb, some succ =>
         match succ.toList.idxOf? s with
         | some j => (termEdgeDefs vb j).map (fun (x : Operand × Loc) => x.1.vreg)
         | none => []
       | _, _ => []) =
      (match vc.blocks[b]?, succs[b]? with
       | some vb, some succ =>
         match succ.toList.idxOf? s with
         | some j => (termEdgeDefs vb j).map (fun (x : Operand × Loc) => x.1.vreg)
         | none => []
       | _, _ => []) := by
    rw [mapBlocks_getElem?]
    cases vc.blocks[b]? with
    | none => rfl
    | some vb =>
      simp only [Option.map_some]
      cases succs[b]? with
      | none => rfl
      | some succ =>
        simp only
        cases succ.toList.idxOf? s with
        | none => rfl
        | some j => exact congrArg (List.map (·.1.vreg)) (ht vb j)
  by_cases hex : ∃ b, preds[s]? = some #[b]
  · obtain ⟨b, hp⟩ := hex
    rw [KillPrep.entryStored_one hp, KillPrep.entryStored_one hp]
    exact hlookup b
  · rw [KillPrep.entryStored_ne (fun b hb => hex ⟨b, hb⟩),
      KillPrep.entryStored_ne (fun b hb => hex ⟨b, hb⟩)]

theorem DelMap.killFree (hT : DelMap T) {vc : VCode} (hk : killFreeB vc = true) :
    killFreeB (mapBlocks T vc) = true := by
  have hK := hT.killedOf_sub vc
  have hcon : ∀ v, (killedOf (mapBlocks T vc)).contains v = true →
      (killedOf vc).contains v = true := fun v h =>
    List.contains_iff_mem.mpr (hK v (List.contains_iff_mem.mp h))
  simp only [killFreeB, hT.cfg vc, Bool.and_eq_true] at hk ⊢
  obtain ⟨h1, h2⟩ := hk
  refine ⟨?_, ?_⟩
  · apply List.all_eq_true.mpr
    intro vb hvb
    apply List.all_eq_true.mpr
    intro i hi
    apply List.all_eq_true.mpr
    intro v hv
    simp only [mapBlocks, Array.toList_map, List.mem_map] at hvb
    obtain ⟨old, hold, rfl⟩ := hvb
    have h := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h1 old hold) i
      ((hT.sub old).subset hi)) v hv
    cases hc : (killedOf (mapBlocks T vc)).contains v
    · rfl
    · rw [hcon v hc] at h
      simp at h
  · cases hcfg : vc.cfg with
    | error e => simp only [hcfg] at h2 ⊢
    | ok p =>
      obtain ⟨succs, preds⟩ := p
      simp only [hcfg] at h2 ⊢
      have hsz : (mapBlocks T vc).blocks.size = vc.blocks.size := (mapBlocks_metadata T vc).2.2.2.2.2
      rw [hsz]
      apply List.all_eq_true.mpr
      intro b hb
      have h := List.all_eq_true.mp h2 b hb
      rw [mapBlocks_getElem?]
      cases hvb : vc.blocks[b]? with
      | none => rfl
      | some vb =>
        simp only [hvb, Option.map] at h ⊢
        rw [hT.map.branchArgs]
        apply List.all_eq_true.mpr
        intro a ha
        have h' := List.all_eq_true.mp h a ha
        rw [hT.entryStored_eq]
        cases hc : (killedOf (mapBlocks T vc)).contains a.homeNum
        · simp
        · rw [hcon _ hc] at h'
          simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h' ⊢
          exact ⟨h'.1, List.all_eq_true.mpr fun i hi => List.all_eq_true.mp h'.2 i
            ((hT.sub vb).subset hi)⟩

/-! ## The skip and the cleanup stage -/

theorem skipStage_lowOk (f : Clif.Function) {vc : VCode} (hv : LowOk vc) :
    LowOk (skipStage f vc) := by
  rw [skipStage_eq]; exact (skipStage_delMap f vc).lowOk hv

theorem cleanupStage_lowOk (f : Clif.Function) {vc : VCode} (hv : LowOk vc) :
    LowOk (cleanupStage f vc) := prune_lowOk (skipStage_lowOk f hv)

theorem skipStage_classes (f : Clif.Function) {vc : VCode} (h : ClassesOkM vc) :
    ClassesOkM (skipStage f vc) := by
  rw [skipStage_eq]; exact (skipStage_delMap f vc).classes h

theorem cleanupStage_classes (f : Clif.Function) {vc : VCode} (h : ClassesOkM vc) :
    ClassesOkM (cleanupStage f vc) := prune_classes (skipStage_classes f h)

theorem skipStage_killFree (f : Clif.Function) {vc : VCode} (hk : killFreeB vc = true) :
    killFreeB (skipStage f vc) = true := by
  rw [skipStage_eq]; exact (skipStage_delMap f vc).killFree hk

theorem cleanupStage_killFree (f : Clif.Function) {vc : VCode} (hk : killFreeB vc = true) :
    killFreeB (cleanupStage f vc) = true := prune_killFree (skipStage_killFree f hk)

/-! ## Positions -/

theorem sublist_getElem?_ge {α : Type} {l' l : List α} (h : l'.Sublist l) :
    ∀ {k : Nat} {x : α}, l'[k]? = some x → ∃ p, k ≤ p ∧ l[p]? = some x := by
  induction h with
  | slnil => intro k x hk; simp at hk
  | cons a _ ih =>
    intro k x hk
    obtain ⟨p, hp, hl⟩ := ih hk
    exact ⟨p + 1, by omega, by simpa using hl⟩
  | cons_cons a _ ih =>
    intro k x hk
    cases k with
    | zero => exact ⟨0, Nat.le_refl _, by simpa using hk⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      obtain ⟨p, hp, hl⟩ := ih hk
      exact ⟨p + 1, by omega, by simpa using hl⟩

/-- An instruction of the mapped code is one of `vc`'s, in the same block, at a later or equal
position. -/
theorem DelMap.pos (hT : DelMap T) {vc : VCode} {b k : Nat} {vbK : VBlock} {i : MInst}
    (hb : (mapBlocks T vc).blocks[b]? = some vbK) (hi : vbK.insts[k]? = some i) :
    ∃ vb p, vc.blocks[b]? = some vb ∧ k ≤ p ∧ vb.insts[p]? = some i := by
  obtain ⟨vb, hvb, rfl⟩ := mapBlocks_block hb
  rw [← Array.getElem?_toList] at hi
  obtain ⟨p, hp, hl⟩ := sublist_getElem?_ge (hT.sub vb) hi
  exact ⟨vb, p, hvb, hp, by rw [← Array.getElem?_toList]; exact hl⟩

theorem skipStage_pos (f : Clif.Function) {vc : VCode} {b k : Nat} {vbK : VBlock} {i : MInst}
    (hb : (skipStage f vc).blocks[b]? = some vbK) (hi : vbK.insts[k]? = some i) :
    ∃ vb p, vc.blocks[b]? = some vb ∧ k ≤ p ∧ vb.insts[p]? = some i := by
  rw [skipStage_eq] at hb
  exact (skipStage_delMap f vc).pos hb hi

/-- **The skip keeps what it may not delete** (`skipDel`: the entry `args`, GOT loads), in the
same block, at an earlier or equal position. -/
theorem skipStage_keep (f : Clif.Function) {vc : VCode} {b k : Nat} {vb : VBlock} {i : MInst}
    (hvb : vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hd : skipDel i = false) :
    ∃ vbK k', k' ≤ k ∧ (skipStage f vc).blocks[b]? = some vbK ∧ vbK.insts[k']? = some i := by
  rcases stageMask_cases f vc with h | ⟨hlc, hdc⟩
  · refine ⟨vb, k, Nat.le_refl _, ?_, hi⟩
    rw [skipStage_eq, h, mapBlocks_skipBlock_nil]
    exact hvb
  · obtain ⟨ctx, st0, R, gn, bl, A, hS, -⟩ := skipDead_spec hlc
    have hD := deletes_of_check hdc
    rw [skipStage_eq, ← deleteWith_eq_mapBlocks hS.labels (fit_of_deleteCheck hdc)]
    obtain ⟨vbK, hK, hins, -, -⟩ := hD.blk b vb hvb
    have hlen := hD.len b vb hvb
    have hk : k < (stageMask f vc b).length := by
      rw [hlen]; exact (Array.getElem?_eq_some_iff.mp hi).1
    cases hm : (stageMask f vc b)[k]? with
    | none => rw [List.getElem?_eq_getElem hk] at hm; cases hm
    | some x =>
      cases x with
      | false => rw [skipDel_of_check hdc hvb hi hm] at hd; cases hd
      | true =>
        refine ⟨vbK, kidx (stageMask f vc b) k,
          Nat.le_trans List.count_le_length (List.length_take_le _ _), hK, ?_⟩
        rw [← Array.getElem?_toList, hins, maskKeep_getElem? (by rw [hlen]; simp) hm,
          Array.getElem?_toList]
        exact hi

end Backend.Proof.Driver
