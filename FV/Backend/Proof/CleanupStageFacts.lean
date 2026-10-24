import FV.Backend.Proof.SkipDeadPrepare
import FV.Backend.Proof.DeadCleanupPrepare
import FV.Backend.CleanupStage

/-!
# Structure of the production cleanup stage (`cleanupStage`)

`Backend.cleanupStage f vc = prune (skipStage f vc)` (`FV/Backend/CleanupStage.lean`). The skip
only deletes instructions, keeping every block's last instruction, label, parameters and branch
arguments: it is the uniform block map `skipBlock (stageMask f vc)` (`skipStage_eq`), which
`prepare` commutes with (`skip_prepare`). This file collects the structural facts the pipeline's
proofs use:

* `DelMap T`: a `BlockMap` whose blocks keep a sublist of their instructions; the facts of
  `mapBlocks T vc` (CFG, metadata, every-instruction facts, `PrepDomain`, `hasTryCall`,
  `hasTls`);
* `stageMask`, `skipStage_eq`, `skipStage_cases` (identity, or a `deleteCheck`ed deletion);
* `stagePrepared f vc raw`: the prepared code of `cleanupStage f vc` from the prepared code `raw`
  of `vc` (`cleanupStage_prepare`, `cleanupStage_prepare_ok`, `cleanupStage_prepare_ok_inv`:
  `prune_prepare`'s counterparts).
-/

namespace Backend.Proof.Driver
open Backend Backend.DeadCleanup Backend.Proof.Prep

/-! ## Deleting block maps -/

/-- A block map that keeps a sublist of each block's instructions. -/
structure DelMap (T : VBlock → VBlock) : Prop where
  map : BlockMap T
  sub : ∀ b, (T b).insts.toList.Sublist b.insts.toList

theorem DelMap.comp {T S : VBlock → VBlock} (hT : DelMap T) (hS : DelMap S) : DelMap (T ∘ S) where
  map := {
    default := by simp [Function.comp_def, hS.map.default, hT.map.default]
    label := fun b => by simp [hT.map.label, hS.map.label]
    params := fun b => by simp [hT.map.params, hS.map.params]
    branchArgs := fun b => by simp [hT.map.branchArgs, hS.map.branchArgs]
    back := fun b => by simp [hT.map.back, hS.map.back]
    jump := fun lab l => by simp [hT.map.jump, hS.map.jump]
    retarget := fun b t t' ls hb hr => by
      simp only [Function.comp_apply]
      rw [hS.map.retarget b t t' ls hb hr]
      exact hT.map.retarget (S b) t t' ls (by rw [hS.map.back]; exact hb) hr }
  sub := fun b => (hT.sub (S b)).trans (hS.sub b)

theorem mapBlocks_comp (T S : VBlock → VBlock) (vc : VCode) :
    mapBlocks T (mapBlocks S vc) = mapBlocks (T ∘ S) vc := by
  simp [mapBlocks, Array.map_map]

theorem mapBlocks_blocks (T : VBlock → VBlock) (vc : VCode) :
    (mapBlocks T vc).blocks = vc.blocks.map T := rfl

theorem mapBlocks_getElem? (T : VBlock → VBlock) (vc : VCode) (b : Nat) :
    (mapBlocks T vc).blocks[b]? = (vc.blocks[b]?).map T := by
  simp [mapBlocks]

/-- A block of the mapped code is the map of the block at the same index. -/
theorem mapBlocks_block {T : VBlock → VBlock} {vc : VCode} {b : Nat} {vb : VBlock}
    (h : (mapBlocks T vc).blocks[b]? = some vb) :
    ∃ raw, vc.blocks[b]? = some raw ∧ vb = T raw := by
  rw [mapBlocks_getElem?] at h
  obtain ⟨raw, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨raw, hr, rfl⟩

/-- No function metadata changes. -/
theorem mapBlocks_metadata (T : VBlock → VBlock) (vc : VCode) :
    (mapBlocks T vc).name = vc.name ∧ (mapBlocks T vc).classes = vc.classes ∧
    (mapBlocks T vc).slotBytes = vc.slotBytes ∧ (mapBlocks T vc).outgoing = vc.outgoing ∧
    (mapBlocks T vc).rulesFired = vc.rulesFired ∧
    (mapBlocks T vc).blocks.size = vc.blocks.size := by
  simp [mapBlocks]

/-- Instruction predicates survive: each block's code is a sublist. -/
theorem DelMap.insts {T : VBlock → VBlock} (hT : DelMap T) (vc : VCode) {P : MInst → Prop}
    (h : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, P i) :
    ∀ vb ∈ (mapBlocks T vc).blocks.toList, ∀ i ∈ vb.insts.toList, P i := by
  intro vb hvb i hi
  simp only [mapBlocks, Array.toList_map, List.mem_map] at hvb
  obtain ⟨raw, hraw, rfl⟩ := hvb
  exact h raw hraw i ((hT.sub raw).subset hi)

theorem DelMap.cfg {T : VBlock → VBlock} (hT : DelMap T) (vc : VCode) :
    (mapBlocks T vc).cfg = vc.cfg := mapBlocks_cfg hT.map vc

theorem DelMap.prepDomain {T : VBlock → VBlock} (hT : DelMap T) {vc : VCode}
    (hd : PrepDomain vc) : PrepDomain (mapBlocks T vc) := by
  refine ⟨by simpa [mapBlocks] using hd.nonempty, ?_, ?_⟩
  · simpa [Lbls, mapBlocks, List.map_map, Function.comp_def, hT.map.label] using hd.labels
  · intro b vb t hb ht hn
    obtain ⟨raw, hr, rfl⟩ := mapBlocks_block hb
    rw [hT.map.back] at ht
    rw [hT.map.branchArgs]
    exact hd.args b raw t hr ht hn

theorem DelMap.any_false {T : VBlock → VBlock} (hT : DelMap T) {vc : VCode} {p : MInst → Bool}
    (h : (vc.blocks.any fun vb => vb.insts.any p) = false) :
    ((mapBlocks T vc).blocks.any fun vb => vb.insts.any p) = false := by
  rw [Array.any_eq_false'] at h ⊢
  intro vb hb
  apply Bool.eq_false_iff.mp
  apply Array.any_eq_false'.mpr
  intro i hi
  exact hT.insts vc (P := fun i => ¬p i = true)
    (fun b hB j hJ => (Array.any_eq_false'.mp
      (Bool.eq_false_iff.mpr (h b (by simpa using hB)))) j (by simpa using hJ))
    vb (by simpa using hb) i (by simpa using hi)

theorem DelMap.noTryCall {T : VBlock → VBlock} (hT : DelMap T) {vc : VCode}
    (h : vc.hasTryCall = false) : (mapBlocks T vc).hasTryCall = false := hT.any_false h

theorem DelMap.noTls {T : VBlock → VBlock} (hT : DelMap T) {vc : VCode}
    (h : vc.hasTls = false) : (mapBlocks T vc).hasTls = false := hT.any_false h

/-! ## The skip's block map -/

theorem maskKeep_sublist (mask : List Bool) (ms : List MInst) : (maskKeep mask ms).Sublist ms := by
  unfold maskKeep
  induction ms generalizing mask with
  | nil => simp
  | cons m ms ih =>
    cases mask with
    | nil => simp
    | cons k mask =>
      simp only [List.zip_cons_cons, List.filterMap_cons]
      cases k
      · exact (ih mask).cons m
      · exact (ih mask).cons₂ m

theorem skipBlock_delMap (mask : Nat → List Bool) : DelMap (skipBlock mask) where
  map := skipBlock_blockMap mask
  sub := fun b => by
    unfold skipBlock
    split
    · simpa using maskKeep_sublist _ _
    · exact List.Sublist.refl _

theorem skipBlock_nil (b : VBlock) : skipBlock (fun _ => []) b = b := by
  unfold skipBlock MaskFits
  simp

theorem mapBlocks_skipBlock_nil (vc : VCode) : mapBlocks (skipBlock fun _ => []) vc = vc := by
  have h : skipBlock (fun _ => []) = id := funext skipBlock_nil
  unfold mapBlocks
  rw [h, Array.map_id]

theorem preparedCleanupBlock_delMap (vc : VCode) : DelMap (preparedCleanupBlock vc) where
  map := preparedCleanupBlock_blockMap vc
  sub := preparedCleanupBlock_sublist vc

/-! ## The skip's mask -/

/-- The mask `skipDead f vc` deletes with (`fun _ => []`, deleting nothing, if it deletes
nothing). -/
def skipMaskOf (f : Clif.Function) (vc : VCode) : Nat → List Bool :=
  match buildCtx f with
  | .error _ => fun _ => []
  | .ok (ctx, _, st0) =>
    match lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length with
    | none => fun _ => []
    | some bl =>
      let R := renOf (gnAt (gnTable st0.nextVreg (aliasOf f bl)))
      let mask := skipMask f R bl vc (skipAt f (skipDrops f R bl vc))
      if deleteCheck vc mask then mask else fun _ => []

theorem skipMaskOf_cases (f : Clif.Function) (vc : VCode) :
    skipMaskOf f vc = (fun _ => []) ∨ deleteCheck vc (skipMaskOf f vc) = true := by
  unfold skipMaskOf
  split
  · exact .inl rfl
  · split
    · exact .inl rfl
    · simp only
      split
      · rename_i h; exact .inr h
      · exact .inl rfl

/-- The fit of a checked mask (`deleteCheck`'s first conjuncts). -/
theorem fit_of_deleteCheck {vc : VCode} {mask : Nat → List Bool} (h : deleteCheck vc mask = true) :
    ∀ l (vb : VBlock), vc.blocks[l]? = some vb →
      (mask l).length = vb.insts.size ∧ (vb.insts.size = 0 ∨ (mask l).getLast? = some true) :=
  fun l vb hvb => ⟨(deletes_of_check h).len l vb hvb, (deletes_of_check h).last l vb hvb⟩

theorem skipDead_eq {f : Clif.Function} {vc : VCode}
    (hlab : ∀ l (vb : VBlock), vc.blocks[l]? = some vb → vb.label = l) :
    skipDead f vc = mapBlocks (skipBlock (skipMaskOf f vc)) vc := by
  unfold skipDead skipMaskOf
  cases hb : buildCtx f with
  | error e => exact (mapBlocks_skipBlock_nil vc).symm
  | ok r =>
    obtain ⟨ctx, ranges, st0⟩ := r
    simp only
    cases hl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length with
    | none => exact (mapBlocks_skipBlock_nil vc).symm
    | some bl =>
      simp only
      split
      · rename_i h
        exact deleteWith_eq_mapBlocks hlab (fit_of_deleteCheck h)
      · exact (mapBlocks_skipBlock_nil vc).symm

/-- **The production stage's mask**: `skipMaskOf f vc` where the skip runs. -/
def stageMask (f : Clif.Function) (vc : VCode) : Nat → List Bool :=
  if Compile.functionE f && lowerCheck f vc then skipMaskOf f vc else fun _ => []

theorem stageMask_cases (f : Clif.Function) (vc : VCode) :
    stageMask f vc = (fun _ => []) ∨
      (lowerCheck f vc = true ∧ deleteCheck vc (stageMask f vc) = true) := by
  unfold stageMask
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    rcases skipMaskOf_cases f vc with h' | h'
    · exact .inl h'
    · exact .inr ⟨h.2, h'⟩
  · exact .inl rfl

/-- **The skip is the block map `skipBlock (stageMask f vc)`.** -/
theorem skipStage_eq (f : Clif.Function) (vc : VCode) :
    skipStage f vc = mapBlocks (skipBlock (stageMask f vc)) vc := by
  unfold skipStage stageMask
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain ⟨ctx, st0, R, gn, bl, A, hS, -⟩ := skipDead_spec h.2
    exact skipDead_eq hS.labels
  · exact (mapBlocks_skipBlock_nil vc).symm

/-- **The skip's hypotheses** (`skipDead_spec` for `skipStage`): the lowering obligations of `vc`
and, for the same renaming and lowering record, `skipStage f vc` is `vc` or the deletion
`SkipHyp` describes it. -/
theorem skipStage_spec {f : Clif.Function} {vc : VCode} (h : lowerCheck f vc = true) :
    ∃ ctx st0 R gn bl A, LowerShape f vc ctx st0 R gn bl ∧ Cert f ctx st0 gn bl A ∧
      (∀ B ∈ f.blocks, BrIdxTyped ctx B.term) ∧
      (skipStage f vc = vc ∨
        SkipHyp f vc R bl (skipAt f (skipDrops f R bl vc)) (skipStage f vc)) := by
  obtain ⟨ctx, st0, R, gn, bl, A, hS, hC, hB, hsk⟩ := skipDead_spec h
  refine ⟨ctx, st0, R, gn, bl, A, hS, hC, hB, ?_⟩
  unfold skipStage
  cases hE : Compile.functionE f
  · exact .inl (by simp)
  · simpa [h] using hsk

theorem skipStage_delMap (f : Clif.Function) (vc : VCode) :
    DelMap (skipBlock (stageMask f vc)) := skipBlock_delMap _

theorem skipStage_cfg (f : Clif.Function) (vc : VCode) : (skipStage f vc).cfg = vc.cfg := by
  rw [skipStage_eq]; exact (skipStage_delMap f vc).cfg vc

theorem skipStage_metadata (f : Clif.Function) (vc : VCode) :
    (skipStage f vc).name = vc.name ∧ (skipStage f vc).classes = vc.classes ∧
    (skipStage f vc).slotBytes = vc.slotBytes ∧ (skipStage f vc).outgoing = vc.outgoing ∧
    (skipStage f vc).rulesFired = vc.rulesFired ∧
    (skipStage f vc).blocks.size = vc.blocks.size := by
  rw [skipStage_eq]; exact mapBlocks_metadata _ vc

theorem skipStage_outgoing (f : Clif.Function) (vc : VCode) :
    (skipStage f vc).outgoing = vc.outgoing := (skipStage_metadata f vc).2.2.2.1

theorem skipStage_insts (f : Clif.Function) {vc : VCode} {P : MInst → Prop}
    (h : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, P i) :
    ∀ vb ∈ (skipStage f vc).blocks.toList, ∀ i ∈ vb.insts.toList, P i := by
  rw [skipStage_eq]; exact (skipStage_delMap f vc).insts vc h

theorem skipStage_prepDomain (f : Clif.Function) {vc : VCode} (hd : PrepDomain vc) :
    PrepDomain (skipStage f vc) := by
  rw [skipStage_eq]; exact (skipStage_delMap f vc).prepDomain hd

theorem skipStage_noTryCall (f : Clif.Function) {vc : VCode} (h : vc.hasTryCall = false) :
    (skipStage f vc).hasTryCall = false := by
  rw [skipStage_eq]; exact (skipStage_delMap f vc).noTryCall h

theorem skipStage_noTls (f : Clif.Function) {vc : VCode} (h : vc.hasTls = false) :
    (skipStage f vc).hasTls = false := by
  rw [skipStage_eq]; exact (skipStage_delMap f vc).noTls h

/-! ## The cleanup stage -/

theorem cleanupStage_cfg (f : Clif.Function) (vc : VCode) : (cleanupStage f vc).cfg = vc.cfg := by
  unfold cleanupStage; rw [prune_cfg, skipStage_cfg]

theorem cleanupStage_outgoing (f : Clif.Function) (vc : VCode) :
    (cleanupStage f vc).outgoing = vc.outgoing := by
  unfold cleanupStage; rw [prune_outgoing, skipStage_outgoing]

theorem cleanupStage_insts (f : Clif.Function) {vc : VCode} {P : MInst → Prop}
    (h : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, P i) :
    ∀ vb ∈ (cleanupStage f vc).blocks.toList, ∀ i ∈ vb.insts.toList, P i :=
  prune_insts (skipStage_insts f h)

theorem cleanupStage_prepDomain (f : Clif.Function) {vc : VCode} (hd : PrepDomain vc) :
    PrepDomain (cleanupStage f vc) := prune_prepDomain (skipStage_prepDomain f hd)

theorem cleanupStage_noTryCall (f : Clif.Function) {vc : VCode} (h : vc.hasTryCall = false) :
    (cleanupStage f vc).hasTryCall = false := prune_noTryCall (skipStage_noTryCall f h)

theorem cleanupStage_noTls (f : Clif.Function) {vc : VCode} (h : vc.hasTls = false) :
    (cleanupStage f vc).hasTls = false := prune_noTls (skipStage_noTls f h)

/-- **The prepared code of the cleanup stage**, from the prepared code `raw` of the lowering:
the skip's deletion, then the transported cleanup (`preparedCleanup`). -/
def stagePrepared (f : Clif.Function) (vc raw : VCode) : VCode :=
  preparedCleanup (skipStage f vc) (mapBlocks (skipBlock (stageMask f vc)) raw)

theorem prepare_skipStage (f : Clif.Function) (vc : VCode) :
    prepare (skipStage f vc) = (prepare vc).map (mapBlocks (skipBlock (stageMask f vc))) := by
  rw [skipStage_eq]; exact prepare_map (skipBlock_blockMap _) vc

/-- **Preparation commutes with the cleanup stage** (`prune_prepare`'s counterpart). -/
theorem cleanupStage_prepare (f : Clif.Function) (vc : VCode) :
    prepare (cleanupStage f vc) = (prepare vc).map (stagePrepared f vc) := by
  unfold cleanupStage stagePrepared
  rw [prune_prepare, prepare_skipStage]
  cases prepare vc <;> rfl

theorem cleanupStage_prepare_ok {f : Clif.Function} {vc raw : VCode} (hp : prepare vc = .ok raw) :
    prepare (cleanupStage f vc) = .ok (stagePrepared f vc raw) := by
  rw [cleanupStage_prepare, hp]; rfl

theorem cleanupStage_prepare_ok_inv {f : Clif.Function} {vc vcp : VCode}
    (hp : prepare (cleanupStage f vc) = .ok vcp) :
    ∃ raw, prepare vc = .ok raw ∧ vcp = stagePrepared f vc raw := by
  rw [cleanupStage_prepare] at hp
  cases hr : prepare vc with
  | error e => simp [hr, Except.map] at hp
  | ok raw =>
    simp only [hr, Except.map, Except.ok.injEq] at hp
    exact ⟨raw, rfl, hp.symm⟩

/-- `stagePrepared f vc raw` is a deleting block map of `raw`. -/
theorem stagePrepared_eq (f : Clif.Function) (vc raw : VCode) :
    stagePrepared f vc raw =
      mapBlocks (preparedCleanupBlock (skipStage f vc) ∘ skipBlock (stageMask f vc)) raw := by
  unfold stagePrepared preparedCleanup
  exact mapBlocks_comp _ _ raw

theorem stagePrepared_delMap (f : Clif.Function) (vc : VCode) :
    DelMap (preparedCleanupBlock (skipStage f vc) ∘ skipBlock (stageMask f vc)) :=
  (preparedCleanupBlock_delMap _).comp (skipBlock_delMap _)

theorem stagePrepared_cfg (f : Clif.Function) (vc raw : VCode) :
    (stagePrepared f vc raw).cfg = raw.cfg := by
  rw [stagePrepared_eq]; exact (stagePrepared_delMap f vc).cfg raw

theorem stagePrepared_metadata (f : Clif.Function) (vc raw : VCode) :
    (stagePrepared f vc raw).name = raw.name ∧ (stagePrepared f vc raw).classes = raw.classes ∧
    (stagePrepared f vc raw).slotBytes = raw.slotBytes ∧
    (stagePrepared f vc raw).outgoing = raw.outgoing ∧
    (stagePrepared f vc raw).rulesFired = raw.rulesFired ∧
    (stagePrepared f vc raw).blocks.size = raw.blocks.size := by
  rw [stagePrepared_eq]; exact mapBlocks_metadata _ raw

theorem stagePrepared_insts (f : Clif.Function) (vc raw : VCode) {P : MInst → Prop}
    (h : ∀ vb ∈ raw.blocks.toList, ∀ i ∈ vb.insts.toList, P i) :
    ∀ vb ∈ (stagePrepared f vc raw).blocks.toList, ∀ i ∈ vb.insts.toList, P i := by
  rw [stagePrepared_eq]; exact (stagePrepared_delMap f vc).insts raw h

end Backend.Proof.Driver
