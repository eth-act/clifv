import FV.Backend.Proof.DeadCleanupPrepareMap
import FV.Backend.Proof.LowerSimSkip

/-!
# Preparation commutes with the skip of unused instructions

`deleteWith vc mask` (`FV/Backend/SkipDead.lean`) deletes, in the block labelled `l`, the
instructions at the `false` positions of `mask l`, keeping the last one. On code whose labels are
the block indices (`LowerShape.labels`) it is the uniform block map `skipBlock mask`, which
`prepare` commutes with (`DeadCleanup.prepare_map`): the prepared skipped code is the prepared code
with the same instructions deleted in the blocks carrying the same labels (`skip_prepare`).
-/

namespace Backend.Proof.Driver
open Backend Backend.DeadCleanup

/-- `mask` fits `ms` and keeps its last element. -/
def MaskFits (mask : List Bool) (ms : List MInst) : Prop :=
  mask.length = ms.length ∧ mask.getLast? = some true

instance (mask : List Bool) (ms : List MInst) : Decidable (MaskFits mask ms) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `skipBlock mask b`: the instructions of `b` at the `true` positions of `mask b.label`, if that
mask fits `b` and keeps its last instruction; `b` itself otherwise. -/
def skipBlock (mask : Nat → List Bool) (b : VBlock) : VBlock :=
  if MaskFits (mask b.label) b.insts.toList then
    { b with insts := (maskKeep (mask b.label) b.insts.toList).toArray }
  else b

theorem maskKeep_append_last (m : List Bool) (ms : List MInst) (x : MInst)
    (h : m.length = ms.length) :
    maskKeep (m ++ [true]) (ms ++ [x]) = maskKeep m ms ++ [x] := by
  unfold maskKeep
  rw [List.zip_append h.symm, List.filterMap_append]
  simp

theorem exists_append_last {α : Type} {l : List α} (h : l ≠ []) : ∃ l' x, l = l' ++ [x] :=
  ⟨l.dropLast, l.getLast h, (List.dropLast_concat_getLast h).symm⟩

theorem maskFits_split {mask : List Bool} {ms : List MInst} (h : MaskFits mask ms) :
    ∃ m' ms' x, mask = m' ++ [true] ∧ ms = ms' ++ [x] ∧ m'.length = ms'.length := by
  obtain ⟨hl, hlast⟩ := h
  obtain ⟨m', hm⟩ := List.getLast?_eq_some_iff.1 hlast
  have hne : ms ≠ [] := by
    intro h0; subst h0; subst hm; simp at hl
  obtain ⟨ms', x, hx⟩ := exists_append_last hne
  refine ⟨m', ms', x, hm, hx, ?_⟩
  subst hm hx
  simpa using hl

theorem maskKeep_fits_last {mask : List Bool} {ms : List MInst} (h : MaskFits mask ms) :
    (maskKeep mask ms).getLast? = ms.getLast? := by
  obtain ⟨m', ms', x, rfl, rfl, hl⟩ := maskFits_split h
  rw [maskKeep_append_last _ _ _ hl]
  simp

theorem skipBlock_blockMap (mask : Nat → List Bool) : BlockMap (skipBlock mask) where
  default := by
    unfold skipBlock MaskFits
    simp [show (default : VBlock).insts = #[] from rfl]
    intro h h'
    simp_all
  label := fun b => by unfold skipBlock; split <;> rfl
  params := fun b => by unfold skipBlock; split <;> rfl
  branchArgs := fun b => by unfold skipBlock; split <;> rfl
  back := fun b => by
    unfold skipBlock
    split
    · rename_i h
      show (List.toArray _).back? = _
      rw [List.back?_toArray, maskKeep_fits_last h, Array.getLast?_toList]
    · rfl
  jump := fun lab l => by
    unfold skipBlock
    split
    · rename_i h
      obtain ⟨m', ms', x, hm, hms, hl⟩ := maskFits_split h
      have hms' : ms' = [] := by
        rcases ms' with _ | ⟨a, as⟩
        · rfl
        · simp at hms
      subst hms'
      have hm' : m' = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
      subst hm'
      simp only at hms hm
      simp [hm, hms, maskKeep]
    · rfl
  retarget := fun b t t' ls hb _ => by
    have hne : b.insts.toList ≠ [] := by
      intro h0
      rw [← Array.getLast?_toList, h0] at hb
      simp at hb
    obtain ⟨ms', x, hx⟩ := exists_append_last hne
    have hpp : (b.insts.pop.push t').toList = ms' ++ [t'] := by
      simp [Array.toList_pop, hx]
    have hlen : (b.insts.pop.push t').toList.length = b.insts.toList.length := by
      rw [hpp, hx]; simp
    unfold skipBlock
    simp only
    by_cases h : MaskFits (mask b.label) b.insts.toList
    · have h' : MaskFits (mask b.label) (b.insts.pop.push t').toList :=
        ⟨h.1.trans hlen.symm, h.2⟩
      rw [if_pos h', if_pos h]
      obtain ⟨m', ms'', y, hm, hms, hl⟩ := maskFits_split h
      rw [hx] at hms
      obtain ⟨rfl, -⟩ := List.append_inj' hms rfl
      simp only [hpp, hx, hm, maskKeep_append_last _ _ _ hl]
      congr 1
      apply Array.toList_inj.mp
      simp
    · have h' : ¬ MaskFits (mask b.label) (b.insts.pop.push t').toList := by
        intro h'; exact h ⟨h'.1.trans hlen, h'.2⟩
      rw [if_neg h', if_neg h]

/-- On code whose labels are the block indices, `deleteWith` with masks that fit every block and
keep its last instruction is the block map `skipBlock`. -/
theorem deleteWith_eq_mapBlocks {vc : VCode} {mask : Nat → List Bool}
    (hlab : ∀ l (vb : VBlock), vc.blocks[l]? = some vb → vb.label = l)
    (hfit : ∀ l (vb : VBlock), vc.blocks[l]? = some vb →
      (mask l).length = vb.insts.size ∧ (vb.insts.size = 0 ∨ (mask l).getLast? = some true)) :
    deleteWith vc mask = mapBlocks (skipBlock mask) vc := by
  unfold deleteWith mapBlocks
  congr 1
  apply Array.ext
  · simp
  · intro i h1 h2
    have hi : i < vc.blocks.size := by simpa using h1
    simp only [Array.getElem_mapIdx, Array.getElem_map]
    have hb : vc.blocks[i]? = some (vc.blocks[i]'hi) := by simp
    generalize vc.blocks[i]'hi = vb at hb ⊢
    have hl := hlab i _ hb
    obtain ⟨hlen, hlast⟩ := hfit i _ hb
    unfold skipBlock
    rw [hl]
    split
    · rfl
    · rename_i hn
      rcases hlast with h0 | hlast
      · have hm : mask i = [] := List.eq_nil_of_length_eq_zero (by omega)
        have hi0 : vb.insts = #[] := Array.eq_empty_of_size_eq_zero h0
        cases vb
        simp_all [maskKeep]
      · exact absurd ⟨by simpa using hlen, hlast⟩ hn

/-- **Preparation commutes with the deletion**: on such code, preparing `deleteWith vc mask` is
preparing `vc` and deleting the same instructions of the blocks with the same labels. -/
theorem skip_prepare {vc : VCode} {mask : Nat → List Bool}
    (hlab : ∀ l (vb : VBlock), vc.blocks[l]? = some vb → vb.label = l)
    (hfit : ∀ l (vb : VBlock), vc.blocks[l]? = some vb →
      (mask l).length = vb.insts.size ∧ (vb.insts.size = 0 ∨ (mask l).getLast? = some true)) :
    prepare (deleteWith vc mask) = (prepare vc).map (mapBlocks (skipBlock mask)) := by
  rw [deleteWith_eq_mapBlocks hlab hfit]
  exact prepare_map (skipBlock_blockMap mask) vc

end Backend.Proof.Driver
