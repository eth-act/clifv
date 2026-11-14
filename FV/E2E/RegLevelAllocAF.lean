import FV.E2E.RegLevelEmit
import FV.Backend.Frameless

/-!
# The allocated function the backend emits: with a frame, or a frameless leaf (#1028)

`lowerRFunc` gives every function a frame. Under `preserve_frame_pointers=false` the backend
drops it for a leaf that needs none (`Backend.frameless`, stock's decision
`Backend.frameRequired`). `AllocAF vc rf af` covers both: `af` with its frame is `lowerRFunc`'s
output, and `af` has no frame only if it is a leaf (`leafB`: no frame size, slot area or callee
saves, no instruction that touches the frame). Every fact of `lowerRFunc`'s output that does not
mention the frame holds for both (`AllocAF.ok`, `AllocAF.saves`).
-/

namespace Backend

/-- **The allocated function the backend emits for `vc` and `rf`**: `lowerRFunc`'s, possibly
without its frame when it is a leaf. -/
def AllocAF (vc : VCode) (rf : RFunc) (af : AFunc) : Prop :=
  lowerRFunc vc rf = .ok { af with frame := true } ∧ (af.frame = false → leafB af = true)

/-- `lowerRFunc`'s output. -/
theorem AllocAF.of_lowerRFunc {vc : VCode} {rf : RFunc} {af : AFunc} (h : lowerRFunc vc rf = .ok af) :
    AllocAF vc rf af := by
  have hf := lowerRFunc_frame h
  refine ⟨?_, fun h' => by rw [hf] at h'; cases h'⟩
  cases af
  simp only at hf
  subst hf
  exact h

/-- `frameless`' output. -/
theorem AllocAF.of_frameless {vc vc' : VCode} {rf : RFunc} {af : AFunc} (pfp : Bool)
    (h : lowerRFunc vc rf = .ok af) : AllocAF vc rf (frameless pfp vc' af) := by
  rcases frameless_cases pfp vc' af with e | ⟨e, hl⟩
  · rw [e]; exact AllocAF.of_lowerRFunc h
  · rw [e]
    have hf := lowerRFunc_frame h
    refine ⟨?_, fun _ => ?_⟩
    · cases af
      simp only at hf
      subst hf
      exact h
    · cases af
      exact hl

/-- With a frame, `AllocAF` is `lowerRFunc`'s output. -/
theorem AllocAF.lowerRFunc_of_frame {vc : VCode} {rf : RFunc} {af : AFunc} (h : AllocAF vc rf af)
    (hf : af.frame = true) : lowerRFunc vc rf = .ok af := by
  have e : { af with frame := true } = af := by cases af; simp only at hf; subst hf; rfl
  rw [← e]; exact h.1

/-- Without a frame, a leaf. -/
theorem AllocAF.leaf {vc : VCode} {rf : RFunc} {af : AFunc} (h : AllocAF vc rf af)
    (hf : af.frame = false) : leafB af = true := h.2 hf

/-- A leaf has no frame size, slot area or callee saves, and none of its instructions touches
the frame. -/
theorem leafB_spec {af : AFunc} (h : leafB af = true) :
    af.frameSize = 0 ∧ af.slotBase = 0 ∧ af.saves = [] ∧
      ∀ l code, (l, code) ∈ af.blocks.toList → ∀ m, AInst.inst m ∈ code.toList → touchesFrame m = false := by
  simp only [leafB, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, Array.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun l code hb m hm => ?_⟩
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hb
  have := h4 i (by simpa using hi)
  simp only [Array.getElem_toList] at e
  rw [e] at this
  simp only [Array.all_eq_true] at this
  obtain ⟨k, hk, e'⟩ := List.getElem_of_mem hm
  have := this k (by simpa using hk)
  simp only [Array.getElem_toList] at e'
  rw [e'] at this
  simpa using this

/-- **`lowerRFunc_ok` for `AllocAF`**: the frame size, slot base, blocks and checks of
`lowerRFunc`'s output, and the frame whenever the frame is not empty. -/
theorem AllocAF.ok {vc : VCode} {rf : RFunc} {af : AFunc} (h : AllocAF vc rf af) :
    (af.frameSize = (RAFrame.compute vc rf).total ∧ af.slotBase = (RAFrame.compute vc rf).size ∧
      af.blocks.size = (vc.blocks.zip rf.blocks).size ∧
      ∀ b vb items, vc.blocks[b]? = some vb → rf.blocks[b]? = some items →
        ∃ code, itemsCode (RAFrame.compute vc rf) vb items.toList = .ok code ∧
          af.blocks[b]? = some (vb.label, ((if b = 0 then [AInst.prologue] else []) ++ code).toArray)) ∧
      ((RAFrame.compute vc rf).total ≠ 0 → af.frame = true) ∧ ctlCheck vc rf = true := by
  obtain ⟨⟨h1, h2, h3, h4⟩, -, h6⟩ := lowerRFunc_ok h.1
  refine ⟨⟨h1, h2, h3, h4⟩, fun ht => ?_, h6⟩
  cases hf : af.frame
  · exact absurd (h1.symm.trans (leafB_spec (h.2 hf)).1) ht
  · rfl

/-- **`lowerRFunc_saves` for `AllocAF`.** -/
theorem AllocAF.saves {vc : VCode} {rf : RFunc} {af : AFunc} (h : AllocAF vc rf af) :
    saveShapeOk vc rf = true ∧ af.saves = rf.saved := by
  have := lowerRFunc_saves h.1
  exact ⟨this.1, this.2⟩

/-- Some `lowerRFunc` output exists (for the facts about `vc` and `rf` only). -/
theorem AllocAF.exists {vc : VCode} {rf : RFunc} {af : AFunc} (h : AllocAF vc rf af) :
    ∃ af0, lowerRFunc vc rf = .ok af0 :=
  ⟨_, h.1⟩

end Backend
