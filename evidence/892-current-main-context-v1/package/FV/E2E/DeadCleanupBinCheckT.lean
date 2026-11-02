import FV.E2E.DeadCleanupBinCheck
import FV.E2E.DeadCleanupLinkCheckT
import FV.E2E.LinkArmT
import FV.E2E.LinkCheckT
import FV.E2E.PipelineCheckT

/-! # Typed copies of `FV.E2E.DeadCleanupBinCheck` (S11e5 Stage C, slice 8)

The declarations of `FV.E2E.DeadCleanupBinCheck` that depend on the integer link contract
(`LinkSys.Ok`, `LinkSys.Thm`, `okB`, `ArmRefines`), for the typed contract `LinkSys.OkT`
(suffix `T`; `LinkSys.Ok.*` as `LinkSys.OkT.*`). -/

namespace E2E.DeadCleanupBinCheck
open E2E E2E.LinkCheck E2E.BinCheck Backend Elf

theorem img_bytesT {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hB : BinOk I D file) (hI : okBCleanupT I = true) {a : BitVec 64} (ha : ImgT (tabOf I.resultsCleanup) a) :
    Elf.ro file a ∧ (loadMem file a = some (memT (tabOf I.resultsCleanup) a) ∨ RelocAt I a) := by
  obtain ⟨e, he, p, hp, hlt⟩ := ha
  obtain ⟨j, hj, hp1⟩ := mem_wordsAt (k := 0) hp
  rw [Nat.zero_add] at hp1
  have hjl : j < e.2.fb.words.size := by
    have := (List.getElem?_eq_some_iff.1 hj).1; simpa using this
  have hj' : e.2.fb.words[j]? = some p.2 := by simpa using hj
  have hA := hB.code e he
  obtain ⟨i, hi⟩ : ∃ i, i = (a - p.1).toNat := ⟨_, rfl⟩
  rw [← hi] at hlt
  have ha' : a = wAt e.2 (4 * j + i) := by
    simp only [wAt]
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, ← hp1, hi, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.add_comm, BitVec.sub_add_cancel]
  refine ⟨ha' ▸ hA.ro j hjl i hlt, ?_⟩
  by_cases hr : ∃ r ∈ e.2.fb.relocs, r.offset = 4 * j
  · obtain ⟨r, hr, hro⟩ := hr
    exact .inr ⟨e, he, r, hr, i, hlt, by rw [hro]; exact ha'⟩
  · left
    have hpl := hA.plain j p.2 hj' fun r hr' hro => hr ⟨r, hr', hro⟩
    have himg : imgB (tabOf I.resultsCleanup) = true := by
      have := okBCleanup_globalT hI ("imgCode: the image reads back", imgB (tabOf I.resultsCleanup))
        (by simp [globalChks])
      exact this
    have hw := imgCode_of himg he (setMem Arm.ArmState.default (memT (tabOf I.resultsCleanup)))
      (fun _ _ => rfl) j p.2 hj'
    obtain ⟨hr1, hb⟩ := readN_bytes hpl
    have heq := read_mem_bytes_bytes 4 _ _ _ (hr1.trans hw.symm) i hlt
    obtain ⟨b, hb1, hb2⟩ := hb i hlt
    have hwa : wAt e.2 (4 * j) + BitVec.ofNat 64 i = a := by
      rw [ha']; simp only [wAt, BitVec.ofNat_add, BitVec.add_assoc]
    rw [hwa] at hb1 hb2 heq
    rw [hb1, ← hb2, heq]
    rfl
end E2E.DeadCleanupBinCheck
