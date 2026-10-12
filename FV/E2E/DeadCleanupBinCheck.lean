import FV.E2E.BinCheck
import FV.E2E.DeadCleanupLinkCheck

namespace E2E.DeadCleanupBinCheck
open E2E E2E.LinkCheck E2E.BinCheck Backend Elf

def artIn (I : LinkInput) (fi : FnInput) : Art := getOk (I.pipeCleanupOf fi)

/-- **The code check of the functions `fs`** (a slice of the input's) on an excerpt. -/
def codeB (I : LinkInput) (ex : Excerpt) (fs : List FnInput) : Bool :=
  match phdrs (exRd ex) with
  | some phs => fs.all fun fi => artB I (exRd ex) phs (artIn I fi)
  | none => false

/-- `ArtOk` for the functions `fs`. -/
def ArtsOk (I : LinkInput) (file : ByteArray) (fs : List FnInput) : Prop :=
  ∀ fi ∈ fs, ArtOk I file (artIn I fi)

theorem artsOk_append {I : LinkInput} {file : ByteArray} {l₁ l₂ : List FnInput}
    (h₁ : ArtsOk I file l₁) (h₂ : ArtsOk I file l₂) : ArtsOk I file (l₁ ++ l₂) := by
  intro fi hfi
  rcases List.mem_append.1 hfi with h | h
  · exact h₁ fi h
  · exact h₂ fi h

theorem codeB_sound {I : LinkInput} {ex : Excerpt} {fs : List FnInput}
    (h : codeB I ex fs = true) {file : ByteArray} (hA : Agrees file ex) : ArtsOk I file fs := by
  unfold codeB at h
  split at h
  · rename_i phs hp
    exact fun fi hfi => artB_sound hA hp (List.all_eq_true.1 h fi hfi)
  · cases h

structure BinOk (I : LinkInput) (D : List Clif.DataObject) (file : ByteArray) : Prop where
  static : Static file
  code : ∀ e ∈ tabOf I.resultsCleanup, ArtOk I file e.2
  data : ∀ o ∈ D, DataOk I file o
  syms : SymsOk I file

theorem binOk_of {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hs : Static file) (hc : ArtsOk I file I.funcs) (hd : ∀ o ∈ D, DataOk I file o)
    (hy : SymsOk I file) : BinOk I D file := by
  refine ⟨hs, fun e he => ?_, hd, hy⟩
  simp only [tabOf, LinkInput.resultsCleanup, List.map_map, List.mem_map, Function.comp] at he
  obtain ⟨fi, hfi, rfl⟩ := he
  exact hc fi hfi

/-! ## Consequences -/

/-- `a` is a byte of a relocated word of the image. -/
def RelocAt (I : LinkInput) (a : BitVec 64) : Prop :=
  ∃ e ∈ tabOf I.resultsCleanup, ∃ r ∈ e.2.fb.relocs, ∃ i < 4, a = wAt e.2 (r.offset + i)

theorem img_bytes {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hB : BinOk I D file) (hI : okBCleanup I = true) {a : BitVec 64} (ha : ImgT (tabOf I.resultsCleanup) a) :
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
      have := okBCleanup_global hI ("imgCode: the image reads back", imgB (tabOf I.resultsCleanup))
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
