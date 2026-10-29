module

public import FV.E2E.BinCheck
public import FV.E2E.ActualPipelineCheck

@[expose] public section

/-! Actual emitted-artifact/ELF provenance. Reuses the existing ELF parser,
relocation, data, symbol and byte checks; the code table is the actual pipeline
result table, without a legacy reconstruction or diagnostic-history rewrite. -/
set_option autoImplicit false

namespace E2E.BinCheck
open Backend E2E.LinkCheck Elf

/-- Actual total-pipeline output with the original source/oracle indices/base. -/
def artInWithLowering (I : LinkInput) (lower : Clif.Function → Except String VCode)
    (stage : Clif.Function → VCode → VCode) (fi : FnInput) : Art :=
  getOk (pipeTWithLowering lower stage fi.func fi.k
    (BitVec.ofNat 64 (I.baseOf fi.func.name)) (raJ fi.ra fi.j))

def codeBWithLowering (I : LinkInput) (lower : Clif.Function → Except String VCode)
    (stage : Clif.Function → VCode → VCode) (ex : Excerpt) (fs : List FnInput) : Bool :=
  match phdrs (exRd ex) with
  | some phs => fs.all fun fi => artB I (exRd ex) phs (artInWithLowering I lower stage fi)
  | none => false

def ArtsOkWithLowering (I : LinkInput) (lower : Clif.Function → Except String VCode)
    (stage : Clif.Function → VCode → VCode) (file : ByteArray) (fs : List FnInput) : Prop :=
  ∀ fi ∈ fs, ArtOk I file (artInWithLowering I lower stage fi)

theorem artsOkWithLowering_append {I : LinkInput}
    {lower : Clif.Function → Except String VCode} {stage : Clif.Function → VCode → VCode}
    {file : ByteArray} {l₁ l₂ : List FnInput}
    (h₁ : ArtsOkWithLowering I lower stage file l₁)
    (h₂ : ArtsOkWithLowering I lower stage file l₂) :
    ArtsOkWithLowering I lower stage file (l₁ ++ l₂) := by
  intro fi hfi
  rcases List.mem_append.1 hfi with h | h
  · exact h₁ fi h
  · exact h₂ fi h

theorem codeBWithLowering_sound {I : LinkInput}
    {lower : Clif.Function → Except String VCode} {stage : Clif.Function → VCode → VCode}
    {ex : Excerpt} {fs : List FnInput}
    (h : codeBWithLowering I lower stage ex fs = true) {file : ByteArray}
    (hA : Agrees file ex) : ArtsOkWithLowering I lower stage file fs := by
  unfold codeBWithLowering at h
  split at h
  · rename_i phs hp
    exact fun fi hfi => artB_sound hA hp (List.all_eq_true.1 h fi hfi)
  · cases h

/-- Same binary obligations, for an explicit actual result table. -/
structure BinOkWithResults (I : LinkInput) (R : Res) (D : List Clif.DataObject)
    (file : ByteArray) : Prop where
  static : Static file
  code : ∀ e ∈ tabOf R, ArtOk I file e.2
  data : ∀ o ∈ D, DataOk I file o
  syms : SymsOk I file

theorem BinOk.toWithResults {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (h : BinOk I D file) : BinOkWithResults I I.results D file :=
  ⟨h.static, h.code, h.data, h.syms⟩

theorem binOkWithResults_ofLowering {I : LinkInput}
    {lower : Clif.Function → Except String VCode} {stage : Clif.Function → VCode → VCode}
    {D : List Clif.DataObject} {file : ByteArray} (hs : Static file)
    (hc : ArtsOkWithLowering I lower stage file I.funcs)
    (hd : ∀ o ∈ D, DataOk I file o) (hy : SymsOk I file) :
    BinOkWithResults I (I.resultsTWithLowering lower stage) D file := by
  refine ⟨hs, fun e he => ?_, hd, hy⟩
  simp only [tabOf, LinkInput.resultsTWithLowering, List.map_map, List.mem_map,
    Function.comp] at he
  obtain ⟨fi, hfi, rfl⟩ := he
  exact hc fi hfi

def RelocAtWithResults (I : LinkInput) (R : Res) (a : BitVec 64) : Prop :=
  ∃ e ∈ tabOf R, ∃ r ∈ e.2.fb.relocs, ∃ i < 4, a = wAt e.2 (r.offset + i)

theorem img_bytesWithResults {I : LinkInput} {R : Res} {D : List Clif.DataObject} {file : ByteArray}
    (hB : BinOkWithResults I R D file) (himg : imgB (tabOf R) = true) {a : BitVec 64} (ha : ImgT (tabOf R) a) :
    Elf.ro file a ∧ (loadMem file a = some (memT (tabOf R) a) ∨ RelocAtWithResults I R a) := by
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
    have hw := imgCode_of himg he (setMem Arm.ArmState.default (memT (tabOf R)))
      (fun _ _ => rfl) j p.2 hj'
    obtain ⟨hr1, hb⟩ := readN_bytes hpl
    have heq := read_mem_bytes_bytes 4 _ _ _ (hr1.trans hw.symm) i hlt
    obtain ⟨b, hb1, hb2⟩ := hb i hlt
    have hwa : wAt e.2 (4 * j) + BitVec.ofNat 64 i = a := by
      rw [ha']; simp only [wAt, BitVec.ofNat_add, BitVec.add_assoc]
    rw [hwa] at hb1 hb2 heq
    rw [hb1, ← hb2, heq]
    rfl


theorem img_bytesWithLowering {I : LinkInput}
    {lower : Clif.Function → Except String VCode} {stage : Clif.Function → VCode → VCode}
    {D : List Clif.DataObject} {file : ByteArray}
    (hB : BinOkWithResults I (I.resultsTWithLowering lower stage) D file)
    (hI : okRWith stage I (I.resultsTWithLowering lower stage) = true)
    {a : BitVec 64} (ha : ImgT (tabOf (I.resultsTWithLowering lower stage)) a) :
    Elf.ro file a ∧
      (loadMem file a = some (memT (tabOf (I.resultsTWithLowering lower stage)) a) ∨
        RelocAtWithResults I (I.resultsTWithLowering lower stage) a) := by
  have himg : imgB (tabOf (I.resultsTWithLowering lower stage)) = true :=
    okRWith_global stage hI
      ("imgCode: the image reads back", imgB (tabOf (I.resultsTWithLowering lower stage)))
      (by simp [globalChks])
  exact img_bytesWithResults hB himg ha

end E2E.BinCheck
