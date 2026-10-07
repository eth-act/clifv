import FV.Link.Image

/-! # The checks of rust-lld's output (L2b)

`leanLink` decides the outside part's facts on the file it writes (`outsideOkB`), with the
whole file as the excerpt (`agrees_self`):

* `outsideOkB_static`: the file is a static AArch64 executable (`hdrB_sound`);
* `outsideOkB_data`: cg_clif's data objects are at their link-map addresses with their resolved
  bytes (`dataB_sound`);
* `symsOkB_sound`, `outsideOkB_syms`: every link-map name but the self-call aliases is a symbol
  of the file at its address (`SymsOk`; the index `symIndex` only names the entry, which
  `symsOkB` re-checks on the file's bytes);
* `leanLink_spec`: `leanLink`'s checks and result, unfolded;
* **`leanLink_static'`**: `leanLink`'s output is a static executable (no premise).
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec

/-- The whole file is an excerpt of itself. -/
theorem agrees_self (file : ByteArray) : Agrees file [(0, file)] := by
  intro c hc i _
  rw [List.mem_singleton] at hc
  subst hc
  rw [Nat.zero_add]

/-- **`symsOkB` is sound**: the entries it finds are re-checked on the file's bytes. -/
theorem symsOkB_sound {I : LinkInput} {file : ByteArray} (h : symsOkB I file = true) :
    SymsOk I file := by
  intro p hp hal
  have := List.all_eq_true.1 h p hp
  simp only [Bool.or_eq_true] at this
  rcases this with h1 | h1
  · rw [Option.isNone_iff_eq_none] at hal; rw [hal] at h1; cases h1
  · split at h1
    · rename_i s i _
      split at h1
      · rename_i o v he
        simp only [Bool.and_eq_true, beq_iff_eq] at h1
        exact ⟨s, i, o, h1.1 ▸ he, h1.2⟩
      · cases h1
    · cases h1

theorem outsideOkB_parts {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (h : outsideOkB I D file = true) :
    hdrB [(0, file)] = true ∧ dataB I D [(0, file)] = true ∧ symsOkB I file = true := by
  simp only [outsideOkB, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **The checked file is a static AArch64 executable.** -/
theorem outsideOkB_static {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (h : outsideOkB I D file = true) : Static file :=
  hdrB_sound (outsideOkB_parts h).1 (agrees_self file)

/-- **The checked file holds the data objects** at their link-map addresses. -/
theorem outsideOkB_data {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (h : outsideOkB I D file = true) : ∀ o ∈ D, DataOk I file o :=
  dataB_sound (outsideOkB_parts h).2.1 (agrees_self file)

/-- **The checked file's symbol table is the link map** (the aliases excepted). -/
theorem outsideOkB_syms {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (h : outsideOkB I D file = true) : SymsOk I file :=
  symsOkB_sound (outsideOkB_parts h).2.2

/-- The placed functions' compiled code, in placement order. -/
abbrev placedArts (S : LinkSpec) : List Art :=
  ((tabOf S.input.resultsT).take S.funcs.length).map (·.2)

/-- The region's bytes the linker writes. -/
abbrev regionOf (S : LinkSpec) (tp : Nat → Option Nat) : ByteArray :=
  ByteArray.mk (regionBytes S.input tp (placedArts S)).toArray

theorem of_not_not {b : Bool} (h : ¬(!b) = true) : b = true := by
  cases b <;> simp_all

/-- `leanLink`'s checks and result, unfolded (`S.input` is the input `leanLink` builds from one
run of the pipeline). -/
theorem leanLink_spec {S : LinkSpec} {file0 file : ByteArray} (h : leanLink S file0 = .ok file) :
    ∃ phs, phdrs (fileRd file0) = some phs ∧ S.placeOkB = true ∧
      S.input.resultsT.all (·.2.toBool) = true ∧
      S.sizesOkB (tabOf S.input.resultsT) = true ∧
      (tabOf S.input.resultsT).all (fun e => relocsOkB S.input (tpOff phs) e.2) = true ∧
      aliasOkB S.input (tpOff phs) (tabOf S.input.resultsT) = true ∧
      aliasShapeB S.input (tabOf S.input.resultsT) = true ∧
      regionOkB file0 S.R (regionOf S (tpOff phs)).size (offsetOf phs S.R) = true ∧
      outsideOkB S.input S.data file = true ∧
      file = patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs)) := by
  unfold leanLink at h
  split at h
  · cases h
  rename_i phs hph
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hp hr hs hv hal hsh hok hout
  cases h
  exact ⟨phs, hph, of_not_not hp, of_not_not hr, of_not_not hs, of_not_not hv, of_not_not hal,
    of_not_not hsh, of_not_not hok, of_not_not hout, rfl⟩

/-- **`leanLink`'s output is a static executable** (its headers are checked: `outsideOkB`). -/
theorem leanLink_static' {S : LinkSpec} {file0 file : ByteArray}
    (h : leanLink S file0 = .ok file) : Static file := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hout, -⟩ := leanLink_spec h
  exact outsideOkB_static hout

end Link
