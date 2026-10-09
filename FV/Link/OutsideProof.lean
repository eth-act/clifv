import FV.Link.Image

/-! # The checks of rust-lld's output (L2b)

`leanLink` decides the outside part's facts on the file it writes (`outsideOkB`), with the
whole file as the excerpt (`agrees_self`):

* `outsideOkB_static`: the file is a static AArch64 executable (`hdrB_sound`);
* `outsideOkB_data`: cg_clif's data objects are at their link-map addresses with their resolved
  bytes (`dataFastB_sound`: `dataFastB` is `dataB` with one address map, `addrMap_get`, so
  `dataB_sound`);
* `symsOkB_sound`, `outsideOkB_syms`: every link-map name is a symbol
  of the file at its address (`SymsOk`; the index `symIndex` only names the entry, which
  `symsOkB` re-checks on the file's bytes);
* `leanLink_spec`: `leanLink`'s checks and result, unfolded (its parallel pipeline is
  `S.input`'s: `parResultsT_eq`);
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

theorem addrMap_foldl (l : List (String × Nat)) (m : Std.HashMap String Nat) (n : String) :
    (l.foldl (fun m p => m.insertIfNew p.1 p.2) m)[n]? = (m[n]?).or (l.lookup n) := by
  induction l generalizing m with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, ih, Std.HashMap.getElem?_insertIfNew, List.lookup_cons]
    by_cases hk : p.1 = n
    · subst hk
      by_cases hm : p.1 ∈ m
      · simp [hm]
      · simp [hm]
    · have : (n == p.1) = false := by simp [Ne.symm hk]
      simp [hk, this]

/-- **`addrMap`'s lookup is the link map's.** -/
theorem addrMap_get (l : List (String × Nat)) (n : String) : (addrMap l)[n]? = l.lookup n := by
  rw [addrMap, addrMap_foldl]
  simp

theorem objFastB_eq (I : LinkInput) (r : Rd) (phs : List Phdr) (o : Clif.DataObject) :
    objFastB (addrMap I.addrs) I r phs o = objB I r phs o := by
  unfold objFastB objB
  rw [addrMap_get]
  cases hl : I.addrs.lookup o.name with
  | none => simp
  | some a =>
    have hat : objAt I o = BitVec.ofNat 64 a := by simp [objAt, addrOf_of_lookup hl]
    simp only [Option.isSome_some, Bool.true_and, List.size_toArray, List.getElem?_toArray, hat]

theorem dataFastB_eq (I : LinkInput) (D : List Clif.DataObject) (ex : Excerpt) :
    dataFastB I D ex = dataB I D ex := by
  unfold dataFastB dataB
  cases phdrs (exRd ex) with
  | none => rfl
  | some phs =>
    show D.all (objFastB (addrMap I.addrs) I (exRd ex) phs) = D.all (objB I (exRd ex) phs)
    congr 1
    funext o
    exact objFastB_eq I _ phs o

/-- **`dataFastB` is sound** (it is `dataB`). -/
theorem dataFastB_sound {I : LinkInput} {D : List Clif.DataObject} {ex : Excerpt}
    (h : dataFastB I D ex = true) {file : ByteArray} (hA : Agrees file ex) :
    ∀ o ∈ D, DataOk I file o :=
  dataB_sound (dataFastB_eq I D ex ▸ h) hA

theorem outsideOkB_parts {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (h : outsideOkB I D file = true) :
    hdrB [(0, file)] = true ∧ dataFastB I D [(0, file)] = true ∧ symsOkB I file = true := by
  simp only [outsideOkB, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **The checked file is a static AArch64 executable.** -/
theorem outsideOkB_static {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (h : outsideOkB I D file = true) : Static file :=
  hdrB_sound (outsideOkB_parts h).1 (agrees_self file)

/-- **The checked file holds the data objects** at their link-map addresses. -/
theorem outsideOkB_data {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (h : outsideOkB I D file = true) : ∀ o ∈ D, DataOk I file o :=
  dataFastB_sound (outsideOkB_parts h).2.1 (agrees_self file)

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
      S.namesOkB (tabOf S.input.resultsT) = true ∧
      S.sizesOkB (tabOf S.input.resultsT) = true ∧
      (tabOf S.input.resultsT).all (fun e => relocsOkB S.input (tpOff phs) e.2) = true ∧
      codeMapB S.input (tabOf S.input.resultsT) = true ∧
      regionOkB file0 S.R (regionOf S (tpOff phs)).size (offsetOf phs S.R) = true ∧
      outsideOkB S.input S.data file = true ∧
      file = patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs)) := by
  unfold leanLink at h
  split at h
  · cases h
  rename_i phs hph
  dsimp only at h
  rw [parResultsT_eq] at h
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
  rename_i hp hr hn hs hv hcm hok hout
  cases h
  exact ⟨phs, hph, of_not_not hp, of_not_not hr, of_not_not hn, of_not_not hs, of_not_not hv,
    of_not_not hcm, of_not_not hok, of_not_not hout, rfl⟩

/-- **`leanLink`'s output is a static executable** (its headers are checked: `outsideOkB`). -/
theorem leanLink_static' {S : LinkSpec} {file0 file : ByteArray}
    (h : leanLink S file0 = .ok file) : Static file := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hout, -⟩ := leanLink_spec h
  exact outsideOkB_static hout

end Link
