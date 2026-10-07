import FV.Link.ImageProof
import FV.Link.LayoutProof
import FV.E2E.LinkScope

/-! # The Lean linker's output is correct by construction (L2b)

For `leanLink S file0 = .ok file`:

* **`leanLink_code`**: every function of the compiler's table `tabOf S.input.resultsT` is in
  `file` (`ArtOk`): a placed function from the region's bytes (`ImageProof.region_words`), an
  alias from its function's words at the same base (`aliasOkB`), both with the relocation checks
  `relocsOkB` (`RelocProof.artOk_of_image`);
* **`leanLink_static`**: the headers are the outside part's, so `Static` carries over;
* **`binOkT_leanLink`**: `BinOkT` (`BinOk` with the code of the compiler's table), given the
  outside part's data objects and symbol table (`DataOk`, `SymsOk`);
* **`crate_correct_leanLink`**: the crate statement of an in-scope input linked by `leanLink`
  (`crate_correct_inScope` with the linker's facts `leanLink_linkerOk`).
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec

/-- The placed functions' compiled code, in placement order. -/
abbrev placedArts (S : LinkSpec) : List Art :=
  ((tabOf S.input.resultsT).take S.funcs.length).map (·.2)

/-- The region's bytes the linker writes. -/
abbrev regionOf (S : LinkSpec) (tp : Nat → Option Nat) : ByteArray :=
  ByteArray.mk (regionBytes S.input tp (placedArts S)).toArray

theorem of_not_not {b : Bool} (h : ¬(!b) = true) : b = true := by
  cases b <;> simp_all

/-- `leanLink`'s checks and result, unfolded. -/
theorem leanLink_spec {S : LinkSpec} {file0 file : ByteArray} (h : leanLink S file0 = .ok file) :
    ∃ phs, phdrs (fileRd file0) = some phs ∧ S.placeOkB = true ∧
      S.input.resultsT.all (·.2.toBool) = true ∧
      (tabOf S.input.resultsT).all (fun e => relocsOkB S.input (tpOff phs) e.2) = true ∧
      aliasOkB S.input (tpOff phs) (tabOf S.input.resultsT) = true ∧
      regionOkB file0 S.R (regionOf S (tpOff phs)).size (offsetOf phs S.R) = true ∧
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
  rename_i hp hr hv hal _ hok
  exact ⟨phs, hph, of_not_not hp, of_not_not hr, of_not_not hv, of_not_not hal, of_not_not hok,
    (Except.ok.inj h).symm⟩

/-- An association list's entry. -/
theorem mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by cases h
  | (k, v) :: l, a, b, h => by
    rw [List.lookup_cons] at h
    split at h
    · rename_i hk
      cases h
      rw [beq_iff_eq.1 hk]
      exact .head _
    · exact .tail _ (mem_of_lookup h)

/-- With distinct keys, `find?` by key finds the element. -/
theorem find?_key {α β : Type} [BEq β] [LawfulBEq β] {f : α → β} {l : List α}
    (hnd : (l.map f).Nodup) {x : α} (hx : x ∈ l) : l.find? (fun y => f y == f x) = some x := by
  induction l with
  | nil => cases hx
  | cons y l ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    rcases List.mem_cons.1 hx with rfl | hx'
    · simp
    · have hne : f y ≠ f x := fun e => hnd.1 (e ▸ List.mem_map.2 ⟨x, hx', rfl⟩)
      simp only [beq_eq_false_iff_ne.2 hne]
      exact ih hnd.2 hx'

/-- The compiler's table's names are the placed functions' and the aliases'. -/
theorem tab_names (S : LinkSpec) (hP : PlaceOk S) :
    ((tabOf S.input.resultsT).map (·.1.name)).Nodup := by
  have : (tabOf S.input.resultsT).map (·.1.name) = S.names ++ S.aliases.map (·.1) := by
    rw [← hP.aliasFns]
    simp [tabOf, LinkInput.resultsT, names, Function.comp_def]
  rw [this]
  exact hP.nodup

/-- The placed functions' sizes are the placement's. -/
theorem placedArts_sizes {S : LinkSpec} (hp : S.placeOkB = true)
    (hr : S.input.resultsT.all (·.2.toBool) = true) :
    (placedArts S).map (·.fb.words.size) = S.sizes := by
  have hTl := tab_length S
  apply List.ext_getElem
  · simp [hTl]
  · intro n h1 h2
    have hn : n < S.funcs.length := by simpa using h2
    obtain ⟨e, he, -, hs, -⟩ := tab_placed hp hr n hn
    have hl : n < (tabOf S.input.resultsT).length := by omega
    rw [List.getElem?_eq_getElem hl, Option.some.injEq] at he
    simp only [List.getElem_map, List.getElem_take, he, hs, getElem!_pos S.sizes n h2]

/-- `leanLink`'s output holds every placed function's resolved words, read-only. -/
theorem leanLink_placed {S : LinkSpec} {file0 : ByteArray} {phs : List Phdr}
    (hp : S.placeOkB = true) (hr : S.input.resultsT.all (·.2.toBool) = true)
    (hok : regionOkB file0 S.R (regionOf S (tpOff phs)).size (offsetOf phs S.R) = true)
    {i : Nat} (hi : i < S.funcs.length) {e : Clif.Function × Art}
    (he : (tabOf S.input.resultsT)[i]? = some e) :
    (∀ k < e.2.fb.words.size, ∀ j < 4,
      Elf.ro (patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs))) (wAt e.2 (4 * k + j))) ∧
    (∀ k < e.2.fb.words.size,
      readN (loadMem (patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs)))) 4 (wAt e.2 (4 * k)) =
        some (resolveWord S.input (tpOff phs) e.2 k)) := by
  have hP := placeOk_of hp
  obtain ⟨e', he', hb, -⟩ := tab_placed hp hr i hi
  rw [he, Option.some.injEq] at he'
  subst he'
  have hsz := placedArts_sizes hp hr
  have ha : (placedArts S)[i]? = some e.2 := by
    simp only [List.getElem?_map, List.getElem?_take, hi, ↓reduceIte, he, Option.map_some]
  refine region_words hok ?_ ha ?_
  · rw [hsz]
    have := hP.fits
    simp only [LinkSpec.size] at this
    omega
  · rw [hsz]
    exact hb

/-- **Every function of the compiler's table is in `leanLink`'s output** (`ArtOk`). -/
theorem leanLink_code {S : LinkSpec} {file0 file : ByteArray} (h : leanLink S file0 = .ok file) :
    ∀ e ∈ tabOf S.input.resultsT, ArtOk S.input file e.2 := by
  obtain ⟨phs, hph, hp, hr, hv, hal, hok, rfl⟩ := leanLink_spec h
  have hP := placeOk_of hp
  have hv' : ∀ e ∈ tabOf S.input.resultsT, relocsOkB S.input (tpOff phs) e.2 = true :=
    fun e he => List.all_eq_true.1 hv e he
  have htp := tpOff_patch hok hph
  intro e he
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 he
  have hil : i < (tabOf S.input.resultsT).length := (List.getElem?_eq_some_iff.1 hi).1
  rw [tab_length] at hil
  by_cases hin : i < S.funcs.length
  · have hw := leanLink_placed hp hr hok hin hi
    exact artOk_of_image (hv' e he) htp hw.1 hw.2
  · -- an alias: its function's words at its function's base
    obtain ⟨e', ef, he', ⟨i', hi', hef⟩, hb, hl⟩ :=
      tab_alias hp hr (i - S.funcs.length) (by omega)
    rw [show S.funcs.length + (i - S.funcs.length) = i by omega, hi, Option.some.injEq] at he'
    subst he'
    have hw := leanLink_placed hp hr hok hi' hef
    have hefm : ef ∈ tabOf S.input.resultsT := List.mem_of_getElem? hef
    have hpm := mem_of_lookup hl
    have hal' := List.all_eq_true.1 hal _ hpm
    simp only [find?_key (tab_names S hP) he, find?_key (tab_names S hP) hefm, Bool.and_eq_true,
      beq_iff_eq, List.all_eq_true, List.mem_range] at hal'
    obtain ⟨hsz, hres⟩ := hal'
    have hwAt : ∀ o, wAt e.2 o = wAt ef.2 o := fun o => by simp only [wAt, hb]
    refine artOk_of_image (hv' e he) htp (fun k hk j hj => ?_) (fun k hk => ?_)
    · rw [hwAt]; exact hw.1 k (hsz ▸ hk) j hj
    · rw [hwAt, hres k hk]; exact hw.2 k (hsz ▸ hk)

/-- **`leanLink`'s output is a static executable** when the outside part is. -/
theorem leanLink_static {S : LinkSpec} {file0 file : ByteArray} (h : leanLink S file0 = .ok file)
    (hs : Static file0) : Static file := by
  obtain ⟨phs, -, -, -, -, -, hok, rfl⟩ := leanLink_spec h
  exact static_patch hok hs

/-- **The file is the linked program `I` with data objects `D`**, the code being the compiler's
table (`tabOf I.resultsT`, the functions the executable runs): `BinOk` over `resultsT`. -/
structure BinOkT (I : LinkInput) (D : List Clif.DataObject) (file : ByteArray) : Prop where
  static : Static file
  code : ∀ e ∈ tabOf I.resultsT, ArtOk I file e.2
  data : ∀ o ∈ D, DataOk I file o
  syms : SymsOk I file

/-- **`BinOkT` of `leanLink`'s output**: the code by construction; the outside part's headers
(`Static file0`), data objects and symbols (`DataOk`, `SymsOk`) as hypotheses. -/
theorem binOkT_leanLink {S : LinkSpec} {D : List Clif.DataObject} {file0 file : ByteArray}
    (h : leanLink S file0 = .ok file) (hs : Static file0) (hd : ∀ o ∈ D, DataOk S.input file o)
    (hy : SymsOk S.input file) : BinOkT S.input D file :=
  ⟨leanLink_static h hs, leanLink_code h, hd, hy⟩

/-- **The crate statement of an in-scope input linked by `leanLink`**: `crate_correct_inScope`
with the linker's facts of `leanLink`'s output (`leanLink_linkerOk`). -/
theorem crate_correct_leanLink (hD : SpillDefinedHyp) {S : LinkSpec} {file0 file : ByteArray}
    (hin : InScopeP S.input = true) (h : leanLink S file0 = .ok file) (n : String) :
    CrateStmtT S.input n :=
  crate_correct_inScope hD hin (leanLink_linkerOk h) n

end Link
