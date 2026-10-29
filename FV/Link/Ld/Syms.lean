module

public import FV.Link.Ld.WriteProof
public import FV.Link.Image

@[expose] public section

/-! # The symbol check on the Lean linker's output (L2b stage 3b)

`symsOkB I file` (`FV/Link/Image.lean`, part of `file0OkB` and of `leanLink`'s checks) asks that
every link-map name be a symbol of the file at its address, found through the index
`symIndex` of the file's symbol tables. For a file written by `Img.write`:

* `symEntry_write`: entry `k + 1` of `.symtab` is symbol `k` (its name's offset in `.strtab`, its
  value); `symEntry_write_inv`: no other entry of any section is a defined symbol;
* `entryKey_write`: its index key is the symbol's name and value (names without NUL);
* **`symsOkB_write`**: every link map whose entries are written symbols (by name, `symName`,
  and value) passes the symbol check.
-/

namespace Link.Ld

open E2E E2E.Elf E2E.BinCheck Link

/-! ## String tables -/

theorem strOffsets_add : ∀ (l : List String) (o d : Nat),
    strOffsets l (o + d) = (strOffsets l o).map (· + d)
  | [], _, _ => rfl
  | n :: l, o, d => by
    simp only [strOffsets, List.map_cons]
    rw [show o + d + n.toUTF8.size + 1 = (o + n.toUTF8.size + 1) + d by omega, strOffsets_add l]

/-- The bytes of a name, then a NUL. -/
def nameRec (n : String) : List UInt8 := n.toUTF8.data.toList ++ [0]

theorem nameRec_length (n : String) : (nameRec n).length = n.toUTF8.size + 1 := by
  simp only [nameRec, List.length_append, Array.length_toList, List.length_singleton]; rfl

/-- The names' records. -/
def nameBytes (l : List String) : List UInt8 := l.flatMap nameRec

/-- **Name `i` in its string table**: its bytes, then a NUL, at its offset. -/
theorem nameBytes_getElem? : ∀ (l : List String) {i off : Nat}, (strOffsets l 0)[i]? = some off →
    ∀ {n : String}, l[i]? = some n → ∀ {j : Nat}, j ≤ n.toUTF8.size →
      (nameBytes l)[off + j]? = (nameRec n)[j]?
  | [], _, _, h, _, _, _, _ => by simp [strOffsets] at h
  | m :: l, 0, off, h, n, hn, j, hj => by
    simp only [strOffsets, List.getElem?_cons_zero, Option.some.injEq] at h hn
    subst h hn
    simp only [nameBytes, List.flatMap_cons, Nat.zero_add]
    rw [List.getElem?_append_left (by rw [nameRec_length]; omega)]
  | m :: l, i + 1, off, h, n, hn, j, hj => by
    simp only [strOffsets, List.getElem?_cons_succ, Nat.zero_add] at h hn
    have h' := h
    have ha := strOffsets_add l 0 (m.toUTF8.size + 1)
    rw [Nat.zero_add] at ha
    rw [ha, List.getElem?_map] at h'
    obtain ⟨off', ho', rfl⟩ := Option.map_eq_some_iff.1 h'
    simp only [nameBytes, List.flatMap_cons]
    rw [List.getElem?_append_right (by rw [nameRec_length]; omega), nameRec_length,
      show off' + (m.toUTF8.size + 1) + j - (m.toUTF8.size + 1) = off' + j by omega]
    exact nameBytes_getElem? l ho' hn hj

theorem strOffsets_getElem? (l : List String) (o : Nat) {i : Nat} (hi : i < l.length) :
    ∃ off, (strOffsets l o)[i]? = some off :=
  ⟨_, List.getElem?_eq_getElem (by rw [strOffsets_length]; exact hi)⟩

/-- **Name `i` in `strtabOf`**, at its offset (`strOffsets l 1`). -/
theorem strtabOf_getElem? (l : List String) {i off : Nat} (ho : (strOffsets l 1)[i]? = some off)
    {n : String} (hn : l[i]? = some n) {j : Nat} (hj : j ≤ n.toUTF8.size) :
    (strtabOf l)[off + j]? = (nameRec n)[j]? := by
  have h1 := strOffsets_add l 0 1
  rw [Nat.zero_add] at h1
  rw [h1, List.getElem?_map] at ho
  obtain ⟨off0, h0, rfl⟩ := Option.map_eq_some_iff.1 ho
  rw [show off0 + 1 + j = (off0 + j) + 1 by omega]
  exact nameBytes_getElem? l h0 hn hj

/-- A name's NUL lies in the table. -/
theorem strOffsets_lt (l : List String) {i off : Nat} (ho : (strOffsets l 1)[i]? = some off)
    {n : String} (hn : l[i]? = some n) : off + n.toUTF8.size < (strtabOf l).length := by
  have h := strtabOf_getElem? l ho hn (j := n.toUTF8.size) (Nat.le_refl _)
  have hr : (nameRec n)[n.toUTF8.size]? = some 0 := by
    rw [nameRec, List.getElem?_append_right (by simp)]
    simp
  rw [hr] at h
  rcases Nat.lt_or_ge (off + n.toUTF8.size) (strtabOf l).length with hc | hc
  · exact hc
  · rw [List.getElem?_eq_none hc] at h; cases h

/-! ## Decoding a name -/

theorem lt_of_getElem? {f : ByteArray} {o : Nat} {b : UInt8} (h : f[o]? = some b) : o < f.size := by
  if hc : o < f.size then exact hc else
    rw [getElem?_neg f o hc] at h
    cases h

theorem getElem_of_getElem? {f : ByteArray} {o : Nat} {b : UInt8} (h : f[o]? = some b) :
    f[o]'(lt_of_getElem? h) = b := by
  rw [getElem?_pos f o (lt_of_getElem? h)] at h
  exact Option.some.inj h

/-- The end of a NUL-terminated string of `d` nonzero bytes. -/
theorem nulFrom_eq {f : ByteArray} : ∀ {d o : Nat}, (∀ j < d, ∃ b, f[o + j]? = some b ∧ b ≠ 0) →
    f[o + d]? = some 0 → nulFrom f o = o + d
  | 0, o, _, h0 => by
    simp only [Nat.add_zero] at h0 ⊢
    rw [nulFrom]
    simp only [lt_of_getElem? h0, ↓reduceDIte, getElem_of_getElem? h0]
    rfl
  | d + 1, o, h, h0 => by
    obtain ⟨b, hb, hb0⟩ := h 0 (by omega)
    simp only [Nat.add_zero] at hb
    rw [nulFrom]
    simp only [lt_of_getElem? hb, ↓reduceDIte, getElem_of_getElem? hb]
    rw [if_pos (by simpa using hb0)]
    rw [nulFrom_eq (d := d) (o := o + 1) (fun j hj => by
        obtain ⟨c, hc, hc0⟩ := h (j + 1) (by omega)
        exact ⟨c, by rw [show o + 1 + j = o + (j + 1) by omega]; exact hc, hc0⟩)
      (by rw [show o + 1 + d = o + (d + 1) by omega]; exact h0)]
    omega

/-- `extract` of a range whose bytes are `s`'s. -/
theorem extract_eq {f : ByteArray} {o : Nat} {s : ByteArray}
    (h : ∀ j < s.size, f[o + j]? = s[j]?) (hend : o + s.size ≤ f.size) :
    f.extract o (o + s.size) = s := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract]
    show min (o + s.size) f.size - o = s.size
    omega
  · intro j h1 h2
    simp only [Array.getElem_extract]
    have := h j h2
    rw [getElem?_pos s j h2] at this
    exact getElem_of_getElem? this

theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  unfold String.fromUTF8?
  split
  · rfl
  · rename_i hn; exact absurd s.isValidUTF8 hn


/-! ## The symbol table's entries -/

/-- The symbols' names (`.strtab`'s strings). -/
abbrev Img.names (img : Img) : List String := img.syms.toList.map (·.name)

theorem names_getElem? (img : Img) {k : Nat} (hk : k < img.syms.size) :
    img.names[k]? = some img.syms[k].name := by simp [hk]

/-- Symbol `k`'s name offset in `.strtab`. -/
def Img.nameOff (img : Img) (k : Nat) : Nat := (strOffsets img.names 1).getD k 0

theorem nameOff_getElem? (img : Img) {k : Nat} (hk : k < img.syms.size) :
    (strOffsets img.names 1)[k]? = some (img.nameOff k) := by
  have hlt : k < (strOffsets img.names 1).length := by rw [strOffsets_length]; simpa using hk
  rw [Img.nameOff, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl

theorem symList_succ (img : Img) {k : Nat} (hk : k < img.syms.size) :
    img.symList[k + 1]? = some (symFields (img.nameOff k) img.syms[k]) := by
  have hz : (img.syms.toList.zip (strOffsets img.names 1))[k]? = some (img.syms[k], img.nameOff k) := by
    rw [List.getElem?_zip_eq_some]
    exact ⟨by simp [hk], nameOff_getElem? img hk⟩
  simp only [Img.symList, List.getElem?_cons_succ, List.getElem?_map]
  rw [hz]
  rfl

theorem symList_zero (img : Img) : img.symList[0]? = some (symFields 0 default) := rfl

theorem hdr_le_body {img : Img} (h : img.hdrFitsB = true) : img.hdr.length ≤ img.body.size := by
  simp only [Img.hdrFitsB, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [hdr_length]; exact h.1.2

/-- The fields `symEntry` reads of entry `i` of `.symtab`: name offset, section, value. -/
theorem fields_sym {img : Img} (h : img.hdrFitsB = true) (ht : img.tabsFitB = true) {i nm : Nat}
    {s : OutSym} (hi : img.symList[i]? = some (symFields nm s)) :
    fields (fileRd img.write) (img.tabs.symOff + 24 * i) [(0, 4), (6, 2), (8, 8)] =
      some [nm, s.shndx, s.value] := by
  have hfit : fieldsFitB (symFields nm s) = true := by
    simp only [Img.tabsFitB, Bool.and_eq_true, List.all_eq_true] at ht
    exact ht.1.1.2 _ (List.mem_of_getElem? hi)
  have hf : ∀ x < 24 * img.symList.length,
      img.write[img.tabs.symOff + x]? = (img.symList.flatMap (record 24))[x]? := fun x hx =>
    write_getElem?_symtab img (hdr_le_body h) (by rw [symList_length] at hx; simp only [Img.tabs]; omega)
  have F : ∀ o n v, (o, n, v) ∈ symFields nm s → o + n ≤ 24 →
      le (fileRd img.write) (img.tabs.symOff + 24 * i + o) n = some v :=
    fun o n v hm hs => le_records hf hi (disj_sym _ _) hm hs (fit_of hfit hm)
  simp only [fields, List.mapM_cons, List.mapM_nil]
  rw [show img.tabs.symOff + 24 * i = img.tabs.symOff + 24 * i + 0 by rfl,
    F 0 4 nm (by simp [symFields]) (by omega), F 6 2 s.shndx (by simp [symFields]) (by omega),
    F 8 8 s.value (by simp [symFields]) (by omega)]
  rfl

theorem syms_fit {img : Img} (ht : img.tabsFitB = true) {k : Nat} (hk : k < img.syms.size) :
    img.syms[k].shndx ≠ 0 ∧ img.syms[k].name.toUTF8.data.contains 0 = false := by
  simp only [Img.tabsFitB, Bool.and_eq_true, Array.all_eq_true] at ht
  have := ht.2 k hk
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at this
  exact this

/-- The file's ELF header (`ehdr_write`). -/
abbrev Img.ehdr (img : Img) : Ehdr :=
  ⟨2, 183, img.entry, 64, img.tabs.shoff, img.phs.length, img.secs.size + 4⟩

theorem strSize_eq (img : Img) : img.tabs.strSize = (strtabOf img.names).length := rfl

/-- **Entry `k + 1` of `.symtab` is symbol `k`.** -/
theorem symEntry_write {img : Img} (h : img.hdrFitsB = true) (ht : img.tabsFitB = true) {k : Nat}
    (hk : k < img.syms.size) :
    symEntry (fileRd img.write) (img.secs.size + 1) (k + 1) =
      some (img.tabs.strOff + img.nameOff k, img.syms[k].value) := by
  obtain ⟨o1, h1⟩ := shdrList_sym img img.tabs
  obtain ⟨o2, h2⟩ := shdrList_str img img.tabs
  have hlt := strOffsets_lt img.names (nameOff_getElem? img hk) (names_getElem? img hk)
  have hsz : 24 * (k + 1 + 1) ≤ img.tabs.symSize := by simp only [Img.tabs]; omega
  simp only [symEntry, ehdr_write h, Option.bind_some, shdr_write h ht h1]
  rw [if_pos ⟨trivial, trivial, hsz⟩]
  simp only [Option.bind_some, shdr_write h ht h2, fields_sym h ht (symList_succ img hk)]
  rw [if_pos ⟨trivial, by rw [strSize_eq]; omega, (syms_fit ht hk).1⟩]

/-- **The only defined symbols of the file** are `.symtab`'s entries `k + 1`. -/
theorem symEntry_write_inv {img : Img} (h : img.hdrFitsB = true) (ht : img.tabsFitB = true)
    {s i o v : Nat} (he : symEntry (fileRd img.write) s i = some (o, v)) :
    ∃ k, ∃ hk : k < img.syms.size, s = img.secs.size + 1 ∧ i = k + 1 ∧
      o = img.tabs.strOff + img.nameOff k ∧ v = img.syms[k].value := by
  have hty : ∀ k (hk : k < img.secs.size), img.secs[k].type ≠ 2 := by
    simp only [Img.tabsFitB, Bool.and_eq_true, Array.all_eq_true] at ht
    intro k hk
    simpa using ht.1.2 k hk
  have hsym : s = img.secs.size + 1 := by
    simp only [symEntry, ehdr_write h, Option.bind_some, Option.bind_eq_some_iff] at he
    obtain ⟨sh, hsh, he⟩ := he
    have hs : s < img.secs.size + 4 := by
      unfold shdr at hsh; split at hsh
      · assumption
      · cases hsh
    have h2 : sh.type = 2 := by
      split at he
      · rename_i hc; exact hc.1
      · cases he
    rcases (show s = 0 ∨ (1 ≤ s ∧ s ≤ img.secs.size) ∨ s = img.secs.size + 1 ∨
        s = img.secs.size + 2 ∨ s = img.secs.size + 3 by omega) with
      rfl | ⟨hs1, hs2⟩ | hs' | rfl | rfl
    · rw [shdr_write h ht (shdrList_zero img img.tabs)] at hsh; cases hsh; cases h2
    · obtain ⟨o, ho⟩ := shdrList_sec img img.tabs (k := s - 1) (by omega)
      rw [show s = s - 1 + 1 by omega, shdr_write h ht ho] at hsh
      rw [← Option.some.inj hsh] at h2
      exact absurd h2 (hty (s - 1) (by omega))
    · exact hs'
    · obtain ⟨o, ho⟩ := shdrList_str img img.tabs
      rw [shdr_write h ht ho] at hsh; cases hsh; cases h2
    · obtain ⟨o, ho⟩ := shdrList_shs img img.tabs
      rw [shdr_write h ht ho] at hsh; cases hsh; cases h2
  subst hsym
  have he0 := he
  obtain ⟨o1, h1⟩ := shdrList_sym img img.tabs
  obtain ⟨o2, h2⟩ := shdrList_str img img.tabs
  simp only [symEntry, ehdr_write h, Option.bind_some, shdr_write h ht h1] at he
  split at he
  · rename_i hc
    obtain ⟨-, -, hi⟩ := hc
    have hi' : i ≤ img.syms.size := by simp only [Img.tabs] at hi; omega
    rcases i with _ | k
    · simp only [Option.bind_some, shdr_write h ht h2, Nat.mul_zero,
        fields_sym h ht (symList_zero img)] at he
      rw [if_neg (fun hc => hc.2.2 rfl)] at he
      cases he
    · refine ⟨k, by omega, rfl, rfl, ?_⟩
      rw [symEntry_write h ht (k := k) (by omega)] at he0
      cases he0
      exact ⟨rfl, rfl⟩
  · cases he


/-! ## Names in the file -/

theorem nameOff_lt {img : Img} {k : Nat} (hk : k < img.syms.size) :
    img.nameOff k + img.syms[k].name.toUTF8.size < img.tabs.strSize := by
  rw [strSize_eq]; exact strOffsets_lt img.names (nameOff_getElem? img hk) (names_getElem? img hk)

/-- **Symbol `k`'s name in the file**: its bytes, then a NUL. -/
theorem name_bytes {img : Img} (h : img.hdrFitsB = true) {k : Nat} (hk : k < img.syms.size)
    {j : Nat} (hj : j ≤ img.syms[k].name.toUTF8.size) :
    img.write[img.tabs.strOff + img.nameOff k + j]? = (nameRec img.syms[k].name)[j]? := by
  have hlt := nameOff_lt hk
  rw [Nat.add_assoc, write_getElem?_strtab img (hdr_le_body h) (by omega)]
  exact strtabOf_getElem? img.names (nameOff_getElem? img hk) (names_getElem? img hk) hj

theorem nameRec_lt (n : String) {j : Nat} (hj : j < n.toUTF8.size) :
    (nameRec n)[j]? = some (n.toUTF8.data[j]'hj) := by
  rw [nameRec, List.getElem?_append_left (by simpa using hj)]
  simp

theorem nameRec_end (n : String) : (nameRec n)[n.toUTF8.size]? = some 0 := by
  rw [nameRec, List.getElem?_append_right (by simp)]
  simp

theorem name_nonzero {img : Img} (ht : img.tabsFitB = true) {k : Nat} (hk : k < img.syms.size)
    {j : Nat} (hj : j < img.syms[k].name.toUTF8.size) : img.syms[k].name.toUTF8.data[j]'hj ≠ 0 := by
  intro h0
  have hc := (syms_fit ht hk).2
  rw [Array.contains_eq_true_of_mem (h0 ▸ Array.getElem_mem hj)] at hc
  cases hc

/-- **Entry `k + 1`'s index key** is symbol `k`'s name and value. -/
theorem entryKey_write {img : Img} (h : img.hdrFitsB = true) (ht : img.tabsFitB = true) {k : Nat}
    (hk : k < img.syms.size) :
    entryKey img.write (img.secs.size + 1) (k + 1) = some (img.syms[k].name, img.syms[k].value) := by
  unfold entryKey
  rw [symEntry_write h ht hk]
  simp only
  have hlt := nameOff_lt hk
  have hn : nulFrom img.write (img.tabs.strOff + img.nameOff k) =
      img.tabs.strOff + img.nameOff k + img.syms[k].name.toUTF8.size :=
    nulFrom_eq (fun j hj => ⟨_, by rw [name_bytes h hk (by omega), nameRec_lt _ hj],
        name_nonzero ht hk hj⟩)
      (by rw [name_bytes h hk (Nat.le_refl _), nameRec_end])
  have hend : img.tabs.strOff + img.nameOff k + img.syms[k].name.toUTF8.size ≤ img.write.size := by
    have := lt_of_getElem? (show img.write[img.tabs.strOff + img.nameOff k +
        img.syms[k].name.toUTF8.size]? = some 0 by rw [name_bytes h hk (Nat.le_refl _), nameRec_end])
    omega
  rw [hn, extract_eq (fun j hj => by
      rw [name_bytes h hk (by omega), nameRec_lt _ hj, getElem?_pos _ j hj]; rfl) hend,
    fromUTF8?_toUTF8]
  rfl

/-- **Symbol `k`'s name is a C string at its offset.** -/
theorem cstrB_write {img : Img} (h : img.hdrFitsB = true) {k : Nat} (hk : k < img.syms.size) :
    cstrB (fileRd img.write) (img.tabs.strOff + img.nameOff k) img.syms[k].name = true := by
  simp only [cstrB, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]
  refine ⟨fun j hj => ?_, ?_⟩
  · simp only [fileRd]
    rw [name_bytes h hk (by omega), nameRec_lt _ hj]
    simp only [Option.map_some, Option.some.injEq]
    rw [getElem!_pos _ j hj]
    rfl
  · simp only [fileRd]
    rw [name_bytes h hk (Nat.le_refl _), nameRec_end]
    rfl

/-! ## The index -/

/-- An invariant kept by a left fold. -/
theorem foldl_inv {α β : Type} {f : β → α → β} (P : β → Prop) (hf : ∀ b a, P b → P (f b a)) :
    ∀ (l : List α) (b : β), P b → P (l.foldl f b)
  | [], _, h => h
  | a :: l, b, h => foldl_inv P hf l (f b a) (hf b a h)

/-- A property reached at a member of the list and kept afterwards. -/
theorem foldl_at {α β : Type} {f : β → α → β} (P : β → Prop) (hf : ∀ b a, P b → P (f b a))
    {a : α} (ha : ∀ b, P (f b a)) : ∀ (l : List α) (b : β), a ∈ l → P (l.foldl f b)
  | [], _, h => by cases h
  | x :: l, b, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact foldl_inv P hf l _ (ha b)
    · exact foldl_at P hf ha l (f b x) h

/-- The step of the index's inner fold. -/
def idxStep (file : ByteArray) (s : Nat) (out : Std.HashMap (String × Nat) (Nat × Nat)) (i : Nat) :
    Std.HashMap (String × Nat) (Nat × Nat) :=
  match entryKey file s i with
  | some k => if !out.contains k then out.insert k (s, i) else out
  | none => out

/-- Every index entry names an entry with its key. -/
def IdxSound (file : ByteArray) (m : Std.HashMap (String × Nat) (Nat × Nat)) : Prop :=
  ∀ k v, m[k]? = some v → entryKey file v.1 v.2 = some k

theorem idxStep_sound {file : ByteArray} {s : Nat} {m : Std.HashMap (String × Nat) (Nat × Nat)}
    (hm : IdxSound file m) (i : Nat) : IdxSound file (idxStep file s m i) := by
  unfold idxStep
  split
  · rename_i k hk
    split
    · intro k' v hv
      rw [Std.HashMap.getElem?_insert] at hv
      split at hv
      · rename_i he
        cases hv
        rw [beq_iff_eq] at he; subst he; exact hk
      · exact hm k' v hv
    · exact hm
  · exact hm

theorem idxStep_mono {file : ByteArray} {s : Nat} {m : Std.HashMap (String × Nat) (Nat × Nat)}
    {k : String × Nat} (hm : m.contains k = true) (i : Nat) : (idxStep file s m i).contains k = true := by
  unfold idxStep
  split
  · split
    · rw [Std.HashMap.contains_insert, hm, Bool.or_true]
    · exact hm
  · exact hm

theorem idxStep_at {file : ByteArray} {s i : Nat} {k : String × Nat} (hk : entryKey file s i = some k)
    (m : Std.HashMap (String × Nat) (Nat × Nat)) : (idxStep file s m i).contains k = true := by
  unfold idxStep
  rw [hk]
  simp only
  split
  · rw [Std.HashMap.contains_insert]; simp
  · rename_i hc; simpa using hc

/-- The index's outer step (one section). -/
def idxSec (file : ByteArray) (e : Ehdr) (out : Std.HashMap (String × Nat) (Nat × Nat)) (s : Nat) :
    Std.HashMap (String × Nat) (Nat × Nat) :=
  match shdr (fileRd file) e s with
  | none => out
  | some sh =>
    if sh.type != 2 || sh.entsize != 24 then out
    else (List.range (sh.size / 24)).foldl (idxStep file s) out

theorem symIndex_eq {file : ByteArray} {e : Ehdr} (he : ehdr (fileRd file) = some e) :
    symIndex file = (List.range e.shnum).foldl (idxSec file e) {} := by
  simp only [symIndex, he]
  rfl

theorem idxSec_sound {file : ByteArray} {e : Ehdr} {m : Std.HashMap (String × Nat) (Nat × Nat)}
    (hm : IdxSound file m) (s : Nat) : IdxSound file (idxSec file e m s) := by
  unfold idxSec
  split
  · exact hm
  · split
    · exact hm
    · exact foldl_inv (IdxSound file) (fun b a hb => idxStep_sound hb a) _ _ hm

theorem idxSec_mono {file : ByteArray} {e : Ehdr} {m : Std.HashMap (String × Nat) (Nat × Nat)}
    {k : String × Nat} (hm : m.contains k = true) (s : Nat) : (idxSec file e m s).contains k = true := by
  unfold idxSec
  split
  · exact hm
  · split
    · exact hm
    · exact foldl_inv (fun b : Std.HashMap (String × Nat) (Nat × Nat) => b.contains k = true) (fun b a hb => idxStep_mono hb a) _ _ hm

/-- **The index is sound**: it maps a key only to an entry with that key. -/
theorem symIndex_sound {file : ByteArray} : IdxSound file (symIndex file) := by
  unfold symIndex
  simp only
  split
  · intro k v hv; simp at hv
  · exact foldl_inv (IdxSound file) (fun b a hb => idxSec_sound hb a) _ _
      (fun k v hv => by simp at hv)

/-- **The index is complete** for the entries of a symbol table. -/
theorem symIndex_complete {file : ByteArray} {e : Ehdr} (he : ehdr (fileRd file) = some e) {s i : Nat}
    (hs : s < e.shnum) {sh : Shdr} (hsh : shdr (fileRd file) e s = some sh) (h2 : sh.type = 2)
    (h24 : sh.entsize = 24) (hi : i < sh.size / 24) {k : String × Nat}
    (hk : entryKey file s i = some k) : (symIndex file).contains k = true := by
  rw [symIndex_eq he]
  refine foldl_at (fun b : Std.HashMap (String × Nat) (Nat × Nat) => b.contains k = true) (fun b a hb => idxSec_mono hb a) (a := s)
    (fun b => ?_) _ _ (List.mem_range.2 hs)
  unfold idxSec
  rw [hsh]
  simp only [h2, h24, bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  exact foldl_at (fun b : Std.HashMap (String × Nat) (Nat × Nat) => b.contains k = true) (fun b a hb => idxStep_mono hb a) (a := i)
    (fun b => idxStep_at hk b) _ _ (List.mem_range.2 hi)

/-! ## The symbol check -/

/-- **The symbol check on `lean-ld`'s output**: every link map whose entries (but the aliases)
are written symbols — name (`symName`) and value — passes `symsOkB`. -/
theorem symsOkB_write {img : Img} (h : img.hdrFitsB = true) (ht : img.tabsFitB = true)
    (I : E2E.LinkCheck.LinkInput)
    (hI : ∀ p ∈ I.addrs, (I.aliases.lookup p.1).isSome = true ∨
      ∃ k, ∃ hk : k < img.syms.size, img.syms[k].name = symName p.1 ∧ img.syms[k].value = p.2) :
    symsOkB I img.write = true := by
  unfold symsOkB
  simp only [List.all_eq_true]
  intro p hp
  rcases hI p hp with ha | ⟨k, hk, hn, hv⟩
  · simp [ha]
  · simp only [Bool.or_eq_true]
    right
    obtain ⟨o1, h1⟩ := shdrList_sym img img.tabs
    have hc := symIndex_complete (ehdr_write h) (s := img.secs.size + 1) (by simp)
      (shdr_write h ht h1) rfl rfl (i := k + 1) (by simp only [Img.tabs]; omega)
      (entryKey_write h ht hk)
    rw [hn, hv] at hc
    rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
    obtain ⟨⟨s', i'⟩, hsv⟩ := Option.isSome_iff_exists.1 hc
    rw [hsv]
    have hkey := symIndex_sound _ _ hsv
    simp only at hkey
    unfold entryKey at hkey
    split at hkey
    · rename_i o' v' hse
      obtain ⟨k', hk', rfl, rfl, rfl, rfl⟩ := symEntry_write_inv h ht hse
      have hk2 := entryKey_write h ht hk'
      unfold entryKey at hk2
      rw [symEntry_write h ht hk'] at hk2
      simp only at hk2 hkey
      rw [hk2] at hkey
      simp only [Option.some.injEq, Prod.mk.injEq] at hkey
      obtain ⟨hn', hv'⟩ := hkey
      simp only [symEntry_write h ht hk', hv', beq_self_eq_true, Bool.true_and]
      rw [← hn']
      exact cstrB_write h hk'
    · cases hkey


/-! ## Non-vacuity -/

/-- `tinyImg` with one symbol `f` at its entry. -/
def tinySymImg : Img :=
  { tinyImg with syms := #[{ name := "f", value := 0x200078, info := 0x12, shndx := 0xfff1 }] }

theorem tinySymImg_hdrFits : tinySymImg.hdrFitsB = true := by decide +kernel

theorem tinySymImg_tabsFit : tinySymImg.tabsFitB = true := by decide +kernel

theorem symsOkB_write_witness (I : E2E.LinkCheck.LinkInput) (hI : I.addrs = [("f", 0x200078)]) :
    symsOkB I tinySymImg.write = true :=
  symsOkB_write tinySymImg_hdrFits tinySymImg_tabsFit I fun p hp => by
    rw [hI, List.mem_singleton] at hp
    subst hp
    exact Or.inr ⟨0, by decide, by native_decide, rfl⟩

end Link.Ld
