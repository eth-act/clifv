import FV.Link.Image
import FV.Link.RelocProof
import FV.Link.LayoutFacts

/-! # The region's bytes in the executable (L2b)

What the patched executable `patch file0 off B` holds, from the outside part's facts
`regionOkB file0 R B.size off`:

* `patch`: `B` inside `[off, off + B.size)`, the file elsewhere (`patch_getElem?`);
* the ELF and program headers lie below `off` and the readers read only them
  (`ehdr_congr`, `phdrs_congr`), so the patched file's are `file0`'s (`ehdr_patch`,
  `phdrs_patch`); hence `TpOff` and `Static` carry over (`tpOff_patch`, `static_patch`);
* the region `[R, R + B.size)` is in one read-only `PT_LOAD` segment (`segIn_region`), its file
  bytes at `off`: the loaded byte at `R + j` is `B[j]`, read-only (`loadMem_patch`, `ro_patch`);
* the region's bytes (`regionBytes`) hold function `j`'s resolved words from its offset
  `span (sizes.take j)` (`regionBytes_getElem?`), little-endian (`readN_wordBytes`);
* **`artOk_region`**: each placed function whose relocations pass `relocsOkB` is `ArtOk` in the
  patched file (by `artOk_of_image`).
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend

/-! ## Patching -/

theorem byteArray_getElem? (file : ByteArray) (i : Nat) : file[i]? = file.data[i]? := by
  by_cases h : i < file.size
  · rw [getElem?_pos file i h, getElem?_pos file.data i h]; rfl
  · rw [getElem?_neg file i h, getElem?_neg file.data i h]

theorem patch_size (file : ByteArray) (off : Nat) (b : ByteArray) :
    (patch file off b).size = file.size :=
  show (Array.ofFn _).size = _ from Array.size_ofFn

/-- **The patched file**: `b` in `[off, off + b.size)` (within the file), the file elsewhere. -/
theorem patch_getElem? (file : ByteArray) (off : Nat) (b : ByteArray) (i : Nat) :
    (patch file off b)[i]? =
      if off ≤ i ∧ i - off < b.size ∧ i < file.size then b[i - off]? else file[i]? := by
  rw [byteArray_getElem?, byteArray_getElem?, byteArray_getElem?]
  simp only [patch, Array.getElem?_ofFn]
  by_cases hi : i < file.size
  · by_cases hb : off ≤ i ∧ i - off < b.size
    · simp only [hi, hb, and_self, ↓reduceDIte, ↓reduceIte]
      rw [getElem!_pos b (i - off) hb.2, getElem?_pos b.data (i - off) hb.2]; rfl
    · simp only [hi, hb, ↓reduceDIte, ↓reduceIte, and_true]
      rw [getElem?_pos file.data i hi]; rfl
  · simp only [hi, ↓reduceDIte, and_false, ↓reduceIte]
    rw [getElem?_neg file.data i hi]

theorem fileRd_patch_lt {file : ByteArray} {off : Nat} {b : ByteArray} {o : Nat} (h : o < off) :
    fileRd (patch file off b) o = fileRd file o := by
  simp only [fileRd, patch_getElem?]
  split
  · omega
  · rfl

theorem fileRd_patch_in {file : ByteArray} {off : Nat} {b : ByteArray} {i : Nat}
    (hi : i < b.size) (hf : off + b.size ≤ file.size) :
    fileRd (patch file off b) (off + i) = b[i]?.map (·.toBitVec) := by
  simp only [fileRd, patch_getElem?]
  split
  · rw [Nat.add_sub_cancel_left]
  · omega

/-! ## The headers read only bytes below an offset -/

/-- `r` and `r'` agree below `n`. -/
def AgreeBelow (r r' : Rd) (n : Nat) : Prop := ∀ o < n, r o = r' o

theorem le_congr {r r' : Rd} : ∀ (n o : Nat), (∀ j < n, r (o + j) = r' (o + j)) →
    Elf.le r o n = Elf.le r' o n
  | 0, _, _ => rfl
  | n + 1, o, h => by
    have h0 : r o = r' o := by simpa using h 0 (by omega)
    have ih := le_congr (r := r) (r' := r') n (o + 1) fun j hj => by
      rw [show o + 1 + j = o + (j + 1) by omega]
      exact h (j + 1) (by omega)
    simp only [Elf.le, h0, ih]

theorem mapM_congr_mem {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, List.mapM_cons, h x (.head _), mapM_congr_mem fun y hy => h y (.tail _ hy)]

theorem fields_congr {r r' : Rd} {n o : Nat} {spec : List (Nat × Nat)}
    (hs : ∀ p ∈ spec, o + p.1 + p.2 ≤ n) (h : AgreeBelow r r' n) :
    fields r o spec = fields r' o spec :=
  mapM_congr_mem fun p hp => le_congr _ _ fun j hj => h _ (by have := hs p hp; omega)

theorem ehdr_congr {r r' : Rd} {n : Nat} (hn : 64 ≤ n) (h : AgreeBelow r r' n) :
    ehdr r = ehdr r' := by
  have hs : ∀ p ∈ ehdrSpec, p.1 + p.2 ≤ 64 := by decide
  unfold ehdr
  rw [fields_congr (fun p hp => by have := hs p hp; omega) h]

theorem phdrs_congr {r r' : Rd} {n : Nat} {e : Ehdr} (he : ehdr r = some e) (hn : 64 ≤ n)
    (hp : e.phoff + 56 * e.phnum ≤ n) (h : AgreeBelow r r' n) : phdrs r = phdrs r' := by
  have hs : ∀ p ∈ phdrSpec, p.1 + p.2 ≤ 56 := by decide
  unfold phdrs
  rw [← ehdr_congr hn h, he, Option.bind_some, Option.bind_some]
  congr 1
  refine mapM_congr_mem fun i hi => fields_congr (fun p hq => ?_) h
  have := hs p hq
  have := List.mem_range.1 hi
  omega

/-! ## The outside part's facts -/

/-- `regionOkB`, unfolded. -/
theorem regionOkB_spec {file : ByteArray} {R n off : Nat} (h : regionOkB file R n off = true) :
    ∃ e phs p, ehdr (fileRd file) = some e ∧ phdrs (fileRd file) = some phs ∧ 64 ≤ off ∧
      e.phoff + 56 * e.phnum ≤ off ∧ off + n ≤ file.size ∧ segIn phs R = some p ∧
      notW p = true ∧ R + n ≤ p.vaddr + p.filesz ∧ p.filesz ≤ p.memsz ∧
      off = p.offset + (R - p.vaddr) ∧
      ∀ q ∈ phs, q = p ∨ q.type ≠ 1 ∨ q.vaddr + q.memsz ≤ R ∨ R + n ≤ q.vaddr := by
  unfold regionOkB at h
  dsimp only at h
  split at h
  · rename_i e phs he hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h⟩ := h
    split at h
    · rename_i p hs
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
        beq_iff_eq, bne_iff_ne, ne_eq] at h
      obtain ⟨⟨⟨⟨h4, h5⟩, h6⟩, h7⟩, h8⟩ := h
      exact ⟨e, phs, p, he, hp, h1, h2, h3, hs, h4, h5, h6, h7, fun q hq => by
        rcases h8 q hq with ((h | h) | h) | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inl h))
        · exact .inr (.inr (.inr h))⟩
    · cases h
  · cases h

section Region

variable {file0 : ByteArray} {R off : Nat} {b : ByteArray}

theorem agreeBelow_patch : AgreeBelow (fileRd (patch file0 off b)) (fileRd file0) off :=
  fun _ ho => fileRd_patch_lt ho

theorem ehdr_patch (hok : regionOkB file0 R b.size off = true) :
    ehdr (fileRd (patch file0 off b)) = ehdr (fileRd file0) := by
  obtain ⟨e, phs, p, he, hp, h1, -⟩ := regionOkB_spec hok
  exact ehdr_congr h1 agreeBelow_patch

theorem phdrs_patch (hok : regionOkB file0 R b.size off = true) :
    phdrs (fileRd (patch file0 off b)) = phdrs (fileRd file0) := by
  obtain ⟨e, phs, p, he, hp, h1, h2, -⟩ := regionOkB_spec hok
  rw [← ehdr_patch hok] at he
  exact phdrs_congr he h1 h2 agreeBelow_patch

theorem static_patch (hok : regionOkB file0 R b.size off = true) (hs : Static file0) :
    Static (patch file0 off b) := by
  obtain ⟨e, phs, he, hp, h⟩ := hs
  exact ⟨e, phs, (ehdr_patch hok).trans he, (phdrs_patch hok).trans hp, h⟩

theorem tpOff_patch (hok : regionOkB file0 R b.size off = true) {phs : List Phdr}
    (hph : phdrs (fileRd file0) = some phs) (v : Nat) :
    TpOff (patch file0 off b) v = tpOff phs v := by
  simp [TpOff, phdrs_patch hok, hph]

/-- Every address of the region is in the region's segment. -/
theorem segIn_region {phs : List Phdr} {p : Phdr} {R n : Nat} (hs : segIn phs R = some p)
    (hend : R + n ≤ p.vaddr + p.filesz) (hfm : p.filesz ≤ p.memsz)
    (hq : ∀ q ∈ phs, q = p ∨ q.type ≠ 1 ∨ q.vaddr + q.memsz ≤ R ∨ R + n ≤ q.vaddr)
    {a : Nat} (ha1 : R ≤ a) (ha2 : a < R + n) : segIn phs a = some p := by
  have hp := List.mem_of_find?_eq_some hs
  have hl := List.find?_some hs
  simp only [isLoad, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hl
  unfold segIn
  cases hf : phs.find? (isLoad a) with
  | none =>
    have := List.find?_eq_none.1 hf p hp
    simp only [isLoad, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact absurd ⟨⟨hl.1.1, by omega⟩, by omega⟩ this
  | some q =>
    have hq1 := List.mem_of_find?_eq_some hf
    have hq2 := List.find?_some hf
    simp only [isLoad, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hq2
    rcases hq q hq1 with h | h | h | h
    · rw [h]
    · exact absurd hq2.1.1 h
    · omega
    · omega

/-- **The loaded byte at `R + j` of the patched file is `b[j]`.** -/
theorem loadMem_patch (hok : regionOkB file0 R b.size off = true) (hR : R + b.size ≤ 2 ^ 64)
    {j : Nat} (hj : j < b.size) :
    loadMem (patch file0 off b) (BitVec.ofNat 64 (R + j)) = b[j]?.map (·.toBitVec) := by
  obtain ⟨e, phs, p, he, hp, h1, h2, h3, hs, h4, h5, h6, h7, h8⟩ := regionOkB_spec hok
  have hseg := segIn_region hs h5 h6 h8 (a := R + j) (by omega) (by omega)
  have hR' := List.find?_some hs
  simp only [isLoad, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hR'
  simp only [loadMem, phdrs_patch hok, hp, Option.bind_some, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show R + j < 2 ^ 64 by omega), loadIn, hseg]
  simp only [show R + j - p.vaddr < p.filesz by omega, ↓reduceIte,
    show p.offset + (R + j - p.vaddr) = off + j by omega]
  exact fileRd_patch_in hj h3

/-- **The region is read-only in the patched file.** -/
theorem ro_patch (hok : regionOkB file0 R b.size off = true) (hR : R + b.size ≤ 2 ^ 64)
    {j : Nat} (hj : j < b.size) : Elf.ro (patch file0 off b) (BitVec.ofNat 64 (R + j)) := by
  obtain ⟨e, phs, p, he, hp, h1, h2, h3, hs, h4, h5, h6, h7, h8⟩ := regionOkB_spec hok
  refine ⟨phs, p, (phdrs_patch hok).trans hp, ?_, h4⟩
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact segIn_region hs h5 h6 h8 (by omega) (by omega)

end Region

/-! ## Words as bytes -/

/-- Four little-endian bytes in memory are the word. -/
theorem rmb_wordBytes {t : Arm.ArmState} {x : BitVec 64} {w : BitVec 32}
    (h : ∀ i < 4, some (t.mem (x + BitVec.ofNat 64 i)) = (wordBytes w)[i]?.map (·.toBitVec)) :
    Arm.read_mem_bytes 4 x t = w := by
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  simp only [wordBytes, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some,
    Option.some.injEq, BitVec.add_zero] at h0 h1 h2 h3
  have e2 : x + 1#64 + 1#64 = x + 2#64 := by rw [BitVec.add_assoc]; rfl
  have e3 : x + 2#64 + 1#64 = x + 3#64 := by rw [BitVec.add_assoc]; rfl
  have hor : ∀ a n : Nat, a <<< 8 ||| n % 2 ^ 8 = a * 256 + n % 2 ^ 8 := fun a n => by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by omega)), Nat.shiftLeft_eq]
  simp only [Arm.read_mem_bytes, Arm.read_mem, Arm.read_store, e2, e3, h0, h1, h2, h3]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_cast, BitVec.toNat_append, UInt8.toNat_toBitVec, UInt8.toNat_ofNat',
    Nat.shiftRight_eq_div_pow, hor, BitVec.toNat_ofNat]
  have := w.isLt
  omega

/-- **`readN` of a word's little-endian bytes is the word.** -/
theorem readN_wordBytes {m : PMem} {x : BitVec 64} {w : BitVec 32}
    (h : ∀ i < 4, m (x + BitVec.ofNat 64 i) = (wordBytes w)[i]?.map (·.toBitVec)) :
    readN m 4 x = some w := by
  have hb : ∀ i < 4, ∃ v, m (x + BitVec.ofNat 64 i) = some v := fun i hi => by
    rw [h i hi]
    have : i < (wordBytes w).length := by simp [wordBytes]; omega
    exact ⟨_, by rw [List.getElem?_eq_getElem this]; rfl⟩
  have hall : (List.range 4).all (fun i => (m (x + BitVec.ofNat 64 i)).isSome) = true :=
    List.all_eq_true.2 fun i hi => by obtain ⟨v, hv⟩ := hb i (List.mem_range.1 hi); simp [hv]
  unfold readN
  simp only [hall, ↓reduceIte]
  congr 1
  refine rmb_wordBytes fun i hi => ?_
  obtain ⟨v, hv⟩ := hb i hi
  simp only [stOf, mem_setMem, hv, Option.getD_some]
  rw [← hv, h i hi]

/-! ## The region's bytes -/

theorem getElem?_flatMap {α β : Type} {f : α → List β} :
    ∀ (l : List α) (j m : Nat) (x : α), l[j]? = some x → m < (f x).length →
      (l.flatMap f)[((l.take j).map fun y => (f y).length).sum + m]? = (f x)[m]?
  | [], _, _, _, h, _ => by simp at h
  | y :: l, 0, m, x, h, hm => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatMap_cons]
    exact List.getElem?_append_left hm
  | y :: l, j + 1, m, x, h, hm => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatMap_cons]
    rw [Nat.add_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    exact getElem?_flatMap l j m x h hm

theorem sum_map_const {α : Type} {f : α → Nat} {c : Nat} :
    ∀ {l : List α}, (∀ x ∈ l, f x = c) → (l.map f).sum = c * l.length
  | [], _ => by simp
  | x :: l, h => by
    rw [List.map_cons, List.sum_cons, h x (.head _), sum_map_const fun y hy => h y (.tail _ hy),
      List.length_cons, Nat.mul_succ]
    omega

theorem wordBytes_length (w : BitVec 32) : (wordBytes w).length = 4 := rfl

theorem artImage_length (I : LinkInput) (tp : Nat → Option Nat) (a : Art) :
    (artImage I tp a).length = 4 * a.fb.words.size + 4 := by
  simp only [artImage, List.length_append, List.length_flatMap, List.length_cons, List.length_nil]
  rw [sum_map_const fun _ _ => wordBytes_length _, List.length_range]

/-- Word `k` of `a` in its image. -/
theorem artImage_getElem? (I : LinkInput) (tp : Nat → Option Nat) (a : Art) {k i : Nat}
    (hk : k < a.fb.words.size) (hi : i < 4) :
    (artImage I tp a)[4 * k + i]? = (wordBytes (resolveWord I tp a k))[i]? := by
  have hfl : ((List.range a.fb.words.size).flatMap
      fun k => wordBytes (resolveWord I tp a k)).length = 4 * a.fb.words.size := by
    rw [List.length_flatMap, sum_map_const fun _ _ => wordBytes_length _, List.length_range]
  unfold artImage
  rw [List.getElem?_append_left (by rw [hfl]; omega)]
  have := getElem?_flatMap (f := fun k => wordBytes (resolveWord I tp a k)) (List.range a.fb.words.size)
    k i k (by simp [hk]) (by rw [wordBytes_length]; exact hi)
  rwa [sum_map_const fun _ _ => wordBytes_length _, List.length_take, List.length_range,
    Nat.min_eq_left (by omega)] at this

theorem regionBytes_length (I : LinkInput) (tp : Nat → Option Nat) (T : List Art) :
    (regionBytes I tp T).length = span (T.map (·.fb.words.size)) := by
  simp only [regionBytes, List.length_flatMap, span, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  simp [artImage_length]

/-- **Function `j`'s image in the region**, from the span of the functions before it. -/
theorem regionBytes_getElem? (I : LinkInput) (tp : Nat → Option Nat) {T : List Art} {j : Nat}
    {a : Art} (ha : T[j]? = some a) {m : Nat} (hm : m < (artImage I tp a).length) :
    (regionBytes I tp T)[span ((T.map (·.fb.words.size)).take j) + m]? = (artImage I tp a)[m]? := by
  have := getElem?_flatMap (f := artImage I tp) T j m a ha hm
  rw [show ((T.take j).map fun y => (artImage I tp y).length).sum =
      span ((T.map (·.fb.words.size)).take j) by
    simp only [span, ← List.map_take, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    simp [artImage_length]] at this
  exact this

/-! ## The placed functions -/

/-- **A placed function is in the patched file**: the region `B` (the `regionBytes` of the
placed functions `T`) written at `off` over the outside part's placeholder (`regionOkB`), the
function `j` at `R` plus its offset, its relocations passing the checks. -/
theorem artOk_region {I : LinkInput} {file0 : ByteArray} {phs : List Phdr}
    (hph : phdrs (fileRd file0) = some phs) {R off : Nat} {T : List Art}
    (hok : regionOkB file0 R (ByteArray.mk (regionBytes I (tpOff phs) T).toArray).size off = true)
    (hR : R + span (T.map (·.fb.words.size)) ≤ 2 ^ 64)
    {j : Nat} {a : Art} (ha : T[j]? = some a) (hv : relocsOkB I (tpOff phs) a = true)
    (hbase : a.base = BitVec.ofNat 64 (R + (offs (T.map (·.fb.words.size)) 0)[j]!)) :
    ArtOk I (patch file0 off (ByteArray.mk (regionBytes I (tpOff phs) T).toArray)) a := by
  have hj : j < T.length := (List.getElem?_eq_some_iff.1 ha).1
  have hBs : (ByteArray.mk (regionBytes I (tpOff phs) T).toArray).size =
      span (T.map (·.fb.words.size)) := by
    show (regionBytes I (tpOff phs) T).toArray.size = _
    rw [List.size_toArray, regionBytes_length]
  rw [offs_getElem! (by simpa using hj), Nat.zero_add] at hbase
  -- the byte at `4k + i` of `a` is the region's byte at its offset plus `4k + i`
  have hbyte : ∀ k < a.fb.words.size, ∀ i < 4,
      ∃ jb, jb < (ByteArray.mk (regionBytes I (tpOff phs) T).toArray).size ∧
        wAt a (4 * k + i) = BitVec.ofNat 64 (R + jb) ∧
        (ByteArray.mk (regionBytes I (tpOff phs) T).toArray)[jb]? =
          (wordBytes (resolveWord I (tpOff phs) a k))[i]? := by
    intro k hk i hi
    have hm : 4 * k + i < (artImage I (tpOff phs) a).length := by
      rw [artImage_length]; omega
    have hr := regionBytes_getElem? I (tpOff phs) ha hm
    rw [artImage_getElem? I (tpOff phs) a hk hi] at hr
    have hw4 : (wordBytes (resolveWord I (tpOff phs) a k))[i]? =
        some (wordBytes (resolveWord I (tpOff phs) a k))[i] :=
      List.getElem?_eq_getElem (by rw [wordBytes_length]; exact hi)
    have hlt : span ((T.map (·.fb.words.size)).take j) + (4 * k + i) <
        (regionBytes I (tpOff phs) T).length :=
      (List.getElem?_eq_some_iff.1 (hr.trans hw4)).1
    refine ⟨_, by rw [hBs, ← regionBytes_length]; exact hlt, ?_, ?_⟩
    · rw [wAt, hbase, ← BitVec.ofNat_add, Nat.add_assoc]
    · rw [byteArray_getElem?]
      show (regionBytes I (tpOff phs) T).toArray[_]? = _
      rw [List.getElem?_toArray, hr]
  refine artOk_of_image (hv) (tpOff_patch hok hph) (fun k hk i hi => ?_) (fun k hk => ?_)
  · obtain ⟨jb, hjb, hw, -⟩ := hbyte k hk i hi
    rw [hw]
    exact ro_patch hok (by rw [hBs]; exact hR) hjb
  · refine readN_wordBytes fun i hi => ?_
    obtain ⟨jb, hjb, hw, hb⟩ := hbyte k hk i hi
    rw [show wAt a (4 * k) + BitVec.ofNat 64 i = wAt a (4 * k + i) by
      rw [wAt, wAt, BitVec.add_assoc, BitVec.ofNat_add], hw,
      loadMem_patch hok (by rw [hBs]; exact hR) hjb, hb]

end Link
