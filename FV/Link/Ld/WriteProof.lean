import FV.Link.Ld.Write

/-! # The ELF writer's output read back (L2b stage 3b)

`Img.write` puts the ELF header and the program headers over the start of the padded body and
appends the symbol and string tables and the section headers. Read back with the reader of the
binary theorems (`FV/E2E/Elf.lean`):

* `ehdr_write`, `phdrs_write`: the header fields and every program header, when the values fit
  their fields (`Img.hdrFitsB`) and the body holds the headers' bytes;
* `fileRd_write_body`: past the headers, the file's bytes in the body are the body's.
-/

namespace Link.Ld

open E2E.Elf

/-! ## Bytes -/

theorem byteArray_getElem? (file : ByteArray) (i : Nat) : file[i]? = file.data[i]? := by
  by_cases h : i < file.size
  · rw [getElem?_pos file i h, getElem?_pos file.data i h]; rfl
  · rw [getElem?_neg file i h, getElem?_neg file.data i h]

theorem byteArray_getElem?_mk (l : List UInt8) (i : Nat) :
    (⟨l.toArray⟩ : ByteArray)[i]? = l[i]? := by
  show (ByteArray.mk l.toArray).data[i]? = _
  simp

theorem size_mk (l : List UInt8) : (⟨l.toArray⟩ : ByteArray).size = l.length := by
  show l.toArray.size = _; simp

theorem leByte_toBitVec (v j : Nat) : (leByte v j).toBitVec = BitVec.ofNat 8 (v >>> (8 * j)) :=
  UInt8.toBitVec_ofNat' _

/-- **Reading a little-endian field.** -/
theorem le_of_bytes {r : Rd} : ∀ {n o v : Nat}, v < 2 ^ (8 * n) →
    (∀ j < n, r (o + j) = some (BitVec.ofNat 8 (v >>> (8 * j)))) → le r o n = some v
  | 0, _, v, hv, _ => by simp at hv; subst hv; rfl
  | n + 1, o, v, hv, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero, Nat.mul_zero, Nat.shiftRight_zero] at h0
    have ih := le_of_bytes (n := n) (o := o + 1) (v := v / 256) (by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        calc v < 2 ^ (8 * (n + 1)) := hv
          _ = 2 ^ (8 * n) * 256 := by rw [Nat.mul_succ, Nat.pow_add])
      (fun j hj => by
        have := h (j + 1) (by omega)
        rw [show o + (j + 1) = o + 1 + j by omega,
          show 8 * (j + 1) = 8 + 8 * j by omega, Nat.shiftRight_add,
          Nat.shiftRight_eq_div_pow v 8] at this
        exact this)
    simp only [le, h0, Option.bind_some, ih, Option.map_some, BitVec.toNat_ofNat]
    congr 1
    omega

/-! ## Records -/

/-- Fields that do not overlap. -/
def Disj (fs : List (Nat × Nat × Nat)) : Prop :=
  fs.Pairwise fun f g => f.1 + f.2.1 ≤ g.1 ∨ g.1 + g.2.1 ≤ f.1

theorem record_length (size : Nat) (fs : List (Nat × Nat × Nat)) : (record size fs).length = size := by
  simp [record]

theorem find?_field {fs : List (Nat × Nat × Nat)} (hd : Disj fs) {f : Nat × Nat × Nat} (hf : f ∈ fs)
    {i : Nat} (hi : f.1 ≤ i ∧ i < f.1 + f.2.1) :
    fs.find? (fun g => decide (g.1 ≤ i ∧ i < g.1 + g.2.1)) = some f := by
  induction fs with
  | nil => cases hf
  | cons g fs ih =>
    unfold Disj at hd
    rw [List.pairwise_cons] at hd
    rcases List.mem_cons.1 hf with rfl | hf
    · simp [List.find?_cons, hi]
    · have hg : ¬ (g.1 ≤ i ∧ i < g.1 + g.2.1) := by
        have := hd.1 f hf; omega
      simp only [List.find?_cons, hg, decide_false]
      exact ih hd.2 hf

/-- **A field's bytes in its record.** -/
theorem record_getElem? {size : Nat} {fs : List (Nat × Nat × Nat)} (hd : Disj fs) {o n v : Nat}
    (hf : (o, n, v) ∈ fs) (hs : o + n ≤ size) {j : Nat} (hj : j < n) :
    (record size fs)[o + j]? = some (leByte v j) := by
  have := find?_field hd hf (i := o + j) (by simp; omega)
  simp only [record, List.getElem?_map, List.getElem?_range (show o + j < size by omega),
    Option.map_some, this]
  congr 2; omega

/-- A list of records of size `m` read at `m * k + j`. -/
theorem flatMap_fixed {α : Type} {g : α → List UInt8} {m : Nat} (hg : ∀ x, (g x).length = m) :
    ∀ {l : List α} {k j : Nat} (x : α), l[k]? = some x → j < m →
      (l.flatMap g)[m * k + j]? = (g x)[j]?
  | [], _, _, _, h, _ => by simp at h
  | y :: l, 0, j, x, h, hj => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    simp [List.getElem?_append_left (show j < (g y).length by rw [hg]; exact hj)]
  | y :: l, k + 1, j, x, h, hj => by
    simp only [List.getElem?_cons_succ] at h
    rw [Nat.mul_succ, List.flatMap_cons, List.getElem?_append_right (by rw [hg]; omega), hg,
      show m * k + m + j - m = m * k + j by omega]
    exact flatMap_fixed hg x h hj

theorem flatMap_length_fixed {α : Type} {g : α → List UInt8} {m : Nat} (hg : ∀ x, (g x).length = m)
    (l : List α) : (l.flatMap g).length = m * l.length := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.flatMap_cons, List.length_append, hg, ih, List.length_cons, Nat.mul_succ]; omega

/-- `mapM` over consecutive indices of a list's entries. -/
theorem mapM_range' {α β : Type} {f : Nat → Option β} {g : α → β} :
    ∀ {l : List α} {s : Nat}, (∀ k x, l[k]? = some x → f (s + k) = some (g x)) →
      (List.range' s l.length).mapM f = some (l.map g)
  | [], _, _ => rfl
  | x :: l, s, h => by
    rw [List.length_cons, List.range'_succ, List.mapM_cons, show f s = some (g x) by
      simpa using h 0 x rfl]
    rw [mapM_range' (l := l) (s := s + 1) fun k y hk => by
      rw [show s + 1 + k = s + (k + 1) by omega]; exact h (k + 1) y (by simpa using hk)]
    rfl

/-! ## The written file -/

theorem pad8_size (b : ByteArray) : (pad8 b).size = b.size + (8 - b.size % 8) % 8 := by
  simp only [pad8, ByteArray.size_append]
  show _ + (Array.replicate _ _).size = _
  rw [Array.size_replicate]

theorem pad8_getElem? (b : ByteArray) {i : Nat} (h : i < b.size) : (pad8 b)[i]? = b[i]? := by
  unfold pad8
  rw [byteArray_getElem?, byteArray_getElem?, ByteArray.data_append, Array.getElem?_append_left h]

theorem overStart_size (f b : ByteArray) : (overStart f b).size = f.size :=
  show (Array.ofFn _).size = _ from Array.size_ofFn

theorem overStart_getElem? (f b : ByteArray) (i : Nat) :
    (overStart f b)[i]? = if i < b.size ∧ i < f.size then b[i]? else f[i]? := by
  rw [byteArray_getElem?, byteArray_getElem?, byteArray_getElem?]
  simp only [overStart, Array.getElem?_ofFn]
  by_cases hi : i < f.size
  · by_cases hb : i < b.size
    · simp [hi, hb]; rfl
    · simp [hi, hb]; rfl
  · simp [hi]

theorem write_size (img : Img) : img.write.size = (pad8 img.body).size + img.tail.length := by
  simp [Img.write, overStart_size, ByteArray.size_append, size_mk]

theorem hdr_length (img : Img) : img.hdr.length = 64 + 56 * img.phs.length := by
  simp only [Img.hdr, List.length_append, record_length]
  rw [flatMap_length_fixed (m := 56) (fun _ => record_length _ _)]

/-- **The file's bytes in the headers' range** are the headers'. -/
theorem write_getElem?_hdr (img : Img) {i : Nat} (hi : i < img.hdr.length)
    (hb : img.hdr.length ≤ img.body.size) : img.write[i]? = img.hdr[i]? := by
  unfold Img.write
  rw [overStart_getElem?, size_mk, if_pos ⟨hi, by rw [ByteArray.size_append, pad8_size]; omega⟩,
    byteArray_getElem?_mk]

/-- **The file's bytes past the headers** are the body's. -/
theorem write_getElem?_body (img : Img) {i : Nat} (hi : img.hdr.length ≤ i)
    (hb : i < img.body.size) : img.write[i]? = img.body[i]? := by
  unfold Img.write
  rw [overStart_getElem?, size_mk, if_neg (by omega), byteArray_getElem?,
    ByteArray.data_append, Array.getElem?_append_left (by
      show i < (pad8 img.body).size; rw [pad8_size]; omega),
    ← byteArray_getElem?, pad8_getElem? _ hb]

theorem fileRd_write_body (img : Img) {i : Nat} (hi : img.hdr.length ≤ i) (hb : i < img.body.size) :
    fileRd img.write i = fileRd img.body i := by
  simp only [fileRd, write_getElem?_body img hi hb]

/-! ## The ELF header and the program headers -/

theorem disj_ehdr (a b c d e : Nat) : Disj (ehdrFields a b c d e) := by
  simp [Disj, ehdrFields]

theorem disj_phdr (p : Phdr) : Disj (phdrFields p) := by
  simp [Disj, phdrFields]

/-- A field of the headers' first record, read in the file. -/
theorem fileRd_ehdr {img : Img} (hb : img.hdr.length ≤ img.body.size) {o n v : Nat}
    (hf : (o, n, v) ∈ ehdrFields img.entry img.phs.length img.tabs.shoff (img.secs.size + 4)
      (img.secs.size + 3)) (hs : o + n ≤ 64) (hv : v < 2 ^ (8 * n)) :
    le (fileRd img.write) o n = some v := by
  apply le_of_bytes hv
  intro j hj
  have hl := hdr_length img
  simp only [fileRd]
  rw [write_getElem?_hdr img (i := o + j) (by omega) hb, Img.hdr,
    List.getElem?_append_left (by rw [record_length]; omega),
    record_getElem? (disj_ehdr _ _ _ _ _) hf hs hj, Option.map_some, leByte_toBitVec]

/-- **The ELF header read back.** -/
theorem ehdr_write {img : Img} (h : img.hdrFitsB = true) :
    ehdr (fileRd img.write) = some ⟨2, 183, img.entry, 64, img.tabs.shoff, img.phs.length,
      img.secs.size + 4⟩ := by
  simp only [Img.hdrFitsB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨he, hn⟩, hs⟩, hsh⟩, hb⟩, -⟩ := h
  have hb' : img.hdr.length ≤ img.body.size := by rw [hdr_length]; exact hb
  have F : ∀ o n v, (o, n, v) ∈ ehdrFields img.entry img.phs.length img.tabs.shoff
      (img.secs.size + 4) (img.secs.size + 3) → o + n ≤ 64 → v < 2 ^ (8 * n) →
      le (fileRd img.write) o n = some v := fun o n v hf hs hv => fileRd_ehdr hb' hf hs hv
  simp only [ehdr, fields, ehdrSpec, List.mapM_cons, List.mapM_nil, Nat.zero_add]
  rw [F 0 4 0x464c457f (by simp [ehdrFields]) (by omega) (by omega),
    F 4 1 2 (by simp [ehdrFields]) (by omega) (by omega),
    F 5 1 1 (by simp [ehdrFields]) (by omega) (by omega),
    F 16 2 2 (by simp [ehdrFields]) (by omega) (by omega),
    F 18 2 183 (by simp [ehdrFields]) (by omega) (by omega),
    F 24 8 _ (by simp [ehdrFields]) (by omega) he,
    F 32 8 64 (by simp [ehdrFields]) (by omega) (by omega),
    F 40 8 _ (by simp [ehdrFields]) (by omega) hsh,
    F 54 2 56 (by simp [ehdrFields]) (by omega) (by omega),
    F 56 2 _ (by simp [ehdrFields]) (by omega) hn,
    F 58 2 64 (by simp [ehdrFields]) (by omega) (by omega),
    F 60 2 (img.secs.size + 4) (by simp [ehdrFields]) (by omega) (by omega)]
  rfl

/-- A field of program header `k`, read in the file. -/
theorem fileRd_phdr {img : Img} (hb : img.hdr.length ≤ img.body.size) {k : Nat} {p : Phdr}
    (hk : img.phs[k]? = some p) {o n v : Nat} (hf : (o, n, v) ∈ phdrFields p) (hs : o + n ≤ 56)
    (hv : v < 2 ^ (8 * n)) :
    le (fileRd img.write) (64 + 56 * k + o) n = some v := by
  apply le_of_bytes hv
  intro j hj
  have hl := hdr_length img
  have hkl : k < img.phs.length := by
    have := List.getElem?_eq_some_iff.1 hk; exact this.1
  have hi : 64 + 56 * k + o + j < img.hdr.length := by
    rw [hl]
    have : 56 * k + 56 ≤ 56 * img.phs.length := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hkl
    omega
  simp only [fileRd, write_getElem?_hdr img hi hb, Img.hdr]
  rw [List.getElem?_append_right (by rw [record_length]; omega), record_length,
    show 64 + 56 * k + o + j - 64 = 56 * k + (o + j) by omega,
    flatMap_fixed (m := 56) (fun _ => record_length _ _) p hk (by omega),
    record_getElem? (disj_phdr p) hf hs hj]
  simp [leByte_toBitVec]

/-- **The program headers read back.** -/
theorem phdrs_write {img : Img} (h : img.hdrFitsB = true) : phdrs (fileRd img.write) = some img.phs := by
  have he := ehdr_write h
  simp only [Img.hdrFitsB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hb⟩, hp⟩ := h
  have hb' : img.hdr.length ≤ img.body.size := by rw [hdr_length]; exact hb
  simp only [phdrs, he, Option.bind_some]
  have key : ∀ k, k < img.phs.length → ∀ p, img.phs[k]? = some p →
      fields (fileRd img.write) (64 + 56 * k) phdrSpec =
        some [p.type, p.flags, p.offset, p.vaddr, p.filesz, p.memsz, p.align] := by
    intro k _ p hk
    have hpm : p ∈ img.phs := List.mem_of_getElem? hk
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hp p hpm
    have F : ∀ o n v, (o, n, v) ∈ phdrFields p → o + n ≤ 56 → v < 2 ^ (8 * n) →
        le (fileRd img.write) (64 + 56 * k + o) n = some v :=
      fun o n v hf hs hv => fileRd_phdr hb' hk hf hs hv
    simp only [fields, phdrSpec, List.mapM_cons, List.mapM_nil]
    rw [show 64 + 56 * k = 64 + 56 * k + 0 by rfl,
      F 0 4 _ (by simp [phdrFields]) (by omega) h1, F 4 4 _ (by simp [phdrFields]) (by omega) h2,
      F 8 8 _ (by simp [phdrFields]) (by omega) h3, F 16 8 _ (by simp [phdrFields]) (by omega) h4,
      F 32 8 _ (by simp [phdrFields]) (by omega) h5, F 40 8 _ (by simp [phdrFields]) (by omega) h6,
      F 48 8 _ (by simp [phdrFields]) (by omega) h7]
    rfl
  have : (List.range img.phs.length).mapM (fun i => fields (fileRd img.write) (64 + 56 * i) phdrSpec) =
      some (img.phs.map fun p => [p.type, p.flags, p.offset, p.vaddr, p.filesz, p.memsz, p.align]) := by
    rw [List.range_eq_range']
    exact mapM_range' (s := 0) fun k x hk => by
      rw [Nat.zero_add]; exact key k (List.getElem?_eq_some_iff.1 hk).1 x hk
  rw [this]
  simp only [Option.map_some, List.map_map]
  congr 1
  conv => rhs; rw [← List.map_id img.phs]
  exact List.map_congr_left fun p _ => by cases p; rfl

/-! ## Non-vacuity -/

/-- A small image (one segment of 120 bytes: the headers' place) whose headers fit. -/
def tinyImg : Img :=
  { entry := 0x200078, body := ⟨Array.replicate 120 0⟩, secs := #[], syms := #[],
    phs := [{ type := 1, flags := 5, offset := 0, vaddr := 0x200000, filesz := 120, memsz := 120,
              align := 0x10000 }] }

theorem tinyImg_hdrFits : tinyImg.hdrFitsB = true := by decide +kernel

theorem ehdr_write_witness : ehdr (fileRd tinyImg.write) = some ⟨2, 183, 0x200078, 64,
    tinyImg.tabs.shoff, 1, 4⟩ := ehdr_write tinyImg_hdrFits

theorem phdrs_write_witness : phdrs (fileRd tinyImg.write) = some tinyImg.phs :=
  phdrs_write tinyImg_hdrFits

end Link.Ld
