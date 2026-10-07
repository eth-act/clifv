import FV.Link.Reloc

/-! # The resolved words are the relocations' forms (L2b)

`artOk_of_image`: a compiled function `a` whose relocations pass the linker's checks
(`relocsOkB`), whose code bytes are read-only and whose words in the loaded image are its
resolved words (`resolveWord`) satisfies `E2E.BinCheck.ArtOk` — every relocation type's
resolved form is the one `RelocOk` names. `relocsOkB`'s one relocation per offset makes
`relocAt?` find each relocation at its own offset (`relocAt?_of_mem`) and the partner lookups
of `resolveWord` find the partner.
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend

/-- Relocations with distinct offsets are equal when their offsets are. -/
theorem eq_of_nodup_offset : ∀ {l : List Reloc}, (l.map (·.offset)).Nodup →
    ∀ {x y : Reloc}, x ∈ l → y ∈ l → x.offset = y.offset → x = y
  | [], _, _, _, hx, _, _ => by cases hx
  | a :: l, h, x, y, hx, hy, he => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 hx with rfl | hx' <;> rcases List.mem_cons.1 hy with rfl | hy'
    · rfl
    · exact (h.1 (List.mem_map.2 ⟨y, hy', he.symm⟩)).elim
    · exact (h.1 (List.mem_map.2 ⟨x, hx', he⟩)).elim
    · exact eq_of_nodup_offset h.2 hx' hy' he

/-- With one relocation per offset, `relocAt?` finds a relocation at its offset. -/
theorem relocAt?_of_mem {a : Art} (hnd : (a.fb.relocs.map (·.offset)).Nodup) {r : Reloc}
    (hr : r ∈ a.fb.relocs) {o : Nat} (ho : r.offset = o) : relocAt? a o = some r := by
  unfold relocAt?
  cases hf : a.fb.relocs.find? (·.offset == o) with
  | none =>
    have := List.find?_eq_none.1 hf r hr
    simp [ho] at this
  | some r' =>
    have h1 := List.mem_of_find?_eq_some hf
    have h2 := List.find?_some hf
    simp only [beq_iff_eq] at h2
    rw [eq_of_nodup_offset hnd h1 hr (h2.trans ho.symm)]

/-- No relocation at `o`: `relocAt?` finds none. -/
theorem relocAt?_none {a : Art} {o : Nat} (h : ∀ r ∈ a.fb.relocs, r.offset ≠ o) :
    relocAt? a o = none :=
  List.find?_eq_none.2 fun r hr => by simpa using h r hr

theorem words_getElem?_of_lt {a : Art} {k : Nat} (hk : k < a.fb.words.size) :
    a.fb.words[k]? = some (wordOf a k) := by
  simp [wordOf, Array.getElem?_eq_getElem hk]

/-- A relocation of type `t` at `o` (`hasAt`) is the relocation `relocAt?` finds there. -/
theorem relocAt?_of_hasAt {a : Art} (hnd : (a.fb.relocs.map (·.offset)).Nodup) {o : Nat}
    {t : RelocType} (h : hasAt a o t = true) :
    ∃ r ∈ a.fb.relocs, r.offset = o ∧ r.type = t ∧ relocAt? a o = some r := by
  simp only [hasAt, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨r, hr, ho, ht⟩ := h
  exact ⟨r, hr, ho, ht, relocAt?_of_mem hnd hr ho⟩

/-- **The resolved image is the relocated code** (`ArtOk`): the relocations pass the checks,
the code is read-only, and the image's words are the resolved words. -/
theorem artOk_of_image {I : LinkInput} {file : ByteArray} {tp : Nat → Option Nat} {a : Art}
    (hv : relocsOkB I tp a = true) (htp : ∀ v, TpOff file v = tp v)
    (hro : ∀ k < a.fb.words.size, ∀ i < 4, Elf.ro file (wAt a (4 * k + i)))
    (himg : ∀ k < a.fb.words.size,
      readN (loadMem file) 4 (wAt a (4 * k)) = some (resolveWord I tp a k)) :
    ArtOk I file a := by
  simp only [relocsOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hv
  obtain ⟨hnd, hall⟩ := hv
  refine ⟨hro, fun k w hk hno => ?_, fun r hr => ?_⟩
  · have hkl : k < a.fb.words.size := (Array.getElem?_eq_some_iff.1 hk).1
    have hx := himg k hkl
    rw [resolveWord, relocAt?_none hno] at hx
    simp only [wordOf, hk, Option.getD_some] at hx
    exact hx
  · have hok := hall r hr
    have hra := relocAt?_of_mem hnd hr rfl
    obtain ⟨o, ty, sym, add⟩ := r
    simp only [relocOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨ho4, hon⟩, hok⟩ := hok
    simp only at ho4 hon hra
    have hx := himg (o / 4) hon
    rw [show 4 * (o / 4) = o by omega] at hx
    refine ⟨ho4, ?_⟩
    cases ty with
    | call26 =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      rw [resolveWord, show 4 * (o / 4) = o by omega, hra] at hx
      exact ⟨hok.1 ▸ words_getElem?_of_lt hon, hok.2, hx⟩
    | adrGotPage | adrPrelPgHi21 =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.any_eq_true] at hok
      obtain ⟨⟨⟨⟨⟨hrd, h1⟩, hw0⟩, hw1⟩, ⟨r', hr', ⟨⟨ho', ht'⟩, hs'⟩, ha'⟩⟩, hin⟩ := hok
      have hra' := relocAt?_of_mem hnd hr' ho'
      have hx1 := himg (o / 4 + 1) h1
      rw [show 4 * (o / 4 + 1) = o + 4 by omega] at hx1
      simp only [resolveWord, show 4 * (o / 4) = o by omega, hra] at hx
      simp only [resolveWord, show 4 * (o / 4 + 1) = o + 4 by omega, hra', ht', loOf,
        Nat.add_sub_cancel, hra] at hx1
      exact ⟨_, _, _, hrd, hw0 ▸ words_getElem?_of_lt (by omega), hw1 ▸ words_getElem?_of_lt h1,
        ⟨r', hr', ho', ht', hs', ha'⟩, hx, hx1, .adrpAdd hin rfl rfl⟩
    | ld64GotLo12Nc | addAbsLo12Nc =>
      simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
      obtain ⟨r', hr', h1, h2⟩ := hok
      exact ⟨r', hr', h1, h2⟩
    | tlsDescAdrPage21 =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨⟨h3, hA⟩, hB⟩, hC⟩, hD⟩ := hok
      split at hD
      · rename_i v hv
        simp only [decide_eq_true_eq] at hD
        obtain ⟨r1, -, -, ht1, hra1⟩ := relocAt?_of_hasAt hnd hA
        obtain ⟨r2, -, -, ht2, hra2⟩ := relocAt?_of_hasAt hnd hB
        obtain ⟨r3, -, -, ht3, hra3⟩ := relocAt?_of_hasAt hnd hC
        have hx1 := himg (o / 4 + 1) (by omega)
        have hx2 := himg (o / 4 + 2) (by omega)
        have hx3 := himg (o / 4 + 3) (by omega)
        rw [show 4 * (o / 4 + 1) = o + 4 by omega] at hx1
        rw [show 4 * (o / 4 + 2) = o + 8 by omega] at hx2
        rw [show 4 * (o / 4 + 3) = o + 12 by omega] at hx3
        simp only [resolveWord, show 4 * (o / 4) = o by omega, hra, hv, Option.getD_some] at hx
        simp only [resolveWord, show 4 * (o / 4 + 1) = o + 4 by omega, hra1, ht1,
          Nat.add_sub_cancel, hra, hv, Option.getD_some] at hx1
        simp only [resolveWord, show 4 * (o / 4 + 2) = o + 8 by omega, hra2, ht2] at hx2
        simp only [resolveWord, show 4 * (o / 4 + 3) = o + 12 by omega, hra3, ht3] at hx3
        exact ⟨v, (htp _).trans hv, hD, hx, hx1, hx2, hx3⟩
      · cases hD
    | tlsDescLd64Lo12 | tlsDescAddLo12 | tlsDescCall =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨r', hr', ho', ht', -⟩ := relocAt?_of_hasAt hnd hok.1
      exact ⟨r', hr', ht', by have := hok.2; simp only at this ⊢; omega⟩

end Link
