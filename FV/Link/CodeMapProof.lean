import FV.Link.LayoutFacts
import FV.E2E.CodeMap

/-! # The code map of an alias-free placement (L1)

`codeMap_place`: without self-call aliases, the code map check `codeMapB` holds on the compiler's
table placed by `leanLink`, by construction — every function's link-map address is its load
address (the placement, `addrs_name`), and two functions' code ranges are disjoint (consecutive
offsets, `off_sep`). With aliases it stays `leanLink`'s check (an alias shares its function's
code, and whether no `blr` enters it depends on the program).
-/

namespace Link

open E2E E2E.LinkCheck Backend LinkSpec

/-- **`codeMapB` of an alias-free placement**, by construction. -/
theorem codeMap_place {S : LinkSpec} (hp : S.placeOkB = true)
    (hr : S.input.resultsT.all (·.2.toBool) = true)
    (hn : S.namesOkB (tabOf S.input.resultsT) = true)
    (hs : S.sizesOkB (tabOf S.input.resultsT) = true) (hal : S.aliasFns = []) :
    codeMapB S.input (tabOf S.input.resultsT) = true := by
  have hP := placeOk_of hp
  have hidx : ∀ e ∈ tabOf S.input.resultsT,
      ∃ i < S.funcs.length, (tabOf S.input.resultsT)[i]? = some e := by
    intro e he
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 he
    have := (List.getElem?_eq_some_iff.1 hi).1
    rw [tab_length, hal] at this
    exact ⟨i, by simpa using this, hi⟩
  have hfit : ∀ i < S.funcs.length, S.R + (offs S.sizes 0)[i]! + 4 * S.sizes[i]! < 2 ^ 64 :=
    fun i hi => by
      have := off_end hP hi
      have := hP.fits
      omega
  simp only [codeMapB, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  intro e he
  obtain ⟨i, hi, hei⟩ := hidx e he
  obtain ⟨e1, h1, hb, hsz, hnm, -⟩ := tab_placed hp hr hn hs i hi
  rw [hei, Option.some.injEq] at h1
  subst h1
  refine ⟨.inl ?_, fun e' he' => ?_⟩
  · simp only [LinkInput.symAddr, LinkInput.addrOf, hnm, input_addrs, addrs_name hP hi,
      Option.getD_some, hb, BitVec.ofInt_ofNat, BitVec.add_zero]
  · obtain ⟨i', hi', hei'⟩ := hidx e' he'
    obtain ⟨e2, h2, hb', hsz', -, -⟩ := tab_placed hp hr hn hs i' hi'
    rw [hei', Option.some.injEq] at h2
    subst h2
    have t1 : e.2.base.toNat = S.R + (offs S.sizes 0)[i]! := by
      rw [hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hfit i hi; omega)]
    have t2 : e'.2.base.toNat = S.R + (offs S.sizes 0)[i']! := by
      rw [hb', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hfit i' hi'; omega)]
    rcases Nat.lt_trichotomy i i' with h | rfl | h
    · have := off_sep hP h hi'
      exact .inl (.inr (.inl (by rw [t1, t2, hsz]; omega)))
    · rw [hei] at hei'
      cases Option.some.inj hei'
      exact .inl (.inl rfl)
    · have := off_sep hP h hi
      exact .inl (.inr (.inr (by rw [t1, t2, hsz']; omega)))

end Link
