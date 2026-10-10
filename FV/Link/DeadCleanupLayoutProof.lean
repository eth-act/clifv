import FV.Link.DeadCleanupLayoutFacts
import FV.Link.DeadCleanupOutsideProof
import FV.Link.LayoutProof
namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec
theorem tab_layout {S : LinkSpec} (hr : S.inputCleanup.resultsCleanupT.all (·.2.toBool) = true)
    {e : Clif.Function × Art} (he : e ∈ tabOf S.inputCleanup.resultsCleanupT) : e.2.fa.layout = .ok e.2.fb := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 he
  have hkl : k < S.funcs.length := by
    have := (List.getElem?_eq_some_iff.1 hk).1
    rwa [tab_length] at this
  obtain ⟨fi, a, -, ha, ht⟩ := tab_entry hr hkl
  rw [hk, Option.some.injEq] at ht
  subst ht
  exact (pipeT_layout ha).1

/-- **Every entry of the compiled table has a home**: the `i`-th placed function. -/
theorem tab_home {S : LinkSpec} (hp : S.placeOkB = true)
    (hr : S.inputCleanup.resultsCleanupT.all (·.2.toBool) = true)
    (hn : S.namesOkB (tabOf S.inputCleanup.resultsCleanupT) = true)
    (hs : S.sizesOkB (tabOf S.inputCleanup.resultsCleanupT) = true)
    {e : Clif.Function × Art} (he : e ∈ tabOf S.inputCleanup.resultsCleanupT) :
    ∃ i < S.funcs.length, ∃ ef, (tabOf S.inputCleanup.resultsCleanupT)[i]? = some ef ∧
      ef.2.base = BitVec.ofNat 64 (S.R + (offs S.sizes 0)[i]!) ∧
      ef.2.fb.words.size = S.sizes[i]! ∧ ef.1.name = S.names[i]! ∧
      e.2.base = ef.2.base ∧ e.2.fb.words = ef.2.fb.words ∧ callShape e.2 = callShape ef.2 ∧
      e.1.name = S.names[i]! := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 he
  have hkl : k < S.funcs.length := by
    have := (List.getElem?_eq_some_iff.1 hk).1
    rwa [tab_length] at this
  obtain ⟨ef, hef, hb, hsz, hnm, -⟩ := tab_placed hp hr hn hs k hkl
  rw [hk, Option.some.injEq] at hef
  subst hef
  exact ⟨k, hkl, e, hk, hb, hsz, hnm, rfl, rfl, rfl, hnm⟩

/-- **The linker's facts by construction**: a placement passing `placeOkB`, the pipeline
accepting every function, and the compiled code of the placement's sizes (`sizesOkB`). -/
theorem linkerOkB_place {S : LinkSpec} (hp : S.placeOkB = true)
    (hr : S.inputCleanup.resultsCleanupT.all (·.2.toBool) = true)
    (hn : S.namesOkB (tabOf S.inputCleanup.resultsCleanupT) = true)
    (hs : S.sizesOkB (tabOf S.inputCleanup.resultsCleanupT) = true) :
    linkerOkR S.inputCleanup S.inputCleanup.resultsCleanupT = true := by
  have hP := placeOk_of hp
  have hR := hP.fits
  have hR4 := hP.align
  have hpos := hP.pos
  -- every address of the `i`-th function, gap word included, is in the region
  have hend : ∀ i < S.funcs.length, ∀ c ≤ 4 * S.sizes[i]!,
      S.R + (offs S.sizes 0)[i]! + c + 4 ≤ S.R + S.size :=
    fun i hi c hc => by have := off_end hP hi; omega
  have hbase : ∀ i < S.funcs.length,
      (BitVec.ofNat 64 (S.R + (offs S.sizes 0)[i]!)).toNat = S.R + (offs S.sizes 0)[i]! :=
    fun i hi => by have := hend i hi 0 (Nat.zero_le _); rw [BitVec.toNat_ofNat]; omega
  have home := fun {e} (he : e ∈ tabOf S.inputCleanup.resultsCleanupT) => tab_home hp hr hn hs he
  unfold linkerOkR
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨?img, ?raStar⟩, ?symInj⟩, ?symOk⟩, ?fns⟩
  case img =>
    refine imgB_of (fun e he => ?_) (fun e he e' he' k hk k' hk' hx => ?_)
    · obtain ⟨i, hi, ef, -, hb, -, -, heb, -⟩ := home he
      rw [heb, hb, hbase i hi]
      have := offs_mod4 (ns := S.sizes) (o := 0) rfl (by rw [hP.sizesLen]; exact hi)
      omega
    · obtain ⟨i, hi, ef, hef, hb, hsz, -, heb, hw, -⟩ := home he
      obtain ⟨i', hi', ef', hef', hb', hsz', -, heb', hw', -⟩ := home he'
      rw [hw, hsz] at hk
      rw [hw', hsz'] at hk'
      have hx' := congrArg BitVec.toNat hx
      rw [heb, heb', hb, hb', toNat_addr (by have := hend i hi (4 * k) (by omega); omega),
        toNat_addr (by have := hend i' hi' (4 * k') (by omega); omega)] at hx'
      obtain ⟨hii, hkk⟩ :=
        addr_inj hP hi hi' (c := 4 * k) (c' := 4 * k') (by omega) (by omega) (by omega)
      subst hii
      rw [hef, Option.some.injEq] at hef'
      subst hef'
      rw [hw, hw', show k = k' by omega]
  case raStar =>
    unfold raStarB
    refine List.all_eq_true.2 fun e he => ?_
    obtain ⟨i, hi, ef, -, hb, hsz, -, heb, hw, -⟩ := home he
    have := hend i hi (4 * S.sizes[i]!) (Nat.le_refl _)
    simp only [LinkCheck.outside, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, heb, hw,
      hb, hbase i hi, hsz, inputCleanup_raStar, BitVec.toNat_ofNat]
    omega
  case symInj =>
    unfold symInjB
    refine List.all_eq_true.2 fun h hh => ?_
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hh
    obtain ⟨i, hi, ef, -, -, -, -, -, -, -, hn⟩ :=
      home (List.mem_map_of_mem (f := fun e => (e.1, getOk e.2)) he)
    have hn : e.1.name = S.names[i]! := hn
    have hA : S.addrs.lookup e.1.name = some (S.R + (offs S.sizes 0)[i]!) := by
      rw [hn, addrs_name hP hi]
    have hAe := hend i hi 0 (Nat.zero_le _)
    simp only [LinkInput.addrOf, inputCleanup_addrs, hA, Option.getD_some, Bool.and_eq_true,
      decide_eq_true_eq, bne_iff_ne, ne_eq, List.all_eq_true, Bool.or_eq_true, beq_iff_eq]
    refine ⟨⟨by omega, by omega⟩, fun x hx => ?_⟩
    by_cases hx1 : x.1 = e.1.name
    · exact .inl hx1
    refine .inr fun hxA => hx1 ?_
    unfold LinkSpec.addrs at hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem hx
      obtain ⟨hi'', hx'⟩ := progAddrs_getElem hP hi'
      rw [hx'] at hxA ⊢
      have := hend i' hi'' 0 (Nat.zero_le _)
      rw [Nat.mod_eq_of_lt (by omega)] at hxA
      obtain ⟨hii, -⟩ :=
        addr_inj hP hi'' hi (c := 0) (c' := 0) (Nat.zero_le _) (Nat.zero_le _) (by omega)
      rw [hii]
      exact hn.symm
    · rcases hP.outside x hx with h | h <;> omega
  case symOk =>
    unfold symOkB
    refine List.all_eq_true.2 fun x hx => ?_
    simp only [inputCleanup_syms, List.mem_filterMap, Option.map_eq_some_iff] at hx
    obtain ⟨n, -, b, hb, rfl⟩ := hx
    simp [LinkInput.addrOf, hb]
  case fns =>
    intro e he
    have he' : (e.1, getOk e.2) ∈ tabOf S.inputCleanup.resultsCleanupT :=
      List.mem_map_of_mem (f := fun e => (e.1, getOk e.2)) he
    obtain ⟨i, hi, ef, hef, hb, hsz, -, heb, hw, hsh, -⟩ := home he'
    have hl : (getOk e.2).fa.layout = .ok (getOk e.2).fb := tab_layout hr he'
    have heb : (getOk e.2).base = BitVec.ofNat 64 (S.R + (offs S.sizes 0)[i]!) := heb.trans hb
    have hw : (getOk e.2).fb.words = ef.2.fb.words := hw
    have hsz : (getOk e.2).fb.words.size = S.sizes[i]! := by rw [hw, hsz]
    have hsh : callShape (getOk e.2) = callShape ef.2 := hsh
    have hai := hend i hi (4 * S.sizes[i]!) (Nat.le_refl _)
    simp only [decide_eq_true_eq]
    refine ⟨by rw [heb, hbase i hi, hsz]; omega, ?_⟩
    unfold raCallB
    refine List.all_eq_true.2 fun j _ => ?_
    split
    · rename_i l hlj
      cases hc : callLine l
      · rfl
      have hle := call_ret_le hl hlj hc
      rw [hsz] at hle
      simp only [Bool.not_true, Bool.false_or]
      refine List.all_eq_true.2 fun e' he' => ?_
      obtain ⟨i', hi', ef', hef', hb', hsz', -, heb', hw', hsh', -⟩ := home he'
      simp only [Bool.or_eq_true]
      refine .inr ?_
      unfold raOkB
      simp only [Bool.or_eq_true]
      have hra : ((getOk e.2).base + BitVec.ofNat 64 (lineOffset (getOk e.2).fa.lines.toList j)
          + 4).toNat = S.R + (offs S.sizes 0)[i]! + lineOffset (getOk e.2).fa.lines.toList j
            + 4 := by
        rw [heb, BitVec.toNat_add, toNat_addr (by omega),
          show (4 : BitVec 64).toNat = 4 from rfl]
        omega
      by_cases hii : i' = i
      · -- a call returns into its own function, not at its entry
        subst hii
        rw [hef, Option.some.injEq] at hef'
        subst hef'
        refine .inr ?_
        have hcs : callShape e'.2 = callShape (getOk e.2) := hsh'.trans hsh.symm
        have hlj' : (getOk e.2).fa.lines.toList[j]? = some l := by simpa using hlj
        have hm := congrArg (·[j]?) hcs
        simp only [callShape, List.getElem?_map, hlj', Option.map_some] at hm
        obtain ⟨l', hl', hfl⟩ := Option.map_eq_some_iff.1 hm
        simp only [Prod.mk.injEq] at hfl
        have hjl : j < e'.2.fa.lines.toList.length := (List.getElem?_eq_some_iff.1 hl').1
        have hlo : lineOffset e'.2.fa.lines.toList j = lineOffset (getOk e.2).fa.lines.toList j := by
          rw [lineOffset_callShape, lineOffset_callShape, hcs]
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, List.mem_range]
        refine ⟨fun h => ?_, j, hjl, ?_⟩
        · have := congrArg BitVec.toNat h
          rw [hra, heb', hb, hbase i' hi'] at this
          omega
        · rw [hl']
          simp only [Bool.and_eq_true, beq_iff_eq, hfl.1, hc, hlo, heb, heb', hb, and_self]
      · refine .inl ?_
        have := hend i' hi' (4 * S.sizes[i']!) (Nat.le_refl _)
        simp only [LinkCheck.outside, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, heb',
          hb', hw', hsz', hbase i' hi', hra]
        refine ⟨by omega, ?_⟩
        rcases Nat.lt_or_gt_of_ne hii with h | h
        · have := off_sep hP h hi; exact .inr (by omega)
        · have := off_sep hP h hi'; exact .inl (by omega)
    · rfl

/-- **The Lean linker's output satisfies the linker's facts**, from the placement and code
checks (`leanLink_spec`). -/
theorem leanLink_linkerOk {S : LinkSpec} {file0 file : ByteArray}
    (h : leanLink S file0 = .ok file) : linkerOkR S.inputCleanup S.inputCleanup.resultsCleanupT = true := by
  obtain ⟨-, -, hp, hr, hn, hs, -⟩ := leanLink_spec h
  exact linkerOkB_place hp hr hn hs


end Link.DeadCleanup
