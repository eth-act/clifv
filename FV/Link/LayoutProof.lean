import FV.Link.LayoutFacts
import FV.Link.OutsideProof

/-! # The linker's facts by construction (L2b)

`linkerOkB S.input` (`FV/E2E/LinkScopeDefs.lean`), the checks about the addresses of the linked
program, holds for every placement that passes `placeOkB`, the pipeline accepting every
function, the compiled code having the placement's sizes (`sizesOkB`) and every self-call
alias having its function's words and call shape (`aliasShapeB`):

* `imgB_of` (any table): aligned code where every address holds one word reads back word by
  word from the image's map (`wordMap_get`, `memOfMap_word`).
* `tab_home`: every entry of the compiled table is a placed function or its alias, at the
  function's base with its words and call shape (`tab_placed`, `tab_alias`, `aliasShapeB`).
* `linkerOkB_place_alias`: consecutive functions separated by a gap word (`offs_sep`,
  `addr_inj`), in the region `[R, R + size)` (`off_end`, `R + size < 2 ^ 64`): one word at each
  address (`imgB`; an alias's words are its function's), `raStar = R + size` past every
  function (`raStarB`), every call's return address within the caller's words or its gap word,
  so outside every function at another base, and a return into the shared code of a function
  and its alias, at the same call line, not at its entry (`raCallB`); distinct nonzero
  addresses — an alias's is the gap word after its function, which no function starts at
  (`sizes` positive) and no other alias has (one alias per function) — no outside symbol
  shares (`symInjB`); the CLIF image's symbols read from the link map (`symOkB`).
  `linkerOkB_place`: the alias-free corollary.
* `leanLink_linkerOk`: the Lean linker's output satisfies `linkerOkB S.input` (its checks
  `placeOkB`, the pipeline, `sizesOkB`, `aliasShapeB`: `leanLink_spec`).
-/

namespace Link

open E2E E2E.LinkCheck Backend LinkSpec

/-! ## Reading a word back from the image's map -/

theorem natAnd_mask (M : Nat) (h : M < 2 ^ 64) : M &&& (2 ^ 64 - 1 - 3) = 4 * (M / 4) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, show (2 ^ 64 - 1 - 3 : Nat) = (2 ^ 62 - 1) * 2 ^ 2 by decide,
    Nat.testBit_mul_two_pow, Nat.mul_comm, show 4 = 2 ^ 2 by rfl, Nat.testBit_mul_two_pow,
    Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases hj : 2 ≤ j
  · rw [Nat.sub_add_cancel hj]
    by_cases hj' : j < 64
    · simp [hj]; omega
    · rw [Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))]
      simp
  · simp [hj]

/-- An address rounded down to 4 (`memOfMap`'s word address). -/
theorem ofNat_and_not3 (M : Nat) (h : M < 2 ^ 64) :
    BitVec.ofNat 64 M &&& ~~~3#64 = BitVec.ofNat 64 (4 * (M / 4)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact natAnd_mask M h

/-- An address's byte index in its word (`memOfMap`'s byte). -/
theorem toNat_ofNat_and3 (M : Nat) (h : M < 2 ^ 64) :
    (BitVec.ofNat 64 M &&& 3#64).toNat = M % 4 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  exact Nat.and_two_pow_sub_one_eq_mod M 2

/-- Four bytes at `x` that are the bytes of `w` read as `w`. -/
theorem rmb4_of (s : Arm.ArmState) (x : BitVec 64) (w : BitVec 32)
    (h : ∀ i < 4, s.mem (x + BitVec.ofNat 64 i) = w.extractLsb' (8 * i) 8) :
    Arm.read_mem_bytes 4 x s = w := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have e2 : x + 1#64 + 1#64 = x + BitVec.ofNat 64 2 := by rw [BitVec.add_assoc]; rfl
  have e3 : x + BitVec.ofNat 64 2 + 1#64 = x + BitVec.ofNat 64 3 := by
    rw [BitVec.add_assoc]; rfl
  simp only [BitVec.add_zero] at h0
  simp only [Arm.read_mem_bytes, Arm.read_mem, Arm.read_store, e2, e3, h0, h1, h2, h3]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  have hw : ∀ k, k = j → w.getLsbD k = w.getLsbD j := fun _ h => h ▸ rfl
  repeat' split
  all_goals first
    | (rw [decide_eq_true (by omega), Bool.true_and]; exact hw _ (by omega))
    | omega

/-- **The word at an aligned address of the map** reads back from the map's memory. -/
theorem memOfMap_word {m : Std.HashMap (BitVec 64) (BitVec 32)} {x : BitVec 64} {w : BitVec 32}
    (hm : m[x]? = some w) (hx : x.toNat % 4 = 0) :
    Arm.read_mem_bytes 4 x (setMem Arm.ArmState.default (memOfMap m)) = w := by
  apply rmb4_of
  intro i hi
  have hN := x.isLt
  have ex : x = BitVec.ofNat 64 x.toNat := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN]
  have ei : x + BitVec.ofNat 64 i = BitVec.ofNat 64 (x.toNat + i) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  show memOfMap m (x + BitVec.ofNat 64 i) = _
  unfold memOfMap
  rw [ei, ofNat_and_not3 _ (by omega), show 4 * ((x.toNat + i) / 4) = x.toNat by omega, ← ex, hm,
    toNat_ofNat_and3 _ (by omega), show (x.toNat + i) % 4 = i by omega]

/-! ## The image's map -/

theorem foldl_inv {α β : Type _} (P : β → Prop) (f : β → α → β) :
    ∀ (L : List α) (m : β), (∀ x ∈ L, ∀ m, P m → P (f m x)) → P m → P (L.foldl f m)
  | [], _, _, h => h
  | x :: L, m, hs, h =>
    foldl_inv P f L (f m x) (fun y hy => hs y (.tail _ hy)) (hs x (.head _) m h)

theorem foldl_est {α β : Type _} (P : β → Prop) (f : β → α → β) :
    ∀ (L : List α) (m : β) {x0 : α}, x0 ∈ L → (∀ m, P (f m x0)) →
      (∀ x ∈ L, ∀ m, P m → P (f m x)) → P (L.foldl f m)
  | [], _, _, hx, _, _ => absurd hx List.not_mem_nil
  | x :: L, m, x0, hx, h0, hs => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact foldl_inv P f L _ (fun y hy => hs y (.tail _ hy)) (h0 m)
    · exact foldl_est P f L _ hx h0 (fun y hy => hs y (.tail _ hy))

/-- **The image's map at an address**: the word every function with a word there has. -/
theorem wordMap_get {T : List (Clif.Function × Art)} {a : BitVec 64} {w : BitVec 32}
    (hc : ∀ e ∈ T, ∀ k < e.2.fb.words.size,
      e.2.base + BitVec.ofNat 64 (4 * k) = a → e.2.fb.words[k]! = w)
    (hx : ∃ e ∈ T, ∃ k < e.2.fb.words.size, e.2.base + BitVec.ofNat 64 (4 * k) = a) :
    (wordMap T)[a]? = some w := by
  obtain ⟨e0, he0, k0, hk0, hx0⟩ := hx
  let P : Std.HashMap (BitVec 64) (BitVec 32) → Prop := fun m => m[a]? = some w
  have step : ∀ e ∈ T, ∀ k < e.2.fb.words.size, ∀ m, P m →
      P (m.insert (e.2.base + BitVec.ofNat 64 (4 * k)) e.2.fb.words[k]!) := by
    intro e he k hk m hm
    show (m.insert _ _)[a]? = _
    rw [Std.HashMap.getElem?_insert]
    split
    · rename_i hb
      rw [hc e he k hk (beq_iff_eq.1 hb)]
    · exact hm
  unfold wordMap
  refine foldl_est P _ T {} he0 (fun m => ?_) (fun e he m hm => ?_)
  · refine foldl_est P _ _ m (List.mem_range.2 hk0) (fun m => ?_)
      (fun k hk m hm => step e0 he0 k (List.mem_range.1 hk) m hm)
    show (m.insert _ _)[a]? = _
    simp only [Std.HashMap.getElem?_insert, hx0, beq_self_eq_true, ↓reduceIte,
      hc e0 he0 k0 hk0 hx0]
  · exact foldl_inv P _ _ m (fun k hk m hm => step e he k (List.mem_range.1 hk) m hm) hm

/-- **`imgB` of aligned code where every address holds one word.** -/
theorem imgB_of {T : List (Clif.Function × Art)}
    (hal : ∀ e ∈ T, e.2.base.toNat % 4 = 0)
    (hcons : ∀ e ∈ T, ∀ e' ∈ T, ∀ k < e.2.fb.words.size, ∀ k' < e'.2.fb.words.size,
      e.2.base + BitVec.ofNat 64 (4 * k) = e'.2.base + BitVec.ofNat 64 (4 * k') →
      e.2.fb.words[k]! = e'.2.fb.words[k']!) : imgB T = true := by
  unfold imgB
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
  intro e he k hk
  apply memOfMap_word
  · exact wordMap_get (fun e' he' k' hk' hx => hcons e' he' e he k' hk' k hk hx)
      ⟨e, he, k, hk, rfl⟩
  · have := hal e he
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-! ## The placement -/

/-- The sum of a placed address and an offset within the address space. -/
theorem toNat_addr {A c : Nat} (h : A + c < 2 ^ 64) :
    (BitVec.ofNat 64 A + BitVec.ofNat 64 c).toNat = A + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- **An address in a placed function or its gap word** determines the function and the
offset (`offs_sep`). -/
theorem addr_inj {S : LinkSpec} (hP : PlaceOk S) {i i' c c' : Nat} (hi : i < S.funcs.length)
    (hi' : i' < S.funcs.length) (hc : c ≤ 4 * S.sizes[i]!) (hc' : c' ≤ 4 * S.sizes[i']!)
    (h : S.R + (offs S.sizes 0)[i]! + c = S.R + (offs S.sizes 0)[i']! + c') : i = i' ∧ c = c' := by
  rcases Nat.lt_trichotomy i i' with hl | rfl | hl
  · have := off_sep hP hl hi'; omega
  · exact ⟨rfl, by omega⟩
  · have := off_sep hP hl hi; omega

/-- The `i`-th entry of the placement: the `i`-th function at its placed address. -/
theorem progAddrs_getElem {S : LinkSpec} (hP : PlaceOk S) {i : Nat} (h : i < S.progAddrs.length) :
    i < S.funcs.length ∧ S.progAddrs[i] = (S.names[i]!, S.R + (offs S.sizes 0)[i]!) := by
  have hi : i < S.funcs.length := by simpa [progAddrs, offs_length, hP.sizesLen] using h
  refine ⟨hi, ?_⟩
  simp [progAddrs, getElem!_pos S.names i (by simpa using hi),
    getElem!_pos (offs S.sizes 0) i (by simpa [offs_length, hP.sizesLen] using hi)]

/-- The placed address of a call line's return address: within the caller's words and gap
word (a call is an instruction line, a word of the function). -/
theorem call_ret_le {a : Art} (hl : a.fa.layout = .ok a.fb) {j : Nat} {l : Line}
    (hj : a.fa.lines[j]? = some l) (hc : callLine l = true) :
    lineOffset a.fa.lines.toList j + 4 ≤ 4 * a.fb.words.size := by
  obtain ⟨m, hm⟩ := FnAsm.layout_labelOffsets hl
  have hlab : l.isLabel = false := by
    cases l with
    | label _ => simp [callLine] at hc
    | _ => rfl
  obtain ⟨hmod, w, -, hw⟩ := FnAsm.layout_word hl hm (j := j) (by simpa using hj) hlab
  have := (Array.getElem?_eq_some_iff.1 hw).1
  omega

/-- A line's offset is read off the call shape (the lines' sizes). -/
theorem lineOffset_callShape (a : Art) (j : Nat) :
    lineOffset a.fa.lines.toList j = (((callShape a).take j).map (·.2)).sum := by
  simp [lineOffset, callShape, List.map_take, Function.comp_def]

/-- Every entry of the compiled table is a layout (`hr`: the pipeline accepts every function). -/
theorem tab_layout {S : LinkSpec} (hr : S.input.resultsT.all (·.2.toBool) = true)
    {e : Clif.Function × Art} (he : e ∈ tabOf S.input.resultsT) : e.2.fa.layout = .ok e.2.fb := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 he
  have hkl : k < S.funcs.length + S.aliasFns.length := by
    have := (List.getElem?_eq_some_iff.1 hk).1
    rwa [tab_length] at this
  obtain ⟨fi, a, -, ha, ht⟩ := tab_entry hr hkl
  rw [hk, Option.some.injEq] at ht
  subst ht
  exact (pipeT_layout ha).1

/-- **Every entry of the compiled table has a home**: the `i`-th placed function `ef`, whose
base, words and call shape it has — it is `ef` itself or `ef`'s self-call alias
(`tab_alias`, `aliasShapeB`). -/
theorem tab_home {S : LinkSpec} (hp : S.placeOkB = true)
    (hr : S.input.resultsT.all (·.2.toBool) = true)
    (hs : S.sizesOkB (tabOf S.input.resultsT) = true)
    (ha : aliasShapeB S.input (tabOf S.input.resultsT) = true)
    {e : Clif.Function × Art} (he : e ∈ tabOf S.input.resultsT) :
    ∃ i < S.funcs.length, ∃ ef, (tabOf S.input.resultsT)[i]? = some ef ∧
      ef.2.base = BitVec.ofNat 64 (S.R + (offs S.sizes 0)[i]!) ∧
      ef.2.fb.words.size = S.sizes[i]! ∧ ef.1.name = S.names[i]! ∧
      e.2.base = ef.2.base ∧ e.2.fb.words = ef.2.fb.words ∧ callShape e.2 = callShape ef.2 ∧
      (e.1.name = S.names[i]! ∨ (e.1.name, S.names[i]!) ∈ S.aliases) := by
  have hP := placeOk_of hp
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 he
  have hkl : k < S.funcs.length + S.aliasFns.length := by
    have := (List.getElem?_eq_some_iff.1 hk).1
    rwa [tab_length] at this
  by_cases hkn : k < S.funcs.length
  · obtain ⟨ef, hef, hb, hsz, hn, -⟩ := tab_placed hp hr hs k hkn
    rw [hk, Option.some.injEq] at hef
    subst hef
    exact ⟨k, hkn, e, hk, hb, hsz, hn, rfl, rfl, rfl, .inl hn⟩
  · obtain ⟨e', ef, he', ⟨i, hi, hef⟩, hb, hl⟩ :=
      tab_alias hp hr hs (k - S.funcs.length) (by omega)
    rw [show S.funcs.length + (k - S.funcs.length) = k by omega, hk, Option.some.injEq] at he'
    subst he'
    obtain ⟨ef', hef', hbf, hszf, hnf, -⟩ := tab_placed hp hr hs i hi
    rw [hef, Option.some.injEq] at hef'
    subst hef'
    have hq : (e.1.name, ef.1.name) ∈ S.aliases := mem_of_lookup hl
    have hnd := tab_names S hP
    have hsh := List.all_eq_true.1 ha _ hq
    have hfe : (tabOf S.input.resultsT).find? (fun y => y.1.name == e.1.name) = some e :=
      find?_key hnd he
    have hff : (tabOf S.input.resultsT).find? (fun y => y.1.name == ef.1.name) = some ef :=
      find?_key hnd (List.mem_iff_getElem?.2 ⟨i, hef⟩)
    simp only [hfe, hff, Bool.and_eq_true, beq_iff_eq] at hsh
    exact ⟨i, hi, ef, hef, hbf, hszf, hnf, hb, hsh.1, hsh.2, .inr (by rw [← hnf]; exact hq)⟩

/-- **The linker's facts by construction**: a placement passing `placeOkB`, the pipeline
accepting every function, the compiled code of the placement's sizes (`sizesOkB`), each
self-call alias with its function's words and call shape (`aliasShapeB`). -/
theorem linkerOkB_place_alias {S : LinkSpec} (hp : S.placeOkB = true)
    (hr : S.input.resultsT.all (·.2.toBool) = true)
    (hs : S.sizesOkB (tabOf S.input.resultsT) = true)
    (ha : aliasShapeB S.input (tabOf S.input.resultsT) = true) :
    linkerOkB S.input = true := by
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
  have home := fun {e} (he : e ∈ tabOf S.input.resultsT) => tab_home hp hr hs ha he
  unfold linkerOkB linkerOkR
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
      hb, hbase i hi, hsz, input_raStar, BitVec.toNat_ofNat]
    omega
  case symInj =>
    unfold symInjB
    refine List.all_eq_true.2 fun h hh => ?_
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hh
    obtain ⟨i, hi, ef, -, -, -, -, -, -, -, hn⟩ :=
      home (List.mem_map_of_mem (f := fun e => (e.1, getOk e.2)) he)
    have hn : e.1.name = S.names[i]! ∨ (e.1.name, S.names[i]!) ∈ S.aliases := hn
    -- the entry's address: its function's (`c = 0`) or the gap word after it (an alias)
    obtain ⟨c, hc, hA, hcase⟩ : ∃ c, c ≤ 4 * S.sizes[i]! ∧
        S.addrs.lookup e.1.name = some (S.R + (offs S.sizes 0)[i]! + c) ∧
        ((c = 0 ∧ e.1.name = S.names[i]!) ∨
          (c = 4 * S.sizes[i]! ∧ (e.1.name, S.names[i]!) ∈ S.aliases)) := by
      rcases hn with hn | hn
      · exact ⟨0, Nat.zero_le _, by rw [hn, addrs_name hP hi, Nat.add_zero], .inl ⟨rfl, hn⟩⟩
      · exact ⟨4 * S.sizes[i]!, Nat.le_refl _,
          (addrs_alias hP hn).trans (congrArg some (gapIn_name hP hi)), .inr ⟨rfl, hn⟩⟩
    have hAe := hend i hi c hc
    simp only [LinkInput.addrOf, input_addrs, hA, Option.getD_some, Bool.and_eq_true,
      decide_eq_true_eq, bne_iff_ne, ne_eq, List.all_eq_true, Bool.or_eq_true, beq_iff_eq]
    refine ⟨⟨by omega, by omega⟩, fun x hx => ?_⟩
    by_cases hx1 : x.1 = e.1.name
    · exact .inl hx1
    refine .inr fun hxA => hx1 ?_
    unfold LinkSpec.addrs at hx
    rw [List.mem_append, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem hx
      obtain ⟨hi'', hx'⟩ := progAddrs_getElem hP hi'
      rw [hx'] at hxA ⊢
      have := hend i' hi'' 0 (Nat.zero_le _)
      rw [Nat.mod_eq_of_lt (by omega)] at hxA
      obtain ⟨hii, hc0⟩ :=
        addr_inj hP hi'' hi (c := 0) (c' := c) (Nat.zero_le _) hc (by omega)
      rcases hcase with ⟨-, hn⟩ | ⟨hc4, -⟩
      · rw [hii]; exact hn.symm
      · have := sizes_pos hP hi; omega
    · unfold LinkSpec.aliasAddrs at hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      obtain ⟨i', hi', hni'⟩ := alias_mem_index hP hq
      have hg := gapIn_name hP hi'
      rw [hni'] at hg
      dsimp only at hxA ⊢
      rw [hg] at hxA
      have := hend i' hi' (4 * S.sizes[i']!) (Nat.le_refl _)
      rw [Nat.mod_eq_of_lt (by omega)] at hxA
      obtain ⟨hii, hc0⟩ := addr_inj hP hi' hi (Nat.le_refl _) hc hxA
      subst hii
      rcases hcase with ⟨hc0', -⟩ | ⟨-, hn⟩
      · have := sizes_pos hP hi'; omega
      · rw [alias_fn_inj hP hq hn hni'.symm]
    · rcases hP.outside x hx with h | h <;> omega
  case symOk =>
    unfold symOkB
    refine List.all_eq_true.2 fun x hx => ?_
    simp only [input_syms, List.mem_filterMap, Option.map_eq_some_iff] at hx
    obtain ⟨n, -, b, hb, rfl⟩ := hx
    simp [LinkInput.addrOf, hb]
  case fns =>
    intro e he
    have he' : (e.1, getOk e.2) ∈ tabOf S.input.resultsT :=
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
      · -- the same code (a function and its alias): the call returns into it
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

/-- **The linker's facts by construction** without self-call aliases (`aliasShapeB` is then
vacuous). -/
theorem linkerOkB_place {S : LinkSpec} (hp : S.placeOkB = true)
    (hr : S.input.resultsT.all (·.2.toBool) = true)
    (hs : S.sizesOkB (tabOf S.input.resultsT) = true) (hal : S.aliases = []) :
    linkerOkB S.input = true :=
  linkerOkB_place_alias hp hr hs (by simp [aliasShapeB, hal])

/-- **The Lean linker's output satisfies the linker's facts** (`linkerOkB_place_alias`, from
`leanLink`'s checks `placeOkB`, the pipeline, `sizesOkB` and `aliasShapeB`). -/
theorem leanLink_linkerOk {S : LinkSpec} {file0 file : ByteArray}
    (h : leanLink S file0 = .ok file) : linkerOkB S.input = true := by
  obtain ⟨-, -, hp, hr, hs, -, -, ha, -⟩ := leanLink_spec h
  exact linkerOkB_place_alias hp hr hs ha

end Link
