import FV.Link.LayoutFacts
import FV.Link.Image

/-! # The linker's facts by construction (L2b)

`linkerOkB S.input` (`FV/E2E/LinkScopeDefs.lean`), the checks about the addresses of the linked
program, holds for every placement that passes `placeOkB` (the pipeline accepting every
function), without self-call aliases:

* `imgB_of` (any table): aligned code where every address holds one word reads back word by
  word from the image's map (`wordMap_get`, `memOfMap_word`).
* `linkerOkB_place`: consecutive functions separated by a gap word (`offs_sep`), in the region
  `[R, R + size)` (`off_end`, `R + size < 2 ^ 64`): no two words at one address (`imgB`),
  `raStar = R + size` past every function (`raStarB`), every call's return address within the
  caller's words or its gap word, so outside every other function (`raCallB`), distinct nonzero
  placed addresses no outside symbol shares (`symInjB`), the CLIF image's symbols read from the
  link map (`symOkB`).
* `leanLink_linkerOk`: the Lean linker's output satisfies `linkerOkB S.input` (without aliases
  by `linkerOkB_place`, with aliases `leanLink` decides `linkerOkR`).
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

/-- Without aliases, every entry of the compiled table is a placed function's. -/
theorem placed_entry {S : LinkSpec} (hp : S.placeOkB = true)
    (hr : S.input.resultsT.all (·.2.toBool) = true) (hf : S.aliasFns = [])
    {e : Clif.Function × Art} (he : e ∈ tabOf S.input.resultsT) :
    ∃ i < S.funcs.length, (tabOf S.input.resultsT)[i]? = some e ∧
      e.2.base = BitVec.ofNat 64 (S.R + (offs S.sizes 0)[i]!) ∧
      e.2.fb.words.size = S.sizes[i]! ∧ e.1.name = S.names[i]! ∧
      e.2.fa.layout = .ok e.2.fb := by
  obtain ⟨i, hei⟩ := List.mem_iff_getElem?.1 he
  have hil : i < S.funcs.length := by
    have := (List.getElem?_eq_some_iff.1 hei).1
    rwa [tab_length, hf, List.length_nil, Nat.add_zero] at this
  obtain ⟨e', he', hb, hs, hn, hl⟩ := tab_placed hp hr i hil
  rw [hei] at he'
  injection he' with hee
  subst hee
  exact ⟨i, hil, hei, hb, hs, hn, hl⟩

/-- The `i`-th entry of the placement: the `i`-th function at its placed address. -/
theorem progAddrs_getElem {S : LinkSpec} {i : Nat} (h : i < S.progAddrs.length) :
    i < S.funcs.length ∧ S.progAddrs[i] = (S.names[i]!, S.R + (offs S.sizes 0)[i]!) := by
  have hi : i < S.funcs.length := by simpa [progAddrs, offs_length] using h
  refine ⟨hi, ?_⟩
  simp [progAddrs, getElem!_pos S.names i (by simpa using hi),
    getElem!_pos (offs S.sizes 0) i (by simpa [offs_length] using hi)]

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

/-- **The linker's facts by construction**: a placement passing `placeOkB`, the pipeline
accepting every function, no self-call aliases. -/
theorem linkerOkB_place {S : LinkSpec} (hp : S.placeOkB = true)
    (hr : S.input.resultsT.all (·.2.toBool) = true) (hal : S.aliases = []) :
    linkerOkB S.input = true := by
  have hP := placeOk_of hp
  have hf : S.aliasFns = [] := by
    have := hP.aliasFns
    rw [hal, List.map_nil, List.map_eq_nil_iff] at this
    exact this
  have hR := hP.fits
  have hR4 := hP.align
  let T := tabOf S.input.resultsT
  -- the `i`-th function's words and gap word end in the region
  have hend : ∀ i < S.funcs.length, S.R + (offs S.sizes 0)[i]! + 4 * S.sizes[i]! + 4 < 2 ^ 64 :=
    fun i hi => by have := off_end hi; omega
  have hbase : ∀ i < S.funcs.length,
      (BitVec.ofNat 64 (S.R + (offs S.sizes 0)[i]!)).toNat = S.R + (offs S.sizes 0)[i]! :=
    fun i hi => by have := hend i hi; rw [BitVec.toNat_ofNat]; omega
  unfold linkerOkB linkerOkR
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨?img, ?raStar⟩, ?symInj⟩, ?symOk⟩, ?fns⟩
  case img =>
    refine imgB_of (fun e he => ?_) (fun e he e' he' k hk k' hk' hx => ?_)
    · obtain ⟨i, hi, -, hb, -⟩ := placed_entry hp hr hf he
      rw [hb, hbase i hi]
      have := offs_mod4 (ns := S.sizes) (o := 0) rfl (by simpa using hi)
      omega
    · obtain ⟨i, hi, hei, hb, hs, -⟩ := placed_entry hp hr hf he
      obtain ⟨i', hi', hei', hb', hs', -⟩ := placed_entry hp hr hf he'
      have hx' := congrArg BitVec.toNat hx
      rw [hb, hb', toNat_addr (by have := hend i hi; omega),
        toNat_addr (by have := hend i' hi'; omega)] at hx'
      have hii : i = i' := by
        rcases Nat.lt_trichotomy i i' with h | h | h
        · have := off_sep h hi'; omega
        · exact h
        · have := off_sep h hi; omega
      subst hii
      rw [hei, Option.some.injEq] at hei'
      subst hei'
      congr 1
      omega
  case raStar =>
    unfold raStarB
    refine List.all_eq_true.2 fun e he => ?_
    obtain ⟨i, hi, -, hb, hs, -⟩ := placed_entry hp hr hf he
    have := off_end hi
    simp only [LinkCheck.outside, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, hb,
      hbase i hi, hs, input_raStar, BitVec.toNat_ofNat]
    omega
  case symInj =>
    unfold symInjB
    refine List.all_eq_true.2 fun h hh => ?_
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hh
    obtain ⟨i, hi, -, -, -, hn, -⟩ :=
      placed_entry hp hr hf (List.mem_map_of_mem (f := fun e => (e.1, getOk e.2)) he)
    have hn : e.1.name = S.names[i]! := hn
    have hai := hend i hi
    simp only [LinkInput.addrOf, input_addrs, hn, addrs_name hP hi, Option.getD_some,
      Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, List.all_eq_true, Bool.or_eq_true,
      beq_iff_eq]
    refine ⟨⟨by omega, by have := hP.pos; omega⟩, fun x hx => ?_⟩
    unfold LinkSpec.addrs at hx
    rw [List.mem_append, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem hx
      obtain ⟨hi'', hx'⟩ := progAddrs_getElem hi'
      rw [hx']
      by_cases hii : i' = i
      · exact .inl (by rw [hii])
      · refine .inr ?_
        have := hend i' hi''
        rw [Nat.mod_eq_of_lt (by omega)]
        rcases Nat.lt_or_gt_of_ne hii with h | h
        · have := off_sep h hi; omega
        · have := off_sep h hi''; omega
    · simp [LinkSpec.aliasAddrs, hal] at hx
    · have := off_end hi
      rcases hP.outside x hx with h | h <;> exact .inr (by omega)
  case symOk =>
    unfold symOkB
    refine List.all_eq_true.2 fun x hx => ?_
    simp only [input_syms, List.mem_filterMap, Option.map_eq_some_iff] at hx
    obtain ⟨n, -, b, hb, rfl⟩ := hx
    simp [LinkInput.addrOf, hb]
  case fns =>
    intro e he
    obtain ⟨i, hi, -, hb, hs, hn, hl⟩ :=
      placed_entry hp hr hf (List.mem_map_of_mem (f := fun e => (e.1, getOk e.2)) he)
    have hb : (getOk e.2).base = BitVec.ofNat 64 (S.R + (offs S.sizes 0)[i]!) := hb
    have hs : (getOk e.2).fb.words.size = S.sizes[i]! := hs
    have hn : e.1.name = S.names[i]! := hn
    have hl : (getOk e.2).fa.layout = .ok (getOk e.2).fb := hl
    have hai := hend i hi
    simp only [decide_eq_true_eq]
    refine ⟨by rw [hb, hbase i hi, hs]; omega, ?_⟩
    unfold raCallB
    refine List.all_eq_true.2 fun j _ => ?_
    split
    · rename_i l hlj
      cases hc : callLine l
      · rfl
      have hle := call_ret_le hl hlj hc
      rw [hs] at hle
      simp only [Bool.not_true, Bool.false_or]
      refine List.all_eq_true.2 fun e' he' => ?_
      obtain ⟨i', hi', -, hb', hs', hn', -⟩ := placed_entry hp hr hf he'
      by_cases hii : i' = i
      · subst hii
        simp [hn, hn']
      · simp only [Bool.or_eq_true]
        refine .inr ?_
        unfold raOkB
        simp only [Bool.or_eq_true]
        refine .inl ?_
        have hra : ((getOk e.2).base + BitVec.ofNat 64 (lineOffset (getOk e.2).fa.lines.toList j)
            + 4).toNat = S.R + (offs S.sizes 0)[i]! + lineOffset (getOk e.2).fa.lines.toList j
              + 4 := by
          rw [hb, BitVec.toNat_add, toNat_addr (by omega),
            show (4 : BitVec 64).toNat = 4 from rfl]
          omega
        have := hend i' hi'
        simp only [LinkCheck.outside, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, hb',
          hbase i' hi', hs', hra]
        refine ⟨by omega, ?_⟩
        rcases Nat.lt_or_gt_of_ne hii with h | h
        · have := off_sep h hi; exact .inr (by omega)
        · have := off_sep h hi'; exact .inl (by omega)
    · rfl

/-- **The Lean linker's output satisfies the linker's facts**: without self-call aliases by
construction (`linkerOkB_place`), with aliases by `leanLink`'s check of `linkerOkR`. -/
theorem leanLink_linkerOk {S : LinkSpec} {file0 file : ByteArray}
    (h : leanLink S file0 = .ok file) : linkerOkB S.input = true := by
  unfold leanLink at h
  split at h
  · cases h
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
  rename_i hp hr _ _ hl
  have hp : S.placeOkB = true := by simpa using hp
  have hr : S.input.resultsT.all (·.2.toBool) = true := by simpa using hr
  have hl : ¬S.aliases = [] → linkerOkR S.input S.input.resultsT = true := by simpa using hl
  by_cases ha : S.aliases = []
  · exact linkerOkB_place hp hr ha
  · exact hl ha

end Link
