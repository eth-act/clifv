import FV.Link.Ld.PlanProof

/-! # The CLIF data objects in `lean-ld`'s plan (L2b stage 3e, #269)

`dataFastB` (part of `file0OkB`) reads the CLIF data objects `D` back from the executable's bytes
outside the region. On `lean-ld`'s output it follows from a check of the plan and the input
objects (`dataPlanB`), which reads no byte of the output:

* each data object of positive size lies in one segment (writable only if the object is);
* either in a piece (an input section) whose file range keeps its address offset in the
  segment's file bytes and lies outside the region, the piece's relocations patching disjoint
  bytes in increasing order (`relBefore`), and the object's items matching the piece
  (`itemsB`): a byte item is the input byte at its place and no relocation patches it; an
  address item `&n + a` is patched by an `R_AARCH64_ABS64` whose `S + A` is the link map's
  `n + a` (modulo `2 ^ 64`);
* or past the segment's file bytes (`.bss`), all its items zero bytes.

`dataFastB_plan`: on the image `assemble` builds from the plan (the body: `buildBody_piece`, the
relocated bytes: `relocated_out`, `relocated_abs64`), `dataPlanB` gives `dataFastB` on the file
without the region's bytes.
-/

namespace Link.Ld

open E2E E2E.Elf E2E.BinCheck E2E.LinkCheck Link

/-! ## The check -/

/-- `r` patches bytes before `r'`'s. -/
def relBefore (r r' : Rel) : Bool := decide (r.off + relocWidth r.ty ≤ r'.off)

/-- The relocations of `rs` (in order) not ending at or before `k`. -/
def relsFrom (k : Nat) (rs : List Rel) : List Rel :=
  rs.dropWhile fun r => decide (r.off + relocWidth r.ty ≤ k)

/-- **A data object's items in a piece's input bytes `bs` from offset `k`**, `rs` the piece's
relocations not before `k`: a byte item is the input byte, unpatched; an address item is an
`ABS64` at its place with the link map's value. -/
def itemsB (I : LinkInput) (bs : ByteArray) : Nat → List Rel → List Clif.DataItem → Bool
  | _, _, [] => true
  | k, rs, .byte b :: is =>
    let rs' := relsFrom k rs
    (match rs' with
     | [] => true
     | r :: _ => decide (k < r.off)) &&
    bs[k]?.map (·.toBitVec) == some b && itemsB I bs (k + 1) rs' is
  | k, rs, .addr n a :: is =>
    match relsFrom k rs with
    | [] => false
    | r :: rs' => r.off == k && r.ty == 257 &&
        BitVec.ofInt 64 (r.ri.S + r.ri.A) == BitVec.ofInt 64 ((I.addrOf n : Int) + a) &&
        itemsB I bs (k + 8) rs' is

/-- A piece holding `[a, a + len)`: the hint's (the piece starting at `a`), else the first. -/
def pieceFor (pa : Array Piece) (hint : Std.HashMap Nat Nat) (a len : Nat) : Option Piece :=
  let has (p : Piece) : Bool := decide (p.addr ≤ a) && decide (a + len ≤ p.addr + p.bytes.size)
  match hint[a]?.bind (pa[·]?) with
  | some p => if has p then some p else pa.find? has
  | none => pa.find? has

/-- **A CLIF data object in the plan** (`am`: the link map's `addrMap`; `off`, `n`: the region's
file offset and size). -/
def objPlanB (am : Std.HashMap String Nat) (I : LinkInput) (pl : Plan) (pa : Array Piece)
    (hint : Std.HashMap Nat Nat) (off n : Nat) (o : Clif.DataObject) : Bool :=
  match am[o.name]? with
  | none => false
  | some a =>
    let len := (objBytes I o).length
    len == 0 || (decide (a + len < 2 ^ 64) &&
      match pl.segs.find? (fun s => decide (s.vaddr ≤ a) && decide (a + len ≤ s.vaddr + s.memsz)) with
      | none => false
      | some s => (o.writable || notW s.ph) &&
        match pieceFor pa hint a len with
        | some p =>
          let y := p.fo + (a - p.addr)
          decide (p.addr ≤ a) && decide (a + len ≤ p.addr + p.bytes.size) &&
            decide (a + len ≤ s.vaddr + s.filesz) && decide (y = s.offset + (a - s.vaddr)) &&
            (decide (y + len ≤ off) || decide (off + n ≤ y)) && chainB relBefore p.rels &&
            itemsB I p.bytes (a - p.addr) p.rels o.items
        | none => decide (s.vaddr + s.filesz ≤ a) && o.items.all (· == .byte 0))

/-- The index of the first piece of positive size at each address. -/
def pieceHint (pa : Array Piece) : Std.HashMap Nat Nat :=
  (List.range pa.size).foldl (fun m k => match pa[k]? with
    | some p => if p.bytes.size == 0 then m else m.insertIfNew p.addr k
    | none => m) {}

/-- **The data check on the plan**: every CLIF data object of `D` is in the plan (`objPlanB`). -/
def dataPlanB (I : LinkInput) (D : List Clif.DataObject) (pl : Plan) (off n : Nat) : Bool :=
  let pa := pl.pieces.toArray
  D.all (objPlanB (addrMap I.addrs) I pl pa (pieceHint pa) off n)

/-! ## Relocations walked in order -/

theorem dropWhile_split {α : Type} (q : α → Bool) :
    ∀ l : List α, ∃ pre, l = pre ++ l.dropWhile q ∧ ∀ x ∈ pre, q x = true
  | [] => ⟨[], rfl, fun _ h => by cases h⟩
  | x :: l => by
    by_cases hx : q x = true
    · obtain ⟨pre, h1, h2⟩ := dropWhile_split q l
      refine ⟨x :: pre, ?_, fun y hy => ?_⟩
      · rw [List.dropWhile_cons_of_pos hx, List.cons_append, ← h1]
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact hx
        · exact h2 y hy
    · exact ⟨[], by rw [List.dropWhile_cons_of_neg hx]; rfl, fun _ h => by cases h⟩

theorem relsFrom_split {k : Nat} {rels rs : List Rel} {pre : List Rel} (h : rels = pre ++ rs)
    (hp : ∀ r ∈ pre, r.off + relocWidth r.ty ≤ k) :
    ∃ pre', rels = pre' ++ relsFrom k rs ∧ ∀ r ∈ pre', r.off + relocWidth r.ty ≤ k := by
  obtain ⟨mid, h1, h2⟩ := dropWhile_split (fun r => decide (r.off + relocWidth r.ty ≤ k)) rs
  refine ⟨pre ++ mid, ?_, fun r hr => ?_⟩
  · rw [h, List.append_assoc]; exact congrArg (pre ++ ·) h1
  · rcases List.mem_append.1 hr with hr | hr
    · exact hp r hr
    · exact of_decide_eq_true (h2 r hr)

theorem relsFrom_head {k : Nat} {rs rs' : List Rel} {r : Rel} (h : relsFrom k rs = r :: rs') :
    k < r.off + relocWidth r.ty := by
  have := List.head_dropWhile_not (fun r => decide (r.off + relocWidth r.ty ≤ k)) (l := rs)
    (by unfold relsFrom at h; rw [h]; simp)
  unfold relsFrom at h
  simp only [h, List.head_cons, decide_eq_false_iff_not] at this
  omega

theorem leByte_ofInt (x : Int) (i : Nat) :
    (leByte (x % 2 ^ 64).toNat i).toBitVec = (BitVec.ofInt 64 x).extractLsb' (8 * i) 8 := by
  rw [leByte_toBitVec]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt]

/-- **The items' bytes are the relocated piece's.** -/
theorem itemsB_sound {I : LinkInput} {p : Piece} {b' : ByteArray} (hb : p.relocated = .ok b')
    (hd : p.rels.Pairwise (fun r r' => relBefore r r' = true)) :
    ∀ (is : List Clif.DataItem) (k : Nat) (rs pre : List Rel), p.rels = pre ++ rs →
      (∀ r ∈ pre, r.off + relocWidth r.ty ≤ k) → itemsB I p.bytes k rs is = true →
      ∀ i (x : BitVec 8), (is.flatMap (itemBytes I))[i]? = some x →
        b'[k + i]?.map (·.toBitVec) = some x
  | [], _, _, _, _, _, _, _, _, hx => by simp at hx
  | .byte b0 :: is, k, rs, pre, hrels, hpre, h, i, x, hx => by
    obtain ⟨pre', hrels', hpre'⟩ := relsFrom_split hrels hpre
    simp only [itemsB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hcov, hbyte⟩, hrest⟩ := h
    rw [List.flatMap_cons] at hx
    simp only [itemBytes, List.cons_append, List.nil_append] at hx
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      rw [Nat.add_zero, relocated_out hb (i := k) fun r hr => ?_]
      · exact hbyte
      · rw [hrels'] at hr
        rcases List.mem_append.1 hr with hr | hr
        · exact .inr (hpre' r hr)
        · revert hcov hr
          cases hrs : relsFrom k rs with
          | nil => intro _ hr; cases hr
          | cons r0 rs0 =>
            intro hcov hr
            simp only [decide_eq_true_eq] at hcov
            rcases List.mem_cons.1 hr with rfl | hr
            · exact .inl hcov
            · rw [hrs] at hrels'
              have hpw := (List.pairwise_append.1 (hrels' ▸ hd)).2.1
              have := List.rel_of_pairwise_cons hpw hr
              simp only [relBefore, decide_eq_true_eq] at this
              exact .inl (by omega)
    | succ i =>
      simp only [List.getElem?_cons_succ] at hx
      rw [show k + (i + 1) = k + 1 + i by omega]
      exact itemsB_sound hb hd is (k + 1) _ pre' hrels' (fun r hr => by have := hpre' r hr; omega)
        hrest i x hx
  | .addr n a :: is, k, rs, pre, hrels, hpre, h, i, x, hx => by
    obtain ⟨pre', hrels', hpre'⟩ := relsFrom_split hrels hpre
    simp only [itemsB] at h
    revert h
    cases hrs : relsFrom k rs with
    | nil => intro h; cases h
    | cons r rs' =>
      intro h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨hoff, hty⟩, hbv⟩, hrest⟩ := h
      rw [hrs] at hrels'
      have hr : r ∈ p.rels := by rw [hrels']; simp
      rw [List.flatMap_cons] at hx
      by_cases hi : i < 8
      · rw [List.getElem?_append_left (by simp [itemBytes]; exact hi)] at hx
        simp only [itemBytes, List.getElem?_map, List.getElem?_range hi, Option.map_some,
          Option.some.injEq] at hx
        subst hx
        have hdj : p.rels.Pairwise RelDisj := hd.imp fun h => by
          simp only [relBefore, decide_eq_true_eq] at h; exact .inl h
        rw [← hoff, relocated_abs64 hb hdj hr hty hi, Option.map_some, leByte_ofInt, hbv]
      · rw [List.getElem?_append_right (by simp [itemBytes]; omega)] at hx
        simp only [itemBytes, List.length_map, List.length_range] at hx
        have hw : relocWidth r.ty = 8 := by rw [hty]; rfl
        rw [show k + i = k + 8 + (i - 8) by omega]
        exact itemsB_sound hb hd is (k + 8) rs' (pre' ++ [r]) (by rw [hrels']; simp)
          (fun r' hr' => by
            rcases List.mem_append.1 hr' with hr' | hr'
            · have := hpre' r' hr'; omega
            · rw [List.mem_singleton.1 hr']; omega)
          hrest (i - 8) x hx

/-! ## The data check gives `dataFastB` -/

theorem body_relocated : ∀ {ps : List Piece} {body body' : ByteArray},
    ps.foldlM bodyStep body = .ok body' → ∀ {p : Piece}, p ∈ ps → ∃ b, p.relocated = .ok b
  | [], _, _, _, _, hp => by cases hp
  | _ :: _, _, _, h, p, hp => by
    obtain ⟨b1, h1, h2⟩ := body_foldlM_cons h
    rcases List.mem_cons.1 hp with rfl | hp
    · obtain ⟨b, hb, -, -⟩ := bodyStep_ok h1
      exact ⟨b, hb⟩
    · exact body_relocated h2 hp

theorem pieceFor_mem {pa : Array Piece} {hint : Std.HashMap Nat Nat} {a len : Nat} {p : Piece}
    (h : pieceFor pa hint a len = some p) : p ∈ pa := by
  unfold pieceFor at h
  dsimp only at h
  split at h
  · split at h
    · rename_i q hq _
      cases h
      obtain ⟨k, -, hk⟩ := Option.bind_eq_some_iff.1 hq
      exact Array.mem_of_getElem? hk
    · exact Array.mem_of_find?_eq_some h
  · exact Array.mem_of_find?_eq_some h

theorem exRd_maskEx {f : ByteArray} {off n i : Nat} (hi : i < f.size) (h : i < off ∨ off + n ≤ i) :
    exRd (maskEx f off n) i = fileRd f i := by
  unfold exRd maskEx
  rcases h with h | h
  · rw [List.find?_cons_of_pos (by simp [ByteArray.size_extract]; omega)]
    simp only [extract_getElem?, Nat.sub_zero, Nat.zero_add, show i < min off f.size by omega,
      ↓reduceIte]
    rfl
  · rw [List.find?_cons_of_neg (by simp [ByteArray.size_extract]; omega),
      List.find?_cons_of_pos (by simp [ByteArray.size_extract]; omega)]
    simp only [extract_getElem?, Nat.min_self, show i - (off + n) < f.size - (off + n) by omega,
      ↓reduceIte, show off + n + (i - (off + n)) = i by omega]
    rfl

theorem zero_items {I : LinkInput} :
    ∀ {is : List Clif.DataItem}, is.all (· == .byte 0) = true → ∀ y ∈ is.flatMap (itemBytes I), y = 0
  | [], _, _, hy => by cases hy
  | it :: is, h, y, hy => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [List.flatMap_cons, itemBytes, List.cons_append, List.nil_append, List.mem_cons] at hy
    rcases hy with rfl | hy
    · rfl
    · exact zero_items h y hy

theorem relBefore_trans {r r' r'' : Rel} (h1 : relBefore r r' = true) (h2 : relBefore r' r'' = true) :
    relBefore r r'' = true := by
  simp only [relBefore, decide_eq_true_eq] at *
  omega

theorem ofNat_add_toNat {a i : Nat} (h : a + i < 2 ^ 64) :
    (BitVec.ofNat 64 a + BitVec.ofNat 64 i).toNat = a + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega),
    Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt h]

/-- **One data object of the plan is in the file without the region's bytes.** -/
theorem objFastB_of_plan {pl : Plan} {img : Img}
    (hp : pl.segs.Pairwise (fun s t => segBefore s t = true))
    (hk : ∀ s ∈ pl.segs, s.kind ≤ 2 ∧ s.filesz ≤ s.memsz ∧ s.offset + s.filesz ≤ pl.size)
    (hdisj : pl.sorted.Pairwise PieceDisj) (hfo : ∀ p ∈ pl.pieces, pl.hdrEnd ≤ p.fo)
    (hbody : buildBody pl.size pl.sorted = .ok img.body) (hbs : img.body.size = pl.size)
    (hhl : img.hdr.length = pl.hdrEnd) (hws : img.body.size ≤ img.write.size)
    {am : Std.HashMap String Nat} {I : LinkInput} {hint : Std.HashMap Nat Nat} {off n : Nat}
    {o : Clif.DataObject} (h : objPlanB am I pl pl.pieces.toArray hint off n o = true) :
    objFastB am I (exRd (maskEx img.write off n)) pl.phdrs o = true := by
  unfold objPlanB at h
  unfold objFastB
  cases ham : am[o.name]? with
  | none => simp only [ham] at h; cases h
  | some a =>
    simp only [ham] at h ⊢
    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]
    intro i hi
    have hil : i < (objBytes I o).length := by simpa using hi
    have hbi : ((objBytes I o).toArray[i]?.getD 0) = (objBytes I o)[i] := by
      rw [List.getElem?_toArray, List.getElem?_eq_getElem hil]; rfl
    rw [hbi]
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h0 | ⟨hlt, h⟩
    · omega
    have hx := ofNat_add_toNat (a := a) (i := i) (by omega)
    revert h
    cases hs : pl.segs.find? (fun s => decide (s.vaddr ≤ a) &&
        decide (a + (objBytes I o).length ≤ s.vaddr + s.memsz)) with
    | none => intro h; cases h
    | some s =>
      intro h
      have hsm := List.mem_of_find?_eq_some hs
      have hsp := List.find?_some hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hsp
      have hseg := segIn_phdrs hp hsm (x := a + i) (by omega) (by omega)
      obtain ⟨-, hfm, hfs⟩ := hk s hsm
      simp only [Bool.and_eq_true, Bool.or_eq_true] at h
      obtain ⟨hro, h⟩ := h
      have hroB : (o.writable = true ∨ roB pl.phdrs (BitVec.ofNat 64 a + BitVec.ofNat 64 i) = true) ∨
          relroB pl.phdrs (BitVec.ofNat 64 a + BitVec.ofNat 64 i) = true := by
        rcases hro with hw | hw
        · exact .inl (.inl hw)
        · refine .inl (.inr ?_)
          simp only [roB, hx, hseg]
          exact hw
      refine ⟨?_, hroB⟩
      unfold loadIn
      rw [hx, hseg]
      revert h
      cases hpf : pieceFor pl.pieces.toArray hint a (objBytes I o).length with
      | some p =>
        intro h
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
        obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
        have hpm : p ∈ pl.pieces := by
          have := pieceFor_mem hpf
          simpa using this
        show (if a + i - s.vaddr < s.filesz then exRd _ (s.offset + (a + i - s.vaddr)) else some 0) = _
        rw [if_pos (by omega)]
        have hy : s.offset + (a + i - s.vaddr) = p.fo + (a - p.addr + i) := by omega
        have hfo' := hfo p hpm
        rw [hy, exRd_maskEx (by omega) (by omega),
          fileRd_write_body img (by omega) (by omega)]
        obtain ⟨b, hb⟩ := body_relocated hbody (mem_sorted.2 hpm)
        have hbsz := relocated_size hb
        have hpiece := buildBody_piece hbody hdisj (mem_sorted.2 hpm) hb (i := a - p.addr + i)
          (by omega)
        have hitem := itemsB_sound (I := I) hb
          (chainB_pairwise (r := relBefore) (fun _ _ _ => relBefore_trans) h6) o.items
          (a - p.addr) p.rels [] rfl (fun _ h => by cases h) h7 i (objBytes I o)[i]
          (List.getElem?_eq_getElem hil)
        simp only [fileRd, hpiece]
        rw [hitem]
      | none =>
        intro h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨h1, h2⟩ := h
        show (if a + i - s.vaddr < s.filesz then exRd _ (s.offset + (a + i - s.vaddr)) else some 0) = _
        rw [if_neg (by omega), zero_items h2 _ (List.getElem_mem hil)]

/-- **The data check of the plan gives `dataFastB`** on the image's file without the region's
bytes (the region's file offset `off` after the headers). -/
theorem dataFastB_plan {pl : Plan} {img : Img} (ha : assemble pl = .ok img)
    (hfit : img.hdrFitsB = true) {I : LinkInput} {D : List Clif.DataObject} {off n : Nat}
    (hoff : pl.hdrEnd ≤ off) (hd : dataPlanB I D pl off n = true) :
    dataFastB I D (maskEx img.write off n) = true := by
  obtain ⟨hok, hbody, hphs, -, -, -⟩ := assemble_ok ha
  obtain ⟨hp, hk, hdisj, hfo⟩ := okB_parts hok
  have hbs := buildBody_size hbody
  have hhl : img.hdr.length = pl.hdrEnd := by rw [hdr_length, hphs, hdrEnd_eq]
  have hws : img.body.size ≤ img.write.size := by rw [write_size, pad8_size]; omega
  have hhb : img.hdr.length ≤ img.body.size := by
    simp only [Img.hdrFitsB, Bool.and_eq_true, decide_eq_true_eq] at hfit
    rw [hdr_length]; exact hfit.1.2
  have hrd : HdrRd img (exRd (maskEx img.write off n)) := fun i hi =>
    exRd_maskEx (by omega) (.inl (by omega))
  unfold dataFastB
  rw [phdrs_rd hfit hrd, hphs]
  exact List.all_eq_true.2 fun o ho =>
    objFastB_of_plan hp hk hdisj hfo hbody hbs hhl hws (List.all_eq_true.1 hd o ho)

end Link.Ld
