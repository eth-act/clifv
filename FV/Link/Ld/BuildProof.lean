module

public import FV.Link.Ld.Build
public import FV.Link.Ld.WriteProof

@[expose] public section

/-! # The body's bytes are the relocated input bytes (L2b stage 3c)

* `place_getElem?`, `writeLE_getElem?`: writing bytes into a byte array;
* `applyRel_out`, `applyRel_abs64`: a relocation changes only the bytes it patches; an
  `R_AARCH64_ABS64` writes the 8 little-endian bytes of `S + A`;
* `relocated_out`, `relocated_abs64`: in a piece whose relocations patch disjoint bytes, a byte
  no relocation patches is the input byte, and an `ABS64`'s bytes are `S + A`'s;
* **`buildBody_piece`**: in the body built from pieces with disjoint file ranges, every
  piece's bytes are its relocated bytes.
-/

namespace Link.Ld

/-! ## Writing bytes -/

theorem place_size {dest b : ByteArray} {o : Nat} (h : o + b.size ≤ dest.size) :
    (place dest o b).size = dest.size := by
  have h' : o + b.data.size ≤ dest.data.size := h
  show (place dest o b).data.size = dest.data.size
  simp only [place, ByteArray.copySlice, Array.size_append, Array.size_extract]
  omega

theorem place_getElem? {dest b : ByteArray} {o : Nat} (h : o + b.size ≤ dest.size) (i : Nat) :
    (place dest o b)[i]? = if o ≤ i ∧ i < o + b.size then b[i - o]? else dest[i]? := by
  have h' : o + b.data.size ≤ dest.data.size := h
  have e1 : b.size = b.data.size := rfl
  rw [byteArray_getElem?, byteArray_getElem?, byteArray_getElem?, e1]
  simp only [place, ByteArray.copySlice]
  simp only [e1]
  by_cases h1 : i < o
  · rw [Array.getElem?_append_left (by simp [Array.size_append]; omega),
      Array.getElem?_append_left (by simp; omega), Array.getElem?_extract]
    rw [if_pos (by omega), if_neg (by omega)]
    simp
  · by_cases h2 : i < o + b.data.size
    · rw [Array.getElem?_append_left (by simp [Array.size_append]; omega),
        Array.getElem?_append_right (by simp; omega), Array.getElem?_extract]
      simp only [Array.size_extract]
      rw [if_pos (by omega), if_pos ⟨by omega, h2⟩]
      congr 1; omega
    · rw [Array.getElem?_append_right (by simp [Array.size_append]; omega), Array.getElem?_extract]
      simp only [Array.size_append, Array.size_extract]
      rw [if_neg (show ¬(o ≤ i ∧ i < o + b.data.size) by omega)]
      by_cases h3 : i < dest.data.size
      · rw [if_pos (by omega)]; congr 1; omega
      · rw [if_neg (by omega), Array.getElem?_eq_none (by omega)]

theorem leBytes_size (n v : Nat) : (leBytes n v).size = n := by
  show ((List.range n).map (leByte v)).toArray.size = n
  simp

theorem leBytes_getElem? {n v j : Nat} (hj : j < n) : (leBytes n v)[j]? = some (leByte v j) := by
  rw [byteArray_getElem?]
  show ((List.range n).map (leByte v)).toArray[j]? = _
  simp [hj]

theorem writeLE_size {b : ByteArray} {o n v : Nat} (h : o + n ≤ b.size) : (writeLE b o n v).size = b.size :=
  place_size (by rw [leBytes_size]; exact h)

theorem writeLE_getElem? {b : ByteArray} {o n v : Nat} (h : o + n ≤ b.size) (i : Nat) :
    (writeLE b o n v)[i]? = if o ≤ i ∧ i < o + n then some (leByte v (i - o)) else b[i]? := by
  unfold writeLE
  rw [place_getElem? (by rw [leBytes_size]; exact h), leBytes_size]
  split
  · rw [leBytes_getElem? (by omega)]
  · rfl

/-! ## One relocation -/

theorem applyRel_ok {b b' : ByteArray} {r : Rel} (h : applyRel b r = .ok b') :
    r.off + relocWidth r.ty ≤ b.size ∧ ∃ v, relocVal r.ty r.ri (rdLE b r.off (relocWidth r.ty)) = .ok v ∧
      b' = writeLE b r.off (relocWidth r.ty) v := by
  unfold applyRel at h
  simp only at h
  split at h
  · rename_i hw
    refine ⟨hw, ?_⟩
    cases hv : relocVal r.ty r.ri (rdLE b r.off (relocWidth r.ty)) with
    | error e => rw [hv] at h; cases h
    | ok v => rw [hv] at h; cases h; exact ⟨v, rfl, rfl⟩
  · cases h

theorem applyRel_size {b b' : ByteArray} {r : Rel} (h : applyRel b r = .ok b') : b'.size = b.size := by
  obtain ⟨hw, v, -, rfl⟩ := applyRel_ok h
  exact writeLE_size hw

/-- A relocation leaves the bytes it does not patch. -/
theorem applyRel_out {b b' : ByteArray} {r : Rel} (h : applyRel b r = .ok b') {i : Nat}
    (hi : i < r.off ∨ r.off + relocWidth r.ty ≤ i) : b'[i]? = b[i]? := by
  obtain ⟨hw, v, -, rfl⟩ := applyRel_ok h
  rw [writeLE_getElem? hw, if_neg (by omega)]

/-- **`R_AARCH64_ABS64` writes `S + A`.** -/
theorem applyRel_abs64 {b b' : ByteArray} {r : Rel} (h : applyRel b r = .ok b') (hty : r.ty = 257)
    {j : Nat} (hj : j < 8) :
    b'[r.off + j]? = some (leByte ((r.ri.S + r.ri.A) % 2 ^ 64).toNat j) := by
  obtain ⟨hw, v, hv, rfl⟩ := applyRel_ok h
  have hw8 : relocWidth r.ty = 8 := by rw [hty]; rfl
  rw [hty] at hv
  simp only [relocVal, pure, Except.pure] at hv
  cases hv
  rw [writeLE_getElem? hw, hw8, if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

/-! ## A piece's relocations -/

/-- Two relocations patch disjoint bytes. -/
def RelDisj (r r' : Rel) : Prop := r.off + relocWidth r.ty ≤ r'.off ∨ r'.off + relocWidth r'.ty ≤ r.off

theorem foldlM_cons_ok {b b' : ByteArray} {r : Rel} {rs : List Rel}
    (h : (r :: rs).foldlM applyRel b = .ok b') :
    ∃ b1, applyRel b r = .ok b1 ∧ rs.foldlM applyRel b1 = .ok b' := by
  simp only [List.foldlM_cons, bind, Except.bind] at h
  cases h1 : applyRel b r with
  | error e => rw [h1] at h; cases h
  | ok b1 => rw [h1] at h; exact ⟨b1, rfl, h⟩

theorem foldlM_size : ∀ {rs : List Rel} {b b' : ByteArray}, rs.foldlM applyRel b = .ok b' →
    b'.size = b.size
  | [], _, _, h => by cases h; rfl
  | _ :: _, _, _, h => by
    obtain ⟨b1, h1, h2⟩ := foldlM_cons_ok h
    rw [foldlM_size h2, applyRel_size h1]

/-- Relocations leave the bytes none of them patches. -/
theorem foldlM_out : ∀ {rs : List Rel} {b b' : ByteArray}, rs.foldlM applyRel b = .ok b' →
    ∀ {i : Nat}, (∀ r ∈ rs, i < r.off ∨ r.off + relocWidth r.ty ≤ i) → b'[i]? = b[i]?
  | [], _, _, h, _, _ => by cases h; rfl
  | r :: rs, _, _, h, i, hi => by
    obtain ⟨b1, h1, h2⟩ := foldlM_cons_ok h
    rw [foldlM_out h2 fun r' hr' => hi r' (.tail _ hr'), applyRel_out h1 (hi r (.head _))]

theorem foldlM_abs64 : ∀ {rs : List Rel} {b b' : ByteArray}, rs.foldlM applyRel b = .ok b' →
    rs.Pairwise RelDisj → ∀ {r : Rel}, r ∈ rs → r.ty = 257 → ∀ {j : Nat}, j < 8 →
      b'[r.off + j]? = some (leByte ((r.ri.S + r.ri.A) % 2 ^ 64).toNat j)
  | [], _, _, _, _, _, hr, _, _, _ => by cases hr
  | r0 :: rs, b, b', h, hd, r, hr, hty, j, hj => by
    obtain ⟨b1, h1, h2⟩ := foldlM_cons_ok h
    rw [List.pairwise_cons] at hd
    rcases List.mem_cons.1 hr with rfl | hr
    · have hw8 : relocWidth r.ty = 8 := by rw [hty]; rfl
      rw [foldlM_out h2 fun r' hr' => by
        have := hd.1 r' hr'; unfold RelDisj at this; rw [hw8] at this; omega]
      exact applyRel_abs64 h1 hty hj
    · exact foldlM_abs64 h2 hd.2 hr hty hj

/-- **A piece's bytes no relocation patches are its input bytes.** -/
theorem relocated_out {p : Piece} {b : ByteArray} (h : p.relocated = .ok b) {i : Nat}
    (hi : ∀ r ∈ p.rels, i < r.off ∨ r.off + relocWidth r.ty ≤ i) : b[i]? = p.bytes[i]? :=
  foldlM_out h hi

/-- **An `ABS64` of a piece writes `S + A`**, when the piece's relocations patch disjoint
bytes. -/
theorem relocated_abs64 {p : Piece} {b : ByteArray} (h : p.relocated = .ok b)
    (hd : p.rels.Pairwise RelDisj) {r : Rel} (hr : r ∈ p.rels) (hty : r.ty = 257) {j : Nat}
    (hj : j < 8) : b[r.off + j]? = some (leByte ((r.ri.S + r.ri.A) % 2 ^ 64).toNat j) :=
  foldlM_abs64 h hd hr hty hj

theorem relocated_size {p : Piece} {b : ByteArray} (h : p.relocated = .ok b) : b.size = p.bytes.size :=
  foldlM_size h

/-! ## The body -/

/-- Two pieces' file ranges are disjoint. -/
def PieceDisj (p q : Piece) : Prop := p.fo + p.bytes.size ≤ q.fo ∨ q.fo + q.bytes.size ≤ p.fo

theorem bodyStep_ok {body body' : ByteArray} {p : Piece} (h : bodyStep body p = .ok body') :
    ∃ b, p.relocated = .ok b ∧ p.fo + b.size ≤ body.size ∧ body' = place body p.fo b := by
  unfold bodyStep at h
  cases hb : p.relocated with
  | error e => rw [hb] at h; cases h
  | ok b =>
    rw [hb] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h; exact ⟨b, rfl, by assumption, rfl⟩
    · cases h

theorem bodyStep_size {body body' : ByteArray} {p : Piece} (h : bodyStep body p = .ok body') :
    body'.size = body.size := by
  obtain ⟨b, -, hs, rfl⟩ := bodyStep_ok h
  exact place_size hs

theorem bodyStep_out {body body' : ByteArray} {p : Piece} (h : bodyStep body p = .ok body') {i : Nat}
    (hi : i < p.fo ∨ p.fo + p.bytes.size ≤ i) : body'[i]? = body[i]? := by
  obtain ⟨b, hb, hs, rfl⟩ := bodyStep_ok h
  rw [place_getElem? hs, if_neg (by rw [relocated_size hb]; omega)]

theorem body_foldlM_cons {body body' : ByteArray} {p : Piece} {ps : List Piece}
    (h : (p :: ps).foldlM bodyStep body = .ok body') :
    ∃ b1, bodyStep body p = .ok b1 ∧ ps.foldlM bodyStep b1 = .ok body' := by
  simp only [List.foldlM_cons, bind, Except.bind] at h
  cases h1 : bodyStep body p with
  | error e => rw [h1] at h; cases h
  | ok b1 => rw [h1] at h; exact ⟨b1, rfl, h⟩

theorem body_out : ∀ {ps : List Piece} {body body' : ByteArray}, ps.foldlM bodyStep body = .ok body' →
    ∀ {i : Nat}, (∀ q ∈ ps, i < q.fo ∨ q.fo + q.bytes.size ≤ i) → body'[i]? = body[i]?
  | [], _, _, h, _, _ => by cases h; rfl
  | q :: ps, _, _, h, i, hi => by
    obtain ⟨b1, h1, h2⟩ := body_foldlM_cons h
    rw [body_out h2 fun q' hq' => hi q' (.tail _ hq'), bodyStep_out h1 (hi q (.head _))]

theorem body_piece : ∀ {ps : List Piece} {body body' : ByteArray}, ps.foldlM bodyStep body = .ok body' →
    ps.Pairwise PieceDisj → ∀ {p : Piece}, p ∈ ps → ∀ {b : ByteArray}, p.relocated = .ok b →
      ∀ {i : Nat}, i < b.size → body'[p.fo + i]? = b[i]?
  | [], _, _, _, _, _, hp, _, _, _, _ => by cases hp
  | q :: ps, body, body', h, hd, p, hp, b, hb, i, hi => by
    obtain ⟨b1, h1, h2⟩ := body_foldlM_cons h
    rw [List.pairwise_cons] at hd
    rcases List.mem_cons.1 hp with rfl | hp
    · have hbs := relocated_size hb
      rw [body_out h2 fun q' hq' => by have := hd.1 q' hq'; unfold PieceDisj at this; omega]
      obtain ⟨b', hb', hs, rfl⟩ := bodyStep_ok h1
      rw [hb] at hb'; cases hb'
      rw [place_getElem? hs, if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
    · exact body_piece h2 hd.2 hp hb hi

/-- **The body's bytes of a piece are its relocated bytes** (pieces with disjoint file
ranges). -/
theorem buildBody_piece {size : Nat} {ps : List Piece} {body : ByteArray}
    (h : buildBody size ps = .ok body) (hd : ps.Pairwise PieceDisj) {p : Piece} (hp : p ∈ ps)
    {b : ByteArray} (hb : p.relocated = .ok b) {i : Nat} (hi : i < b.size) :
    body[p.fo + i]? = b[i]? :=
  body_piece (body := ⟨Array.replicate size 0⟩) h hd hp hb hi

/-! ## Non-vacuity -/

/-- A piece of 8 bytes with one `ABS64` against `0x1234`. -/
def tinyPiece : Piece :=
  { addr := 0x200000, fo := 0, bytes := ⟨Array.replicate 8 0⟩,
    rels := [{ off := 0, ty := 257, ri := { S := 0x1234, A := 0, P := 0x200000 } }] }

theorem tinyPiece_relocated : tinyPiece.relocated = .ok (writeLE ⟨Array.replicate 8 0⟩ 0 8 0x1234) := by
  rfl

theorem relocated_abs64_witness :
    (writeLE ⟨Array.replicate 8 0⟩ 0 8 0x1234 : ByteArray)[0]? = some (leByte 0x1234 0) :=
  relocated_abs64 tinyPiece_relocated (List.pairwise_singleton _ _) (.head _) rfl (j := 0) (by decide)

theorem buildBody_piece_witness :
    ∀ body, buildBody 8 [tinyPiece] = .ok body →
      body[0]? = (writeLE ⟨Array.replicate 8 0⟩ 0 8 0x1234 : ByteArray)[0]? := fun _ h =>
  buildBody_piece h (List.pairwise_singleton _ _) (.head _) tinyPiece_relocated (i := 0) (by decide +kernel)

end Link.Ld
