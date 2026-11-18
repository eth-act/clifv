import FV.Link.Ld.Spec

/-! # `dataPlanB` in linear time (#1109)

`dataPlanB` (`FV/Link/Ld/Data.lean`) checks every CLIF data object against `lean-ld`'s plan. Per
object it finds the piece holding it (`pieceFor`: the piece starting at the object's address, else
a scan of all pieces, `pa.find?`), checks that the piece's relocations patch disjoint bytes in
increasing order (`chainB relBefore p.rels`, every relocation of the piece) and reads the object's
items from the piece, starting with the piece's relocations not ending before the object
(`relsFrom`, a walk from the piece's first relocation). On ruint's test executable (329,607 data
objects, 4,744 pieces) most objects are not at a piece start, and many share a piece with many
relocations, so all three are per object × per piece.

`dataPlanF` decides the same (`dataPlanF_eq`, `@[csimp] dataPlanB_eq_fast`) with the pieces
indexed once (`PieceIx.of`):
* the piece of an address by binary search over the pieces of positive size sorted by address,
  when those follow each other (`keyBefore`, checked once); the search's answer is checked
  where it is used, and is the scan's because at most one such piece holds a nonempty range
  (`search_spec`); otherwise the scan as before;
* `chainB relBefore` once per piece;
* the relocations from the object's offset by binary search over the piece's relocation ends and
  a table of the piece's relocation suffixes (`relsFrom_drop`: on a chain the relocations before
  the found position all end at or before the offset).

`Plan.specOkF` is `Plan.specOkB` with it (`@[csimp] specOkB_eq_fast`); `lake exe lean-link --ld`
decides it. No statement changes.
-/

namespace Link.Ld

open E2E Link

open E2E E2E.Elf E2E.BinCheck E2E.LinkCheck Link

/-- A chosen piece: the piece, its `chainB relBefore` value, and for each offset `k` a list of
relocations with the piece's `relsFrom k` (on a chain). -/
abbrev PieceView := Piece × Bool × (Nat → List Rel)

/-- `objPlanB` with the piece choice `find` (`objPlanWith_eq`). -/
def objPlanWith (am : Std.HashMap String Nat) (pl : Plan) (find : Nat → Nat → Option PieceView)
    (off n : Nat) (o : Clif.DataObject) : Bool :=
  match am[o.name]? with
  | none => false
  | some a =>
    let len := itemsLen o.items
    len == 0 || (decide (a + len < 2 ^ 64) &&
      match pl.segs.find? (fun s => decide (s.vaddr ≤ a) && decide (a + len ≤ s.vaddr + s.memsz)) with
      | none => false
      | some s => (o.writable || notW s.ph) &&
        match find a len with
        | some (p, c, sfx) =>
          let y := p.fo + (a - p.addr)
          decide (p.addr ≤ a) && decide (a + len ≤ p.addr + p.bytes.size) &&
            decide (a + len ≤ s.vaddr + s.filesz) && decide (y = s.offset + (a - s.vaddr)) &&
            (decide (y + len ≤ off) || decide (off + n ≤ y)) && c &&
            itemsB am p.bytes (a - p.addr) (sfx (a - p.addr)) o.items
        | none => decide (s.vaddr + s.filesz ≤ a) && o.items.all (· == .byte 0))

/-- `itemsB` reads its relocations only through `relsFrom` at its offset. -/
theorem itemsB_congr (am : Std.HashMap String Nat) (bs : ByteArray) {k : Nat} {rs rs' : List Rel}
    (h : relsFrom k rs = relsFrom k rs') (is : List Clif.DataItem) :
    itemsB am bs k rs is = itemsB am bs k rs' is := by
  cases is with
  | nil => rfl
  | cons it is => cases it <;> simp only [itemsB, h]

theorem objPlanWith_eq {am : Std.HashMap String Nat} {pl : Plan} {pa : Array Piece}
    {hint : Std.HashMap Nat Nat} {find : Nat → Nat → Option PieceView}
    (hf : ∀ a len, len ≠ 0 → (find a len).map (·.1) = pieceFor pa hint a len)
    (hc : ∀ a len v, find a len = some v → v.2.1 = chainB relBefore v.1.rels)
    (hs : ∀ a len v k, find a len = some v → chainB relBefore v.1.rels = true →
      relsFrom k (v.2.2 k) = relsFrom k v.1.rels)
    (off n : Nat) (o : Clif.DataObject) :
    objPlanWith am pl find off n o = objPlanB am pl pa hint off n o := by
  unfold objPlanWith objPlanB
  cases am[o.name]? with
  | none => rfl
  | some a =>
    dsimp only
    by_cases h0 : itemsLen o.items = 0
    · simp only [h0, beq_self_eq_true, Bool.true_or]
    · have hfa := hf a _ h0
      cases hfind : find a (itemsLen o.items) with
      | none =>
        rw [hfind, Option.map_none] at hfa
        rw [← hfa]
        rfl
      | some v =>
        obtain ⟨p, c, sfx⟩ := v
        have hp : pieceFor pa hint a (itemsLen o.items) = some p := by
          rw [← hf a _ h0, hfind]; rfl
        rw [hp]
        have hc' : c = chainB relBefore p.rels := hc _ _ _ hfind
        subst hc'
        dsimp only
        cases hch : chainB relBefore p.rels
        · simp only [Bool.and_false, Bool.false_and]
          first | rfl | (split <;> rfl)
        · rw [itemsB_congr am p.bytes (hs _ _ _ (a - p.addr) hfind hch)]
          rfl

/-! ## Relocations from an offset on a chain -/

/-- The end of the bytes a relocation patches. -/
def relEnd (r : Rel) : Nat := r.off + relocWidth r.ty

/-- **On a chain, the relocations before a position whose predecessor ends at or before `k` all
do**, so `relsFrom k` may start there. -/
theorem relsFrom_drop {rels : List Rel} (hch : chainB relBefore rels = true) {j k : Nat}
    (hj : j ≤ rels.length) (hk : j = 0 ∨ ∃ h : j - 1 < rels.length, relEnd rels[j - 1] ≤ k) :
    relsFrom k (rels.drop j) = relsFrom k rels := by
  have hpw := chainB_pairwise (r := relBefore) (fun _ _ _ => relBefore_trans) hch
  have hall : ∀ x ∈ rels.take j, relEnd x ≤ k := by
    intro x hx
    rcases hk with rfl | ⟨hj1, hk⟩
    · simp at hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < j := by simp at hi; omega
    rw [List.getElem_take]
    by_cases hij : i = j - 1
    · subst hij; exact hk
    · have hlt : i < j - 1 := by omega
      have := List.pairwise_iff_getElem.1 hpw i (j - 1) (by omega) hj1 hlt
      simp only [relBefore, decide_eq_true_eq] at this
      simp only [relEnd] at hk ⊢
      omega
  conv => rhs; rw [← List.take_append_drop j rels]
  unfold relsFrom
  rw [List.dropWhile_append_of_pos]
  intro x hx
  simpa [relEnd] using hall x hx

/-- The suffixes of `l` after `acc` (`tailsArr_get`). -/
def tailsArr {α : Type} : List α → Array (List α) → Array (List α)
  | [], acc => acc.push []
  | x :: l, acc => tailsArr l (acc.push (x :: l))

theorem tailsArr_size {α : Type} : ∀ (l : List α) (acc : Array (List α)),
    (tailsArr l acc).size = acc.size + l.length + 1
  | [], acc => by simp [tailsArr]
  | x :: l, acc => by rw [tailsArr, tailsArr_size l]; simp; omega

theorem tailsArr_prefix {α : Type} : ∀ (l : List α) (acc : Array (List α)) (i : Nat),
    i < acc.size → (tailsArr l acc)[i]? = acc[i]?
  | [], acc, i, hi => by simp [tailsArr, Array.getElem?_push, show i ≠ acc.size by omega]
  | x :: l, acc, i, hi => by
    rw [tailsArr, tailsArr_prefix l _ i (by simp; omega)]
    simp [Array.getElem?_push, show i ≠ acc.size by omega]

theorem tailsArr_get {α : Type} : ∀ (l : List α) (acc : Array (List α)) (j : Nat),
    j ≤ l.length → (tailsArr l acc)[acc.size + j]? = some (l.drop j)
  | [], acc, j, hj => by
    have : j = 0 := by simpa using hj
    subst this
    simp [tailsArr]
  | x :: l, acc, j, hj => by
    rw [tailsArr]
    cases j with
    | zero => rw [Nat.add_zero, tailsArr_prefix l _ _ (by simp)]; simp
    | succ j =>
      have := tailsArr_get l (acc.push (x :: l)) j (by simp at hj; omega)
      rw [Array.size_push] at this
      rw [show acc.size + (j + 1) = acc.size + 1 + j by omega, this]
      rfl

/-! ## The pieces indexed -/

/-- The first position in `[lo, hi)` whose value `f` is above `k` (binary search; its answer is
checked where it is used). -/
def cntLe (f : Nat → Nat) (k : Nat) (lo hi : Nat) : Nat :=
  if h : lo < hi then
    let mid := (lo + hi) / 2
    if f mid ≤ k then cntLe f k (mid + 1) hi else cntLe f k lo mid
  else lo
termination_by hi - lo
decreasing_by all_goals omega

/-- Piece `x`'s bytes end at or before piece `y`'s address (indices into `pa`). -/
def keyBefore (pa : Array Piece) (x y : Nat) : Bool :=
  decide (pa[x]!.addr + pa[x]!.bytes.size ≤ pa[y]!.addr)

theorem keyBefore_trans (pa : Array Piece) (x y z : Nat) (h1 : keyBefore pa x y = true)
    (h2 : keyBefore pa y z = true) : keyBefore pa x z = true := by
  simp only [keyBefore, decide_eq_true_eq] at *
  omega

/-- The indices of the pieces of positive size, sorted by address. -/
def pieceKeys (pa : Array Piece) : Array Nat :=
  (((List.range pa.size).filter fun k => pa[k]!.bytes.size != 0).mergeSort
    fun x y => decide (pa[x]!.addr ≤ pa[y]!.addr)).toArray

theorem mem_pieceKeys {pa : Array Piece} {k : Nat} :
    k ∈ (pieceKeys pa).toList ↔ k < pa.size ∧ pa[k]!.bytes.size ≠ 0 := by
  simp [pieceKeys, List.mem_mergeSort]

/-- The pieces of `pa` indexed for `dataPlanF`: `pieceHint`, the pieces of positive size by
address (`ks`) and whether they follow each other (`ok`), and per piece its `chainB relBefore`
value, its relocation suffixes and its relocation ends. -/
structure PieceIx where
  hint : Std.HashMap Nat Nat
  ks : Array Nat
  ok : Bool
  chain : Array Bool
  tails : Array (Array (List Rel))
  ends : Array (Array Nat)

def PieceIx.of (pa : Array Piece) : PieceIx :=
  let ks := pieceKeys pa
  { hint := pieceHint pa, ks, ok := chainB (keyBefore pa) ks.toList,
    chain := pa.map fun p => chainB relBefore p.rels,
    tails := pa.map fun p => tailsArr p.rels #[],
    ends := pa.map fun p => (p.rels.map relEnd).toArray }

/-- Piece `k`'s relocations from offset `off` (`sfx_relsFrom`). -/
def PieceIx.sfx (ix : PieceIx) (pa : Array Piece) (k off : Nat) : List Rel :=
  let e := ix.ends[k]!
  let j := cntLe (fun i => e[i]!) off 0 e.size
  if decide (j ≤ e.size) && (j == 0 || decide (e[j - 1]! ≤ off)) then ix.tails[k]![j]!
  else pa[k]!.rels

theorem sfx_relsFrom (pa : Array Piece) {k : Nat} (hk : k < pa.size)
    (hch : chainB relBefore pa[k].rels = true) (off : Nat) :
    relsFrom off ((PieceIx.of pa).sfx pa k off) = relsFrom off pa[k].rels := by
  have he : (PieceIx.of pa).ends[k]! = (pa[k].rels.map relEnd).toArray := by
    simp only [PieceIx.of]
    rw [getElem!_pos _ _ (by simpa using hk), Array.getElem_map]
  have ht : (PieceIx.of pa).tails[k]! = tailsArr pa[k].rels #[] := by
    simp only [PieceIx.of]
    rw [getElem!_pos _ _ (by simpa using hk), Array.getElem_map]
  unfold PieceIx.sfx
  rw [he, ht]
  dsimp only
  generalize cntLe _ off 0 _ = j
  split
  · rename_i hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hv
    obtain ⟨hj, hj0⟩ := hv
    simp only [List.size_toArray, List.length_map] at hj
    have hget := tailsArr_get pa[k].rels #[] j hj
    have hget' : (tailsArr pa[k].rels #[])[j]? = some (pa[k].rels.drop j) := by
      simpa using hget
    rw [getElem!_def, hget']
    refine relsFrom_drop hch hj ?_
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · exact .inl h0
    · right
      have hj1 : j - 1 < pa[k].rels.length := by omega
      refine ⟨hj1, ?_⟩
      rcases hj0 with h | h
      · omega
      rw [getElem!_pos (pa[k].rels.map relEnd).toArray (j - 1) (by simp; omega)] at h
      simpa using h
  · rw [getElem!_pos pa k hk]

/-- Piece `k` as a chosen piece, with the index's chain value and suffixes. -/
def PieceIx.view (ix : PieceIx) (pa : Array Piece) (k : Nat) : PieceView :=
  if k < pa.size then (pa[k]!, ix.chain[k]!, ix.sfx pa k)
  else (pa[k]!, chainB relBefore pa[k]!.rels, fun _ => pa[k]!.rels)

/-- A piece by the scan, with its chain value and its own relocations. -/
def slowView (p : Piece) : PieceView := (p, chainB relBefore p.rels, fun _ => p.rels)

/-- The piece holding `[a, a + len)` among the pieces of positive size, by binary search
(`none` when the answer is not one the search can give). -/
def PieceIx.search (ix : PieceIx) (pa : Array Piece) (a len : Nat) : Option (Option Nat) :=
  let has (p : Piece) : Bool := decide (p.addr ≤ a) && decide (a + len ≤ p.addr + p.bytes.size)
  let c := cntLe (fun i => pa[ix.ks[i]!]!.addr) a 0 ix.ks.size
  if ix.ok && len != 0 && decide (c ≤ ix.ks.size) &&
      (c == ix.ks.size || decide (a < pa[ix.ks[c]!]!.addr)) &&
      (c == 0 || decide (pa[ix.ks[c - 1]!]!.addr ≤ a)) then
    some (if c != 0 && has pa[ix.ks[c - 1]!]! then some ix.ks[c - 1]! else none)
  else none

/-- **The piece choice of `pieceFor`** through the index (`find_spec`). -/
def PieceIx.find (ix : PieceIx) (pa : Array Piece) (a len : Nat) : Option PieceView :=
  let has (p : Piece) : Bool := decide (p.addr ≤ a) && decide (a + len ≤ p.addr + p.bytes.size)
  let rest := match ix.search pa a len with
    | some r => r.map (ix.view pa)
    | none => (pa.find? has).map slowView
  match ix.hint[a]? with
  | some k => if h : k < pa.size then (if has pa[k] then some (ix.view pa k) else rest) else rest
  | none => rest

/-! ## The binary search's answer is the scan's -/

theorem find?_unique {pa : Array Piece} {has : Piece → Bool} {q : Nat} (hq : q < pa.size)
    (hu : ∀ j (hj : j < pa.size), has pa[j] = true → j = q) :
    pa.find? has = if has pa[q] then some pa[q] else none := by
  rw [← Array.find?_toList]
  split
  · rename_i hh
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨hh, q, by simpa using hq, by simp, fun j hj => ?_⟩
    have hjq : j < pa.size := by omega
    simp only [Array.getElem_toList, Bool.not_eq_eq_eq_not, Bool.not_true]
    cases hx : has pa[j]
    · rfl
    · exact absurd (hu j hjq hx) (by omega)
  · rename_i hh
    rw [List.find?_eq_none]
    intro x hx hx'
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hj' : j < pa.size := by simpa using hj
    have := hu j hj' (by simpa using hx')
    subst this
    exact hh (by simpa using hx')

theorem find?_none {pa : Array Piece} {has : Piece → Bool}
    (hu : ∀ j (hj : j < pa.size), has pa[j] = true → False) : pa.find? has = none := by
  rw [← Array.find?_toList, List.find?_eq_none]
  intro x hx hx'
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  exact hu j (by simpa using hj) (by simpa using hx')

theorem view_fst (ix : PieceIx) (pa : Array Piece) (k : Nat) : (ix.view pa k).1 = pa[k]! := by
  unfold PieceIx.view; split <;> rfl

/-- **The search's answer**: the index of the scan's piece, or none when the scan finds none. -/
theorem search_spec {pa : Array Piece} {a len : Nat} {r : Option Nat}
    (h : (PieceIx.of pa).search pa a len = some r) :
    r.map (fun k => pa[k]!) =
      pa.find? (fun p => decide (p.addr ≤ a) && decide (a + len ≤ p.addr + p.bytes.size)) := by
  unfold PieceIx.search at h
  dsimp only at h
  generalize hc : cntLe _ a 0 _ = c at h
  split at h
  · rename_i hv
    cases h
    have hks : (PieceIx.of pa).ks = pieceKeys pa := rfl
    have hok0 : (PieceIx.of pa).ok = chainB (keyBefore pa) (pieceKeys pa).toList := rfl
    simp only [hks, hok0] at hv ⊢
    generalize hK : pieceKeys pa = ks at hv ⊢
    have hmemK : ∀ k, k ∈ ks.toList ↔ k < pa.size ∧ pa[k]!.bytes.size ≠ 0 := by
      intro k; rw [← hK]; exact mem_pieceKeys
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, bne_iff_ne,
      ne_eq] at hv
    obtain ⟨⟨⟨⟨hok, hlen⟩, hcs⟩, hhi⟩, hlo⟩ := hv
    have hpw : ks.toList.Pairwise (fun x y => keyBefore pa x y = true) :=
      chainB_pairwise (keyBefore_trans pa) hok
    -- every piece holding the range is the search's candidate
    have huniq : ∀ j (hj : j < pa.size), (decide (pa[j].addr ≤ a) &&
        decide (a + len ≤ pa[j].addr + pa[j].bytes.size)) = true →
        ∃ h : c - 1 < ks.size, c ≠ 0 ∧ ks[c - 1] = j := by
      intro j hj hh
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
      have hmem : j ∈ ks.toList := by
        rw [hmemK, getElem!_pos pa j hj]; exact ⟨hj, by omega⟩
      obtain ⟨t, ht, htj⟩ := List.getElem_of_mem hmem
      simp only [Array.length_toList] at ht
      simp only [Array.getElem_toList] at htj
      have hjt : pa[ks[t]]! = pa[j] := by rw [htj, getElem!_pos pa j hj]
      by_cases htc : t < c
      · by_cases htc' : t = c - 1
        · exact ⟨by omega, by omega, by subst htc'; exact htj⟩
        · exfalso
          have hc1 : c - 1 < ks.size := by omega
          have := List.pairwise_iff_getElem.1 hpw t (c - 1) (by simpa using ht) (by simpa using hc1)
            (by omega)
          simp only [keyBefore, Array.getElem_toList, hjt] at this
          rcases hlo with h0 | hlo
          · omega
          · rw [getElem!_pos ks (c - 1) hc1] at hlo
            simp only [decide_eq_true_eq] at this
            omega
      · exfalso
        have hcs' : c < ks.size := by omega
        rcases hhi with hhi | hhi
        · omega
        · rw [getElem!_pos ks c hcs'] at hhi
          by_cases htc' : t = c
          · subst htc'; rw [hjt] at hhi; omega
          · have := List.pairwise_iff_getElem.1 hpw c t (by simpa using hcs') (by simpa using ht)
              (by omega)
            simp only [keyBefore, Array.getElem_toList, hjt, decide_eq_true_eq] at this
            omega
    split
    · rename_i hcand
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hcand
      obtain ⟨hc0, hhas⟩ := hcand
      have hc1 : c - 1 < ks.size := by omega
      have hq : ks[c - 1]! < pa.size := by
        have : ks[c - 1]! ∈ ks.toList := by
          rw [getElem!_pos ks (c - 1) hc1]; exact Array.getElem_mem_toList hc1
        rw [hmemK] at this; exact this.1
      rw [find?_unique hq (fun j hj hh => by
        obtain ⟨h1, -, h2⟩ := huniq j hj hh
        rw [getElem!_pos ks (c - 1) h1]; exact h2.symm)]
      rw [getElem!_pos pa _ hq] at hhas
      have he : pa[ks[c - 1]!]! = pa[ks[c - 1]!] := getElem!_pos pa (ks[c - 1]!) hq
      simp [he, hhas]
    · rename_i hcand
      rw [find?_none (fun j hj hh => by
        obtain ⟨h1, hc0, h2⟩ := huniq j hj hh
        apply hcand
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
        refine ⟨hc0, ?_⟩
        rw [getElem!_pos ks (c - 1) h1, h2, getElem!_pos pa j hj]
        simpa [Bool.and_eq_true] using hh)]
      rfl
  · cases h

/-- **`find` chooses `pieceFor`'s piece.** -/
theorem find_spec (pa : Array Piece) (a len : Nat) :
    ((PieceIx.of pa).find pa a len).map (·.1) = pieceFor pa (pieceHint pa) a len := by
  have hrest : (match (PieceIx.of pa).search pa a len with
      | some r => r.map ((PieceIx.of pa).view pa)
      | none => (pa.find? (fun p : Piece => decide (p.addr ≤ a) &&
          decide (a + len ≤ p.addr + p.bytes.size))).map slowView).map (fun v : PieceView => v.1) =
      pa.find? (fun p : Piece => decide (p.addr ≤ a) && decide (a + len ≤ p.addr + p.bytes.size)) := by
    split
    · rename_i r hr
      rw [← search_spec hr, Option.map_map]
      congr 1
      funext k
      exact view_fst _ pa k
    · simp only [Option.map_map, Function.comp_def, slowView, Option.map_id']
  unfold PieceIx.find pieceFor
  have hh : (PieceIx.of pa).hint = pieceHint pa := rfl
  rw [hh]
  cases (pieceHint pa)[a]? with
  | none => exact hrest
  | some k =>
    simp only [Option.bind]
    by_cases hk : k < pa.size
    · simp only [hk, ↓reduceDIte, Array.getElem?_eq_getElem hk]
      by_cases hh : (decide (pa[k].addr ≤ a) && decide (a + len ≤ pa[k].addr + pa[k].bytes.size)) = true
      · simp only [hh, ↓reduceIte, Option.map_some, view_fst, getElem!_pos pa k hk]
      · simp only [hh, ↓reduceIte, Bool.false_eq_true]
        exact hrest
    · have hn : pa[k]? = none := Array.getElem?_eq_none (by omega)
      simp only [hk, ↓reduceDIte, hn]
      exact hrest

theorem find_chain (pa : Array Piece) (a len : Nat) (v : PieceView)
    (h : (PieceIx.of pa).find pa a len = some v) : v.2.1 = chainB relBefore v.1.rels := by
  have hview : ∀ k, ((PieceIx.of pa).view pa k).2.1 = chainB relBefore ((PieceIx.of pa).view pa k).1.rels := by
    intro k
    by_cases hk : k < pa.size
    · simp only [PieceIx.view, hk, ↓reduceIte, getElem!_pos pa k hk]
      simp only [PieceIx.of]
      rw [getElem!_pos _ k (by simpa using hk), Array.getElem_map]
    · simp only [PieceIx.view, hk, ↓reduceIte]
  unfold PieceIx.find at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; exact hview _)
    | (obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h; rfl)
    | (obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.1 h; exact hview _)
    | cases h

theorem find_sfx (pa : Array Piece) (a len : Nat) (v : PieceView) (k : Nat)
    (h : (PieceIx.of pa).find pa a len = some v) (hch : chainB relBefore v.1.rels = true) :
    relsFrom k (v.2.2 k) = relsFrom k v.1.rels := by
  have hview : ∀ q, chainB relBefore ((PieceIx.of pa).view pa q).1.rels = true →
      relsFrom k (((PieceIx.of pa).view pa q).2.2 k) = relsFrom k ((PieceIx.of pa).view pa q).1.rels := by
    intro q hq
    by_cases hk : q < pa.size
    · simp only [PieceIx.view, hk, ↓reduceIte, getElem!_pos pa q hk] at hq ⊢
      exact sfx_relsFrom pa hk hq k
    · simp only [PieceIx.view, hk, ↓reduceIte]
  unfold PieceIx.find at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; exact hview _ hch)
    | (obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h; rfl)
    | (obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.1 h; exact hview _ hch)
    | cases h

/-! ## The data check -/

/-- **`dataPlanB` with the pieces indexed** (`dataPlanF_eq`). -/
def dataPlanF (I : LinkInput) (D : List Clif.DataObject) (pl : Plan) (off n : Nat) : Bool :=
  let pa := pl.pieces.toArray
  let ix := PieceIx.of pa
  D.all (objPlanWith (addrMap I.addrs) pl (ix.find pa) off n)

theorem dataPlanF_eq (I : LinkInput) (D : List Clif.DataObject) (pl : Plan) (off n : Nat) :
    dataPlanF I D pl off n = dataPlanB I D pl off n := by
  unfold dataPlanF dataPlanB
  dsimp only
  congr 1
  funext o
  exact objPlanWith_eq (hint := pieceHint pl.pieces.toArray)
    (fun a len _ => find_spec _ a len) (fun a len v h => find_chain _ a len v h)
    (fun a len v k h hch => find_sfx _ a len v k h hch) off n o

@[csimp] theorem dataPlanB_eq_fast : @dataPlanB = @dataPlanF := by
  funext I D pl off n
  exact (dataPlanF_eq I D pl off n).symm

/-- `Plan.specOkB` with `dataPlanF` (`specOkF_eq`). -/
def Plan.specOkF (pl : Plan) (P : LinkSpec) : Bool :=
  pl.regionInB P.R P.size && symsPlanB P.input0 pl && tlsBoundB P pl &&
    dataPlanF P.input0 P.data pl (offsetOf pl.phdrs P.R) P.size

theorem Plan.specOkF_eq (pl : Plan) (P : LinkSpec) : pl.specOkF P = pl.specOkB P := by
  simp only [Plan.specOkF, Plan.specOkB, dataPlanF_eq]

@[csimp] theorem specOkB_eq_fast : @Plan.specOkB = @Plan.specOkF := by
  funext pl P
  exact (Plan.specOkF_eq pl P).symm

end Link.Ld
