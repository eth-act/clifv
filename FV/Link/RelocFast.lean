import FV.Link.Reloc
import FV.E2E.LinkScopeFast

/-! # The relocation checks and the region's words with their lookups indexed (#1108)

`relocsOkB` (`FV/Link/Reloc.lean`) looks each relocation's symbol up in the link map
(`LinkInput.addrOf`, a `List.lookup` in `I.addrs`) and its partner relocations up in the
function's list (`a.fb.relocs.any`, once per relocation), and decides the offsets' `Nodup` by
comparing every pair; `artImage` finds the relocation at every word of the function
(`relocAt?`, a scan of its list). At ruint's scale (232,604 functions, #1108) that is a scan of
the link map per relocation and a scan of the function's relocations per word.

Here the same functions with the link map and the aliases in hash maps built once per link
(`RelocCtx.of`, `assocMap_get`), a function's relocations grouped by offset once per function
(`relocIdx`, `relocIdx_getD`) and the offsets' `Nodup` decided with a hash set
(`offsNodupB_eq`): `relocsAllF_eq` (the writer's relocation check over the table), `artPush_toList`
(a function's bytes, appended to a byte array). The writer evaluates them in its place
(`Link.leanLink_eq_fast`, `FV/Link/Image.lean`). No statement changes.
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck Backend

/-! ## The link map and the aliases as hash maps -/

/-- What the relocations look up in the input: the link map (`am`, `I.addrs`) and the aliases
(`al`, `I.aliases`), as hash maps (`RelocCtx.of`). -/
structure RelocCtx where
  am : Std.HashMap String Nat
  al : Std.HashMap String String

/-- The input's link map and aliases as hash maps (built once per link). -/
def RelocCtx.of (I : LinkInput) : RelocCtx := ⟨assocMap I.addrs, assocMap I.aliases⟩

/-- `LinkInput.addrOf` through the hash map (`RelocCtx.addrOf_of`). -/
def RelocCtx.addrOf (C : RelocCtx) (n : String) : Nat := (C.am[n]?).getD 0

/-- `LinkInput.baseOf` through the hash maps (`RelocCtx.baseOf_of`). -/
def RelocCtx.baseOf (C : RelocCtx) (n : String) : Nat := C.addrOf ((C.al[n]?).getD n)

/-- `LinkInput.symAddr` through the hash map (`RelocCtx.symAddr_of`). -/
def RelocCtx.symAddr (C : RelocCtx) (n : String) (off : Int) : BitVec 64 :=
  BitVec.ofNat 64 (C.addrOf n) + BitVec.ofInt 64 off

theorem RelocCtx.addrOf_of (I : LinkInput) (n : String) :
    (RelocCtx.of I).addrOf n = I.addrOf n := by
  simp only [RelocCtx.addrOf, RelocCtx.of, assocMap_get, LinkInput.addrOf]

theorem RelocCtx.baseOf_of (I : LinkInput) (n : String) :
    (RelocCtx.of I).baseOf n = I.baseOf n := by
  simp only [RelocCtx.baseOf, RelocCtx.addrOf, RelocCtx.of, assocMap_get, LinkInput.baseOf,
    LinkInput.addrOf]

theorem RelocCtx.symAddr_of (I : LinkInput) (n : String) (off : Int) :
    (RelocCtx.of I).symAddr n off = I.symAddr n off := by
  simp only [RelocCtx.symAddr, RelocCtx.addrOf_of, LinkInput.symAddr]

/-! ## A function's relocations by offset -/

/-- The relocations of `rs` at each offset, in order (`relocIdx_getD`). -/
def relocIdx (rs : List Reloc) : Std.HashMap Nat (List Reloc) :=
  rs.foldr (fun r m => m.insert r.offset (r :: m.getD r.offset [])) {}

theorem relocIdx_getD (rs : List Reloc) (o : Nat) :
    (relocIdx rs).getD o [] = rs.filter (·.offset == o) := by
  induction rs with
  | nil => simp [relocIdx]
  | cons r rs ih =>
    simp only [relocIdx, List.foldr_cons] at ih ⊢
    rw [Std.HashMap.getD_insert, List.filter_cons]
    by_cases h : r.offset = o
    · simp [h, ih]
    · have h' : (r.offset == o) = false := by simpa using h
      simp [h', ih]

/-- A scan for `p` over the elements of `l` satisfying `q` is the scan over `l` when `p` implies
`q`. -/
theorem any_filter_of_imp {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x, p x = true → q x = true) : (l.filter q).any p = l.any p := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.filter_cons]
    cases hq : q x
    · have hp : p x = false := by
        cases hp : p x
        · rfl
        · exact absurd (h x hp) (by simp [hq])
      simp [hp, ih]
    · simp [ih]

/-- `find?` over the elements of `l` satisfying `q` is `find?` over `l` when `p` implies `q`. -/
theorem find?_filter_of_imp {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x, p x = true → q x = true) : (l.filter q).find? p = l.find? p := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.filter_cons]
    cases hq : q x
    · have hp : p x = false := by
        cases hp : p x
        · rfl
        · exact absurd (h x hp) (by simp [hq])
      simp [hp, ih, List.find?_cons]
    · simp [ih, List.find?_cons]

/-- `hasAt` through the index (`hasAtF_eq`). -/
def hasAtF (X : Std.HashMap Nat (List Reloc)) (o : Nat) (t : RelocType) : Bool :=
  (X.getD o []).any fun r => r.offset == o && decide (r.type = t)

theorem hasAtF_eq (a : Art) (o : Nat) (t : RelocType) :
    hasAtF (relocIdx a.fb.relocs) o t = hasAt a o t := by
  unfold hasAtF hasAt
  rw [relocIdx_getD]
  exact any_filter_of_imp _ _ _ fun x hx => by
    simp only [Bool.and_eq_true] at hx
    exact hx.1

/-- `relocAt?` through the index (`relocAtF_eq`). -/
def relocAtF (X : Std.HashMap Nat (List Reloc)) (o : Nat) : Option Reloc :=
  (X.getD o []).find? (·.offset == o)

theorem relocAtF_eq (a : Art) (o : Nat) : relocAtF (relocIdx a.fb.relocs) o = relocAt? a o := by
  unfold relocAtF relocAt?
  rw [relocIdx_getD]
  exact find?_filter_of_imp _ _ _ fun _ hx => hx

/-- `relocOkB`'s partner of a page relocation `r` at `o`: its low half at `o + 4`
(`pairAtF_eq`). -/
def pairAtF (X : Std.HashMap Nat (List Reloc)) (o : Nat) (r : Reloc) : Bool :=
  (X.getD (o + 4) []).any fun r' => r'.offset == o + 4 && decide (r'.type = loOf r.type) &&
    r'.sym == r.sym && r'.addend == r.addend

theorem pairAtF_eq (a : Art) (o : Nat) (r : Reloc) :
    pairAtF (relocIdx a.fb.relocs) o r = a.fb.relocs.any fun r' => r'.offset == o + 4 &&
      decide (r'.type = loOf r.type) && r'.sym == r.sym && r'.addend == r.addend := by
  unfold pairAtF
  rw [relocIdx_getD]
  exact any_filter_of_imp _ _ _ fun x hx => by
    simp only [Bool.and_eq_true] at hx
    exact hx.1.1.1

/-- `relocOkB`'s partner of a low-half relocation at `o`: a page relocation at `o - 4`
(`hiAtF_eq`). -/
def hiAtF (X : Std.HashMap Nat (List Reloc)) (o : Nat) : Bool :=
  (X.getD (o - 4) []).any fun r' => r'.offset + 4 == o &&
    decide (r'.type = .adrGotPage ∨ r'.type = .adrPrelPgHi21)

theorem hiAtF_eq (a : Art) (o : Nat) :
    hiAtF (relocIdx a.fb.relocs) o = a.fb.relocs.any fun r' => r'.offset + 4 == o &&
      decide (r'.type = .adrGotPage ∨ r'.type = .adrPrelPgHi21) := by
  unfold hiAtF
  rw [relocIdx_getD]
  exact any_filter_of_imp _ _ _ fun x hx => by
    simp only [Bool.and_eq_true, beq_iff_eq] at hx ⊢
    have := hx.1
    omega

/-! ## The offsets' `Nodup` with a hash set -/

/-- No element of `l` is in `s` or twice in `l`. -/
def offsNodupGo : List Nat → Std.HashSet Nat → Bool
  | [], _ => true
  | x :: xs, s => !s.contains x && offsNodupGo xs (s.insert x)

/-- `l` has no duplicates, decided with a hash set (`offsNodupB_eq`). -/
def offsNodupB (l : List Nat) : Bool := offsNodupGo l {}

theorem offsNodupGo_eq : ∀ (l : List Nat) (s : Std.HashSet Nat),
    offsNodupGo l s = (decide l.Nodup && l.all fun x => !s.contains x)
  | [], s => by simp [offsNodupGo]
  | x :: xs, s => by
    rw [offsNodupGo, offsNodupGo_eq xs (s.insert x)]
    apply Bool.eq_iff_iff.2
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, List.all_eq_true,
      Std.HashSet.contains_insert, Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.nodup_cons,
      List.mem_cons, forall_eq_or_imp, ne_eq]
    constructor
    · rintro ⟨hx, hn, ha⟩
      exact ⟨⟨fun hm => (ha x hm).1 rfl, hn⟩, hx, fun y hy => (ha y hy).2⟩
    · rintro ⟨⟨hm, hn⟩, hx, ha⟩
      exact ⟨hx, hn, fun y hy => ⟨fun e => hm (e ▸ hy), ha y hy⟩⟩

theorem offsNodupB_eq (l : List Nat) : offsNodupB l = decide l.Nodup := by
  simp [offsNodupB, offsNodupGo_eq]

/-! ## The relocation check -/

/-- `relocOkB` with the lookups through `C` and the function's relocations through `X`
(`relocOkF_eq` at `RelocCtx.of I` and `relocIdx a.fb.relocs`). -/
def relocOkF (C : RelocCtx) (tp : Nat → Option Nat) (a : Art) (X : Std.HashMap Nat (List Reloc))
    (r : Reloc) : Bool :=
  let o := r.offset
  let n := a.fb.words.size
  o % 4 == 0 && decide (o / 4 < n) && match r.type with
  | .call26 =>
    wordOf a (o / 4) == blW 0 && blRange ((C.baseOf r.sym : Int) - (wAt a o).toNat)
  | .adrGotPage | .adrPrelPgHi21 =>
    let got := decide (r.type = .adrGotPage)
    let rd := rd5 (wordOf a (o / 4))
    decide (rd < 31) && decide (o / 4 + 1 < n) && wordOf a (o / 4) == adrpW rd 0 &&
      wordOf a (o / 4 + 1) == (if got then ldrW rd rd 0 else addW rd rd 0) &&
      pairAtF X o r &&
      inR (-2 ^ 20) (2 ^ 20) (pageOf (C.symAddr r.sym r.addend).toNat - pageOf (wAt a o).toNat)
  | .ld64GotLo12Nc | .addAbsLo12Nc => hiAtF X o
  | .tlsDescAdrPage21 =>
    decide (o / 4 + 3 < n) && hasAtF X (o + 4) .tlsDescLd64Lo12 &&
      hasAtF X (o + 8) .tlsDescAddLo12 && hasAtF X (o + 12) .tlsDescCall &&
      match tp (C.addrOf r.sym) with
      | some v => decide (v < 2 ^ 32)
      | none => false
  | .tlsDescLd64Lo12 => hasAtF X (o - 4) .tlsDescAdrPage21 && decide (4 ≤ o)
  | .tlsDescAddLo12 => hasAtF X (o - 8) .tlsDescAdrPage21 && decide (8 ≤ o)
  | .tlsDescCall => hasAtF X (o - 12) .tlsDescAdrPage21 && decide (12 ≤ o)

theorem relocOkF_eq (I : LinkInput) (tp : Nat → Option Nat) (a : Art) (r : Reloc) :
    relocOkF (RelocCtx.of I) tp a (relocIdx a.fb.relocs) r = relocOkB I tp a r := by
  simp only [relocOkF, relocOkB, RelocCtx.baseOf_of, RelocCtx.addrOf_of, RelocCtx.symAddr_of,
    target, hasAtF_eq, pairAtF_eq, hiAtF_eq]
  rfl

theorem relocOkF_fun (I : LinkInput) (tp : Nat → Option Nat) (a : Art) :
    relocOkF (RelocCtx.of I) tp a (relocIdx a.fb.relocs) = relocOkB I tp a :=
  funext (relocOkF_eq I tp a)

/-- `relocsOkB` through `C`, the function's relocations indexed once (`relocsOkF_eq`). -/
def relocsOkF (C : RelocCtx) (tp : Nat → Option Nat) (a : Art) : Bool :=
  offsNodupB (a.fb.relocs.map (·.offset)) && a.fb.relocs.all (relocOkF C tp a (relocIdx a.fb.relocs))

theorem relocsOkF_eq (I : LinkInput) (tp : Nat → Option Nat) (a : Art) :
    relocsOkF (RelocCtx.of I) tp a = relocsOkB I tp a := by
  rw [relocsOkF, relocsOkB, offsNodupB_eq, relocOkF_fun]

/-- **The writer's relocation check over the table** (`T.all fun e => relocsOkB I tp e.2`), the
lookups built once and the functions checked in parallel (`relocsAllF_eq`). -/
def relocsAllF (I : LinkInput) (tp : Nat → Option Nat) (T : List (Clif.Function × Art)) : Bool :=
  let C := RelocCtx.of I
  (parMap (fun e => relocsOkF C tp e.2) T).all id

theorem relocsAllF_eq (I : LinkInput) (tp : Nat → Option Nat) (T : List (Clif.Function × Art)) :
    relocsAllF I tp T = T.all fun e => relocsOkB I tp e.2 := by
  simp only [relocsAllF, parMap_eq, List.all_map, Function.comp_def, id_eq, relocsOkF_eq]

/-! ## A function's bytes -/

/-- `resolveWord` with the lookups through `C` and the relocations through `X`
(`resolveWordF_eq`). -/
def resolveWordF (C : RelocCtx) (tp : Nat → Option Nat) (a : Art)
    (X : Std.HashMap Nat (List Reloc)) (k : Nat) : BitVec 32 :=
  let w := wordOf a k
  let P := (wAt a (4 * k)).toNat
  match relocAtF X (4 * k) with
  | none => w
  | some r => match r.type with
    | .call26 => blW ((C.baseOf r.sym : Int) - P)
    | .adrGotPage | .adrPrelPgHi21 => adrpW (rd5 w) (pageOf (C.symAddr r.sym r.addend).toNat - pageOf P)
    | .ld64GotLo12Nc | .addAbsLo12Nc =>
      match relocAtF X (4 * k - 4) with
      | some r' => let rd := rd5 (wordOf a (k - 1)); addW rd rd ((C.symAddr r'.sym r'.addend).toNat % 4096)
      | none => w
    | .tlsDescAdrPage21 => movzW 0 ((tp (C.addrOf r.sym)).getD 0 / 65536)
    | .tlsDescLd64Lo12 =>
      match relocAtF X (4 * k - 4) with
      | some r' => movkW 0 ((tp (C.addrOf r'.sym)).getD 0 % 65536)
      | none => w
    | .tlsDescAddLo12 | .tlsDescCall => nopW

theorem resolveWordF_eq (I : LinkInput) (tp : Nat → Option Nat) (a : Art) (k : Nat) :
    resolveWordF (RelocCtx.of I) tp a (relocIdx a.fb.relocs) k = resolveWord I tp a k := by
  simp only [resolveWordF, resolveWord, relocAtF_eq, RelocCtx.baseOf_of, RelocCtx.addrOf_of,
    RelocCtx.symAddr_of, target]
  rfl

/-- `b` with the bytes `l` appended. -/
def pushAll (b : ByteArray) (l : List UInt8) : ByteArray := l.foldl ByteArray.push b

theorem pushAll_toList : ∀ (l : List UInt8) (b : ByteArray),
    (pushAll b l).data.toList = b.data.toList ++ l
  | [], b => by simp [pushAll]
  | x :: l, b => by
    have h := pushAll_toList l (b.push x)
    simp only [pushAll, List.foldl_cons] at h ⊢
    rw [h]
    simp [ByteArray.push, Array.toList_push]

theorem foldl_pushAll_toList (g : Nat → List UInt8) : ∀ (ks : List Nat) (b : ByteArray),
    (ks.foldl (fun b k => pushAll b (g k)) b).data.toList = b.data.toList ++ ks.flatMap g
  | [], b => by simp
  | k :: ks, b => by
    rw [List.foldl_cons, foldl_pushAll_toList g ks, pushAll_toList, List.flatMap_cons,
      List.append_assoc]

/-- `b` with `artImage`'s bytes of `a` appended, its relocations indexed once
(`artPush_toList`). -/
def artPush (C : RelocCtx) (tp : Nat → Option Nat) (a : Art) (b : ByteArray) : ByteArray :=
  let X := relocIdx a.fb.relocs
  pushAll ((List.range a.fb.words.size).foldl
    (fun b k => pushAll b (wordBytes (resolveWordF C tp a X k))) b) [0, 0, 0, 0]

theorem artPush_toList (I : LinkInput) (tp : Nat → Option Nat) (a : Art) (b : ByteArray) :
    (artPush (RelocCtx.of I) tp a b).data.toList = b.data.toList ++ artImage I tp a := by
  simp only [artPush, pushAll_toList, foldl_pushAll_toList, artImage, resolveWordF_eq,
    List.append_assoc]

end Link
