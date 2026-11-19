import FV.E2E.BinCheck
import FV.E2E.CodeMap
import FV.E2E.StackBound
import FV.E2E.LinkCheckFast
import FV.E2E.LinkIdx

/-! # The stack budgets with hash maps (T3d)

`budMap` (`FV/E2E/StackBound.lean`) builds the call graph by testing every pair of functions with
`g`'s externs scanned and the CLIF image's symbols looked up (`List.lookup`) per pair, and finds
each function's image by a scan of the results (`artOf`). On a 28k-function program (std through
`cargo fv --build-std`) that is hours of `link-check`.

`budMapFast` (`budMapFast_eq`) is the same function with the lookups in hash maps and each
function's facts computed once. `link-check` evaluates it. The code map (`codeMapB`) is decided
through `codeMapLinB` (`FV/E2E/CodeMapFast.lean`, `@[csimp] codeMapB_eq_lin`). No statement
changes.
-/

namespace E2E

open Backend LinkCheck

namespace LinkCheck

/-- The compiled image of each function of the results by name, the first one of a name
(`artOf`: `artMap_artOf`). -/
def artMap (R : Res) : Std.HashMap String Art := assocMap (R.map fun e => (e.1.name, getOk e.2))

theorem artMap_artOf (R : Res) (g : Clif.Function) :
    ((artMap R)[g.name]?).getD default = artOf R g := by
  rw [artMap, assocMap_get, artOf]
  induction R with
  | nil => rfl
  | cons e R ih =>
    simp only [List.map_cons, List.lookup_cons, List.find?_cons]
    by_cases h : e.1.name = g.name
    · have h1 : (g.name == e.1.name) = true := by simp [h]
      have h2 : (e.1.name == g.name) = true := by simp [h]
      simp [h1, h2]
    · have h1 : (g.name == e.1.name) = false := by simpa using Ne.symm h
      have h2 : (e.1.name == g.name) = false := by simpa using h
      simp only [h1, h2]
      exact ih

end LinkCheck

namespace StackBound

/-- `edgeW S g` with `declB g` given (`D`). -/
def edgeWithW (S : String → Option Nat) (D : String → Bool) (ind : Bool)
    (sigs : List Clif.Signature) (h : Clif.Function) : Bool :=
  D h.name || (ind && (S h.name).isSome && sigs.any fun s => decide (LinkSys.IndSigMatch s h))

/-- `budSucc` with the symbols looked up through `S` and `declB g` a hash set. -/
def budSuccFast (S : String → Option Nat) (fs : Array Clif.Function) : Array (List Nat) :=
  fs.map fun g =>
    let D := declSet g
    let ind := !indFreeB g
    let sigs := indSigs g
    (List.range fs.size).filter fun j => edgeWithW S (fun n => D.contains n) ind sigs fs[j]!

theorem budSuccFast_eq (I : LinkInput) (fs : Array Clif.Function) :
    budSuccFast (fun n => (assocMap I.syms)[n]?) fs = budSucc I fs := by
  simp only [budSuccFast, assocMap_fun, declSet_contains]
  rfl

/-- The positions of `fs` by name (the candidate edges to the functions a caller declares). -/
def budByName (fs : Array Clif.Function) : Std.HashMap String (List Nat) :=
  groupMulti (fun j => [fs[j]!.name]) (List.range fs.size)

/-- The positions of the functions of `fs` with a symbol by parameter types (the candidate edges
of an indirect call: `LinkSys.IndSigMatch.ty`). -/
def budByTys (S : String → Option Nat) (fs : Array Clif.Function) :
    Std.HashMap (List Clif.Ty) (List Nat) :=
  groupMulti (fun j => if (S fs[j]!.name).isSome then [Clif.AbiParam.tys fs[j]!.sig.params] else [])
    (List.range fs.size)

/-- The positions `g` may have an edge to (`budCands_of`): those of the names it declares and,
when it has an indirect call, those of the functions with a symbol and the parameter types of one
of its indirect-call signatures. -/
def budCands (byName : Std.HashMap String (List Nat)) (byTys : Std.HashMap (List Clif.Ty) (List Nat))
    (g : Clif.Function) : Std.HashSet Nat :=
  Std.HashSet.ofList ((g.externs.flatMap fun e => byName.getD e.2.name []) ++
    (if !indFreeB g then (indSigs g).flatMap fun s => byTys.getD (Clif.AbiParam.tys s.params) []
      else []))

theorem budCands_of (S : String → Option Nat) (fs : Array Clif.Function) (g : Clif.Function)
    {j : Nat} (hj : j < fs.size)
    (h : edgeWithW S (fun n => (declSet g).contains n) (!indFreeB g) (indSigs g) fs[j]! = true) :
    (budCands (budByName fs) (budByTys S fs) g).contains j = true := by
  simp only [budCands, Std.HashSet.contains_ofList, List.contains_iff_mem, List.mem_append,
    List.mem_flatMap]
  simp only [edgeWithW, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true,
    decide_eq_true_eq] at h
  rcases h with hd | ⟨⟨hind, hs⟩, s, hsm, hm⟩
  · left
    have hd' : declB g fs[j]!.name = true := by rw [← declSet_contains g]; exact hd
    simp only [declB, List.any_eq_true, beq_iff_eq] at hd'
    obtain ⟨e, he, hen⟩ := hd'
    refine ⟨e, he, ?_⟩
    rw [budByName, mem_groupMulti]
    exact ⟨List.mem_range.mpr hj, by simp [hen]⟩
  · right
    simp only [hind, ↓reduceIte, List.mem_flatMap]
    refine ⟨s, hsm, ?_⟩
    rw [budByTys, mem_groupMulti]
    refine ⟨List.mem_range.mpr hj, ?_⟩
    simp only [hs, ↓reduceIte, List.mem_singleton]
    exact (LinkSys.IndSigMatch.ty hm).symm

/-- **`budSuccFast` with the candidate edges indexed and one task per function** (`@[csimp]
`budSuccFast_eq_idx`): `budSuccFast` tests every pair of functions, with `g`'s indirect-call
signatures compared per pair; on ruint's test executable (226,990 functions, #1108) that phase
of `link-check` ran for hours. Each pair is now first tested against `g`'s candidates (a hash
set), the edge test only on those. -/
def budSuccIdx (S : String → Option Nat) (fs : Array Clif.Function) : Array (List Nat) :=
  let rg := List.range fs.size
  let byName := budByName fs
  let byTys := budByTys S fs
  (Link.parMap (fun g =>
    let D := declSet g
    let ind := !indFreeB g
    let sigs := indSigs g
    let C := budCands byName byTys g
    rg.filter fun j => C.contains j && edgeWithW S (fun n => D.contains n) ind sigs fs[j]!)
    fs.toList).toArray

@[csimp] theorem budSuccFast_eq_idx : @budSuccFast = @budSuccIdx := by
  funext S fs
  apply Array.ext'
  simp only [budSuccFast, budSuccIdx, Link.parMap_eq, Array.toList_map, List.toList_toArray]
  apply List.map_congr_left
  intro g _
  apply List.filter_congr
  intro j hj
  cases hp : edgeWithW S (fun n => (declSet g).contains n) (!indFreeB g) (indSigs g) fs[j]! with
  | false => simp
  | true => simp [budCands_of S fs g (List.mem_range.mp hj) hp]

/-- `budFd` with the images in a hash map. -/
def budFdFast (M : Std.HashMap String Art) (fs : Array Clif.Function) : Array Nat :=
  fs.map fun g => frameDrop ((M[g.name]?).getD default).af

theorem budFdFast_eq (R : Res) (fs : Array Clif.Function) :
    budFdFast (artMap R) fs = budFd R fs := by
  simp only [budFdFast, budFd, artMap_artOf]

/-- `budPb` with the images in a hash map. -/
def budPbFast (M : Std.HashMap String Art) (fs : Array Clif.Function) : Array Nat :=
  fs.map fun g => probeBelow ((M[g.name]?).getD default).af

theorem budPbFast_eq (R : Res) (fs : Array Clif.Function) :
    budPbFast (artMap R) fs = budPb R fs := by
  simp only [budPbFast, budPb, artMap_artOf]

/-- **`budMap` with hash maps** (`budMapFast_eq`). The symbol map is built once, outside the
edge test (inside the lambda it was rebuilt per candidate edge of every indirect caller). -/
def budMapFast (I : LinkInput) (R : Res) : Std.HashMap String Nat :=
  let fs := (progOf R).funcs.toArray
  let sm := assocMap I.syms
  let b := budIter (budFdFast (artMap R) fs) (budPbFast (artMap R) fs) (budSuccFast (fun n => sm[n]?) fs)
    (fs.size + 1) (fs.map fun _ => none)
  (List.range fs.size).foldl (fun m j => match b[j]! with
    | some v => m.insert fs[j]!.name v
    | none => m) {}

theorem budMapFast_eq (I : LinkInput) (R : Res) : budMapFast I R = budMap I R := by
  simp only [budMapFast, budFdFast_eq, budPbFast_eq, budSuccFast_eq]
  rfl

end StackBound

end E2E

namespace E2E.BinCheck

open E2E E2E.LinkCheck Backend Elf

/-! ## The binary checks with the link map in a hash map

`relocB`, `itemBytes`, `objB` and `symsB` look names up in the link map, the aliases and the
symbol certificate (`List.lookup`) per relocation, per data byte (`objB` evaluates `objAt I o`
at every byte) and per link-map entry. The `…WithB` forms take the lookups as functions (`ad`:
`I.addrOf`, `al`: `I.aliases.lookup`, `look`: `I.addrs.lookup`, `ce`: `cert.lookup`) and are the
checks at those; `link-check` passes hash maps built once (`artWithB_assocMap`,
`objWithB_assocMap`, `symsWithB_assocMap`). -/

/-- `relocB I` with `I.addrOf = ad` and `I.aliases.lookup = al`. -/
def relocWithB (ad : String → Nat) (al : String → Option String) (m : PMem) (phs : List Phdr)
    (a : Art) (r : Reloc) : Bool :=
  let o := r.offset
  o % 4 == 0 && match r.type with
  | .call26 =>
    let d : Int := (ad ((al r.sym).getD r.sym) : Int) - (wAt a o).toNat
    a.fb.words[o / 4]? == some (blW 0) && blRange d && readN m 4 (wAt a o) == some (blW d)
  | .adrGotPage | .adrPrelPgHi21 =>
    let got := decide (r.type = .adrGotPage)
    let rd := rd5 (a.fb.words[o / 4]?.getD 0)
    decide (rd < 31) && a.fb.words[o / 4]? == some (adrpW rd 0) &&
      a.fb.words[o / 4 + 1]? == some (if got then ldrW rd rd 0 else addW rd rd 0) &&
      a.fb.relocs.any (fun r' => r'.offset == o + 4 && decide (r'.type = loOf r.type) &&
        r'.sym == r.sym && r'.addend == r.addend) &&
      (match readN m 4 (wAt a o), readN m 4 (wAt a (o + 4)) with
       | some x0, some x1 => pairB m (wAt a o).toNat
          (BitVec.ofNat 64 (ad r.sym) + BitVec.ofInt 64 r.addend).toNat rd got x0 x1
       | _, _ => false)
  | .ld64GotLo12Nc | .addAbsLo12Nc =>
    a.fb.relocs.any fun r' => r'.offset + 4 == o &&
      decide (r'.type = .adrGotPage ∨ r'.type = .adrPrelPgHi21)
  | .tlsDescAdrPage21 =>
    match tpOff phs (ad r.sym) with
    | some v => decide (v < 2 ^ 32) && readN m 4 (wAt a o) == some (movzW 0 (v / 65536)) &&
      readN m 4 (wAt a (o + 4)) == some (movkW 0 (v % 65536)) &&
      readN m 4 (wAt a (o + 8)) == some nopW && readN m 4 (wAt a (o + 12)) == some nopW
    | none => false
  | .tlsDescLd64Lo12 =>
    a.fb.relocs.any fun r' => decide (r'.type = .tlsDescAdrPage21) && r'.offset + 4 == o
  | .tlsDescAddLo12 =>
    a.fb.relocs.any fun r' => decide (r'.type = .tlsDescAdrPage21) && r'.offset + 8 == o
  | .tlsDescCall =>
    a.fb.relocs.any fun r' => decide (r'.type = .tlsDescAdrPage21) && r'.offset + 12 == o

theorem relocWithB_eq (I : LinkInput) :
    relocWithB I.addrOf (fun n => I.aliases.lookup n) = relocB I := rfl

/-- `artB I` with `I.addrOf = ad` and `I.aliases.lookup = al`. -/
def artWithB (ad : String → Nat) (al : String → Option String) (r : Rd) (phs : List Phdr)
    (a : Art) : Bool :=
  let m := memIn r phs
  (List.range a.fb.words.size).all (fun k =>
    (List.range 4).all (fun i => roB phs (wAt a (4 * k + i))) &&
    (a.fb.relocs.any (·.offset == 4 * k) ||
      readN m 4 (wAt a (4 * k)) == some (a.fb.words[k]?.getD 0))) &&
  a.fb.relocs.all (relocWithB ad al m phs a)

theorem artWithB_eq (I : LinkInput) :
    artWithB I.addrOf (fun n => I.aliases.lookup n) = artB I := rfl

theorem artWithB_assocMap (I : LinkInput) :
    artWithB (fun n => ((assocMap I.addrs)[n]?).getD 0) (fun n => (assocMap I.aliases)[n]?) =
      artB I := by
  simp only [assocMap_get]
  exact artWithB_eq I

/-- `itemBytes I` with `I.addrOf = ad`. -/
def itemBytesWith (ad : String → Nat) : Clif.DataItem → List (BitVec 8)
  | .byte b => [b]
  | .addr n off =>
    let v := BitVec.ofInt 64 ((ad n : Int) + off)
    (List.range 8).map fun j => v.extractLsb' (8 * j) 8

theorem itemBytesWith_eq (I : LinkInput) : itemBytesWith I.addrOf = itemBytes I := by
  funext it
  cases it <;> rfl

/-- **`objB` with the link map looked up through `look`** and the object's address and bytes
computed once (an array; `objWithB_eq`). -/
def objWithB (look : String → Option Nat) (r : Rd) (phs : List Phdr) (o : Clif.DataObject) : Bool :=
  match look o.name with
  | none => false
  | some a0 =>
    let bs := (o.items.flatMap (itemBytesWith fun n => (look n).getD 0)).toArray
    let at0 := BitVec.ofNat 64 a0
    (List.range bs.size).all fun i =>
      let x := at0 + BitVec.ofNat 64 i
      loadIn r phs x.toNat == some (bs[i]?.getD 0) && (o.writable || roB phs x || relroB phs x)

theorem objWithB_eq (I : LinkInput) (r : Rd) (phs : List Phdr) (o : Clif.DataObject) :
    objWithB (fun n => I.addrs.lookup n) r phs o = objB I r phs o := by
  have hi : itemBytesWith (fun n => (I.addrs.lookup n).getD 0) = itemBytes I := itemBytesWith_eq I
  simp only [objWithB, objB, objBytes, objAt, hi]
  cases h : I.addrs.lookup o.name with
  | none => simp
  | some a0 => simp [LinkInput.addrOf, h]

theorem objWithB_assocMap (I : LinkInput) :
    objWithB (fun n => (assocMap I.addrs)[n]?) = objB I := by
  funext r phs o
  rw [assocMap_fun, objWithB_eq]

/-- `symsB` with the aliases and the certificate looked up through `al`, `ce`. -/
def symsWithB (al : String → Option String) (ce : String → Option (Nat × Nat)) (I : LinkInput)
    (ex : Excerpt) : Bool :=
  let r := exRd ex
  I.addrs.all fun p => (al p.1).isSome ||
    match ce p.1 with
    | some (s, i) => match symEntry r s i with
      | some (o, v) => v == p.2 && cstrB r o (symName p.1)
      | none => false
    | none => false

theorem symsWithB_eq (I : LinkInput) (ex : Excerpt) (cert : List (String × Nat × Nat)) :
    symsWithB (fun n => I.aliases.lookup n) (fun n => cert.lookup n) I ex = symsB I ex cert := rfl

theorem symsWithB_assocMap (I : LinkInput) (ex : Excerpt) (cert : List (String × Nat × Nat)) :
    symsWithB (fun n => (assocMap I.aliases)[n]?) (fun n => (assocMap cert)[n]?) I ex =
      symsB I ex cert := by
  rw [assocMap_fun, assocMap_fun, symsWithB_eq]

end E2E.BinCheck
