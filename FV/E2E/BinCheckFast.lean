import FV.E2E.BinCheck
import FV.E2E.CodeMap
import FV.E2E.StackBound
import FV.E2E.LinkCheckFast

/-! # The code map and the stack budgets with hash maps (T3d)

`codeMapB` (`FV/E2E/CodeMap.lean`) looks every function's address up in the link map
(`List.lookup`) and compares every pair of functions of the table; `budMap`
(`FV/E2E/StackBound.lean`) builds the call graph by testing every pair of functions with `g`'s
externs scanned and the CLIF image's symbols looked up (`List.lookup`) per pair, and finds each
function's image by a scan of the results (`artOf`). On a 28k-function program (std through
`cargo fv --build-std`) that is hours of `link-check`.

`codeMapFastB` (`codeMapFastB_eq`) and `budMapFast` (`budMapFast_eq`) are the same functions with
the lookups in hash maps and each function's facts computed once. `link-check` evaluates these.
No statement changes.
-/

namespace E2E

open Backend LinkCheck

namespace LinkCheck

/-- `noBlrB I T` with the CLIF image's symbols looked up through `S`. -/
def noBlrWithB (S : String → Option Nat) (T : List (Clif.Function × Art)) (n : String) : Bool :=
  (S n).isNone && T.all fun e => !(e.1.externs.any fun x => x.2.name == n) || blrGotB e.2.vcp n

/-- `codeMapB`'s test of the pair (`x`, `y`) of functions of the table, the range test first. -/
def RaEnt.codeOk (pt : Clif.Program) (x y : RaEnt) : Bool :=
  decide (x.hi ≤ y.lo ∨ y.hi ≤ x.lo) || x.name == y.name ||
    (x.art.base == y.art.base && linesAlikeB pt x.art.fa.lines.toList y.art.fa.lines.toList)

theorem or_swap12 (a b c : Bool) : (a || b || c) = (b || a || c) := by
  cases a <;> cases b <;> rfl

/-- **`codeMapB` with the link map and the symbols in hash maps** (`A`, `S`) and the code ranges
computed once (`codeMapFastB_eq`). -/
def codeMapFastB (A S : String → Option Nat) (T : List (Clif.Function × Art)) : Bool :=
  let E := T.map RaEnt.of
  let pt := progT T
  T.all fun e =>
    (BitVec.ofNat 64 ((A e.1.name).getD 0) + BitVec.ofInt 64 0 == e.2.base ||
      noBlrWithB S T e.1.name) &&
    let x := RaEnt.of e
    E.all fun y => x.codeOk pt y

theorem codeMapFastB_eq (I : LinkInput) (T : List (Clif.Function × Art)) :
    codeMapFastB (fun n => (assocMap I.addrs)[n]?) (fun n => (assocMap I.syms)[n]?) T =
      codeMapB I T := by
  simp only [codeMapFastB, codeMapB, assocMap_fun, List.all_map, Function.comp_def]
  congr 1
  funext e
  congr 1
  congr 1
  funext e'
  exact or_swap12 _ _ _

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
