import FV.Link.Layout
import FV.Link.Reloc
import FV.E2E.Elf
import FV.E2E.CodeMap
import FV.E2E.CodeMapFast
import FV.E2E.LinkScopeFast
import FV.E2E.LinkScopeIdx
import FV.Link.RelocFast

/-! # Writing the program part into the executable (L2b)

rust-lld links the outside part with a placeholder of the region's size at `R` (the input
section `.text.fvlean`); `leanLink S file0` writes the program part's bytes over it:

* `patch file off b`: `file` with `b` written at `off`.
* `leanLink S file0`: the compiler's pipeline on every function, once (`resultsT` of
  `S.input0`, whose link map is the placement; `S.input` adds the stack depth), then the
  linker's checks of its own output — the placement's conditions (`placeOkB`), the code has the
  placement's sizes (`sizesOkB`), the relocation shapes (`relocsOkB`), and the code map
  (`codeMapB`: link-map addresses are load addresses and distinct code ranges are disjoint) — then the
  region's bytes (`regionBytes`) written at the region's file offset, and the checks of
  rust-lld's output (`outsideOkB`, below). Every check failing is a link error.
* **The outside part's facts**, decided on rust-lld's output because rust-lld wrote those bytes
  (the headers, cg_clif's data objects, the symbol table): `regionOkB file0 R n off` (the ELF and
  program headers lie before the region's file bytes; the first `PT_LOAD` segment containing
  `R` holds `[R, R + n)` in its file bytes at `off`, is not writable, and no other `PT_LOAD`
  segment meets `[R, R + n)`) and `outsideOkB I D file` on the written file: a static AArch64
  executable (`hdrB`), the CLIF data objects `D` at their link-map addresses with their
  resolved bytes (`dataB`), every link-map name a symbol of the file at its address (`symsOkB`;
  for the program's functions this is that rust-lld put them at their placement, through which
  the outside part calls them).
-/

namespace Link

open E2E.LinkCheck in
/-- `LinkSpec.input0` with the CLIF image's symbols looked up in a hash map of the link map
(`input0_eq_fast`, `@[csimp]`): `List.lookup` per symbol name is quadratic in the program. -/
def LinkSpec.input0Fast (S : LinkSpec) : LinkInput :=
  let a := S.addrs
  let m := assocMap a
  { funcs := S.funcs, addrs := a, syms := S.symNames.filterMap fun n => m[n]?.map (n, ·),
    raStar := S.R + S.size, D := 0, aliases := [], fallback := true }

open E2E.LinkCheck in
@[csimp] theorem LinkSpec.input0_eq_fast : @LinkSpec.input0 = @LinkSpec.input0Fast := by
  funext S
  simp only [LinkSpec.input0, LinkSpec.input0Fast, assocMap_get]

end Link

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend

/-- `file` with the bytes `b` written at offset `off` (bytes past the end of `file` dropped). -/
def patch (file : ByteArray) (off : Nat) (b : ByteArray) : ByteArray :=
  ⟨Array.ofFn (n := file.size) fun i =>
    if off ≤ i.1 ∧ i.1 - off < b.size then b[i.1 - off]! else file[i.1]'i.2⟩

/-- **The outside part's facts about the region** `[R, R + n)` at file offset `off` of `file`. -/
def regionOkB (file : ByteArray) (R n off : Nat) : Bool :=
  let r := fileRd file
  match ehdr r, phdrs r with
  | some e, some phs =>
    decide (64 ≤ off) && decide (e.phoff + 56 * e.phnum ≤ off) && decide (off + n ≤ file.size) &&
    match segIn phs R with
    | some p => notW p && decide (R + n ≤ p.vaddr + p.filesz) && decide (p.filesz ≤ p.memsz) &&
        decide (off = p.offset + (R - p.vaddr)) &&
        phs.all fun q => q == p || q.type != 1 || decide (q.vaddr + q.memsz ≤ R) ||
          decide (R + n ≤ q.vaddr)
    | none => false
  | _, _ => false

/-- The file offset of address `R` in its `PT_LOAD` segment. -/
def offsetOf (phs : List Phdr) (R : Nat) : Nat :=
  match segIn phs R with
  | some p => p.offset + (R - p.vaddr)
  | none => 0

/-- The call lines and sizes of a function's laid-out lines (what `raOkB` reads of them). -/
def callShape (a : Art) : List (Bool × Nat) := a.fa.lines.toList.map fun l => (callLine l, l.size)

/-- The end of the NUL-terminated string at `j`: the offset of its first `0` byte at or after
`j`, or the end of the file. -/
def nulFrom (file : ByteArray) (j : Nat) : Nat :=
  if h : j < file.size then if file[j] != 0 then nulFrom file (j + 1) else j else j
termination_by file.size - j

/-- Entry `i` of section `s` as an index key: its name (the string at its name offset, up to
the NUL) and its value. -/
def entryKey (file : ByteArray) (s i : Nat) : Option (String × Nat) :=
  match symEntry (fileRd file) s i with
  | some (o, v) => (String.fromUTF8? (file.extract o (nulFrom file o))).map (·, v)
  | none => none

/-- The defined symbols of a file: `(name, value) → (section, entry)`, the first entry of each
key (an index only: `symsOkB` checks the entries it names). -/
def symIndex (file : ByteArray) : Std.HashMap (String × Nat) (Nat × Nat) :=
  let r := fileRd file
  match ehdr r with
  | none => {}
  | some e =>
    (List.range e.shnum).foldl (fun out s =>
      match shdr r e s with
      | none => out
      | some sh =>
        if sh.type != 2 || sh.entsize != 24 then out
        else (List.range (sh.size / 24)).foldl (fun out i =>
          match entryKey file s i with
          | some k => if !out.contains k then out.insert k (s, i) else out
          | none => out) out) {}

/-- **Every link-map name is a symbol of the file at its address** (`SymsOk`; the self-call
aliases, whose addresses are fresh, excepted). -/
def symsOkB (I : LinkInput) (file : ByteArray) : Bool :=
  let r := fileRd file
  let idx := symIndex file
  I.addrs.all fun p => (I.aliases.lookup p.1).isSome ||
    match idx[(symName p.1, p.2)]? with
    | some (s, i) => match symEntry r s i with
      | some (o, v) => v == p.2 && cstrB r o (symName p.1)
      | none => false
    | none => false

/-- The first address of every name of a link map (`addrMap_get`: the map's lookup is the
list's, `List.lookup`). -/
def addrMap (l : List (String × Nat)) : Std.HashMap String Nat :=
  l.foldl (fun m p => m.insertIfNew p.1 p.2) {}

/-- `objB` with the object's address looked up once in `am` (the link map's `addrMap`) and its
bytes indexed in an array (`objB` looks the address up and indexes the list per byte). -/
def objFastB (am : Std.HashMap String Nat) (I : LinkInput) (r : Rd) (phs : List Phdr)
    (o : Clif.DataObject) : Bool :=
  match am[o.name]? with
  | none => false
  | some a =>
    let bs := (objBytes I o).toArray
    let at0 := BitVec.ofNat 64 a
    (List.range bs.size).all fun i =>
      let x := at0 + BitVec.ofNat 64 i
      loadIn r phs x.toNat == some (bs[i]?.getD 0) && (o.writable || roB phs x || relroB phs x)

/-- `dataB` with `objFastB`. -/
def dataFastB (I : LinkInput) (D : List Clif.DataObject) (ex : Excerpt) : Bool :=
  match phdrs (exRd ex) with
  | some phs => let am := addrMap I.addrs; D.all (objFastB am I (exRd ex) phs)
  | none => false

/-- `itemBytes` with the link map in `C` (`itemBytesF_eq`). -/
def itemBytesF (C : RelocCtx) : Clif.DataItem → List (BitVec 8)
  | .byte b => [b]
  | .addr n off =>
    let v := BitVec.ofInt 64 ((C.addrOf n : Int) + off)
    (List.range 8).map fun j => v.extractLsb' (8 * j) 8

theorem itemBytesF_eq (I : LinkInput) : itemBytesF (RelocCtx.of I) = itemBytes I := by
  funext d
  cases d <;> simp only [itemBytesF, itemBytes, RelocCtx.addrOf_of]

/-- `objFastB` with the data items' addresses looked up in `C` (`objFastF_eq`). -/
def objFastF (am : Std.HashMap String Nat) (C : RelocCtx) (r : Rd) (phs : List Phdr)
    (o : Clif.DataObject) : Bool :=
  match am[o.name]? with
  | none => false
  | some a =>
    let bs := (o.items.flatMap (itemBytesF C)).toArray
    let at0 := BitVec.ofNat 64 a
    (List.range bs.size).all fun i =>
      let x := at0 + BitVec.ofNat 64 i
      loadIn r phs x.toNat == some (bs[i]?.getD 0) && (o.writable || roB phs x || relroB phs x)

theorem objFastF_eq (am : Std.HashMap String Nat) (I : LinkInput) (r : Rd) (phs : List Phdr) :
    objFastF am (RelocCtx.of I) r phs = objFastB am I r phs := by
  funext o
  simp only [objFastF, objFastB, objBytes, itemBytesF_eq]

/-- **`dataFastB` with the data items' addresses in a hash map** (`dataFastB` looks each one up
in the link map's list, `LinkInput.addrOf`): `dataFastF_eq`, `@[csimp]`. -/
def dataFastF (I : LinkInput) (D : List Clif.DataObject) (ex : Excerpt) : Bool :=
  match phdrs (exRd ex) with
  | some phs => let am := addrMap I.addrs; let C := RelocCtx.of I; D.all (objFastF am C (exRd ex) phs)
  | none => false

@[csimp] theorem dataFastB_eq_fast : @dataFastB = @dataFastF := by
  funext I D ex
  unfold dataFastB dataFastF
  cases phdrs (exRd ex) <;> simp only [objFastF_eq]

/-- **The checks of rust-lld's output** on the written file: static (`hdrB`), the CLIF data
objects `D` in place (`dataFastB`, i.e. `dataB`), the symbol table (`symsOkB`). -/
def outsideOkB (I : LinkInput) (D : List Clif.DataObject) (file : ByteArray) : Bool :=
  let ex : Excerpt := [(0, file)]
  hdrB ex && dataFastB I D ex && symsOkB I file

/-- `LinkInput.resultsT`, the functions compiled in parallel (`parResultsT_eq`). -/
def parResultsT (I : LinkInput) : Res :=
  parMap (fun fi => let f := fi.func
    (f, pipeT f fi.k (BitVec.ofNat 64 (I.baseOf f.name)) (raJ fi.ra fi.j))) I.funcs

theorem parResultsT_eq (I : LinkInput) : parResultsT I = I.resultsT := by
  simp only [parResultsT, parMap_eq]; rfl

/-- The region's bytes from offset `o`, the functions `T` at their aligned offsets (`offsA`,
alignments `as`): before each function the zero bytes up to its offset (`udf #0` words, the
filler rust-lld writes when it aligns a section), then its image (`artImage`: its resolved
words and the gap word). -/
def regionGo (I : LinkInput) (tp : Nat → Option Nat) : List Art → List Nat → Nat → List UInt8
  | [], _, _ => []
  | a :: T, as, o =>
    List.replicate (alignW o (as.headD 4) - o) 0 ++ artImage I tp a ++
      regionGo I tp T as.tail (alignW o (as.headD 4) + 4 * a.fb.words.size + 4)

/-- **The region's bytes** (#1061): the placed functions' images, each at its aligned offset. -/
def regionBytesA (I : LinkInput) (tp : Nat → Option Nat) (as : List Nat) (T : List Art) :
    List UInt8 :=
  regionGo I tp T as 0

/-- `regionGo`'s bytes appended to `b`, with the lookups through `C` and each function's
relocations indexed (`regionPush_toList`; tail-recursive). -/
def regionPush (C : RelocCtx) (tp : Nat → Option Nat) :
    List Art → List Nat → Nat → ByteArray → ByteArray
  | [], _, _, b => b
  | a :: T, as, o, b =>
    regionPush C tp T as.tail (alignW o (as.headD 4) + 4 * a.fb.words.size + 4)
      (artPush C tp a (pushAll b (List.replicate (alignW o (as.headD 4) - o) 0)))

theorem regionPush_toList (I : LinkInput) (tp : Nat → Option Nat) :
    ∀ (T : List Art) (as : List Nat) (o : Nat) (b : ByteArray),
      (regionPush (RelocCtx.of I) tp T as o b).data.toList = b.data.toList ++ regionGo I tp T as o
  | [], _, _, b => by simp [regionPush, regionGo]
  | a :: T, as, o, b => by
    rw [regionPush, regionPush_toList I tp T, artPush_toList, pushAll_toList, regionGo]
    simp only [List.append_assoc]

/-- **The region's bytes as a byte array** (`regionBA_eq`: `regionBytesA`'s, without the list
of bytes and with the lookups indexed). -/
def regionBA (I : LinkInput) (tp : Nat → Option Nat) (as : List Nat) (T : List Art) : ByteArray :=
  regionPush (RelocCtx.of I) tp T as 0 ByteArray.empty

theorem regionBA_eq (I : LinkInput) (tp : Nat → Option Nat) (as : List Nat) (T : List Art) :
    regionBA I tp as T = ByteArray.mk (regionBytesA I tp as T).toArray := by
  have h := regionPush_toList I tp T as 0 ByteArray.empty
  have h0 : ByteArray.empty.data.toList = [] := rfl
  rw [h0, List.nil_append] at h
  unfold regionBA regionBytesA
  rw [← h]

/-- **The Lean linker**: the executable `file0` (the outside part, linked around a placeholder
of the region) with the program part written into the region. -/
def leanLink (S : LinkSpec) (file0 : ByteArray) : Except String ByteArray :=
  match phdrs (fileRd file0) with
  | none => .error "no program headers"
  | some phs =>
    -- the pipeline once, in parallel: `S.input` is `S.input0.withDepth S.input0.resultsT`, and
    -- `resultsT` does not read the depth
    let I0 := S.input0
    let Rs := parResultsT I0
    let I := I0.withDepth Rs
    let T := tabOf Rs
    let tp := tpOff phs
    if !S.placeOkB then .error "the placement's conditions fail (placeOkB)"
    else if !(Rs.all (·.2.toBool)) then .error "the compiler's pipeline rejects a function"
    else if !(S.namesOkB T) then .error "the compiled functions' names are not the placement's (namesOkB)"
    else if !(S.sizesOkB T) then .error "the compiled code's sizes are not the placement's (sizesOkB)"
    else if !(T.all fun e => relocsOkB I tp e.2) then .error "a relocation fails the checks (relocsOkB)"
    else if !(codeMapB I T) then .error "the code map check fails (codeMapB)"
    else
      let B := ByteArray.mk (regionBytesA I tp S.aligns ((T.take S.funcs.length).map (·.2))).toArray
      let off := offsetOf phs S.R
      if !regionOkB file0 S.R B.size off then
        .error "the region is not a read-only part of one PT_LOAD segment (regionOkB)"
      else
        let file := patch file0 off B
        if !outsideOkB I S.data file then
          .error "rust-lld's output fails the checks: static headers, data objects, symbols (outsideOkB)"
        else .ok file

/-- **The writer's checks and bytes on a result table** `Rs` of the input `I0` (the part of
`leanLink` after the pipeline), with the relocation checks (`relocsAllF`) and the region's
bytes (`regionBA`) indexed; `codeMapB` and `outsideOkB` run their `@[csimp]` forms
(`E2E.LinkCheck.codeMapB_eq_lin`, `dataFastB_eq_fast`). -/
def writeTail (S : LinkSpec) (file0 : ByteArray) (phs : List Phdr) (I0 : LinkInput) (Rs : Res) :
    Except String ByteArray :=
  let I := I0.withDepth Rs
  let T := tabOf Rs
  let tp := tpOff phs
  if !S.placeOkB then .error "the placement's conditions fail (placeOkB)"
  else if !(Rs.all (·.2.toBool)) then .error "the compiler's pipeline rejects a function"
  else if !(S.namesOkB T) then .error "the compiled functions' names are not the placement's (namesOkB)"
  else if !(S.sizesOkB T) then .error "the compiled code's sizes are not the placement's (sizesOkB)"
  else if !(relocsAllF I tp T) then .error "a relocation fails the checks (relocsOkB)"
  else if !(codeMapB I T) then .error "the code map check fails (codeMapB)"
  else
    let B := regionBA I tp S.aligns ((T.take S.funcs.length).map (·.2))
    let off := offsetOf phs S.R
    if !regionOkB file0 S.R B.size off then
      .error "the region is not a read-only part of one PT_LOAD segment (regionOkB)"
    else
      let file := patch file0 off B
      if !outsideOkB I S.data file then
        .error "rust-lld's output fails the checks: static headers, data objects, symbols (outsideOkB)"
      else .ok file

/-- **The Lean linker's writer on the result table `results S.input0`**, indexed (`leanLink`,
`DeadCleanup.leanLink` and `leanLinkWithResults` are this at their tables: `leanLink_eq_fast`,
`DeadCleanup.leanLink_eq_fast`, `leanLinkWithResults_eq_fast`). -/
def writeWith (S : LinkSpec) (file0 : ByteArray) (results : LinkInput → Res) :
    Except String ByteArray :=
  match phdrs (fileRd file0) with
  | none => .error "no program headers"
  | some phs => let I0 := S.input0; writeTail S file0 phs I0 (results I0)

/-- `leanLink` through `writeWith` (`leanLink_eq_fast`). -/
def leanLinkFast (S : LinkSpec) (file0 : ByteArray) : Except String ByteArray :=
  writeWith S file0 parResultsT

/-- **`leanLink`'s writer indexed** (#1108): the relocation checks, the region's bytes, the code
map and the data objects without a scan of the link map or of a function's relocations per item,
and without comparing every pair of functions. -/
@[csimp] theorem leanLink_eq_fast : @leanLink = @leanLinkFast := by
  funext S file0
  unfold leanLink leanLinkFast writeWith writeTail
  cases phdrs (fileRd file0) with
  | none => rfl
  | some phs => simp only [relocsAllF_eq, regionBA_eq]

end Link
