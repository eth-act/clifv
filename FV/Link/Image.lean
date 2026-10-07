import FV.Link.Reloc
import FV.E2E.Elf

/-! # Writing the program part into the executable (L2b)

rust-lld links the outside part with a placeholder of the region's size at `R` (the input
section `.text.fvlean`); `leanLink S file0` writes the program part's bytes over it:

* `patch file off b`: `file` with `b` written at `off`.
* `leanLink S file0`: the compiler's pipeline on every function, once (`resultsT` of
  `S.input0`, whose link map is the placement; `S.input` adds the stack depth), then the
  linker's checks of its own output — the placement's conditions (`placeOkB`), the code has the
  placement's sizes (`sizesOkB`), the relocation shapes (`relocsOkB`), each self-call alias's
  resolved words are its function's (`aliasOkB`) and its raw words and call lines too
  (`aliasShapeB`) — then the region's bytes (`regionBytes`) written at the region's file
  offset, and the checks of rust-lld's output (`outsideOkB`, below). Every check failing is a
  link error.
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

/-- Each alias's words, resolved, are its function's (one copy of the code at one address). -/
def aliasOkB (I : LinkInput) (tp : Nat → Option Nat) (T : List (Clif.Function × Art)) : Bool :=
  I.aliases.all fun p =>
    match T.find? (·.1.name == p.1), T.find? (·.1.name == p.2) with
    | some ea, some ef =>
      ea.2.fb.words.size == ef.2.fb.words.size &&
        (List.range ea.2.fb.words.size).all fun k =>
          resolveWord I tp ea.2 k == resolveWord I tp ef.2 k
    | _, _ => false

/-- The call lines and sizes of a function's laid-out lines (what `raOkB` reads of them). -/
def callShape (a : Art) : List (Bool × Nat) := a.fa.lines.toList.map fun l => (callLine l, l.size)

/-- Each alias's compiled words and call lines are its function's (the image holds one word per
address, `imgB`; a call of the shared code returns into it, `raOkB`). -/
def aliasShapeB (I : LinkInput) (T : List (Clif.Function × Art)) : Bool :=
  I.aliases.all fun p =>
    match T.find? (·.1.name == p.1), T.find? (·.1.name == p.2) with
    | some ea, some ef => ea.2.fb.words == ef.2.fb.words && callShape ea.2 == callShape ef.2
    | _, _ => false

/-- The defined symbols of a file: `(name, value) → (section, entry)` (an index only: `symsOkB`
checks the entries it names). -/
def symIndex (file : ByteArray) : Std.HashMap (String × Nat) (Nat × Nat) := Id.run do
  let r := fileRd file
  let some e := ehdr r | return {}
  let mut out : Std.HashMap (String × Nat) (Nat × Nat) := {}
  for s in [0:e.shnum] do
    let some sh := shdr r e s | continue
    if sh.type != 2 || sh.entsize != 24 then continue
    for i in [0:sh.size / 24] do
      let some (o, v) := symEntry r s i | continue
      let mut j := o
      while j < file.size && file[j]! != 0 do j := j + 1
      match String.fromUTF8? (file.extract o j) with
      | some n => if !out.contains (n, v) then out := out.insert (n, v) (s, i)
      | none => pure ()
  return out

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

/-- **The checks of rust-lld's output** on the written file: static (`hdrB`), the CLIF data
objects `D` in place (`dataB`), the symbol table (`symsOkB`). -/
def outsideOkB (I : LinkInput) (D : List Clif.DataObject) (file : ByteArray) : Bool :=
  let ex : Excerpt := [(0, file)]
  hdrB ex && dataB I D ex && symsOkB I file

/-- **The Lean linker**: the executable `file0` (the outside part, linked around a placeholder
of the region) with the program part written into the region. -/
def leanLink (S : LinkSpec) (file0 : ByteArray) : Except String ByteArray :=
  match phdrs (fileRd file0) with
  | none => .error "no program headers"
  | some phs =>
    -- the pipeline once: `S.input` is `S.input0.withDepth S.input0.resultsT`, and `resultsT`
    -- does not read the depth
    let Rs := S.input0.resultsT
    let I := S.input0.withDepth Rs
    let T := tabOf Rs
    let tp := tpOff phs
    if !S.placeOkB then .error "the placement's conditions fail (placeOkB)"
    else if !(Rs.all (·.2.toBool)) then .error "the compiler's pipeline rejects a function"
    else if !(S.sizesOkB T) then .error "the compiled code's sizes are not the placement's (sizesOkB)"
    else if !(T.all fun e => relocsOkB I tp e.2) then .error "a relocation fails the checks (relocsOkB)"
    else if !(aliasOkB I tp T) then .error "an alias's resolved words differ from its function's"
    else if !(aliasShapeB I T) then .error "an alias's code differs from its function's (aliasShapeB)"
    else
      let B := ByteArray.mk (regionBytes I tp ((T.take S.funcs.length).map (·.2))).toArray
      let off := offsetOf phs S.R
      if !regionOkB file0 S.R B.size off then
        .error "the region is not a read-only part of one PT_LOAD segment (regionOkB)"
      else
        let file := patch file0 off B
        if !outsideOkB I S.data file then
          .error "rust-lld's output fails the checks: static headers, data objects, symbols (outsideOkB)"
        else .ok file

end Link
