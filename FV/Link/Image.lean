import FV.Link.Reloc
import FV.E2E.Elf

/-! # Writing the program part into the executable (L2b)

rust-lld links the outside part with a placeholder of the region's size at `R` (the input
section `.text.fvlean`); `leanLink S file0` writes the program part's bytes over it:

* `regionOkB file0 R n off`: **the outside part's facts** the result needs (decided on the
  linked file, not proven): the ELF and program headers lie before the region's file bytes; the
  first `PT_LOAD` segment containing `R` holds `[R, R + n)` in its file bytes at `off`, is not
  writable, and no other `PT_LOAD` segment meets `[R, R + n)`.
* `patch file off b`: `file` with `b` written at `off`.
* `leanLink S file0`: the input `S.input` (the placement), the compiler's pipeline on every
  function (`resultsT`), the placement's conditions (`placeOkB`), the relocation checks
  (`relocsOkB`), each alias's words are its function's, with self-call aliases the linker's
  facts `linkerOkR` (decided: without aliases they are proven, `leanLink_linkerOk`), then the
  region's bytes (`regionBytes`) written at the region's file offset. Every check failing is a
  link error.
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

/-- **The Lean linker**: the executable `file0` (the outside part, linked around a placeholder
of the region) with the program part written into the region. -/
def leanLink (S : LinkSpec) (file0 : ByteArray) : Except String ByteArray :=
  match phdrs (fileRd file0) with
  | none => .error "no program headers"
  | some phs =>
    let I := S.input
    let Rs := I.resultsT
    let T := tabOf Rs
    let tp := tpOff phs
    if !S.placeOkB then .error "the placement's conditions fail (placeOkB)"
    else if !(Rs.all (·.2.toBool)) then .error "the compiler's pipeline rejects a function"
    else if !(T.all fun e => relocsOkB I tp e.2) then .error "a relocation fails the checks (relocsOkB)"
    else if !(aliasOkB I tp T) then .error "an alias's words differ from its function's"
    else if !(S.aliases.isEmpty || linkerOkR I Rs) then
      .error "with self-call aliases: the linker's facts fail (linkerOkR)"
    else
      let B := ByteArray.mk (regionBytes I tp ((T.take S.funcs.length).map (·.2))).toArray
      let off := offsetOf phs S.R
      if !regionOkB file0 S.R B.size off then
        .error "the region is not a read-only part of one PT_LOAD segment (regionOkB)"
      else .ok (patch file0 off B)

end Link
