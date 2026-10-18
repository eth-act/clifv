import FV.Link.Ld.Build

/-! # Lean static linker: the plan and the image (L2b stage 3e)

The layout (`FV/Link/Ld/Layout.lean`) decides everything about the executable and returns it as
a `Plan`: the `PT_LOAD` segments (`Seg`), the TLS template, the `.eh_frame_hdr` table's place,
the body's size, its pieces (placed input sections, `.eh_frame` records and synthesized
tables with their resolved relocations), the section headers and the symbols. `assemble`
turns a plan into the image description `Img` the writer writes:

* the program headers are `Plan.phdrs`, a fixed shape: `PT_PHDR`, one `PT_LOAD` per segment
  (`Seg.ph`: `R`, `R E` or `RW`), `PT_TLS`, `PT_GNU_EH_FRAME`, `PT_GNU_STACK`;
* the body is `buildBody` of the pieces sorted by file offset (`Plan.sorted`).

`assemble` first checks the plan's own conditions (`Plan.okB`; a link error otherwise): the
segments in increasing, disjoint 64 KiB pages with `p_filesz ≤ p_memsz` and their file bytes in
the body, the pieces in disjoint file ranges after the headers. Its theorems
(`FV/Link/Ld/PlanProof.lean`) derive `file0OkB`'s header, region and TLS conditions from them.
-/

namespace Link.Ld

open E2E.Elf

/-- A `PT_LOAD` segment: its kind (`0` R, `1` R E, `2` RW), address, file offset, file and
memory sizes. -/
structure Seg where
  kind : Nat
  vaddr : Nat
  offset : Nat
  filesz : Nat
  memsz : Nat
  deriving Inhabited, Repr

/-- The segment's flags: `PF_R`, `PF_R | PF_X`, `PF_R | PF_W`. -/
def Seg.flags (s : Seg) : Nat := if s.kind == 0 then 4 else if s.kind == 1 then 5 else 6

/-- The segment's program header (64 KiB alignment). -/
def Seg.ph (s : Seg) : Phdr :=
  { type := 1, flags := s.flags, offset := s.offset, vaddr := s.vaddr, filesz := s.filesz,
    memsz := s.memsz, align := 0x10000 }

/-- **The plan of a link.** `tls*`: the TLS template (`.tdata`, then `.tbss`); `eh*`: the
`.eh_frame_hdr` table (size `0` without one); `size`: the body's size. -/
structure Plan where
  base : Nat
  entry : Nat
  segs : List Seg
  tlsAddr : Nat
  tlsOff : Nat
  tlsFilesz : Nat
  tlsMemsz : Nat
  tlsAlign : Nat
  ehOff : Nat
  ehAddr : Nat
  ehSize : Nat
  size : Nat
  pieces : List Piece
  secs : Array OutSec
  syms : Array OutSym
  deriving Inhabited

namespace Plan

variable (pl : Plan)

/-- **The program headers**: `PT_PHDR`, the segments, `PT_TLS`, `PT_GNU_EH_FRAME`,
`PT_GNU_STACK`. -/
def phdrs : List Phdr :=
  { type := 6, flags := 4, offset := 64, vaddr := pl.base + 64, filesz := 56 * (pl.segs.length + 4),
    memsz := 56 * (pl.segs.length + 4), align := 8 } ::
  (pl.segs.map Seg.ph ++
    [{ type := 7, flags := 4, offset := pl.tlsOff, vaddr := pl.tlsAddr, filesz := pl.tlsFilesz,
       memsz := pl.tlsMemsz, align := pl.tlsAlign },
     { type := 0x6474e550, flags := 4, offset := pl.ehOff, vaddr := pl.ehAddr, filesz := pl.ehSize,
       memsz := pl.ehSize, align := 4 },
     { type := 0x6474e551, flags := 6, offset := 0, vaddr := 0, filesz := 0, memsz := 0, align := 0 }])

/-- The end of the headers (the ELF header and the program headers). -/
def hdrEnd : Nat := 64 + 56 * (pl.segs.length + 4)

/-- The pieces sorted by file offset. -/
def sorted : List Piece := pl.pieces.mergeSort fun p q => decide (p.fo ≤ q.fo)

end Plan

/-- `r` holds of every two consecutive elements. -/
def chainB {α : Type} (r : α → α → Bool) : List α → Bool
  | a :: b :: rest => r a b && chainB r (b :: rest)
  | _ => true

/-- `s`'s 64 KiB pages lie before `t`'s. -/
def segBefore (s t : Seg) : Bool := decide ((s.vaddr + s.memsz + 65535) / 65536 ≤ t.vaddr / 65536)

/-- `p`'s file range ends before `q`'s starts. -/
def pieceBefore (p q : Piece) : Bool := decide (p.fo + p.bytes.size ≤ q.fo)

/-- **The plan's conditions**: the segments in increasing, disjoint pages (`segBefore`), each
of a known kind, with `p_filesz ≤ p_memsz` and its file bytes in the body; the pieces in
disjoint file ranges (`pieceBefore` on `sorted`) after the headers. -/
def Plan.okB (pl : Plan) : Bool :=
  chainB segBefore pl.segs &&
  pl.segs.all (fun s => decide (s.kind ≤ 2) && decide (s.filesz ≤ s.memsz) &&
    decide (s.offset + s.filesz ≤ pl.size)) &&
  chainB pieceBefore pl.sorted && pl.pieces.all fun p => decide (pl.hdrEnd ≤ p.fo)

/-- **The image of a plan**: its program headers, the body built from its pieces. -/
def assemble (pl : Plan) : Except String Img := do
  if !pl.okB then throw "the plan's conditions fail: segments in disjoint pages, pieces in disjoint file ranges after the headers (Plan.okB)"
  let body ← buildBody pl.size pl.sorted
  pure { entry := pl.entry, phs := pl.phdrs, body, secs := pl.secs, syms := pl.syms }

end Link.Ld
