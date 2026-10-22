import FV.Link.Ld.Resolve
import FV.Link.Ld.Reloc
import FV.Link.Ld.Plan

/-! # Lean static linker: layout, synthesized sections, relocation, the image

After resolution and `--gc-sections` (`FV/Link/Ld/Resolve.lean`), the live input sections are
grouped into output sections and laid out in three `PT_LOAD` segments in disjoint 64 KiB pages,
the file offsets congruent to the addresses modulo 64 KiB (docs/research/lean-linker.md §6):

* **R** (from file offset `0`, the ELF and program headers first): `.rodata`, read-only
  sections with C-identifier names, `.gcc_except_table`, `.eh_frame_hdr`, `.eh_frame`,
  `.data.rel.ro`, `.got`, `.init_array`, `.fini_array`, `.preinit_array`, `.tdata` (a static
  executable resolves every relocation at link time, so none of these is written at run time);
* **R E**: `.text` (with the region `.text.fvlean`), `.init`, `.fini`;
* **RW**: `.data`, writable sections with C-identifier names, `.bss` and the common symbols.

`PT_TLS` (always present; `.tdata` then `.tbss`), `PT_GNU_EH_FRAME`, `PT_GNU_STACK`. The GOT
holds link-time values; `.eh_frame` keeps the CIEs and the FDEs of live functions (CIE pointers
rewritten) and `.eh_frame_hdr` its sorted table. Linker-defined symbols: `__init_array_start`,
…, `__start_X`/`__stop_X`, `_end`, `_etext`, `_edata`, `__bss_start`, `__ehdr_start`,
`_GLOBAL_OFFSET_TABLE_`.
-/

namespace Link.Ld

open E2E.Elf

/-- Options of a link. -/
structure Opts where
  entry : String := "_start"
  undefs : List String := []
  gc : Bool := true
  base : Nat := 0x200000
  deriving Inhabited

/-- The result: the image description, the link map's text and the plan the image is
`assemble`d from (`FV/Link/Ld/Plan.lean`). -/
structure LinkOut where
  img : Img
  map : String
  plan : Plan

/-- `n` rounded up to a multiple of `a` (an alignment `0` counts as `1`). -/
def alignUp (n a : Nat) : Nat := (n + max a 1 - 1) / max a 1 * max a 1

/-- The priority of an init/fini array section (`.init_array.N`; `65536` without one). -/
def arrPrio (n : String) : Nat :=
  match (n.splitOn ".").getLast? with
  | some s => if !s.isEmpty && s.all Char.isDigit then s.toNat! else 65536
  | none => 65536

/-- The output section of an input section and its segment (`0` R, `1` R E, `2` RW). -/
def outOf (s : Sec) : String × Nat :=
  if s.has shfTls then (if s.type == shtNobits then (".tbss", 0) else (".tdata", 0))
  else if s.has shfExec then
    (if s.name == ".init" then ".init" else if s.name == ".fini" then ".fini" else ".text", 1)
  else if s.type == shtInitArray || s.name.startsWith ".init_array" then (".init_array", 0)
  else if s.type == shtFiniArray || s.name.startsWith ".fini_array" then (".fini_array", 0)
  else if s.type == shtPreinitArray || s.name.startsWith ".preinit_array" then (".preinit_array", 0)
  else if isCIdent s.name then (s.name, if s.has shfWrite then 2 else 0)
  else if s.has shfWrite then
    if s.name.startsWith ".data.rel.ro" then (".data.rel.ro", 0)
    else if s.type == shtNobits then (".bss", 2) else (".data", 2)
  else if s.name.startsWith ".gcc_except_table" then (".gcc_except_table", 0)
  else (".rodata", 0)

/-- The order of the output sections (C-identifier sections after `.rodata` / `.data`). -/
def outRank (n : String) (seg : Nat) : Nat :=
  match n with
  | ".rodata" => 0 | ".gcc_except_table" => 2 | ".eh_frame_hdr" => 3 | ".eh_frame" => 4
  | ".data.rel.ro" => 5 | ".got" => 6 | ".init_array" => 7 | ".fini_array" => 8
  | ".preinit_array" => 9 | ".tdata" => 10 | ".tbss" => 11
  | ".text" => 20 | ".init" => 21 | ".fini" => 22
  | ".data" => 30 | ".bss" => 32
  | _ => if seg == 2 then 31 else 1

/-- A part of an output section: an input section, or a synthesized one (`got`, `eh`,
`ehHdr`, `common f k`). -/
inductive Part where
  | input (s : SecId)
  | got
  | eh
  | ehHdr
  | common (f k : Nat)
  deriving Inhabited, Repr, BEq

/-- An output section being laid out. -/
structure OSec where
  name : String
  seg : Nat
  parts : Array Part
  deriving Inhabited

/-- A kept `.eh_frame` record: file, record, its offset in the output `.eh_frame`. -/
structure EhOut where
  file : Nat
  ei : Nat
  piece : EhPiece
  out : Nat
  deriving Inhabited

/-! ## Placement

The output sections are placed in order by `placeSec`, a fold whose state `PSt` holds the
address and file offset reached, the open segment and the placed parts (`Slot`s: address, file
offset, size). The pieces of the body are then made slot by slot (`Lay.slotPiece`), each at its
slot's address and file offset and at most its size, so that the plan's own conditions
(`Plan.okB`) hold by construction (`FV/Link/Ld/LayoutProof.lean`). -/

/-- A placed part: the part, its address and file offset, its size, its output section's index
(from `1`), whether that output section has file bytes and whether it is thread-local
(`.tdata`, `.tbss`). -/
structure Slot where
  part : Part
  addr : Nat
  fo : Nat
  size : Nat
  out : Nat
  bits : Bool
  tls : Bool
  deriving Inhabited

/-- The placement's state: the output sections and closed segments so far, the address and
file offset reached, the open segment (start, kind), the TLS template (address, offset, file
size, memory size, alignment), the end of the file bytes, the `.tbss` address, the placed
parts. -/
structure PSt where
  outs : Array OutSec
  segs : Array Seg
  va : Nat
  off : Nat
  segVa : Nat
  segOff : Nat
  cur : Nat
  tls : Nat × Nat × Nat × Nat × Nat
  fileEnd : Nat
  tbssVa : Nat
  slots : Array Slot
  deriving Inhabited

/-- The headers' size: the ELF header and seven program headers (`PT_PHDR`, three `PT_LOAD`,
`PT_TLS`, `PT_GNU_EH_FRAME`, `PT_GNU_STACK`). -/
def hdrSize : Nat := 64 + 56 * 7

/-- The state before the first output section: the headers at the start of the `R` segment. -/
def PSt.init (base : Nat) : PSt :=
  { outs := #[], segs := #[], va := base + hdrSize, off := hdrSize, segVa := base, segOff := 0,
    cur := 0, tls := (0, 0, 0, 0, 1), fileEnd := hdrSize, tbssVa := 0, slots := #[] }

/-- The open segment, closed. -/
def PSt.seg (s : PSt) : Seg :=
  { kind := s.cur, vaddr := s.segVa, offset := s.segOff, filesz := s.fileEnd - s.segOff,
    memsz := s.va - s.segVa }

/-- The parts of an output section placed from address `a`, each aligned (`al`) and of size
`sz`; a part at `b` has file offset `soff + (b - start)`. -/
def placeParts (sz al : Part → Nat) (start soff out : Nat) (bits tl : Bool) :
    Nat → List Part → Array Slot → Nat × Array Slot
  | a, [], acc => (a, acc)
  | a, p :: ps, acc =>
    let b := alignUp a (al p)
    placeParts sz al start soff out bits tl (b + sz p) ps
      (acc.push { part := p, addr := b, fo := soff + (b - start), size := sz p, out, bits, tls := tl })

/-- A new segment of kind `k`, in a fresh 64 KiB page, when the kind changes (the open one
closed). -/
def PSt.openSeg (st : PSt) (k : Nat) : PSt :=
  if k != st.cur then
    let va := alignUp st.va 0x10000 + st.fileEnd % 0x10000
    { st with segs := st.segs.push st.seg, cur := k, off := st.fileEnd, va, segVa := va,
              segOff := st.fileEnd }
  else st

/-- An output section placed in the open segment (`sz`, `al`: its parts' sizes and alignments,
`nb`: the parts without file bytes). `.tbss` takes no address or file space: it follows
`.tdata` in the TLS template only. -/
def placeIn (sz al : Part → Nat) (nb : Part → Bool) (tlsAlign : Nat) (st : PSt) (s : OSec) :
    PSt :=
  let a0 := s.parts.foldl (fun m p => max m (al p)) (if s.name == ".tdata" then tlsAlign else 1)
  let tbss := s.name == ".tbss"
  let tdata := s.name == ".tdata"
  let nobits := tbss || s.name == ".bss" || s.parts.all nb
  let start := if tbss then alignUp st.tbssVa a0 else alignUp st.va a0
  let soff := if tbss then st.off else st.off + (start - st.va)
  let r := placeParts sz al start soff (st.outs.size + 1) (!nobits) (tdata || tbss) start s.parts.toList
    st.slots
  let a := r.1
  let size := a - start
  let flags := (if s.seg == 2 || tdata || tbss then shfWrite else 0) |||
    shfAlloc ||| (if s.seg == 1 then shfExec else 0) |||
    (if tdata || tbss then shfTls else 0)
  let ty := if nobits then shtNobits else if s.name == ".init_array" then shtInitArray
    else if s.name == ".fini_array" then shtFiniArray else shtProgbits
  let os : OutSec :=
    { name := s.name, type := ty, flags := flags, addr := start, off := soff, size := size, align := a0 }
  let off := if tbss then st.off else st.off + (a - st.va)
  { st with
    outs := st.outs.push os, slots := r.2,
    tls := if tdata then (start, soff, size, size, a0)
      else if tbss then (st.tls.1, st.tls.2.1, st.tls.2.2.1, a - st.tls.1, st.tls.2.2.2.2)
      else st.tls,
    tbssVa := if tdata then a else st.tbssVa,
    off := off, va := if tbss then st.va else a,
    fileEnd := if nobits then st.fileEnd else off }

/-- **One output section placed**: in a new segment when its kind changes. -/
def placeSec (sz al : Part → Nat) (nb : Part → Bool) (tlsAlign : Nat) (st : PSt) (s : OSec) :
    PSt :=
  placeIn sz al nb tlsAlign (st.openSeg s.seg) s

/-- `b` cut to at most `n` bytes. -/
def clampTo (n : Nat) (b : ByteArray) : ByteArray := if b.size ≤ n then b else b.extract 0 n

/-- The piece of slot `sl`: at its address and file offset, the bytes `bytes` cut to its size,
the relocations `rels`. -/
def Slot.piece (sl : Slot) (bytes : ByteArray) (rels : List Rel) : Piece :=
  { addr := sl.addr, fo := sl.fo, bytes := clampTo sl.size bytes, rels }

/-- The GOT slot's key of symbol `j` of file `fi` (a local symbol: per file and index). -/
def gotKey (files : Array Obj) (fi j : Nat) : String :=
  let sy := files[fi]!.syms[j]!
  if sy.bind == 0 || j < files[fi]!.firstGlobal then s!"\x00{fi}:{j}" else sy.name

/-- **The layout's decisions** before any placement: the output sections (unsorted), the kept
`.eh_frame` records (offsets in the output `.eh_frame`, its size with the terminator, the FDE
count, the CIEs' and records' output offsets, each input `.eh_frame`'s start), the GOT's
symbols. -/
structure LayD where
  osecs : Array OSec
  ehs : Array EhOut
  ehTotal : Nat
  fdeCount : Nat
  cieOut : Std.HashMap (Nat × Nat × Nat) Nat
  pieceOut : Std.HashMap (Nat × Nat × Nat) Nat
  ehStart : Std.HashMap (Nat × Nat) Nat
  gotSlot : Std.HashMap String Nat
  gotSyms : Array (Nat × Nat)

namespace LayD

variable (D : LayD) (files : Array Obj)

/-- A part's size. -/
def partSize (p : Part) : Nat := match p with
  | .input (f, i) => files[f]!.secs[i]!.size
  | .got => 8 * D.gotSyms.size
  | .eh => D.ehTotal
  | .ehHdr => 12 + 8 * D.fdeCount
  | .common f k => files[f]!.syms[k]!.size

/-- A part's alignment (at least `1`). -/
def partAlign (p : Part) : Nat := match p with
  | .input (f, i) => max files[f]!.secs[i]!.align 1
  | .got | .eh => 8
  | .ehHdr => 4
  | .common f k => max files[f]!.syms[k]!.value 1

/-- A part without file bytes. -/
def partNb (p : Part) : Bool := match p with
  | .input (f, i) => files[f]!.secs[i]!.type == shtNobits
  | .common _ _ => true
  | _ => false

end LayD

/-- **The layout**: its decisions, the output sections in order, the placement and the places it
gives (input sections' addresses and output section indices, the synthesized parts' and common
symbols' addresses). -/
structure Lay extends LayD where
  sorted : Array OSec
  pst : PSt
  segs : List Seg
  secAddr : Array (Array Nat)
  secOut : Array (Array Nat)
  partAddr : Std.HashMap String Nat
  commonAddr : Std.HashMap (Nat × Nat) Nat

/-- The order of output sections: by segment, then rank (C-identifier sections by name). -/
def osecLt (a b : OSec) : Bool :=
  a.seg < b.seg || (a.seg == b.seg && (outRank a.name a.seg < outRank b.name b.seg ||
    (outRank a.name a.seg == outRank b.name b.seg && a.name < b.name)))

/-- An init/fini array's parts by priority (a stable sort: by priority, then input order). -/
def arrOrder (files : Array Obj) (s : OSec) : OSec :=
  if s.name == ".init_array" || s.name == ".fini_array" || s.name == ".preinit_array" then
    let prio (p : Part) : Nat := match p with
      | .input (f, i) => arrPrio files[f]!.secs[i]!.name
      | _ => 65536
    let idx := s.parts.mapIdx fun i p => (prio p, i, p)
    { s with parts := (idx.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)).map (·.2.2) }
  else s

/-- The output sections in order (`osecLt`, segment by segment), init/fini arrays' parts by
priority. -/
def sortOSecs (files : Array Obj) (osecs : Array OSec) : Array OSec :=
  (([0, 1, 2].flatMap fun k =>
    (osecs.toList.filter (·.seg == k)).mergeSort fun a b => !osecLt b a).map (arrOrder files)).toArray

/-- **The layout's decisions** of the resolved inputs (`LayD`). -/
def layDecide (st : St) (g : GcOut) : LayD := Id.run do
  let files := st.files
  let live := g.live
  -- output sections
  let mut byName : Std.HashMap String Nat := {}
  let mut osecs : Array OSec := #[]
  let addPart (osecs : Array OSec) (byName : Std.HashMap String Nat) (n : String) (seg : Nat)
      (p : Part) : Array OSec × Std.HashMap String Nat :=
    match byName[n]? with
    | some i => (osecs.modify i fun s => { s with parts := s.parts.push p }, byName)
    | none => (osecs.push { name := n, seg, parts := #[p] }, byName.insert n osecs.size)
  for fi in [0:files.size] do
    let f := files[fi]!
    for si in [0:f.secs.size] do
      if live[fi]![si]! then
        let (n, seg) := outOf f.secs[si]!
        (osecs, byName) := addPart osecs byName n seg (.input (fi, si))
  for (_, d) in st.syms.toList do
    if let .common f k := d then
      (osecs, byName) := addPart osecs byName ".bss" 2 (.common f k)
  -- `.eh_frame`: CIEs used by kept FDEs and the FDEs of live sections, in input order
  let placedIn (t : SecId) : Bool := (live[t.1]?.bind (·[t.2]?)).getD false
  let mut ehs : Array EhOut := #[]
  let mut ehSize := 0
  let mut fdeCount := 0
  let mut cieOut : Std.HashMap (Nat × Nat × Nat) Nat := {}
  let mut pieceOut : Std.HashMap (Nat × Nat × Nat) Nat := {}
  let mut ehStart : Std.HashMap (Nat × Nat) Nat := {}
  for fi in [0:files.size] do
    for ei in [0:g.eh[fi]!.size] do
      ehStart := ehStart.insert (fi, ei) ehSize
      let ps := g.eh[fi]![ei]!.pieces
      let rs := g.eh[fi]![ei]!.relas
      let mut byOff : Std.HashMap Nat Nat := {}
      for k in [0:rs.size] do
        byOff := byOff.insert rs[k]!.off k
      let keep (p : EhPiece) : Bool :=
        match byOff[p.off + 8]? with
        | some k => match st.target fi rs[k]!.sym with
          | .sec t _ _ => placedIn t
          | _ => false
        | none => false
      let used : Std.HashSet Nat := ps.foldl (fun s p => if !p.cie && keep p then s.insert p.cieOff else s) {}
      for p in ps do
        if (p.cie && used.contains p.off) || (!p.cie && keep p) then
          if p.cie then cieOut := cieOut.insert (fi, ei, p.off) ehSize else fdeCount := fdeCount + 1
          pieceOut := pieceOut.insert (fi, ei, p.off) ehSize
          ehs := ehs.push { file := fi, ei, piece := p, out := ehSize }
          ehSize := ehSize + p.size
  let ehTotal := if ehs.isEmpty then 0 else ehSize + 4
  if ehTotal > 0 then
    (osecs, byName) := addPart osecs byName ".eh_frame" 0 .eh
    (osecs, byName) := addPart osecs byName ".eh_frame_hdr" 0 .ehHdr
  -- GOT slots: one per symbol a GOT relocation of a live section names
  let mut gotSlot : Std.HashMap String Nat := {}
  let mut gotSyms : Array (Nat × Nat) := #[]
  for fi in [0:files.size] do
    for si in [0:files[fi]!.secs.size] do
      if live[fi]![si]! then
        for r in files[fi]!.relas si do
          if gotType r.type then
            let k := gotKey files fi r.sym
            if !gotSlot.contains k then
              gotSlot := gotSlot.insert k gotSyms.size
              gotSyms := gotSyms.push (fi, r.sym)
  if !gotSyms.isEmpty then
    (osecs, byName) := addPart osecs byName ".got" 0 .got
  -- `PT_TLS` is always present (`tlsOkB`): an empty `.tdata` when nothing is thread-local
  if !byName.contains ".tdata" then
    byName := byName.insert ".tdata" osecs.size
    osecs := osecs.push { name := ".tdata", seg := 0, parts := #[] }
  return { osecs, ehs, ehTotal, fdeCount, cieOut, pieceOut, ehStart, gotSlot, gotSyms }

/-- The places the placement gives, one slot at a time (`slotMaps`). -/
def slotStep (m : Array (Array Nat) × Array (Array Nat) × Std.HashMap String Nat ×
    Std.HashMap (Nat × Nat) Nat) (sl : Slot) :
    Array (Array Nat) × Array (Array Nat) × Std.HashMap String Nat × Std.HashMap (Nat × Nat) Nat :=
  match sl.part with
  | .input (f, i) => (m.1.modify f (·.set! i sl.addr), m.2.1.modify f (·.set! i sl.out), m.2.2)
  | .common f k => (m.1, m.2.1, m.2.2.1, m.2.2.2.insert (f, k) sl.addr)
  | .got => (m.1, m.2.1, m.2.2.1.insert "got" sl.addr, m.2.2.2)
  | .eh => (m.1, m.2.1, m.2.2.1.insert "eh" sl.addr, m.2.2.2)
  | .ehHdr => (m.1, m.2.1, m.2.2.1.insert "ehHdr" sl.addr, m.2.2.2)

/-- The places the placement gives: per input section its address and output section index,
the synthesized parts' and the common symbols' addresses. -/
def slotMaps (files : Array Obj) (slots : Array Slot) :
    Array (Array Nat) × Array (Array Nat) × Std.HashMap String Nat × Std.HashMap (Nat × Nat) Nat :=
  slots.foldl slotStep
    (files.map fun f => Array.replicate f.secs.size 0, files.map fun f => Array.replicate f.secs.size 0, {}, {})

/-- The TLS template's alignment: the largest of `.tdata`'s and `.tbss`'s parts. -/
def tlsAlignOf (al : Part → Nat) (sorted : Array OSec) : Nat :=
  sorted.foldl (fun m s => if s.name == ".tdata" || s.name == ".tbss" then
    s.parts.foldl (fun m p => max m (al p)) m else m) 1

/-- **The layout** of the resolved inputs: the decisions (`layDecide`), the output sections
sorted (`sortOSecs`) and placed (`placeSec`), from the base address after the headers. -/
def layPre (o : Opts) (st : St) (g : GcOut) : Lay :=
  let D := layDecide st g
  let files := st.files
  let sorted := sortOSecs files D.osecs
  let pst := sorted.foldl (placeSec (D.partSize files) (LayD.partAlign files) (LayD.partNb files)
    (tlsAlignOf (LayD.partAlign files) sorted)) (PSt.init o.base)
  let (secAddr, secOut, partAddr, commonAddr) := slotMaps files pst.slots
  { D with sorted, pst, segs := (pst.segs.push pst.seg).toList, secAddr, secOut, partAddr,
           commonAddr }

namespace Lay

variable (L : Lay) (o : Opts) (st : St) (g : GcOut)

/-- The output section `n`'s address range. -/
def outRange (n : String) : Option (Nat × Nat) :=
  (L.pst.outs.find? (·.name == n)).map fun s => (s.addr, s.addr + s.size)

/-- The values of the linker-defined symbols with fixed names. -/
def synthFixed (n : String) : Option Nat :=
  let lastSeg := L.segs.getLastD default
  let textEnd := ((L.segs.find? (·.kind == 1)).map fun s => s.vaddr + s.memsz).getD 0
  let dataEnd := lastSeg.vaddr + lastSeg.filesz
  let arr (k : String) (e : Bool) : Nat := match L.outRange k with
    | some (a, b) => if e then b else a
    | none => dataEnd
  match n with
  | "__init_array_start" => some (arr ".init_array" false)
  | "__init_array_end" => some (arr ".init_array" true)
  | "__fini_array_start" => some (arr ".fini_array" false)
  | "__fini_array_end" => some (arr ".fini_array" true)
  | "__preinit_array_start" => some (arr ".preinit_array" false)
  | "__preinit_array_end" => some (arr ".preinit_array" true)
  | "_end" | "end" | "__end" => some (lastSeg.vaddr + lastSeg.memsz)
  | "_etext" | "etext" | "__etext" => some textEnd
  | "_edata" | "edata" => some dataEnd
  | "__bss_start" => some ((L.outRange ".bss").elim dataEnd (·.1))
  | "__ehdr_start" | "__executable_start" => some o.base
  | "_GLOBAL_OFFSET_TABLE_" => some (L.partAddr.getD "got" 0)
  | "__eh_frame_start" => L.partAddr["eh"]?
  | "__eh_frame_hdr_start" => L.partAddr["ehHdr"]?
  | _ => none

/-- **The values of the linker-defined symbols**: `__start_X`/`__stop_X` (the output section
`X`'s bounds), the fixed names (`synthFixed`; none of them starts with `__start_` or
`__stop_`). -/
def synth (n : String) : Option Nat :=
  if n.startsWith "__start_" then (L.outRange (n.drop 8).toString).map (·.1)
  else if n.startsWith "__stop_" then (L.outRange (n.drop 7).toString).map (·.2)
  else L.synthFixed o n

/-- The output `.eh_frame`'s address. -/
def ehAddr : Nat := L.partAddr.getD "eh" 0

/-- **A symbol's value** (and whether it is an undefined weak one). -/
def value (fi j : Nat) : Except String (Int × Bool) :=
  let files := st.files
  match st.target fi j with
  | .sec t x _ =>
    if (g.live[t.1]?.bind (·[t.2]?)).getD false then pure ((L.secAddr[t.1]![t.2]! + x : Nat), false)
    else match g.eh[t.1]!.findIdx? (·.sec == t.2) with
    | some ei =>
      -- a place in an input `.eh_frame`: its record's place in the output one
      let ps := g.eh[t.1]![ei]!.pieces
      let start := L.ehAddr + L.ehStart.getD (t.1, ei) 0
      match ps.find? (fun p => p.off ≤ x ∧ x < p.off + p.size) with
      | some p => match L.pieceOut[(t.1, ei, p.off)]? with
        | some q => pure ((L.ehAddr + q + (x - p.off) : Nat), false)
        | none => pure ((start : Nat), false)
      | none => pure ((start : Nat), false)
    | none =>
      throw s!"{files[fi]!.name}: symbol {files[fi]!.syms[j]!.name} in a discarded section {files[t.1]!.secs[t.2]!.name} of {files[t.1]!.name}"
  | .abs v => pure (v, false)
  | .common f k => pure (L.commonAddr.getD (f, k) 0, false)
  | .undef n w => match L.synth o n with
    | some v => pure (v, false)
    | none => if w then pure (0, true) else throw s!"undefined symbol {n} (referenced from {files[fi]!.name})"

/-- **A relocation's inputs** at place `P`. -/
def relIn (fi : Nat) (r : Rela) (P : Nat) : Except String RelIn := do
  let (S, uw) ← L.value o st g fi r.sym
  let G : Int := (L.gotSlot[gotKey st.files fi r.sym]?.map fun k => (L.partAddr.getD "got" 0 + 8 * k : Nat)).getD 0
  let S := if uw && branchType r.type then (P : Int) + 4 - r.addend
    else if uw && (r.type == 275 || r.type == 274) then (P : Int) - r.addend else S
  let tlsStart := L.pst.tls.1
  let tpBase := alignUp 16 L.pst.tls.2.2.2.2
  pure { S, A := r.addend, P, G, tp := tpBase + (S + r.addend - tlsStart) }

/-- The GOT's bytes: each slot's symbol's link-time value. -/
def gotBytes : Except String ByteArray :=
  L.gotSyms.foldlM (fun got (fi, j) => do
    let (v, _) ← L.value o st g fi j
    pure (got ++ leBytes 8 (v % 2 ^ 64).toNat)) .empty

/-- One relocation of a kept `.eh_frame` record `e` (of the input `.eh_frame` `es`): resolved
at its place in the output `.eh_frame`; an FDE's function start goes to the `.eh_frame_hdr`
table. -/
def ehRel (e : EhOut) (acc : Array Rel × Array (Nat × Nat)) (r : Rela) :
    Except String (Array Rel × Array (Nat × Nat)) := do
  let P := L.ehAddr + e.out + (r.off - e.piece.off)
  let ri ← L.relIn o st g e.file r P
  let rels := acc.1.push { off := e.out + (r.off - e.piece.off), ty := r.type, ri }
  if !e.piece.cie && r.off == e.piece.off + 8 then
    let (v, _) ← L.value o st g e.file r.sym
    pure (rels, acc.2.push (((v + r.addend) % 2 ^ 64).toNat, L.ehAddr + e.out))
  else pure (rels, acc.2)

/-- A kept `.eh_frame` record's bytes (its CIE pointer rewritten for an FDE). -/
def ehBytes (e : EhOut) (es : EhSec) : ByteArray :=
  let f := st.files[e.file]!
  let src := f.secs[es.sec]!
  let bytes := f.data.extract (src.off + e.piece.off) (src.off + e.piece.off + e.piece.size)
  if !e.piece.cie then writeLE bytes 4 4 (e.out + 4 - L.cieOut.getD (e.file, e.ei, e.piece.cieOff) 0)
  else bytes

/-- One kept `.eh_frame` record placed in the output `.eh_frame` (`ehOut`). -/
def ehRec (acc : ByteArray × Array Rel × Array (Nat × Nat)) (e : EhOut) :
    Except String (ByteArray × Array Rel × Array (Nat × Nat)) :=
  match g.eh[e.file]![e.ei]? with
  | none => pure acc
  | some es => do
    let rt ← (es.relasIn e.piece.off (e.piece.off + e.piece.size)).foldlM (L.ehRel o st g e)
      (acc.2.1, acc.2.2)
    pure (place acc.1 e.out (L.ehBytes st e es), rt.1, rt.2)

/-- **The output `.eh_frame`**: its bytes (each kept record at its offset, the CIE pointers
rewritten), its relocations, and the `.eh_frame_hdr` table (function start, FDE address). -/
def ehOut : Except String (ByteArray × Array Rel × Array (Nat × Nat)) :=
  L.ehs.foldlM (L.ehRec o st g) (⟨Array.replicate L.ehTotal 0⟩, #[], #[])

/-- The `.eh_frame_hdr` table's bytes. -/
def ehHdrBytes (table : Array (Nat × Nat)) : ByteArray :=
  let hAddr := L.partAddr.getD "ehHdr" 0
  let sortedT := table.qsort (fun a b => a.1 < b.1)
  sortedT.foldl (fun hdr (pc, fde) => hdr ++ leBytes 4 (((pc : Int) - hAddr) % 2 ^ 32).toNat ++
      leBytes 4 (((fde : Int) - hAddr) % 2 ^ 32).toNat)
    (leBytes 4 (1 + 0x1b * 256 + 0x03 * 65536 + 0x3b * 2 ^ 24) ++
      leBytes 4 (((L.ehAddr : Int) - (hAddr + 4)) % 2 ^ 32).toNat ++ leBytes 4 sortedT.size)

/-- An input section's piece in its slot (none for `SHT_NOBITS`), with its relocations resolved
at the section's address (sorted by offset: the data check, `FV/Link/Ld/Data.lean`, walks them
in order). -/
def inputPiece (sl : Slot) (fi si : Nat) : Except String (Option Piece) := do
  let f := st.files[fi]!
  let s := f.secs[si]!
  if s.type == shtNobits then return none
  let rels ← (f.relas si).toList.mapM fun r => do
    let ri ← (L.relIn o st g fi r (L.secAddr[fi]![si]! + r.off)).mapError (s!"{f.name}({s.name})+{r.off}: " ++ ·)
    pure ({ off := r.off, ty := r.type, ri } : Rel)
  return some (sl.piece (f.data.extract s.off (s.off + s.size)) (rels.mergeSort fun r r' => decide (r.off ≤ r'.off)))

/-- **The piece of a placed part** (none without file bytes): an input section's, the GOT,
`.eh_frame`, `.eh_frame_hdr`. -/
def slotPiece (got : ByteArray) (eh : ByteArray × Array Rel) (hdr : ByteArray) (sl : Slot) :
    Except String (Option Piece) :=
  if !sl.bits then pure none else
  match sl.part with
  | .input fs => L.inputPiece o st g sl fs.1 fs.2
  | .got => pure (some (sl.piece got []))
  | .eh => pure (some (sl.piece eh.1 eh.2.toList))
  | .ehHdr => pure (some (sl.piece hdr []))
  | .common _ _ => pure none

/-- **The pieces of the body**: one per placed part with file bytes, in placement order. -/
def pieces : Except String (List Piece) := do
  let got ← L.gotBytes o st g
  let (eh, rels, table) ← L.ehOut o st g
  let ps ← L.pst.slots.toList.mapM (L.slotPiece o st g got (eh, rels) (L.ehHdrBytes table))
  return ps.filterMap id

/-- **The symbols**: locals, then globals (the winners), then linker-defined ones; and per input
section, its symbols for the map. -/
def syms : Array OutSym × Array (Array (Array (Nat × String))) := Id.run do
  let files := st.files
  let live := g.live
  let tlsStart := L.pst.tls.1
  let mut locals : Array OutSym := #[]
  let mut globals : Array OutSym := #[]
  let mut mapSyms : Array (Array (Array (Nat × String))) := files.map fun f => Array.replicate f.secs.size #[]
  for fi in [0:files.size] do
    let f := files[fi]!
    for j in [1:f.syms.size] do
      let sy := f.syms[j]!
      if sy.name.isEmpty || sy.type == 3 || sy.type == 4 || sy.name.startsWith "$" then continue
      let isLocal := sy.bind == 0 || j < f.firstGlobal
      let win := isLocal || (match st.syms[sy.name]? with
        | some (.defd f' k _) => f' == fi && k == j
        | _ => false)
      if !win || !sy.inSec || !live[fi]![sy.shndx]! then continue
      let a := L.secAddr[fi]![sy.shndx]! + sy.value
      let tlsSym := sy.type == 6
      let os : OutSym := { name := sy.name, value := if tlsSym then a - tlsStart else a, size := sy.size,
                           info := (if isLocal then 0 else sy.bind) * 16 + sy.type,
                           shndx := L.secOut[fi]![sy.shndx]! }
      if isLocal then locals := locals.push os else globals := globals.push os
      mapSyms := mapSyms.modify fi (·.modify sy.shndx (·.push (a, sy.name)))
  for (n, d) in st.syms.toList do
    match d with
    | .common f k =>
      globals := globals.push { name := n, value := L.commonAddr.getD (f, k) 0,
                                size := files[f]!.syms[k]!.size, info := 16 + 1,
                                shndx := (L.pst.outs.findIdx? (·.name == ".bss")).elim 0 (· + 1) }
    | .undef _ => if let some v := L.synth o n then globals := globals.push { name := n, value := v, info := 16, shndx := shnAbs }
    | _ => pure ()
  return (locals ++ globals, mapSyms)

/-- The entry symbol's address. -/
def entry : Except String Nat :=
  match st.syms[o.entry]? with
  | some (.defd f k _) =>
    let sy := st.files[f]!.syms[k]!
    if sy.inSec && g.live[f]![sy.shndx]! then pure (L.secAddr[f]![sy.shndx]! + sy.value)
    else throw s!"entry {o.entry} not placed"
  | _ => throw s!"undefined entry symbol {o.entry}"

/-- **The link map** (lld's format). -/
def map (mapSyms : Array (Array (Array (Nat × String)))) : String := Id.run do
  let files := st.files
  let outs := L.pst.outs
  let mut map := "             VMA              LMA     Size Align Out     In      Symbol\n"
  for i in [0:outs.size] do
    let os := outs[i]!
    map := map ++ mapLine os.addr os.size os.align 0 os.name
    for p in L.sorted[i]!.parts do
      match p with
      | .input (f, si) =>
        let s := files[f]!.secs[si]!
        map := map ++ mapLine L.secAddr[f]![si]! s.size (max s.align 1) 8 s!"{files[f]!.name}:({s.name})"
        for (a, n) in (((mapSyms[f]?.bind (·[si]?)).getD #[]).qsort fun x y => x.1 < y.1) do
          map := map ++ mapLine a 0 0 16 n
      | _ => pure ()
  return map

/-- **The plan** of the layout, with the pieces, the entry and the symbols. -/
def plan (entry : Nat) (pieces : List Piece) (syms : Array OutSym) : Plan :=
  let P := L.pst
  { base := o.base, entry, segs := L.segs, tlsAddr := P.tls.1, tlsOff := P.tls.2.1,
    tlsFilesz := P.tls.2.2.1, tlsMemsz := P.tls.2.2.2.1, tlsAlign := P.tls.2.2.2.2,
    ehOff := (P.outs.find? (·.name == ".eh_frame_hdr")).elim 0 (·.off),
    ehAddr := L.partAddr.getD "ehHdr" 0, ehSize := if L.ehTotal > 0 then 12 + 8 * L.fdeCount else 0,
    size := P.fileEnd, pieces, secs := P.outs, syms }

end Lay

/-- **The Lean static linker's layout** of the resolved inputs: the plan and the link map. -/
def layout (o : Opts) (st : St) (g : GcOut) : Except String (Plan × String) := do
  let L := layPre o st g
  let pieces ← L.pieces o st g
  let entry ← L.entry o st g
  let (syms, mapSyms) := L.syms o st g
  pure (L.plan o entry pieces syms, L.map st mapSyms)

/-- **Links** the inputs: resolution (the entry and `-u` symbols as roots), `--gc-sections`,
layout, the image of the plan (`assemble`). -/
def link (o : Opts) (ins : List Input) : Except String LinkOut := do
  let roots := o.entry :: o.undefs
  let st ← resolve roots ins
  let g ← st.gc roots o.gc
  let (plan, map) ← layout o st g
  let img ← assemble plan
  -- the writer's theorems (`FV/Link/Ld/WriteProof.lean`) assume the headers' values fit
  if !img.hdrFitsB then throw "the headers' values do not fit their fields (hdrFitsB)"
  if !img.tabsFitB then throw "the tables' values do not fit their fields (tabsFitB)"
  pure { img, map, plan }

end Link.Ld
