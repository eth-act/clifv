import FV.Link.Ld.Resolve
import FV.Link.Ld.Reloc
import FV.Link.Ld.Write

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

/-- The result: the image description and the link map's text. -/
structure LinkOut where
  img : Img
  map : String

/-- `n` rounded up to a multiple of `a` (`a ≥ 1`). -/
def alignUp (n a : Nat) : Nat := (n + a - 1) / max a 1 * max a 1

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
  piece : EhPiece
  out : Nat
  deriving Inhabited

/-- **The Lean static linker** on the resolved inputs. -/
def layout (o : Opts) (st : St) (g : GcOut) : Except String LinkOut := do
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
  let mut cieOut : Std.HashMap (Nat × Nat) Nat := {}
  let mut pieceOut : Std.HashMap (Nat × Nat) Nat := {}
  let mut ehStart : Array Nat := Array.replicate files.size 0
  for fi in [0:files.size] do
    ehStart := ehStart.set! fi ehSize
    if let some (_, ps, rs) := g.eh[fi]! then
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
          if p.cie then cieOut := cieOut.insert (fi, p.off) ehSize else fdeCount := fdeCount + 1
          pieceOut := pieceOut.insert (fi, p.off) ehSize
          ehs := ehs.push { file := fi, piece := p, out := ehSize }
          ehSize := ehSize + p.size
  let ehTotal := if ehs.isEmpty then 0 else ehSize + 4
  if ehTotal > 0 then
    (osecs, byName) := addPart osecs byName ".eh_frame" 0 .eh
    (osecs, byName) := addPart osecs byName ".eh_frame_hdr" 0 .ehHdr
  -- GOT slots: one per symbol a GOT relocation of a live section names
  let gotKey (fi j : Nat) : String :=
    let sy := files[fi]!.syms[j]!
    if sy.bind == 0 || j < files[fi]!.firstGlobal then s!"\x00{fi}:{j}" else sy.name
  let mut gotSlot : Std.HashMap String Nat := {}
  let mut gotSyms : Array (Nat × Nat) := #[]
  for fi in [0:files.size] do
    for si in [0:files[fi]!.secs.size] do
      if live[fi]![si]! then
        for r in files[fi]!.relas si do
          if gotType r.type then
            let k := gotKey fi r.sym
            if !gotSlot.contains k then
              gotSlot := gotSlot.insert k gotSyms.size
              gotSyms := gotSyms.push (fi, r.sym)
  if !gotSyms.isEmpty then
    (osecs, byName) := addPart osecs byName ".got" 0 .got
  -- `PT_TLS` is always present (`tlsOkB`): an empty `.tdata` when nothing is thread-local
  if !byName.contains ".tdata" then
    byName := byName.insert ".tdata" osecs.size
    osecs := osecs.push { name := ".tdata", seg := 0, parts := #[] }
  -- sort: by segment, then rank (C-identifier sections by name), init/fini arrays by priority
  let sorted := (osecs.qsort fun a b =>
    a.seg < b.seg || (a.seg == b.seg && (outRank a.name a.seg < outRank b.name b.seg ||
      (outRank a.name a.seg == outRank b.name b.seg && a.name < b.name)))).map fun s =>
    if s.name == ".init_array" || s.name == ".fini_array" || s.name == ".preinit_array" then
      let prio (p : Part) : Nat := match p with
        | .input (f, i) => arrPrio files[f]!.secs[i]!.name
        | _ => 65536
      -- a stable sort: by priority, then input order
      let idx := s.parts.mapIdx fun i p => (prio p, i, p)
      { s with parts := (idx.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)).map (·.2.2) }
    else s
  -- sizes and alignments of parts
  let partSize (p : Part) : Nat := match p with
    | .input (f, i) => files[f]!.secs[i]!.size
    | .got => 8 * gotSyms.size
    | .eh => ehTotal
    | .ehHdr => 12 + 8 * fdeCount
    | .common f k => files[f]!.syms[k]!.size
  let partAlign (p : Part) : Nat := match p with
    | .input (f, i) => max files[f]!.secs[i]!.align 1
    | .got | .eh => 8
    | .ehHdr => 4
    | .common f k => max files[f]!.syms[k]!.value 1
  let nph := 7
  -- addresses
  let mut secAddr : Array (Array Nat) := files.map fun f => Array.replicate f.secs.size 0
  let mut secOut : Array (Array Nat) := files.map fun f => Array.replicate f.secs.size 0
  let mut partAddr : Std.HashMap String Nat := {}
  let mut commonAddr : Std.HashMap (Nat × Nat) Nat := {}
  let mut outs : Array OutSec := #[]
  let mut segs : Array (Nat × Nat × Nat × Nat × Nat) := #[]   -- kind, vaddr, offset, filesz, memsz
  let mut va := o.base
  let mut off := 0
  let mut segStart : Nat × Nat := (o.base, 0)
  let mut cur := 0
  let mut tls : Nat × Nat × Nat × Nat × Nat := (0, 0, 0, 0, 1)  -- vaddr, offset, filesz, memsz, align
  let tlsAlign := sorted.foldl (fun m s => if s.name == ".tdata" || s.name == ".tbss" then
      s.parts.foldl (fun m p => max m (partAlign p)) m else m) 1
  va := va + 64 + 56 * nph
  off := off + 64 + 56 * nph
  let mut fileEnd := 0
  let mut tbssVa := 0
  for s in sorted do
    if s.seg != cur then
      -- close the segment, open the next in a fresh 64 KiB page
      segs := segs.push (cur, segStart.1, segStart.2, fileEnd - segStart.2, va - segStart.1)
      cur := s.seg
      off := fileEnd
      va := alignUp va 0x10000 + off % 0x10000
      segStart := (va, off)
    let a0 := s.parts.foldl (fun m p => max m (partAlign p)) (if s.name == ".tdata" then tlsAlign else 1)
    let nobits := s.name == ".tbss" || s.name == ".bss" ||
      s.parts.all (fun p => match p with
        | .input (f, i) => files[f]!.secs[i]!.type == shtNobits
        | .common _ _ => true
        | _ => false)
    let start0 := if s.name == ".tbss" then alignUp tbssVa a0 else alignUp va a0
    let mut a := start0
    for p in s.parts do
      a := alignUp a (partAlign p)
      match p with
      | .input (f, i) =>
        secAddr := secAddr.modify f (·.set! i a)
        secOut := secOut.modify f (·.set! i (outs.size + 1))
      | .common f k => commonAddr := commonAddr.insert (f, k) a
      | .got => partAddr := partAddr.insert "got" a
      | .eh => partAddr := partAddr.insert "eh" a
      | .ehHdr => partAddr := partAddr.insert "ehHdr" a
      a := a + partSize p
    let size := a - start0
    let soff := if s.name == ".tbss" then off else off + (start0 - va)
    let flags := (if s.seg == 2 || s.name == ".tdata" || s.name == ".tbss" then shfWrite else 0) |||
      shfAlloc ||| (if s.seg == 1 then shfExec else 0) |||
      (if s.name == ".tdata" || s.name == ".tbss" then shfTls else 0)
    let ty := if nobits then shtNobits else if s.name == ".init_array" then shtInitArray
      else if s.name == ".fini_array" then shtFiniArray else shtProgbits
    outs := outs.push { name := s.name, type := ty, flags, addr := start0, off := soff, size, align := a0 }
    if s.name == ".tdata" then
      tls := (start0, soff, size, size, a0)
      tbssVa := a
    if s.name == ".tbss" then
      tls := (tls.1, tls.2.1, tls.2.2.1, a - tls.1, tls.2.2.2.2)
    else
      off := off + (a - va)
      va := a
      if !nobits then fileEnd := off
  segs := segs.push (cur, segStart.1, segStart.2, fileEnd - segStart.2, va - segStart.1)
  -- linker-defined symbols
  let outRange (n : String) : Option (Nat × Nat) :=
    (outs.find? (·.name == n)).map fun s => (s.addr, s.addr + s.size)
  let lastSeg := segs.back!.2
  let textEnd := ((segs.find? (·.1 == 1)).map fun s => s.2.1 + s.2.2.2.2).getD 0
  let dataEnd := lastSeg.1 + lastSeg.2.2.1
  let synth (n : String) : Option Nat :=
    let arr (k : String) (e : Bool) : Nat := match outRange k with
      | some (a, b) => if e then b else a
      | none => dataEnd
    match n with
    | "__init_array_start" => some (arr ".init_array" false)
    | "__init_array_end" => some (arr ".init_array" true)
    | "__fini_array_start" => some (arr ".fini_array" false)
    | "__fini_array_end" => some (arr ".fini_array" true)
    | "__preinit_array_start" => some (arr ".preinit_array" false)
    | "__preinit_array_end" => some (arr ".preinit_array" true)
    | "_end" | "end" | "__end" => some (lastSeg.1 + lastSeg.2.2.2)
    | "_etext" | "etext" | "__etext" => some textEnd
    | "_edata" | "edata" => some dataEnd
    | "__bss_start" => some ((outRange ".bss").elim dataEnd (·.1))
    | "__ehdr_start" | "__executable_start" => some o.base
    | "_GLOBAL_OFFSET_TABLE_" => some (partAddr.getD "got" 0)
    | "__eh_frame_start" => partAddr["eh"]?
    | "__eh_frame_hdr_start" => partAddr["ehHdr"]?
    | _ =>
      if n.startsWith "__start_" then (outRange (n.drop 8).toString).map (·.1)
      else if n.startsWith "__stop_" then (outRange (n.drop 7).toString).map (·.2)
      else none
  let tlsStart := tls.1
  let ehAddr := partAddr.getD "eh" 0
  let tlsBase := alignUp 16 tls.2.2.2.2
  -- symbol values: (value, undefined weak)
  let value (fi j : Nat) : Except String (Int × Bool) :=
    match st.target fi j with
    | .sec t x _ =>
      if placedIn t then pure ((secAddr[t.1]![t.2]! + x : Nat), false)
      else if (g.eh[t.1]!.map (·.1)) == some t.2 then
        -- a place in an input `.eh_frame`: its record's place in the output one
        let ps := (g.eh[t.1]!.map (·.2.1)).getD #[]
        match ps.find? (fun p => p.off ≤ x ∧ x < p.off + p.size) with
        | some p => match pieceOut[(t.1, p.off)]? with
          | some q => pure ((ehAddr + q + (x - p.off) : Nat), false)
          | none => pure ((ehAddr + ehStart[t.1]! : Nat), false)
        | none => pure ((ehAddr + ehStart[t.1]! : Nat), false)
      else throw s!"{files[fi]!.name}: symbol {files[fi]!.syms[j]!.name} in a discarded section {files[t.1]!.secs[t.2]!.name} of {files[t.1]!.name}"
    | .abs v => pure (v, false)
    | .common f k => pure (commonAddr.getD (f, k) 0, false)
    | .undef n w => match synth n with
      | some v => pure (v, false)
      | none => if w then pure (0, true) else throw s!"undefined symbol {n} (referenced from {files[fi]!.name})"
  -- the body: segment bytes
  let mut body := ByteArray.mk (Array.replicate fileEnd 0)
  let gotAddr := partAddr.getD "got" 0
  let relIn (fi : Nat) (r : Rela) (P : Nat) : Except String (RelIn × Bool) := do
    let (S, uw) ← value fi r.sym
    let G : Int := (gotSlot[gotKey fi r.sym]?.map fun k => (gotAddr + 8 * k : Nat)).getD 0
    let S := if uw && branchType r.type then (P : Int) + 4 - r.addend
      else if uw && (r.type == 275 || r.type == 274) then (P : Int) - r.addend else S
    pure ({ S, A := r.addend, P, G, tp := tlsBase + (S + r.addend - tlsStart) }, uw)
  let apply (body : ByteArray) (fi : Nat) (r : Rela) (P fo : Nat) : Except String ByteArray := do
    let (ri, _) ← relIn fi r P
    let w := relocWidth r.type
    let v ← (relocVal r.type ri (rdLE body fo w)).mapError
      (s!"{files[fi]!.name}+{r.off}: " ++ ·)
    pure (putLE body fo w v)
  for fi in [0:files.size] do
    let f := files[fi]!
    for si in [0:f.secs.size] do
      if live[fi]![si]! && f.secs[si]!.type != shtNobits && !(f.secs[si]!.has shfTls && f.secs[si]!.type == shtNobits) then
        let s := f.secs[si]!
        let oo := outs[secOut[fi]![si]! - 1]!
        let fo := oo.off + (secAddr[fi]![si]! - oo.addr)
        body := f.data.copySlice s.off body fo s.size
        for r in f.relas si do
          body ← apply body fi r (secAddr[fi]![si]! + r.off) (fo + r.off)
  -- the GOT
  let gotOff := (outs.find? (·.name == ".got")).elim 0 (·.off)
  for k in [0:gotSyms.size] do
    let (fi, j) := gotSyms[k]!
    let (v, _) ← value fi j
    body := putLE body (gotOff + 8 * k) 8 (v % 2 ^ 64).toNat
  -- `.eh_frame` and `.eh_frame_hdr`
  let ehOff := (outs.find? (·.name == ".eh_frame")).elim 0 (·.off)
  let mut table : Array (Nat × Nat) := #[]
  for e in ehs do
    if let some (es, _, rs) := g.eh[e.file]! then
      let f := files[e.file]!
      let src := f.secs[es]!
      let fo := ehOff + e.out
      body := f.data.copySlice (src.off + e.piece.off) body fo e.piece.size
      if !e.piece.cie then
        let c := cieOut.getD (e.file, e.piece.cieOff) 0
        body := putLE body (fo + 4) 4 (e.out + 4 - c)
      for r in rs do
        if r.off ≥ e.piece.off && r.off < e.piece.off + e.piece.size then
          let P := ehAddr + e.out + (r.off - e.piece.off)
          body ← apply body e.file r P (fo + (r.off - e.piece.off))
          if !e.piece.cie && r.off == e.piece.off + 8 then
            let (v, _) ← value e.file r.sym
            table := table.push (((v + r.addend) % 2 ^ 64).toNat, ehAddr + e.out)
  if ehTotal > 0 then
    let hAddr := partAddr.getD "ehHdr" 0
    let hOff := (outs.find? (·.name == ".eh_frame_hdr")).elim 0 (·.off)
    let sortedT := table.qsort (fun a b => a.1 < b.1)
    body := putLE body hOff 4 (1 + 0x1b * 256 + 0x03 * 65536 + 0x3b * 2 ^ 24)
    body := putLE body (hOff + 4) 4 (((ehAddr : Int) - (hAddr + 4)) % 2 ^ 32).toNat
    body := putLE body (hOff + 8) 4 sortedT.size
    for i in [0:sortedT.size] do
      let (pc, fde) := sortedT[i]!
      body := putLE body (hOff + 12 + 8 * i) 4 (((pc : Int) - hAddr) % 2 ^ 32).toNat
      body := putLE body (hOff + 16 + 8 * i) 4 (((fde : Int) - hAddr) % 2 ^ 32).toNat
  -- program headers
  let segPh (s : Nat × Nat × Nat × Nat × Nat) : Phdr :=
    let (k, v, of, fs, ms) := s
    { type := 1, flags := if k == 0 then 4 else if k == 1 then 5 else 6, offset := of, vaddr := v,
      filesz := fs, memsz := ms, align := 0x10000 }
  let hdrA := partAddr.getD "ehHdr" 0
  let phs : List Phdr := [
    { type := 6, flags := 4, offset := 64, vaddr := o.base + 64, filesz := 56 * (4 + segs.size), memsz := 56 * (4 + segs.size), align := 8 }
  ] ++ segs.toList.map segPh ++ [
    { type := 7, flags := 4, offset := tls.2.1, vaddr := tls.1, filesz := tls.2.2.1, memsz := tls.2.2.2.1, align := tls.2.2.2.2 },
    { type := 0x6474e550, flags := 4, offset := (outs.find? (·.name == ".eh_frame_hdr")).elim 0 (·.off),
      vaddr := hdrA, filesz := if ehTotal > 0 then 12 + 8 * fdeCount else 0,
      memsz := if ehTotal > 0 then 12 + 8 * fdeCount else 0, align := 4 },
    { type := 0x6474e551, flags := 6, offset := 0, vaddr := 0, filesz := 0, memsz := 0, align := 0 }]
  -- symbols: locals, then globals (the winners), then linker-defined ones
  let mut locals : Array OutSym := #[]
  let mut globals : Array OutSym := #[]
  let mut mapSyms : Std.HashMap SecId (Array (Nat × String)) := {}
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
      let a := secAddr[fi]![sy.shndx]! + sy.value
      let tlsSym := sy.type == 6
      let os : OutSym := { name := sy.name, value := if tlsSym then a - tlsStart else a, size := sy.size,
                           info := (if isLocal then 0 else sy.bind) * 16 + sy.type,
                           shndx := secOut[fi]![sy.shndx]! }
      if isLocal then locals := locals.push os else globals := globals.push os
      mapSyms := mapSyms.insert (fi, sy.shndx) ((mapSyms.getD (fi, sy.shndx) #[]).push (a, sy.name))
  for (n, d) in st.syms.toList do
    match d with
    | .common f k =>
      globals := globals.push { name := n, value := commonAddr.getD (f, k) 0,
                                size := files[f]!.syms[k]!.size, info := 16 + 1,
                                shndx := (outs.findIdx? (·.name == ".bss")).elim 0 (· + 1) }
    | .undef _ => if let some v := synth n then globals := globals.push { name := n, value := v, info := 16, shndx := shnAbs }
    | _ => pure ()
  let entry ← match st.syms[o.entry]? with
    | some (.defd f k _) =>
      let sy := files[f]!.syms[k]!
      if sy.inSec && live[f]![sy.shndx]! then pure (secAddr[f]![sy.shndx]! + sy.value)
      else throw s!"entry {o.entry} not placed"
    | _ => throw s!"undefined entry symbol {o.entry}"
  -- the link map
  let mut map := "             VMA              LMA     Size Align Out     In      Symbol\n"
  for i in [0:outs.size] do
    let os := outs[i]!
    map := map ++ mapLine os.addr os.size os.align 0 os.name
    for p in sorted[i]!.parts do
      match p with
      | .input (f, si) =>
        let s := files[f]!.secs[si]!
        map := map ++ mapLine secAddr[f]![si]! s.size (max s.align 1) 8 s!"{files[f]!.name}:({s.name})"
        for (a, n) in ((mapSyms.getD (f, si) #[]).qsort fun x y => x.1 < y.1) do
          map := map ++ mapLine a 0 0 16 n
      | _ => pure ()
  pure { img := { entry, phs, body, secs := outs, syms := locals ++ globals }, map }

/-- **Links** the inputs: resolution (the entry and `-u` symbols as roots), `--gc-sections`,
layout. -/
def link (o : Opts) (ins : List Input) : Except String LinkOut := do
  let roots := o.entry :: o.undefs
  let st ← resolve roots ins
  let g ← st.gc roots o.gc
  let r ← layout o st g
  -- the writer's theorems (`FV/Link/Ld/WriteProof.lean`) assume the headers' values fit
  if !r.img.hdrFitsB then throw "the headers' values do not fit their fields (hdrFitsB)"
  if !r.img.tabsFitB then throw "the tables' values do not fit their fields (tabsFitB)"
  pure r

end Link.Ld
