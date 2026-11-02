import FV.Backend.Encode
import FV.Backend.Unwind

/-!
# ELF64 relocatable object writer (AArch64, little-endian)

`Backend.elfObject` turns laid-out functions (`FnBin`, `FV/Backend/Encode.lean`) into a
relocatable object with the sections

| # | name | type | content |
| --- | --- | --- | --- |
| 0 | — | `SHT_NULL` | |
| 1 | `.text` | `SHT_PROGBITS`, `AX`, align 4 | the functions' words, in order |
| 2 | `.rela.text` | `SHT_RELA`, `I`, link 3, info 1 | `R_AARCH64_*` relocations with addends |
| 3 | `.symtab` | `SHT_SYMTAB`, link 4 | null; mapping symbols `$x`/`$d` (local); functions (`STT_FUNC`, global, with sizes); undefined referenced symbols (global; `STT_TLS` for the targets of TLS relocations) |
| 4 | `.strtab` | `SHT_STRTAB` | symbol names |
| 5 | `.shstrtab` | `SHT_STRTAB` | section names |
| 6 | `.eh_frame` | `SHT_PROGBITS`, `A`, align 8 | CIE(s) + one FDE per function (if unwind rows are given) |
| 7 | `.rela.eh_frame` | `SHT_RELA`, `I`, link 3, info 6 | `R_AARCH64_PREL32` of each FDE's `pc_begin` (and LSDA), `R_AARCH64_PREL64` of the personality |
| 8 | `.gcc_except_table` | `SHT_PROGBITS`, `A`, align 4 | the LSDAs (only with a personality and a function with landing pads) |
| 9 | `.data.rel.ro` | `SHT_PROGBITS`, `WA`, align 8 | `DW.ref.<personality>` (likewise) |
| 10 | `.rela.data.rel.ro` | `SHT_RELA`, `I`, link 3, info 9 | `R_AARCH64_ABS64` of the personality |

following the System V gABI (ELF-64 object file format) and "ELF for the Arm 64-bit
Architecture (AAELF64)" (`EM_AARCH64` = 183; relocation codes in `RelocType.elf`; mapping
symbols `$x` at the start of A64 code and `$d` at the start of data, i.e. jump tables).
Relocations refer to the target's symbol, also for functions defined in the object (as
`llvm-mc` does for global symbols).

With unwind rows (`FV/Backend/Unwind.lean`, unverified), the symbol table also has the
`.text` section symbol (local, right after the null symbol), which the `pc_begin`
relocations refer to (`.text` + the function's offset), as Cranelift's objects do.

With a personality routine (`lean-backend --personality rust_eh_personality`, what `cargo fv`
passes) and a function with landing pads (`try_call`), the object is laid out like
cg_clif's (`rustc_codegen_cranelift/src/debuginfo/unwind.rs`, `unwinding` feature): a second
CIE with augmentation `zLPR` (LSDA `pcrel|sdata4`, personality `indirect|pcrel|sdata8` through
the local 8-byte `DW.ref.<personality>` in `.data.rel.ro`), used by the FDEs of the functions
with an LSDA, whose augmentation data is the LSDA pointer into `.gcc_except_table`
(`lsdaBytes`). The other functions keep the `zR` CIE (no LSDA: the personality is never
called for their frames, as for LLVM frames without landing pads).
-/

namespace Backend

/-- Little-endian bytes. -/
def le (width n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity width
  for i in [0:width] do
    b := b.push (UInt8.ofNat (n >>> (8 * i)))
  return b

def le16 (n : Nat) : ByteArray := le 2 n
def le32 (n : Nat) : ByteArray := le 4 n
def le64 (n : Nat) : ByteArray := le 8 n

/-- Zero bytes to pad `n` up to a multiple of `a`. -/
def padTo (a n : Nat) : ByteArray := ⟨Array.replicate ((a - n % a) % a) 0⟩

/-- A string table: the bytes (starting with the empty name) and each name's offset. -/
def strTable (names : List String) : ByteArray × List Nat := Id.run do
  let mut b : ByteArray := ⟨#[0]⟩
  let mut offs : Array Nat := #[]
  for n in names do
    offs := offs.push b.size
    b := b ++ n.toUTF8 ++ ⟨#[0]⟩
  return (b, offs.toList)

/-- An ELF symbol. -/
structure ElfSym where
  name : String
  /-- `STB_LOCAL` 0, `STB_GLOBAL` 1. -/
  bind : Nat
  /-- `STT_NOTYPE` 0, `STT_FUNC` 2, `STT_TLS` 6. -/
  type : Nat
  /-- Section index (0 = undefined). -/
  shndx : Nat
  value : Nat
  size : Nat

/-- `Elf64_Sym` (24 bytes). -/
def ElfSym.bytes (s : ElfSym) (nameOff : Nat) : ByteArray :=
  le32 nameOff ++ ⟨#[UInt8.ofNat (s.bind * 16 + s.type), 0]⟩ ++ le16 s.shndx ++ le64 s.value ++
    le64 s.size

/-- `Elf64_Shdr` (64 bytes). -/
def shdr (name type flags offset size link info align entsize : Nat) : ByteArray :=
  le32 name ++ le32 type ++ le64 flags ++ le64 0 ++ le64 offset ++ le64 size ++ le32 link ++
    le32 info ++ le64 align ++ le64 entsize

/-- Mapping symbols of `.text` (functions placed at the given offsets): `$x` where a run of
instructions starts and `$d` where a run of jump-table words starts. -/
def mappingSyms (placed : List (Nat × FnAsm)) : List ElfSym := Id.run do
  let mut out : Array ElfSym := #[]
  let mut inData : Option Bool := none
  for (base, f) in placed do
    let mut off := 0
    for ln in f.lines do
      let d? : Option Bool := match ln with
        | .ins .. => some false | .word .. => some true | .label _ => none
      if let some d := d? then
        if inData != some d then
          out := out.push { name := if d then "$d" else "$x", bind := 0, type := 0, shndx := 1,
                            value := base + off, size := 0 }
          inData := some d
      off := off + ln.size
  return out.toList

/-- `.eh_frame` for functions `(offset in .text, size, rows, LSDA offset)`: one CIE and one
FDE per function, and its relocations `(offset, type, symbol index, addend)`. The first CIE is
Cranelift's aarch64 `create_cie` with cg_clif's pointer encoding for objects: version 1,
augmentation `zR`, code alignment 4, data alignment -8, return address x30, FDE addresses
`DW_EH_PE_pcrel | DW_EH_PE_sdata4` (0x1b), initial rule CFA = sp+0. If a function has an
LSDA, a second CIE, cg_clif's with personality (`zLPR`: LSDA `0x1b`, personality `0x9c` =
`indirect | pcrel | sdata8` pointing at `DW.ref.<personality>`, symbol `dwref`), serves the
FDEs with an LSDA (pointer into `.gcc_except_table`, symbol `gcc`). Entries are padded with
`DW_CFA_nop` to 8 bytes; there is no terminator (the linker adds it), as in Cranelift's
objects. The `.text` symbol is 1. -/
def ehFrame (fdes : List (Nat × Nat × List (Nat × Cfi) × Option Nat)) (gcc dwref : Nat) :
    ByteArray × List (Nat × Nat × Nat × Int) := Id.run do
  let entry (body : ByteArray) : ByteArray :=
    let body := body ++ padTo 8 (4 + body.size)
    le32 body.size ++ body
  let cie := entry (le32 0 ++ ⟨#[1]⟩ ++ "zR".toUTF8 ++ ⟨#[0]⟩ ++ uleb 4 ++ sleb (-8) ++
    ⟨#[30, 1, 0x1b, 0x0c, 31, 0]⟩)
  let mut out := cie
  let mut relocs : Array (Nat × Nat × Nat × Int) := #[]
  let mut cieP := 0
  if fdes.any (·.2.2.2.isSome) then
    cieP := out.size
    out := out ++ entry (le32 0 ++ ⟨#[1]⟩ ++ "zLPR".toUTF8 ++ ⟨#[0]⟩ ++ uleb 4 ++ sleb (-8) ++
      ⟨#[30]⟩ ++ uleb 11 ++ ⟨#[0x1b, 0x9c]⟩ ++ le64 0 ++ ⟨#[0x1b, 0x0c, 31, 0]⟩)
    relocs := relocs.push (cieP + 14 + 6, 260, dwref, 0)
  for (start, size, rows, lsda?) in fdes do
    let at_ := out.size
    -- CIE pointer: the distance from this field back to the CIE
    match lsda? with
    | none =>
      out := out ++ entry (le32 (at_ + 4) ++ le32 0 ++ le32 size ++ uleb 0 ++ cfiProgram rows)
    | some lo =>
      out := out ++ entry (le32 (at_ + 4 - cieP) ++ le32 0 ++ le32 size ++ uleb 4 ++ le32 0 ++
        cfiProgram rows)
      relocs := relocs.push (at_ + 17, 261, gcc, lo)
    relocs := relocs.push (at_ + 8, 261, 1, start)
  return (out, relocs.toList)

/-- cg_clif's LSDA (`debuginfo/gcc_except_table.rs` `GccExceptTable::write`): `lpStart`
omitted (landing pads relative to the function start), type table `udata4` with the single
entry 0 (catch-all, `catch_unwind`'s type), the call-site table (`uleb128`), the action table
with the one catch action (`ttypeIndex` 1, no next action), padding so that the type table is
4-aligned, the type table, and padding to a multiple of 4. -/
def lsdaBytes (sites : List CallSite) : ByteArray := Id.run do
  let entries := sites.foldl (fun b s => b ++ uleb s.start ++ uleb s.len ++ uleb s.pad ++ uleb s.action)
    ByteArray.empty
  let cs : ByteArray := ⟨#[0x01]⟩ ++ uleb entries.size ++ entries
  let actions : ByteArray := ⟨#[0x01, 0x00]⟩
  let typeInfo := le32 0
  let noPad := cs.size + actions.size + typeInfo.size
  -- `type_info_is_aligned`: the class-info offset field is at 2
  let mut pad := 0
  for p in [0:8] do
    if (2 + (uleb (noPad + p)).size + cs.size + actions.size + p) % 4 == 0 then
      pad := p
      break
  let body : ByteArray := ⟨#[0xff, 0x03]⟩ ++ uleb (noPad + pad) ++ cs ++ actions ++
    ⟨Array.replicate pad 0⟩ ++ typeInfo
  return body ++ padTo 4 body.size

/-- The relocatable object of laid-out functions (`funcs` pairs each function's final line
list with its layout). With `unwind` (rows per function name), `.eh_frame` gets an FDE for
every function; without, the object has no `.eh_frame`. With a `personality`, the functions
that have call-site tables (`lsda`, per function name) get an LSDA (see the module doc). -/
def elfObject (funcs : List (FnAsm × FnBin)) (unwind : List (String × List (Nat × Cfi)) := [])
    (lsda : List (String × List CallSite) := []) (personality : Option String := none) :
    ByteArray := Id.run do
  -- .text and function placement
  let mut text : ByteArray := .empty
  let mut placed : Array (Nat × FnAsm × FnBin) := #[]
  for (fa, fb) in funcs do
    placed := placed.push (text.size, fa, fb)
    text := text ++ wordsBytes fb.words
  let eh := !unwind.isEmpty && !placed.isEmpty
  -- LSDAs (only with unwind info and a personality)
  let pers : Option String := if eh then personality else none
  let mut gccTable : ByteArray := .empty
  let mut lsdaOff : Array (String × Nat) := #[]
  if pers.isSome then
    for (_, _, fb) in placed do
      if let some sites := lsda.lookup fb.name then
        lsdaOff := lsdaOff.push (fb.name, gccTable.size)
        gccTable := gccTable ++ lsdaBytes sites
  let exc := !lsdaOff.isEmpty
  -- symbols: locals (null, section symbols, `DW.ref.*`, mapping), then defined functions, then
  -- undefined targets
  let secSym : List ElfSym :=
    if eh then [{ name := "", bind := 0, type := 3, shndx := 1, value := 0, size := 0 }] else []
  let persName := pers.getD ""
  let excSyms : List ElfSym :=
    if exc then
      [{ name := "", bind := 0, type := 3, shndx := 8, value := 0, size := 0 },
       { name := s!"DW.ref.{persName}", bind := 0, type := 1, shndx := 9, value := 0, size := 8 }]
    else []
  let locals : List ElfSym :=
    secSym ++ excSyms ++ mappingSyms (placed.toList.map fun (b, fa, _) => (b, fa))
  let defined : List ElfSym := placed.toList.map fun (b, _, fb) =>
    { name := fb.name, bind := 1, type := 2, shndx := 1, value := b, size := fb.size }
  let targets : List String :=
    ((placed.toList.flatMap fun (_, _, fb) => fb.relocs.map (·.sym)) ++
      (if exc then [persName] else [])).eraseDups
  -- a thread-local variable (the target of a TLS relocation) is `STT_TLS` 6, as the assembler
  -- marks it
  let tls (t : String) : Bool :=
    placed.toList.any fun (_, _, fb) => fb.relocs.any fun r => r.sym == t && r.type.isTls
  let undef : List ElfSym := (targets.filter fun t => !defined.any (·.name == t)).map fun t =>
    { name := t, bind := 1, type := if tls t then 6 else 0, shndx := 0, value := 0, size := 0 }
  let syms := locals ++ defined ++ undef
  let (strtab, nameOffs) := strTable (syms.map (·.name))
  let symtab : ByteArray := syms.zip nameOffs |>.foldl (fun acc (s, o) => acc ++ s.bytes o)
    (ElfSym.bytes { name := "", bind := 0, type := 0, shndx := 0, value := 0, size := 0 } 0)
  let symIdx (n : String) : Nat :=
    match (syms.zipIdx.find? fun (s, _) => s.bind == 1 && s.name == n) with
    | some (_, i) => i + 1
    | none => 0
  -- relocations
  let mut rela : ByteArray := .empty
  for (b, _, fb) in placed do
    for r in fb.relocs do
      rela := rela ++ le64 (b + r.offset) ++ le64 (symIdx r.sym * 2 ^ 32 + r.type.elf) ++
        le64 (r.addend % (2 ^ 64 : Int)).toNat
  -- unwind info
  let (ehBytes, ehRel) := if eh then
      ehFrame (placed.toList.map fun (b, _, fb) =>
        (b, fb.size, (unwind.lookup fb.name).getD [], lsdaOff.toList.lookup fb.name)) 2 3
    else (.empty, [])
  let ehRela : ByteArray := ehRel.foldl (fun acc (o, t, s, a) =>
    acc ++ le64 o ++ le64 (s * 2 ^ 32 + t) ++ le64 (a % (2 ^ 64 : Int)).toNat) .empty
  let dataRo : ByteArray := le64 0
  let dataRela : ByteArray := le64 0 ++ le64 (symIdx persName * 2 ^ 32 + 257) ++ le64 0
  -- section names
  let (shstrtab, shOffs) := strTable
    ([".text", ".rela.text", ".symtab", ".strtab", ".shstrtab"] ++
      (if eh then [".eh_frame", ".rela.eh_frame"] else []) ++
      (if exc then [".gcc_except_table", ".data.rel.ro", ".rela.data.rel.ro"] else []))
  let sh (i : Nat) : Nat := shOffs.getD i 0
  -- file layout
  let textOff := 64
  let relaOff := textOff + text.size + (padTo 8 (textOff + text.size)).size
  let symOff := relaOff + rela.size
  let strOff := symOff + symtab.size
  let shstrOff := strOff + strtab.size
  let ehOff := shstrOff + shstrtab.size + (padTo 8 (shstrOff + shstrtab.size)).size
  let ehRelaOff := ehOff + ehBytes.size + (padTo 8 (ehOff + ehBytes.size)).size
  let gccOff := ehRelaOff + ehRela.size
  let dataOff := gccOff + gccTable.size + (padTo 8 (gccOff + gccTable.size)).size
  let dataRelaOff := dataOff + dataRo.size
  let shOff := if exc then dataRelaOff + dataRela.size
    else if eh then ehRelaOff + ehRela.size else ehOff
  let nsec := if exc then 11 else if eh then 8 else 6
  let header : ByteArray :=
    ⟨#[0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ ++
    le16 1 ++ le16 183 ++ le32 1 ++ le64 0 ++ le64 0 ++ le64 shOff ++ le32 0 ++ le16 64 ++
    le16 0 ++ le16 0 ++ le16 64 ++ le16 nsec ++ le16 5
  let shdrs : ByteArray :=
    shdr 0 0 0 0 0 0 0 0 0 ++
    shdr (sh 0) 1 0x6 textOff text.size 0 0 4 0 ++
    shdr (sh 1) 4 0x40 relaOff rela.size 3 1 8 24 ++
    shdr (sh 2) 2 0 symOff symtab.size 4 (1 + locals.length) 8 24 ++
    shdr (sh 3) 3 0 strOff strtab.size 0 0 1 0 ++
    shdr (sh 4) 3 0 shstrOff shstrtab.size 0 0 1 0 ++
    (if eh then
      shdr (sh 5) 1 0x2 ehOff ehBytes.size 0 0 8 0 ++
      shdr (sh 6) 4 0x40 ehRelaOff ehRela.size 3 6 8 24
     else .empty) ++
    (if exc then
      shdr (sh 7) 1 0x2 gccOff gccTable.size 0 0 4 0 ++
      shdr (sh 8) 1 0x3 dataOff dataRo.size 0 0 8 0 ++
      shdr (sh 9) 4 0x40 dataRelaOff dataRela.size 3 9 8 24
     else .empty)
  let ehPart : ByteArray :=
    if eh then ehBytes ++ padTo 8 (ehOff + ehBytes.size) ++ ehRela else .empty
  let excPart : ByteArray :=
    if exc then gccTable ++ padTo 8 (gccOff + gccTable.size) ++ dataRo ++ dataRela else .empty
  return header ++ text ++ padTo 8 (textOff + text.size) ++ rela ++ symtab ++ strtab ++
    shstrtab ++ padTo 8 (shstrOff + shstrtab.size) ++ ehPart ++ excPart ++ shdrs

end Backend
