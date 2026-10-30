import FV.E2E.Elf

/-! # Lean static linker: the ELF writer

An image description `Img` — the entry, the program headers, the file bytes of the loaded
segments (`body`, from offset `0`; its first `64 + 56 · |phs|` bytes are the headers' place),
the section headers of the allocated output sections and the symbols — becomes the executable:
the ELF header and the program headers written at the start of `body`, then `.shstrtab`,
`.strtab`, `.symtab` and the section header table appended after it (so everything a symbol
lookup reads lies after the segments' bytes).
-/

namespace Link.Ld

open E2E.Elf

/-- An output section header (allocated sections, for tools; `.symtab` and the string tables are
added by the writer). -/
structure OutSec where
  name : String
  type : Nat
  flags : Nat
  addr : Nat
  off : Nat
  size : Nat
  align : Nat
  entsize : Nat := 0
  deriving Inhabited, Repr

/-- An output symbol: name, value, size, `st_info` (`bind << 4 | type`), section index (`0xfff1`
absolute; indices count from `1` over `secs`). -/
structure OutSym where
  name : String
  value : Nat
  size : Nat := 0
  info : Nat
  shndx : Nat
  deriving Inhabited, Repr

/-- **An image description.** `syms`: the local symbols first. -/
structure Img where
  entry : Nat
  phs : List Phdr
  body : ByteArray
  secs : Array OutSec
  syms : Array OutSym
  deriving Inhabited

/-- `b` with the little-endian `n`-byte value `v` written at `o` (`b` grown with zeros as
needed; the planner's in-place patches). -/
def putLE (b : ByteArray) (o n v : Nat) : ByteArray := Id.run do
  let mut b := b
  while b.size < o + n do
    b := b.push 0
  for i in [0:n] do
    b := b.set! (o + i) (UInt8.ofNat (v >>> (8 * i) % 256))
  return b

/-- Byte `i` of the little-endian representation of `v`. -/
def leByte (v i : Nat) : UInt8 := UInt8.ofNat (v >>> (8 * i))

/-- **A record** of `size` bytes: the fields `(offset, width, value)`, little-endian, zeros
elsewhere (the first field covering a byte wins). -/
def record (size : Nat) (fs : List (Nat × Nat × Nat)) : List UInt8 :=
  (List.range size).map fun i =>
    match fs.find? (fun f => decide (f.1 ≤ i ∧ i < f.1 + f.2.1)) with
    | some f => leByte f.2.2 (i - f.1)
    | none => 0

/-- The ELF header's fields: `e_ident` (magic, `ELFCLASS64`, `ELFDATA2LSB`, version), `ET_EXEC`,
`EM_AARCH64`, `e_version`, `e_entry`, `e_phoff = 64`, `e_shoff`, the header and entry sizes, the
counts and `e_shstrndx`. -/
def ehdrFields (entry phnum shoff shnum shstrndx : Nat) : List (Nat × Nat × Nat) :=
  [(0, 4, 0x464c457f), (4, 1, 2), (5, 1, 1), (6, 1, 1), (16, 2, 2), (18, 2, 183), (20, 4, 1),
   (24, 8, entry), (32, 8, 64), (40, 8, shoff), (52, 2, 64), (54, 2, 56), (56, 2, phnum),
   (58, 2, 64), (60, 2, shnum), (62, 2, shstrndx)]

/-- A program header's fields. -/
def phdrFields (p : Phdr) : List (Nat × Nat × Nat) :=
  [(0, 4, p.type), (4, 4, p.flags), (8, 8, p.offset), (16, 8, p.vaddr), (24, 8, p.vaddr),
   (32, 8, p.filesz), (40, 8, p.memsz), (48, 8, p.align)]

/-- A symbol table entry's fields (`st_name`, `st_info`, `st_shndx`, `st_value`, `st_size`). -/
def symFields (nm : Nat) (s : OutSym) : List (Nat × Nat × Nat) :=
  [(0, 4, nm), (4, 1, s.info), (6, 2, s.shndx), (8, 8, s.value), (16, 8, s.size)]

/-- A section header's fields. -/
def shdrFields (name type flags addr off size link info align entsize : Nat) :
    List (Nat × Nat × Nat) :=
  [(0, 4, name), (4, 4, type), (8, 8, flags), (16, 8, addr), (24, 8, off), (32, 8, size),
   (40, 4, link), (44, 4, info), (48, 8, align), (56, 8, entsize)]

/-- The offsets of `names` in their string table (after the leading NUL). -/
def strOffsets : List String → Nat → List Nat
  | [], _ => []
  | n :: ns, o => o :: strOffsets ns (o + n.toUTF8.size + 1)

/-- A string table: a NUL, then every name followed by a NUL. -/
def strtabOf (names : List String) : List UInt8 :=
  0 :: names.flatMap fun n => n.toUTF8.data.toList ++ [0]

/-- `b` with zeros up to a multiple of 8. -/
def pad8 (b : ByteArray) : ByteArray :=
  b ++ ⟨Array.replicate ((8 - b.size % 8) % 8) 0⟩

/-- `file` with `b` written over its start (within the file). -/
def overStart (file : ByteArray) (b : ByteArray) : ByteArray :=
  ⟨Array.ofFn (n := file.size) fun i => if h : i.1 < b.size then b[i.1] else file[i.1]'i.2⟩

/-- The layout of the tables after the body: the offsets of `.symtab`, `.strtab`, `.shstrtab`
and the section header table, from the body's padded size `b`. -/
structure Tabs where
  symOff : Nat
  symSize : Nat
  strOff : Nat
  strSize : Nat
  shsOff : Nat
  shsSize : Nat
  shoff : Nat
  deriving Repr

/-- The section names: the output sections', then `.symtab`, `.strtab`, `.shstrtab`. -/
def Img.secNames (img : Img) : List String :=
  img.secs.toList.map (·.name) ++ [".symtab", ".strtab", ".shstrtab"]

/-- The tables' layout. -/
def Img.tabs (img : Img) : Tabs :=
  let b := (pad8 img.body).size
  let symSize := 24 * (img.syms.size + 1)
  let strSize := (strtabOf (img.syms.toList.map (·.name))).length
  let shsSize := (strtabOf img.secNames).length
  let shsEnd := b + symSize + strSize + shsSize
  { symOff := b, symSize, strOff := b + symSize, strSize, shsOff := b + symSize + strSize,
    shsSize, shoff := shsEnd + (8 - shsEnd % 8) % 8 }

/-- The index of the first global symbol in `.symtab` (`sh_info`). -/
def Img.firstGlobal (img : Img) : Nat := 1 + (img.syms.toList.takeWhile (·.info >>> 4 == 0)).length

/-- The section headers' fields: the null entry, the output sections, `.symtab` (linked to
`.strtab`), `.strtab`, `.shstrtab`. -/
def Img.shdrList (img : Img) (t : Tabs) : List (List (Nat × Nat × Nat)) :=
  let nsec := img.secs.size
  let offs := strOffsets img.secNames 1
  shdrFields 0 0 0 0 0 0 0 0 0 0 ::
  ((img.secs.toList.zip offs).map fun (s, o) =>
    shdrFields o s.type s.flags s.addr s.off s.size 0 0 s.align s.entsize) ++
  [shdrFields (offs.getD nsec 0) 2 0 0 t.symOff t.symSize (nsec + 2) img.firstGlobal 8 24,
   shdrFields (offs.getD (nsec + 1) 0) 3 0 0 t.strOff t.strSize 0 0 1 0,
   shdrFields (offs.getD (nsec + 2) 0) 3 0 0 t.shsOff t.shsSize 0 0 1 0]

/-- The section header table. -/
def Img.shdrs (img : Img) (t : Tabs) : List UInt8 := (img.shdrList t).flatMap (record 64)

/-- The symbol table's entries' fields: the null entry, then the symbols. -/
def Img.symList (img : Img) : List (List (Nat × Nat × Nat)) :=
  symFields 0 default :: (img.syms.toList.zip (strOffsets (img.syms.toList.map (·.name)) 1)).map
    fun (s, o) => symFields o s

/-- The bytes after the padded body: `.symtab`, `.strtab`, `.shstrtab`, padding, the section
header table. -/
def Img.tail (img : Img) : List UInt8 :=
  let t := img.tabs
  img.symList.flatMap (record 24) ++ strtabOf (img.syms.toList.map (·.name)) ++
    strtabOf img.secNames ++ List.replicate (t.shoff - t.shsOff - t.shsSize) 0 ++ img.shdrs t

/-- The headers: the ELF header and the program headers. -/
def Img.hdr (img : Img) : List UInt8 :=
  record 64 (ehdrFields img.entry img.phs.length img.tabs.shoff (img.secs.size + 4)
    (img.secs.size + 3)) ++
  img.phs.flatMap fun p => record 56 (phdrFields p)

/-- The values of the headers fit their fields, and the body holds the headers' bytes. -/
def Img.hdrFitsB (img : Img) : Bool :=
  decide (img.entry < 2 ^ 64) && decide (img.phs.length < 2 ^ 16) &&
  decide (img.secs.size + 4 < 2 ^ 16) && decide (img.tabs.shoff < 2 ^ 64) &&
  decide (64 + 56 * img.phs.length ≤ img.body.size) &&
  img.phs.all fun p => decide (p.type < 2 ^ 32) && decide (p.flags < 2 ^ 32) &&
    decide (p.offset < 2 ^ 64) && decide (p.vaddr < 2 ^ 64) && decide (p.filesz < 2 ^ 64) &&
    decide (p.memsz < 2 ^ 64) && decide (p.align < 2 ^ 64)

/-- The values of a record's fields fit their widths. -/
def fieldsFitB (fs : List (Nat × Nat × Nat)) : Bool := fs.all fun f => decide (f.2.2 < 2 ^ (8 * f.2.1))

/-- **The tables' values fit their fields**: every section header and symbol entry; no output
section is a symbol table; every symbol is defined (`st_shndx ≠ 0`) and its name has no NUL. -/
def Img.tabsFitB (img : Img) : Bool :=
  (img.shdrList img.tabs).all fieldsFitB && img.symList.all fieldsFitB &&
  img.secs.all (·.type != 2) &&
  img.syms.all fun s => s.shndx != 0 && !s.name.toUTF8.data.contains 0

/-- **The executable of an image description**: the padded body and the tables, with the
headers written over the body's start. -/
def Img.write (img : Img) : ByteArray :=
  overStart (pad8 img.body ++ ⟨img.tail.toArray⟩) ⟨img.hdr.toArray⟩

/-! ## The link map (lld's format, read by `cargo fv link-proof`) -/

/-- `n` in hex, right-aligned in `w` columns. -/
def hexCol (n w : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (w - s.length) ' ') ++ s

/-- A map line: address, size, alignment, then `text` indented by `ind`. -/
def mapLine (addr size align ind : Nat) (text : String) : String :=
  let al := toString align
  s!"{hexCol addr 16} {hexCol addr 16} {hexCol size 8} {String.ofList (List.replicate (5 - min 5 al.length) ' ')}{al} " ++
    String.ofList (List.replicate ind ' ') ++ text ++ "\n"

end Link.Ld
