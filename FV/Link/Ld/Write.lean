import FV.E2E.Elf
import FV.Link.Ld.Obj

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
needed). -/
def putLE (b : ByteArray) (o n v : Nat) : ByteArray := Id.run do
  let mut b := b
  while b.size < o + n do
    b := b.push 0
  for i in [0:n] do
    b := b.set! (o + i) (UInt8.ofNat (v >>> (8 * i) % 256))
  return b

/-- `b` padded with zeros to a multiple of `a`. -/
def padTo (b : ByteArray) (a : Nat) : ByteArray := Id.run do
  let mut b := b
  while b.size % a != 0 do
    b := b.push 0
  return b

/-- The ELF header fields of an executable with `phnum` program headers at `64`, `shnum` section
headers at `shoff`, section names in section `shstrndx`. -/
def ehdrBytes (entry phnum shoff shnum shstrndx : Nat) : ByteArray :=
  let b := ByteArray.mk (Array.replicate 64 0)
  let b := putLE b 0 4 0x464c457f
  let b := putLE b 4 1 2
  let b := putLE b 5 1 1
  let b := putLE b 6 1 1
  let b := putLE b 16 2 2
  let b := putLE b 18 2 183
  let b := putLE b 20 4 1
  let b := putLE b 24 8 entry
  let b := putLE b 32 8 64
  let b := putLE b 40 8 shoff
  let b := putLE b 52 2 64
  let b := putLE b 54 2 56
  let b := putLE b 56 2 phnum
  let b := putLE b 58 2 64
  let b := putLE b 60 2 shnum
  putLE b 62 2 shstrndx

/-- A program header's 56 bytes. -/
def phdrBytes (p : Phdr) : ByteArray :=
  let b := ByteArray.mk (Array.replicate 56 0)
  let b := putLE b 0 4 p.type
  let b := putLE b 4 4 p.flags
  let b := putLE b 8 8 p.offset
  let b := putLE b 16 8 p.vaddr
  let b := putLE b 24 8 p.vaddr
  let b := putLE b 32 8 p.filesz
  let b := putLE b 40 8 p.memsz
  putLE b 48 8 p.align

/-- A string table of `names` (a leading NUL) and each name's offset. -/
def strtab (names : Array String) : ByteArray × Array Nat := Id.run do
  let mut b := ByteArray.mk #[0]
  let mut offs : Array Nat := Array.mkEmpty names.size
  for n in names do
    offs := offs.push b.size
    b := b ++ n.toUTF8
    b := b.push 0
  return (b, offs)

/-- A section header's 64 bytes. -/
def shdrBytes (name type flags addr off size link info align entsize : Nat) : ByteArray :=
  let b := ByteArray.mk (Array.replicate 64 0)
  let b := putLE b 0 4 name
  let b := putLE b 4 4 type
  let b := putLE b 8 8 flags
  let b := putLE b 16 8 addr
  let b := putLE b 24 8 off
  let b := putLE b 32 8 size
  let b := putLE b 40 4 link
  let b := putLE b 44 4 info
  let b := putLE b 48 8 align
  putLE b 56 8 entsize

/-- **The executable of an image description.** -/
def Img.write (img : Img) : ByteArray := Id.run do
  let nsec := img.secs.size
  -- section indices: 0 null, 1..nsec the output sections, then .symtab, .strtab, .shstrtab
  let iSym := nsec + 1
  let iStr := nsec + 2
  let iShs := nsec + 3
  let (shs, shOffs) := strtab ((img.secs.map (·.name)) ++ #[".symtab", ".strtab", ".shstrtab"])
  let (strs, strOffs) := strtab (img.syms.map (·.name))
  let mut f := padTo img.body 8
  -- .symtab
  let symOff := f.size
  f := f ++ ByteArray.mk (Array.replicate 24 0)
  for i in [0:img.syms.size] do
    let s := img.syms[i]!
    let o := f.size
    f := putLE f o 4 strOffs[i]!
    f := putLE f (o + 4) 1 s.info
    f := putLE f (o + 6) 2 s.shndx
    f := putLE f (o + 8) 8 s.value
    f := putLE f (o + 16) 8 s.size
  let symSize := f.size - symOff
  let firstGlobal := 1 + (img.syms.toList.takeWhile (·.info >>> 4 == 0)).length
  let strOff := f.size
  f := f ++ strs
  let shsOff := f.size
  f := padTo (f ++ shs) 8
  let shoff := f.size
  f := f ++ ByteArray.mk (Array.replicate 64 0)
  for i in [0:nsec] do
    let s := img.secs[i]!
    f := f ++ shdrBytes shOffs[i]! s.type s.flags s.addr s.off s.size 0 0 s.align s.entsize
  f := f ++ shdrBytes shOffs[nsec]! 2 0 0 symOff symSize iStr firstGlobal 8 24
  f := f ++ shdrBytes shOffs[nsec + 1]! 3 0 0 strOff strs.size 0 0 1 0
  f := f ++ shdrBytes shOffs[nsec + 2]! 3 0 0 shsOff shs.size 0 0 1 0
  -- the ELF header and the program headers over the start of the body
  let h := ehdrBytes img.entry img.phs.length shoff (nsec + 4) iShs
  for i in [0:64] do
    f := f.set! i h[i]!
  let mut k := 0
  for p in img.phs do
    let pb := phdrBytes p
    for i in [0:56] do
      f := f.set! (64 + 56 * k + i) pb[i]!
    k := k + 1
  let _ := iSym
  return f

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
