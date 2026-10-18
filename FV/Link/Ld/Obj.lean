import Std.Data.HashMap
import Std.Data.HashSet

/-! # Lean static linker (L2b stage 3): ELF64 relocatable objects and `ar` archives

The inputs rustc gives the linker (docs/research/lean-linker.md §6): ELF64 little-endian
AArch64 relocatable objects (`ET_REL`), and `ar` archives (rlibs, `libc.a`, `libunwind.a`)
whose ELF members are such objects. This file reads them: section headers, symbols, the
`SHT_RELA` relocations of a section (read on demand: most of a sysroot object's relocations are
in debug sections, which the linker drops), the GNU archive symbol table.
-/

namespace Link.Ld

/-- The little-endian unsigned `n`-byte value at `o` of `b` (`0` past the end). -/
def rdLE (b : ByteArray) (o n : Nat) : Nat := Id.run do
  let mut v := 0
  for i in [0:n] do
    v := v + (b[o + i]!).toNat <<< (8 * i)
  return v

/-- The big-endian unsigned 4-byte value at `o` (the archive symbol table's). -/
def rdBE32 (b : ByteArray) (o : Nat) : Nat :=
  (b[o]!).toNat <<< 24 + (b[o + 1]!).toNat <<< 16 + (b[o + 2]!).toNat <<< 8 + (b[o + 3]!).toNat

/-- The offset of the first `0` byte at or after `o` (or `b.size`). -/
def nulAt (b : ByteArray) (o : Nat) : Nat := Id.run do
  let mut j := o
  while j < b.size && b[j]! != 0 do
    j := j + 1
  return j

/-- The NUL-terminated string at `o` (invalid UTF-8 read byte by byte as Latin-1). -/
def cstrAt (b : ByteArray) (o : Nat) : String :=
  let e := nulAt b o
  let s := b.extract o e
  match String.fromUTF8? s with
  | some t => t
  | none => String.ofList (s.toList.map fun c => Char.ofNat c.toNat)

/-! ## ELF relocatable objects -/

/-- `SHT_*` and `SHF_*` values used. -/
def shtProgbits : Nat := 1
def shtSymtab : Nat := 2
def shtStrtab : Nat := 3
def shtRela : Nat := 4
def shtNobits : Nat := 8
def shtInitArray : Nat := 14
def shtFiniArray : Nat := 15
def shtPreinitArray : Nat := 16
def shtGroup : Nat := 17
def shtNote : Nat := 7
def shfWrite : Nat := 1
def shfAlloc : Nat := 2
def shfExec : Nat := 4
def shfTls : Nat := 0x400
def shfRetain : Nat := 0x200000

/-- A section header of an input object. -/
structure Sec where
  name : String
  type : Nat
  flags : Nat
  off : Nat
  size : Nat
  link : Nat
  info : Nat
  align : Nat
  entsize : Nat
  deriving Inhabited, Repr

/-- A symbol of an input object (`bind`: `0` local, `1` global, `2` weak; `type`: `6` TLS,
`3` section, `4` file; `shndx`: `0` undefined, `0xfff1` absolute, `0xfff2` common). -/
structure Sym where
  name : String
  value : Nat
  size : Nat
  bind : Nat
  type : Nat
  shndx : Nat
  deriving Inhabited, Repr

/-- A relocation with addend (`SHT_RELA`): offset in its section, type, symbol index. -/
structure Rela where
  off : Nat
  type : Nat
  sym : Nat
  addend : Int
  deriving Inhabited, Repr

/-- An input object: its display name (`path` or `archive(member)`), bytes, sections, symbols,
the first global symbol's index (`sh_info` of `.symtab`), and per section the index of the
`SHT_RELA` section applying to it. -/
structure Obj where
  name : String
  member : String
  data : ByteArray
  secs : Array Sec
  syms : Array Sym
  firstGlobal : Nat
  relaOf : Array (Option Nat)
  deriving Inhabited

def Sec.has (s : Sec) (f : Nat) : Bool := s.flags &&& f != 0

/-- Reads the object `data` (`name` for messages and the map, `member` its archive member name
or its file name). -/
def Obj.parse (name member : String) (data : ByteArray) : Except String Obj := do
  if data.size < 64 || rdLE data 0 4 != 0x464c457f then throw s!"{name}: not an ELF file"
  if data[4]! != 2 || data[5]! != 1 then throw s!"{name}: not ELF64 little-endian"
  if rdLE data 16 2 != 1 then throw s!"{name}: not a relocatable object (e_type {rdLE data 16 2})"
  if rdLE data 18 2 != 183 then throw s!"{name}: not AArch64 (e_machine {rdLE data 18 2})"
  let shoff := rdLE data 40 8
  let shnum0 := rdLE data 60 2
  let shnum := if shnum0 == 0 && shoff != 0 then rdLE data (shoff + 32) 8 else shnum0
  let shstrndx0 := rdLE data 62 2
  let shstrndx := if shstrndx0 == 0xffff then rdLE data (shoff + 40) 4 else shstrndx0
  if shoff + 64 * shnum > data.size then throw s!"{name}: section headers past the end"
  let hdr (i : Nat) : Nat → Nat → Nat := fun d n => rdLE data (shoff + 64 * i + d) n
  let strOff := hdr shstrndx 24 8
  let mut secs : Array Sec := Array.mkEmpty shnum
  for i in [0:shnum] do
    secs := secs.push {
      name := cstrAt data (strOff + hdr i 0 4), type := hdr i 4 4, flags := hdr i 8 8,
      off := hdr i 24 8, size := hdr i 32 8, link := hdr i 40 4, info := hdr i 44 4,
      align := hdr i 48 8, entsize := hdr i 56 8 }
  let mut relaOf : Array (Option Nat) := Array.replicate shnum none
  let mut symtab : Option Nat := none
  for i in [0:shnum] do
    let s := secs[i]!
    if s.type == shtRela && s.info < shnum then relaOf := relaOf.set! s.info (some i)
    if s.type == shtSymtab then symtab := some i
  let mut syms : Array Sym := #[]
  let mut firstGlobal := 0
  if let some t := symtab then
    let st := secs[t]!
    let strO := (secs[st.link]!).off
    let n := st.size / 24
    firstGlobal := st.info
    syms := Array.mkEmpty n
    for j in [0:n] do
      let o := st.off + 24 * j
      let info := rdLE data (o + 4) 1
      syms := syms.push {
        name := cstrAt data (strO + rdLE data o 4), value := rdLE data (o + 8) 8,
        size := rdLE data (o + 16) 8, bind := info >>> 4, type := info &&& 15,
        shndx := rdLE data (o + 6) 2 }
  return { name, member, data, secs, syms, firstGlobal, relaOf }

/-- The relocations applying to section `i`. -/
def Obj.relas (o : Obj) (i : Nat) : Array Rela := Id.run do
  match o.relaOf[i]? with
  | some (some r) =>
    let s := o.secs[r]!
    let n := s.size / 24
    let mut out : Array Rela := Array.mkEmpty n
    for j in [0:n] do
      let b := s.off + 24 * j
      let info := rdLE o.data (b + 8) 8
      let a := rdLE o.data (b + 16) 8
      out := out.push { off := rdLE o.data b 8, type := info % 2 ^ 32, sym := info >>> 32,
                        addend := if a < 2 ^ 63 then (a : Int) else (a : Int) - 2 ^ 64 }
    return out
  | _ => return #[]

/-- The bytes of section `i` (zeros for `SHT_NOBITS`). -/
def Obj.secBytes (o : Obj) (i : Nat) : ByteArray :=
  let s := o.secs[i]!
  if s.type == shtNobits then ByteArray.mk (Array.replicate s.size 0)
  else o.data.extract s.off (s.off + s.size)

/-! ## Archives -/

/-- An archive member: its name and its bytes' range in the archive. -/
structure Member where
  name : String
  off : Nat
  size : Nat
  deriving Inhabited

/-- An `ar` archive: path, bytes, members, and the GNU symbol table (`name`, member index). -/
structure Archive where
  path : String
  data : ByteArray
  members : Array Member
  symtab : Array (String × Nat)
  deriving Inhabited

/-- The trimmed ASCII text of `b[o, o + n)`. -/
def asciiAt (b : ByteArray) (o n : Nat) : String :=
  (String.ofList ((b.extract o (o + n)).toList.map fun c => Char.ofNat c.toNat)).trimAscii.toString

/-- Reads an `ar` archive (GNU format: `/` symbol table, `//` long names). -/
def Archive.parse (path : String) (data : ByteArray) : Except String Archive := do
  if data.size < 8 || data.extract 0 8 != "!<arch>\n".toUTF8 then throw s!"{path}: not an archive"
  let mut o := 8
  let mut members : Array Member := #[]
  let mut hdrAt : Std.HashMap Nat Nat := {}
  let mut longNames : ByteArray := .empty
  let mut symRaw : Option (Nat × Nat) := none
  while o + 60 ≤ data.size do
    let raw := asciiAt data o 16
    let size := (asciiAt data (o + 48) 10).toNat!
    let body := o + 60
    if raw == "/" || raw == "/SYM64/" then
      symRaw := some (body, size)
    else if raw == "//" then
      longNames := data.extract body (body + size)
    else
      let name :=
        if raw.startsWith "/" then
          let k := (raw.drop 1).toString.toNat!
          let e := Id.run do
            let mut j := k
            while j < longNames.size && longNames[j]! != 10 do j := j + 1
            return j
          let s := asciiAt longNames k (e - k)
          if s.endsWith "/" then (s.dropEnd 1).toString else s
        else if raw.endsWith "/" then (raw.dropEnd 1).toString else raw
      hdrAt := hdrAt.insert o members.size
      members := members.push { name, off := body, size }
    o := body + size + size % 2
  let mut symtab : Array (String × Nat) := #[]
  if let some (b, _) := symRaw then
    let n := rdBE32 data b
    let mut p := b + 4 + 4 * n
    for i in [0:n] do
      let e := nulAt data p
      let nm := cstrAt data p
      if let some m := hdrAt[rdBE32 data (b + 4 + 4 * i)]? then symtab := symtab.push (nm, m)
      p := e + 1
  return { path, data, members, symtab }

/-- The bytes of member `i`. -/
def Archive.memberBytes (a : Archive) (i : Nat) : ByteArray :=
  let m := a.members[i]!
  a.data.extract m.off (m.off + m.size)

/-- Member `i` is an ELF file (rlibs also hold `lib.rmeta`). -/
def Archive.isElf (a : Archive) (i : Nat) : Bool :=
  let m := a.members[i]!
  m.size ≥ 4 && rdLE a.data m.off 4 == 0x464c457f

end Link.Ld
