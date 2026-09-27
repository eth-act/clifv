import FV.Backend.Encode

/-!
# ELF64 relocatable object writer (AArch64, little-endian)

`Backend.elfObject` turns laid-out functions (`FnBin`, `FV/Backend/Encode.lean`) into a
relocatable object with the sections

| # | name | type | content |
| --- | --- | --- | --- |
| 0 | — | `SHT_NULL` | |
| 1 | `.text` | `SHT_PROGBITS`, `AX`, align 4 | the functions' words, in order |
| 2 | `.rela.text` | `SHT_RELA`, `I`, link 3, info 1 | `R_AARCH64_*` relocations with addends |
| 3 | `.symtab` | `SHT_SYMTAB`, link 4 | null; mapping symbols `$x`/`$d` (local); functions (`STT_FUNC`, global, with sizes); undefined referenced symbols (global) |
| 4 | `.strtab` | `SHT_STRTAB` | symbol names |
| 5 | `.shstrtab` | `SHT_STRTAB` | section names |

following the System V gABI (ELF-64 object file format) and "ELF for the Arm 64-bit
Architecture (AAELF64)" (`EM_AARCH64` = 183; relocation codes in `RelocType.elf`; mapping
symbols `$x` at the start of A64 code and `$d` at the start of data, i.e. jump tables).
Relocations refer to the target's symbol, also for functions defined in the object (as
`llvm-mc` does for global symbols).
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
  /-- `STT_NOTYPE` 0, `STT_FUNC` 2. -/
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

/-- The relocatable object of laid-out functions (`funcs` pairs each function's final line
list with its layout). -/
def elfObject (funcs : List (FnAsm × FnBin)) : ByteArray := Id.run do
  -- .text and function placement
  let mut text : ByteArray := .empty
  let mut placed : Array (Nat × FnAsm × FnBin) := #[]
  for (fa, fb) in funcs do
    placed := placed.push (text.size, fa, fb)
    text := text ++ wordsBytes fb.words
  -- symbols: locals (null, mapping), then defined functions, then undefined targets
  let locals : List ElfSym := mappingSyms (placed.toList.map fun (b, fa, _) => (b, fa))
  let defined : List ElfSym := placed.toList.map fun (b, _, fb) =>
    { name := fb.name, bind := 1, type := 2, shndx := 1, value := b, size := fb.size }
  let targets : List String := (placed.toList.flatMap fun (_, _, fb) => fb.relocs.map (·.sym)).eraseDups
  let undef : List ElfSym := (targets.filter fun t => !defined.any (·.name == t)).map fun t =>
    { name := t, bind := 1, type := 0, shndx := 0, value := 0, size := 0 }
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
  -- section names
  let (shstrtab, shOffs) := strTable [".text", ".rela.text", ".symtab", ".strtab", ".shstrtab"]
  let sh (i : Nat) : Nat := shOffs.getD i 0
  -- file layout
  let textOff := 64
  let relaOff := textOff + text.size + (padTo 8 (textOff + text.size)).size
  let symOff := relaOff + rela.size
  let strOff := symOff + symtab.size
  let shstrOff := strOff + strtab.size
  let shOff := shstrOff + shstrtab.size + (padTo 8 (shstrOff + shstrtab.size)).size
  let header : ByteArray :=
    ⟨#[0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ ++
    le16 1 ++ le16 183 ++ le32 1 ++ le64 0 ++ le64 0 ++ le64 shOff ++ le32 0 ++ le16 64 ++
    le16 0 ++ le16 0 ++ le16 64 ++ le16 6 ++ le16 5
  let shdrs : ByteArray :=
    shdr 0 0 0 0 0 0 0 0 0 ++
    shdr (sh 0) 1 0x6 textOff text.size 0 0 4 0 ++
    shdr (sh 1) 4 0x40 relaOff rela.size 3 1 8 24 ++
    shdr (sh 2) 2 0 symOff symtab.size 4 (1 + locals.length) 8 24 ++
    shdr (sh 3) 3 0 strOff strtab.size 0 0 1 0 ++
    shdr (sh 4) 3 0 shstrOff shstrtab.size 0 0 1 0
  return header ++ text ++ padTo 8 (textOff + text.size) ++ rela ++ symtab ++ strtab ++
    shstrtab ++ padTo 8 (shstrOff + shstrtab.size) ++ shdrs

end Backend
