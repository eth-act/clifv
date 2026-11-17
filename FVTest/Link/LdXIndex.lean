import FV.Link.Ld.Resolve

/-! # `lean-ld` on an object with more than `0xff00` sections (#1077)

ruint's codegen unit, merged by `ld -r`, has 551,555 sections; a symbol of section 264,603 has
`st_shndx = SHN_XINDEX` (`0xffff`) and its index in the `SHT_SYMTAB_SHNDX` section. `xindexObj n`
is a relocatable AArch64 object with `n` sections, the count and `e_shstrndx` in section header
0 (`e_shnum = 0`, `e_shstrndx = 0xffff`), and a global function `f` in its last section, through
`SHN_XINDEX`. `Obj.parse` reads the extended index (`Sym.xidx`) and `Sym.inSec` holds: `f` is
defined in that section, not undefined. -/

namespace Link.Ld

private def le (n w : Nat) : Array UInt8 :=
  (Array.range w).map fun i => UInt8.ofNat ((n >>> (8 * i)) % 256)

/-- A section header. -/
private def shdr (name type flags off size link info align entsize : Nat) : Array UInt8 :=
  le name 4 ++ le type 4 ++ le flags 8 ++ le 0 8 ++ le off 8 ++ le size 8 ++ le link 4 ++
    le info 4 ++ le align 8 ++ le entsize 8

/-- The object: ELF header (64 bytes), `.shstrtab` at 64 (47 bytes), `.strtab` at 111, `.symtab`
at 120 (the null symbol and `f`), `.symtab_shndx` at 168, the code (`ret`) at 176, the section
headers at 184: null (`sh_size` the count, `sh_link` `e_shstrndx`), `.shstrtab`, `.strtab`,
`.symtab`, `.symtab_shndx`, then `.text` sections up to `n`. -/
def xindexObj (n : Nat) : ByteArray := Id.run do
  let mut b : Array UInt8 := #[0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0] ++ Array.replicate 8 0
  b := b ++ le 1 2 ++ le 183 2 ++ le 1 4 ++ le 0 8 ++ le 0 8 ++ le 184 8 ++ le 0 4 ++ le 64 2 ++
    le 0 2 ++ le 0 2 ++ le 64 2 ++ le 0 2 ++ le 0xffff 2
  b := b ++ "\x00.text\x00.symtab\x00.strtab\x00.shstrtab\x00.symtab_shndx\x00".toUTF8.data
  b := b ++ "\x00f\x00".toUTF8.data ++ Array.replicate 6 0
  b := b ++ Array.replicate 24 0 ++ le 1 4 ++ #[0x12, 0] ++ le 0xffff 2 ++ le 0 8 ++ le 4 8
  b := b ++ le 0 4 ++ le (n - 1) 4
  b := b ++ le 0xd65f03c0 4 ++ Array.replicate 4 0
  b := b ++ shdr 0 0 0 0 n 1 0 0 0
  b := b ++ shdr 23 3 0 64 47 0 0 1 0
  b := b ++ shdr 15 3 0 111 3 0 0 1 0
  b := b ++ shdr 7 2 0 120 48 2 1 8 24
  b := b ++ shdr 33 18 0 168 8 3 0 4 4
  for _ in [5:n] do
    b := b ++ shdr 1 1 6 176 4 0 0 4 0
  return ⟨b⟩

/-- `f` (symbol 1) parses with its extended section index `n - 1` and is defined there. -/
def xindexOk (n : Nat) : Bool :=
  match Obj.parse "xindex.o" "xindex.o" (xindexObj n) with
  | .ok o =>
    o.secs.size == n && o.syms.size == 2 && (o.syms[1]!).name == "f" &&
      (o.syms[1]!).shndx == n - 1 && (o.syms[1]!).xidx && (o.syms[1]!).inSec &&
      (o.secs[n - 1]!).name == ".text"
  | .error _ => false

#guard xindexOk (0xff00 + 4)

end Link.Ld
