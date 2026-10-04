/-! # An ELF64 reader (M9, "binary in, binary out"; docs/contracts/e2e.md, "Binary level (M9)")

The executables `cargo fv` links are static (non-PIE) little-endian AArch64 ELF64 files
(`ET_EXEC`, lld, musl): no dynamic section, no interpreter, no dynamic relocations; the OS maps
each `PT_LOAD` segment at its link address (`p_vaddr`), the bytes past `p_filesz` up to
`p_memsz` zero. This file reads such a file in Lean:

* `Rd`: a byte source (the byte at a file offset, when known); `fileRd file` for a whole file,
  `exRd ex` for an **excerpt** `ex` (some ranges of the file: the proof files embed only the
  ranges their checks read). `Ext r r'`: `r'` knows every byte `r` knows; `Agrees file ex`: the
  excerpt's bytes are the file's, so `Ext (exRd ex) (fileRd file)` (`agrees_ext`). Every reader
  below is monotone in its byte source (`*_ext`), so what a check computes from an excerpt holds
  for every file agreeing with it.
* `ehdr` (the ELF header; magic, class, data encoding and entry sizes checked), `phdrs` (the
  program headers), `shdr` (a section header), `symEntry` (an entry of a symbol table: its name's
  file offset and its value), `cstrB` (a NUL-terminated name).
* `loadIn r phs a`: the byte at address `a` of the loaded image (the first `PT_LOAD` segment of
  `phs` containing `a`); `loadMem file`; `ro`/`relro` (in a segment without `PF_W` / in
  `PT_GNU_RELRO`); `Static file` (`ET_EXEC`, `EM_AARCH64`, no `PT_DYNAMIC`/`PT_INTERP`, the
  `PT_LOAD` segments occupy disjoint 64 KiB pages and have `p_filesz ≤ p_memsz`).

Trusted (the loader): the OS loads a `Static` file as `loadMem` describes.
-/

namespace E2E.Elf

/-! ## Byte sources -/

/-- A byte source: the byte at a file offset, when known. -/
abbrev Rd := Nat → Option (BitVec 8)

/-- The bytes of a file. -/
def fileRd (file : ByteArray) : Rd := fun o => file[o]?.map (·.toBitVec)

/-- `r'` extends `r`: every byte `r` knows, `r'` has too. -/
def Ext (r r' : Rd) : Prop := ∀ o b, r o = some b → r' o = some b

/-- An excerpt of a file: ranges `(file offset, bytes)`. -/
abbrev Excerpt := List (Nat × ByteArray)

/-- The byte at `o` of an excerpt (from the first range containing it). -/
def exRd (ex : Excerpt) : Rd := fun o =>
  match ex.find? (fun c => decide (c.1 ≤ o) && decide (o < c.1 + c.2.size)) with
  | some c => c.2[o - c.1]?.map (·.toBitVec)
  | none => none

/-- The excerpt's bytes are the file's. -/
def Agrees (file : ByteArray) (ex : Excerpt) : Prop :=
  ∀ c ∈ ex, ∀ i, i < c.2.size → file[c.1 + i]? = c.2[i]?

theorem agrees_ext {file : ByteArray} {ex : Excerpt} (h : Agrees file ex) :
    Ext (exRd ex) (fileRd file) := by
  intro o b hb
  unfold exRd at hb
  split at hb
  · rename_i c hc
    have hmem := List.mem_of_find?_eq_some hc
    have hp := List.find?_some hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    have := h c hmem (o - c.1) (by omega)
    rw [show c.1 + (o - c.1) = o by omega] at this
    simp only [fileRd, this]
    exact hb
  · cases hb

theorem agrees_append {file : ByteArray} {a b : Excerpt} :
    Agrees file (a ++ b) ↔ Agrees file a ∧ Agrees file b := by
  simp only [Agrees, List.mem_append]
  exact ⟨fun h => ⟨fun c hc => h c (.inl hc), fun c hc => h c (.inr hc)⟩,
    fun h c hc => hc.elim (h.1 c) (h.2 c)⟩

/-- The bytes of a string of hexadecimal digits (two per byte; how the proof files embed
excerpts). -/
def ofHex (s : String) : ByteArray := Id.run do
  let d (c : Char) : Nat :=
    if c.isDigit then c.toNat - '0'.toNat
    else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
    else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10 else 0
  let cs := s.toList.toArray
  let mut out := ByteArray.emptyWithCapacity (cs.size / 2)
  for i in [0:cs.size / 2] do
    out := out.push (UInt8.ofNat (16 * d cs[2 * i]! + d cs[2 * i + 1]!))
  return out

/-- The hexadecimal digits of bytes (`ofHex` reads them back). -/
def toHex (b : ByteArray) : String := Id.run do
  let hx (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  let mut s := ""
  for x in b.data do
    s := (s.push (hx (x.toNat / 16))).push (hx (x.toNat % 16))
  return s

/-! ## Fields -/

/-- The little-endian unsigned `n`-byte value at `o`. -/
def le (r : Rd) (o : Nat) : Nat → Option Nat
  | 0 => some 0
  | n + 1 => (r o).bind fun b => (le r (o + 1) n).map fun v => b.toNat + 256 * v

theorem le_ext {r r' : Rd} (h : Ext r r') : ∀ n o v, le r o n = some v → le r' o n = some v
  | 0, _, _, hv => hv
  | n + 1, o, v, hv => by
    simp only [le, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hv ⊢
    obtain ⟨b, hb, w, hw, rfl⟩ := hv
    exact ⟨b, h _ _ hb, w, le_ext h n _ _ hw, rfl⟩

theorem mapM_ext {α β : Type} {f g : α → Option β} :
    ∀ {l : List α} {vs : List β}, (∀ x ∈ l, ∀ v, f x = some v → g x = some v) →
      l.mapM f = some vs → l.mapM g = some vs
  | [], _, _, h => h
  | x :: l, vs, hfg, h => by
    rw [List.mapM_cons] at h ⊢
    cases hx : f x with
    | none => rw [hx] at h; cases h
    | some y =>
      rw [hx] at h
      cases hl : l.mapM f with
      | none => rw [hl] at h; cases h
      | some ys =>
        rw [hl] at h
        rw [hfg x (.head _) y hx, mapM_ext (fun z hz => hfg z (.tail _ hz)) hl]
        exact h

/-- The fields `(offset, size)` of a record at `o`. -/
def fields (r : Rd) (o : Nat) (spec : List (Nat × Nat)) : Option (List Nat) :=
  spec.mapM fun p => le r (o + p.1) p.2

theorem fields_ext {r r' : Rd} (h : Ext r r') {o : Nat} {spec : List (Nat × Nat)}
    {vs : List Nat} (hv : fields r o spec = some vs) : fields r' o spec = some vs :=
  mapM_ext (fun _ _ _ hp => le_ext h _ _ _ hp) hv

/-! ## Headers -/

/-- The ELF header fields used. -/
structure Ehdr where
  type : Nat
  machine : Nat
  entry : Nat
  phoff : Nat
  shoff : Nat
  phnum : Nat
  shnum : Nat
  deriving Repr, DecidableEq, Inhabited

/-- `e_ident[EI_MAG0..3]`, `EI_CLASS`, `EI_DATA`, `e_type`, `e_machine`, `e_entry`, `e_phoff`,
`e_shoff`, `e_phentsize`, `e_phnum`, `e_shentsize`, `e_shnum`. -/
def ehdrSpec : List (Nat × Nat) :=
  [(0, 4), (4, 1), (5, 1), (16, 2), (18, 2), (24, 8), (32, 8), (40, 8), (54, 2), (56, 2),
   (58, 2), (60, 2)]

/-- An ELF64 little-endian header with 56-byte program and 64-byte section header entries. -/
def mkEhdr : List Nat → Option Ehdr
  | [mag, cls, dat, ty, mach, entry, phoff, shoff, phes, phnum, shes, shnum] =>
    if mag = 0x464c457f ∧ cls = 2 ∧ dat = 1 ∧ phes = 56 ∧ shes = 64 then
      some ⟨ty, mach, entry, phoff, shoff, phnum, shnum⟩
    else none
  | _ => none

def ehdr (r : Rd) : Option Ehdr := (fields r 0 ehdrSpec).bind mkEhdr

theorem ehdr_ext {r r' : Rd} (h : Ext r r') {e : Ehdr} (he : ehdr r = some e) :
    ehdr r' = some e := by
  simp only [ehdr, Option.bind_eq_some_iff] at he ⊢
  obtain ⟨l, hl, he⟩ := he
  exact ⟨l, fields_ext h hl, he⟩

/-- A program header. -/
structure Phdr where
  type : Nat
  flags : Nat
  offset : Nat
  vaddr : Nat
  filesz : Nat
  memsz : Nat
  align : Nat
  deriving Repr, DecidableEq, Inhabited

/-- `p_type`, `p_flags`, `p_offset`, `p_vaddr`, `p_filesz`, `p_memsz`, `p_align`. -/
def phdrSpec : List (Nat × Nat) := [(0, 4), (4, 4), (8, 8), (16, 8), (32, 8), (40, 8), (48, 8)]

def mkPhdr : List Nat → Phdr
  | [t, f, o, v, fs, ms, al] => ⟨t, f, o, v, fs, ms, al⟩
  | _ => default

/-- The program headers. -/
def phdrs (r : Rd) : Option (List Phdr) :=
  (ehdr r).bind fun e =>
    ((List.range e.phnum).mapM fun i => fields r (e.phoff + 56 * i) phdrSpec).map (·.map mkPhdr)

theorem phdrs_ext {r r' : Rd} (h : Ext r r') {phs : List Phdr} (hp : phdrs r = some phs) :
    phdrs r' = some phs := by
  simp only [phdrs, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp ⊢
  obtain ⟨e, he, l, hl, rfl⟩ := hp
  exact ⟨e, ehdr_ext h he, l, mapM_ext (fun i _ v hv => fields_ext h hv) hl, rfl⟩

/-- A section header. -/
structure Shdr where
  type : Nat
  flags : Nat
  addr : Nat
  offset : Nat
  size : Nat
  link : Nat
  entsize : Nat
  deriving Repr, DecidableEq, Inhabited

/-- `sh_type`, `sh_flags`, `sh_addr`, `sh_offset`, `sh_size`, `sh_link`, `sh_entsize`. -/
def shdrSpec : List (Nat × Nat) := [(4, 4), (8, 8), (16, 8), (24, 8), (32, 8), (40, 4), (56, 8)]

def mkShdr : List Nat → Shdr
  | [t, f, a, o, s, l, es] => ⟨t, f, a, o, s, l, es⟩
  | _ => default

/-- Section header `i`. -/
def shdr (r : Rd) (e : Ehdr) (i : Nat) : Option Shdr :=
  if i < e.shnum then (fields r (e.shoff + 64 * i) shdrSpec).map mkShdr else none

theorem shdr_ext {r r' : Rd} (h : Ext r r') {e : Ehdr} {i : Nat} {s : Shdr}
    (hs : shdr r e i = some s) : shdr r' e i = some s := by
  unfold shdr at hs ⊢
  by_cases hi : i < e.shnum
  · simp only [hi, ↓reduceIte, Option.map_eq_some_iff] at hs ⊢
    obtain ⟨l, hl, rfl⟩ := hs
    exact ⟨l, fields_ext h hl, rfl⟩
  · simp [hi] at hs

/-! ## Symbols -/

/-- Entry `i` of the symbol table in section `s` (`SHT_SYMTAB`, 24-byte entries), a defined
symbol (`st_shndx ≠ SHN_UNDEF`): the file offset of its name (in the string table `sh_link`)
and its value `st_value`. -/
def symEntry (r : Rd) (s i : Nat) : Option (Nat × Nat) :=
  (ehdr r).bind fun e => (shdr r e s).bind fun sh =>
    if sh.type = 2 ∧ sh.entsize = 24 ∧ 24 * (i + 1) ≤ sh.size then
      (shdr r e sh.link).bind fun st =>
        (fields r (sh.offset + 24 * i) [(0, 4), (6, 2), (8, 8)]).bind fun l => match l with
          | [nm, ndx, v] =>
            if st.type = 3 ∧ nm < st.size ∧ ndx ≠ 0 then some (st.offset + nm, v) else none
          | _ => none
    else none

theorem symEntry_ext {r r' : Rd} (h : Ext r r') {s i : Nat} {p : Nat × Nat}
    (hp : symEntry r s i = some p) : symEntry r' s i = some p := by
  simp only [symEntry, Option.bind_eq_some_iff] at hp ⊢
  obtain ⟨e, he, sh, hsh, hp⟩ := hp
  refine ⟨e, ehdr_ext h he, sh, shdr_ext h hsh, ?_⟩
  by_cases hc : sh.type = 2 ∧ sh.entsize = 24 ∧ 24 * (i + 1) ≤ sh.size
  · simp only [hc, and_self, ↓reduceIte, Option.bind_eq_some_iff] at hp ⊢
    obtain ⟨st, hst, l, hl, hp⟩ := hp
    exact ⟨st, shdr_ext h hst, l, fields_ext h hl, hp⟩
  · simp [hc] at hp

/-- The NUL-terminated string at `o` is `n`. -/
def cstrB (r : Rd) (o : Nat) (n : String) : Bool :=
  let bs := n.toUTF8
  (List.range bs.size).all (fun j => r (o + j) == some (bs[j]!).toBitVec) &&
    r (o + bs.size) == some 0

theorem cstrB_ext {r r' : Rd} (h : Ext r r') {o : Nat} {n : String} (hc : cstrB r o n = true) :
    cstrB r' o n = true := by
  simp only [cstrB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hc ⊢
  exact ⟨fun j hj => h _ _ (hc.1 j hj), h _ _ hc.2⟩

/-- **The file's symbol table has a symbol named `n` with value `v`.** -/
def SymHas (file : ByteArray) (n : String) (v : Nat) : Prop :=
  ∃ s i o, symEntry (fileRd file) s i = some (o, v) ∧ cstrB (fileRd file) o n = true

/-! ## The loaded image -/

/-- `a` is in the `PT_LOAD` segment `p`. -/
def isLoad (a : Nat) (p : Phdr) : Bool := p.type == 1 && decide (p.vaddr ≤ a) && decide (a < p.vaddr + p.memsz)

/-- The `PT_LOAD` segment containing `a` (the first one). -/
def segIn (phs : List Phdr) (a : Nat) : Option Phdr := phs.find? (isLoad a)

/-- The byte at address `a` of the loaded image: the segment's file byte, `0` past `p_filesz`. -/
def loadIn (r : Rd) (phs : List Phdr) (a : Nat) : Option (BitVec 8) :=
  match segIn phs a with
  | some p => if a - p.vaddr < p.filesz then r (p.offset + (a - p.vaddr)) else some 0
  | none => none

theorem loadIn_ext {r r' : Rd} (h : Ext r r') {phs : List Phdr} {a : Nat} {b : BitVec 8}
    (hb : loadIn r phs a = some b) : loadIn r' phs a = some b := by
  unfold loadIn at hb ⊢
  cases hs : segIn phs a with
  | none => rw [hs] at hb; cases hb
  | some p =>
    rw [hs] at hb
    simp only at hb ⊢
    by_cases hf : a - p.vaddr < p.filesz
    · simp only [hf, ↓reduceIte] at hb ⊢; exact h _ _ hb
    · simp only [hf, ↓reduceIte] at hb ⊢; exact hb

/-- **The memory of the loaded executable** (`none`: unmapped). -/
def loadMem (file : ByteArray) (a : BitVec 64) : Option (BitVec 8) :=
  (phdrs (fileRd file)).bind fun phs => loadIn (fileRd file) phs a.toNat

/-- The segment flags have no `PF_W`. -/
def notW (p : Phdr) : Bool := p.flags % 4 / 2 == 0

/-- `a` is in a segment the program cannot write (no `PF_W`). -/
def ro (file : ByteArray) (a : BitVec 64) : Prop :=
  ∃ phs p, phdrs (fileRd file) = some phs ∧ segIn phs a.toNat = some p ∧ notW p = true

/-- `PT_GNU_RELRO`. -/
def relroType : Nat := 0x6474e552

/-- `a` is in `PT_GNU_RELRO`, writable during startup only (static musl does not `mprotect`
it: what holds there is the file's bytes at entry). -/
def relro (file : ByteArray) (a : BitVec 64) : Prop :=
  ∃ phs, phdrs (fileRd file) = some phs ∧ ∃ p ∈ phs, p.type = relroType ∧
    p.vaddr ≤ a.toNat ∧ a.toNat < p.vaddr + p.memsz

/-- The 64 KiB pages of a `PT_LOAD` segment are not another's. -/
def pagesApart (p q : Phdr) : Bool :=
  decide ((p.vaddr + p.memsz + 65535) / 65536 ≤ q.vaddr / 65536) ||
    decide ((q.vaddr + q.memsz + 65535) / 65536 ≤ p.vaddr / 65536)

/-- A static AArch64 executable whose image `loadMem` describes: `ET_EXEC`, `EM_AARCH64`, no
`PT_DYNAMIC` or `PT_INTERP`, `PT_LOAD` segments in disjoint pages with `p_filesz ≤ p_memsz`. -/
def staticB (e : Ehdr) (phs : List Phdr) : Bool :=
  let ls := (phs.filter (·.type == 1)).zipIdx
  e.type == 2 && e.machine == 183 && phs.all (fun p => p.type != 2 && p.type != 3) &&
    ls.all (fun x => decide (x.1.filesz ≤ x.1.memsz) &&
      ls.all fun y => x.2 == y.2 || pagesApart x.1 y.1)

/-- **The file is a static AArch64 executable** (`staticB`). -/
def Static (file : ByteArray) : Prop :=
  ∃ e phs, ehdr (fileRd file) = some e ∧ phdrs (fileRd file) = some phs ∧ staticB e phs = true

/-- The offset of a thread-local symbol of value `v` (`st_value` of an `STT_TLS` symbol in an
executable: its offset in the TLS segment) from the thread pointer (AArch64, TLS variant 1: a
16-byte TCB, then the TLS block aligned to `PT_TLS`'s `p_align`). -/
def tpOff (phs : List Phdr) (v : Nat) : Option Nat :=
  (phs.find? (·.type == 7)).map fun p => let al := max p.align 1; (16 + al - 1) / al * al + v

end E2E.Elf
