import FV.E2E.LinkCheck
import FV.E2E.Elf

/-! # Binary checks: code bytes, data objects, GOT, symbols (M9 items 1 and 2)

docs/contracts/e2e.md, "Binary level (M9)". The crate theorem (`crate_correct`) is about the
image the Lean pipeline rebuilds (`LinkSys.ofInput I B F`: each function's words `fb.words` at
its link-map address, relocated fields **zero**; the machine `ArmStepX` runs `bl`/`adrp`/`ldr`
/`add`/TLSDESC through hooks and the link map `I.symAddr`). These checks relate it to the
executable file, read by the ELF reader `FV/E2E/Elf.lean`:

* **Statement names (the interface).** For a file `file : ByteArray`:
  - `Elf.loadMem file : BitVec 64 → Option (BitVec 8)` (the loaded image), `Elf.ro file a`
    (no `PF_W`), `Elf.relro file a`, `Elf.Static file`, `Elf.SymHas file n v`;
  - `readN (loadMem file) n a`: the `n` bytes at `a` as `Arm.read_mem_bytes` reads them;
  - `ArtOk I file a` (per compiled function `a`): every byte of its code is `ro`; every word
    without a relocation is the compiled word (`plain`); every relocation is resolved
    (`RelocOk`): `bl` → `blW (T - P)` with `T = I.baseOf sym`; an `adrp`/`add` or GOT
    `adrp`/`ldr` pair → `PairOk` (the executable's two words put `T = I.symAddr sym addend`
    into the compiled `adrp`'s register `rd`: `adrp`+`add` (the compiled pair with its
    immediates resolved; `cargo fv` links with `--no-relax`, so lld's `nop`+`adr` relaxation
    is not accepted), or, for the GOT, `adrp`+`ldr` of a GOT slot `G` with `readN (loadMem file) 8 G = T`); a
    TLSDESC sequence → lld's local-exec relaxation `movz x0`/`movk x0`/`nop`/`nop` of the
    symbol's thread-pointer offset (`TpOff`);
  - `DataOk I file o` (per CLIF data object `o`): at `I.addrOf o.name` the loaded image holds
    `objBytes I o` (its bytes, each `%sym+off` item as the 8 little-endian bytes of
    `I.addrOf sym + off`); a read-only object's bytes are `ro` or `relro`;
  - `SymsOk I file`: every link-map entry `(n, v) ∈ I.addrs` (but the self-call aliases'
    fresh addresses) is a defined symbol `n` of value `v` in the file's symbol table;
  - **`BinOk I D file`**: `Static file`, `ArtOk` for every function of `tabOf I.results`,
    `DataOk` for every `o ∈ D`, `SymsOk`.
* **Consequences** for the boundary theorem: `img_bytes` (with `okB I`: every code address of
  the image is `ro`, and holds the image's byte `memT (tabOf I.results) a` unless it is a byte
  of a relocated word, `RelocAt`), `dataByte_sound` / `roByte_sound` (the resolved byte of a
  data object / a read-only one, `dataByte I D a` / `roByte I D a`, is the loaded byte).
* **Checkers** on an excerpt `ex` of the file (`Elf.Excerpt`): `hdrB` (`Static`), `codeB I ex
  fs` (`ArtOk` for the functions `fs` of the input, one slice at a time), `dataB I D ex`,
  `symsB I ex cert` (`cert`: where each symbol is). Soundness: `hdrB_sound`, `codeB_sound`,
  `dataB_sound`, `symsB_sound`, for every `file` with `Agrees file ex`; `binOk_of` assembles
  `BinOk`. A crate's proof (`crate-proofs/Crates/NAME*.lean`, written by `link-check`)
  evaluates them by `native_decide` on the excerpts it embeds and proves
  `bin_ok : ∀ file, Agrees file exAll → BinOk input dataObjs file`.
-/

namespace E2E.BinCheck

open E2E E2E.LinkCheck Backend Elf

/-! ## Partial memories and their words -/

/-- A partial memory (`none`: no byte there). -/
abbrev PMem := BitVec 64 → Option (BitVec 8)

/-- The Arm state with memory `m` (absent bytes `0`). -/
def stOf (m : PMem) : Arm.ArmState := setMem Arm.ArmState.default fun a => (m a).getD 0

/-- **The `n` bytes at `a`** (little-endian, as `Arm.read_mem_bytes`), when all are present. -/
def readN (m : PMem) (n : Nat) (a : BitVec 64) : Option (BitVec (n * 8)) :=
  if (List.range n).all (fun i => (m (a + BitVec.ofNat 64 i)).isSome) then
    some (Arm.read_mem_bytes n a (stOf m))
  else none

/-- `m'` extends `m`. -/
def PExt (m m' : PMem) : Prop := ∀ a b, m a = some b → m' a = some b

theorem readN_bytes {m : PMem} {n : Nat} {a : BitVec 64} {w : BitVec (n * 8)}
    (h : readN m n a = some w) :
    Arm.read_mem_bytes n a (stOf m) = w ∧ ∀ i < n, ∃ b, m (a + BitVec.ofNat 64 i) = some b ∧
      (stOf m).mem (a + BitVec.ofNat 64 i) = b := by
  unfold readN at h
  by_cases hall : (List.range n).all (fun i => (m (a + BitVec.ofNat 64 i)).isSome) = true
  · simp only [hall, ↓reduceIte, Option.some.injEq] at h
    refine ⟨h, fun i hi => ?_⟩
    have := List.all_eq_true.1 hall i (List.mem_range.2 hi)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 this
    exact ⟨b, hb, by simp [stOf, setMem, hb]⟩
  · simp only [hall, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

theorem readN_ext {m m' : PMem} (h : PExt m m') {n : Nat} {a : BitVec 64} {w : BitVec (n * 8)}
    (hr : readN m n a = some w) : readN m' n a = some w := by
  obtain ⟨hw, hb⟩ := readN_bytes hr
  unfold readN
  have hall : (List.range n).all (fun i => (m' (a + BitVec.ofNat 64 i)).isSome) = true := by
    refine List.all_eq_true.2 fun i hi => ?_
    obtain ⟨b, hb1, -⟩ := hb i (List.mem_range.1 hi)
    simp [h _ _ hb1]
  simp only [hall, ↓reduceIte, Option.some.injEq]
  rw [← hw]
  exact rmb_congr n a fun i hi => by
    obtain ⟨b, hb1, -⟩ := hb i hi
    simp [stOf, setMem, hb1, h _ _ hb1]

/-- The loaded image of an excerpt's byte source with program headers `phs`. -/
def memIn (r : Rd) (phs : List Phdr) : PMem := fun a => loadIn r phs a.toNat

theorem memIn_ext {file : ByteArray} {ex : Excerpt} (hA : Agrees file ex) {phs : List Phdr}
    (hp : phdrs (exRd ex) = some phs) : PExt (memIn (exRd ex) phs) (loadMem file) := by
  intro a b hb
  simp only [loadMem, phdrs_ext (agrees_ext hA) hp, Option.bind_some]
  exact loadIn_ext (agrees_ext hA) hb

/-- `a` is in a `PT_LOAD` segment of `phs` without `PF_W`. -/
def roB (phs : List Phdr) (a : BitVec 64) : Bool :=
  match segIn phs a.toNat with
  | some p => notW p
  | none => false

/-- `a` is in a `PT_GNU_RELRO` segment of `phs`. -/
def relroB (phs : List Phdr) (a : BitVec 64) : Bool :=
  phs.any fun p => p.type == relroType && decide (p.vaddr ≤ a.toNat) &&
    decide (a.toNat < p.vaddr + p.memsz)

theorem roB_sound {file : ByteArray} {ex : Excerpt} (hA : Agrees file ex) {phs : List Phdr}
    (hp : phdrs (exRd ex) = some phs) {a : BitVec 64} (h : roB phs a = true) : Elf.ro file a := by
  unfold roB at h
  split at h
  · rename_i p hs
    exact ⟨phs, p, phdrs_ext (agrees_ext hA) hp, hs, h⟩
  · cases h

theorem relroB_sound {file : ByteArray} {ex : Excerpt} (hA : Agrees file ex) {phs : List Phdr}
    (hp : phdrs (exRd ex) = some phs) {a : BitVec 64} (h : relroB phs a = true) :
    Elf.relro file a := by
  simp only [relroB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨p, hp', ⟨h1, h2⟩, h3⟩ := h
  exact ⟨phs, phdrs_ext (agrees_ext hA) hp, p, hp', h1, h2, h3⟩

/-! ## Instruction words (Arm ARM C6.2) -/

/-- The Rd/Rt field (bits 4:0) of a word. -/
def rd5 (w : BitVec 32) : Nat := w.toNat % 32

/-- A signed 21-bit immediate as its two's-complement field. -/
def imm21 (d : Int) : Nat := (d % 2 ^ 21).toNat

/-- `ADRP` (`op = 1`) of register `rd` with immediate `d` (`immhi:immlo`). -/
def adrLike (op rd : Nat) (d : Int) : BitVec 32 :=
  BitVec.ofNat 32 (op * 2 ^ 31 + imm21 d % 4 * 2 ^ 29 + 0x10000000 + imm21 d / 4 * 32 + rd)

/-- `ADRP Xrd, page(pc) + dp pages`. -/
def adrpW (rd : Nat) (dp : Int) : BitVec 32 := adrLike 1 rd dp

/-- `ADD Xrd, Xrn, #imm` (64-bit, immediate, no shift). -/
def addW (rd rn imm : Nat) : BitVec 32 := BitVec.ofNat 32 (0x91000000 + imm * 1024 + rn * 32 + rd)

/-- `LDR Xrt, [Xrn, #8 * imm]` (64-bit, unsigned offset). -/
def ldrW (rt rn imm : Nat) : BitVec 32 := BitVec.ofNat 32 (0xf9400000 + imm * 1024 + rn * 32 + rt)

/-- `BL pc + d`. -/
def blW (d : Int) : BitVec 32 := BitVec.ofNat 32 (0x94000000 + (d / 4 % 2 ^ 26).toNat)

/-- `NOP`. -/
def nopW : BitVec 32 := BitVec.ofNat 32 0xd503201f

/-- `MOVZ Xrd, #imm, LSL #16`. -/
def movzW (rd imm : Nat) : BitVec 32 := BitVec.ofNat 32 (0xd2a00000 + imm * 32 + rd)

/-- `MOVK Xrd, #imm`. -/
def movkW (rd imm : Nat) : BitVec 32 := BitVec.ofNat 32 (0xf2800000 + imm * 32 + rd)

/-- `lo ≤ d < hi`. -/
def inR (lo hi d : Int) : Bool := decide (lo ≤ d) && decide (d < hi)

/-- The 4 KiB page number of an address. -/
def pageOf (x : Nat) : Int := ((x / 4096 : Nat) : Int)

/-- A `bl` reaches `d` (word-aligned, ±128 MiB). -/
def blRange (d : Int) : Bool := d % 4 == 0 && inR (-2 ^ 27) (2 ^ 27) d

/-- The GOT slot an `adrp`/`ldr` pair at `P` loads from. -/
def gotOf (P : Nat) (x0 x1 : BitVec 32) : Nat :=
  let imm : Nat := x0.toNat / 32 % 2 ^ 19 * 4 + x0.toNat / 2 ^ 29 % 4
  let s : Int := if imm < 2 ^ 20 then imm else (imm : Int) - 2 ^ 21
  ((pageOf P + s) * 4096).toNat + x1.toNat / 1024 % 4096 * 8

/-! ## The resolved code -/

/-- **The executable's words `x0`, `x1` at `P`, `P + 4` put the address `T` into register
`rd`**, as the compiled pair with resolved immediates (lld with `--no-relax`): `ADRP`+`ADD`; for
a GOT access (`got`), `ADRP`+`LDR` of a GOT slot `G` holding `T`. -/
inductive PairOk (m : PMem) (P T rd : Nat) (got : Bool) (x0 x1 : BitVec 32) : Prop
  | adrpAdd : inR (-2 ^ 20) (2 ^ 20) (pageOf T - pageOf P) = true →
      x0 = adrpW rd (pageOf T - pageOf P) → x1 = addW rd rd (T % 4096) → PairOk m P T rd got x0 x1
  | adrpLdr (G : Nat) : got = true → G % 8 = 0 → inR (-2 ^ 20) (2 ^ 20) (pageOf G - pageOf P) = true →
      x0 = adrpW rd (pageOf G - pageOf P) → x1 = ldrW rd rd (G % 4096 / 8) →
      readN m 8 (BitVec.ofNat 64 G) = some (BitVec.ofNat (8 * 8) T) → PairOk m P T rd got x0 x1

def pairB (m : PMem) (P T rd : Nat) (got : Bool) (x0 x1 : BitVec 32) : Bool :=
  (inR (-2 ^ 20) (2 ^ 20) (pageOf T - pageOf P) && x0 == adrpW rd (pageOf T - pageOf P) &&
    x1 == addW rd rd (T % 4096)) ||
  (let G := gotOf P x0 x1
   got && G % 8 == 0 && inR (-2 ^ 20) (2 ^ 20) (pageOf G - pageOf P) &&
    x0 == adrpW rd (pageOf G - pageOf P) && x1 == ldrW rd rd (G % 4096 / 8) &&
    readN m 8 (BitVec.ofNat 64 G) == some (BitVec.ofNat (8 * 8) T))

theorem pairB_sound {m m' : PMem} (hm : PExt m m') {P T rd : Nat} {got : Bool}
    {x0 x1 : BitVec 32} (h : pairB m P T rd got x0 x1 = true) : PairOk m' P T rd got x0 x1 := by
  simp only [pairB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with (⟨⟨h1, h2⟩, h3⟩ | h)
  · exact .adrpAdd h1 h2 h3
  · obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    exact .adrpLdr _ h1 h2 h3 h4 h5 (readN_ext hm h6)

/-- The address of offset `o` of a compiled function. -/
def wAt (a : Art) (o : Nat) : BitVec 64 := a.base + BitVec.ofNat 64 o

/-- The thread-pointer offset of a thread-local symbol of value `v` in the file. -/
def TpOff (file : ByteArray) (v : Nat) : Option Nat := (phdrs (fileRd file)).bind (tpOff · v)

/-- The page relocation of a pair and its low-12-bits partner. -/
def loOf : RelocType → RelocType
  | .adrGotPage => .ld64GotLo12Nc
  | _ => .addAbsLo12Nc

/-- **Relocation `r` of the compiled function `a` is resolved in the file** (by its type). -/
def RelocOk (I : LinkInput) (file : ByteArray) (a : Art) (r : Reloc) : Prop :=
  let o := r.offset
  let m := loadMem file
  o % 4 = 0 ∧ match r.type with
  | .call26 =>
    a.fb.words[o / 4]? = some (blW 0) ∧ blRange ((I.baseOf r.sym : Int) - (wAt a o).toNat) = true ∧
      readN m 4 (wAt a o) = some (blW ((I.baseOf r.sym : Int) - (wAt a o).toNat))
  | .adrGotPage | .adrPrelPgHi21 =>
    let got := decide (r.type = .adrGotPage)
    ∃ rd x0 x1, a.fb.words[o / 4]? = some (adrpW rd 0) ∧
      a.fb.words[o / 4 + 1]? = some (if got then ldrW rd rd 0 else addW rd rd 0) ∧
      (∃ r' ∈ a.fb.relocs, r'.offset = o + 4 ∧ r'.type = loOf r.type ∧ r'.sym = r.sym ∧
        r'.addend = r.addend) ∧
      readN m 4 (wAt a o) = some x0 ∧ readN m 4 (wAt a (o + 4)) = some x1 ∧
      PairOk m (wAt a o).toNat (I.symAddr r.sym r.addend).toNat rd got x0 x1
  | .ld64GotLo12Nc | .addAbsLo12Nc =>
    ∃ r' ∈ a.fb.relocs, r'.offset + 4 = o ∧ (r'.type = .adrGotPage ∨ r'.type = .adrPrelPgHi21)
  | .tlsDescAdrPage21 =>
    ∃ v, TpOff file (I.addrOf r.sym) = some v ∧ v < 2 ^ 32 ∧
      readN m 4 (wAt a o) = some (movzW 0 (v / 65536)) ∧
      readN m 4 (wAt a (o + 4)) = some (movkW 0 (v % 65536)) ∧
      readN m 4 (wAt a (o + 8)) = some nopW ∧ readN m 4 (wAt a (o + 12)) = some nopW
  | .tlsDescLd64Lo12 => ∃ r' ∈ a.fb.relocs, r'.type = .tlsDescAdrPage21 ∧ r'.offset + 4 = o
  | .tlsDescAddLo12 => ∃ r' ∈ a.fb.relocs, r'.type = .tlsDescAdrPage21 ∧ r'.offset + 8 = o
  | .tlsDescCall => ∃ r' ∈ a.fb.relocs, r'.type = .tlsDescAdrPage21 ∧ r'.offset + 12 = o

/-- The check of `RelocOk` on the image `m` with program headers `phs`. -/
def relocB (I : LinkInput) (m : PMem) (phs : List Phdr) (a : Art) (r : Reloc) : Bool :=
  let o := r.offset
  o % 4 == 0 && match r.type with
  | .call26 =>
    let d : Int := (I.baseOf r.sym : Int) - (wAt a o).toNat
    a.fb.words[o / 4]? == some (blW 0) && blRange d && readN m 4 (wAt a o) == some (blW d)
  | .adrGotPage | .adrPrelPgHi21 =>
    let got := decide (r.type = .adrGotPage)
    let rd := rd5 (a.fb.words[o / 4]?.getD 0)
    a.fb.words[o / 4]? == some (adrpW rd 0) &&
      a.fb.words[o / 4 + 1]? == some (if got then ldrW rd rd 0 else addW rd rd 0) &&
      a.fb.relocs.any (fun r' => r'.offset == o + 4 && decide (r'.type = loOf r.type) &&
        r'.sym == r.sym && r'.addend == r.addend) &&
      (match readN m 4 (wAt a o), readN m 4 (wAt a (o + 4)) with
       | some x0, some x1 => pairB m (wAt a o).toNat (I.symAddr r.sym r.addend).toNat rd got x0 x1
       | _, _ => false)
  | .ld64GotLo12Nc | .addAbsLo12Nc =>
    a.fb.relocs.any fun r' => r'.offset + 4 == o &&
      decide (r'.type = .adrGotPage ∨ r'.type = .adrPrelPgHi21)
  | .tlsDescAdrPage21 =>
    match tpOff phs (I.addrOf r.sym) with
    | some v => decide (v < 2 ^ 32) && readN m 4 (wAt a o) == some (movzW 0 (v / 65536)) &&
      readN m 4 (wAt a (o + 4)) == some (movkW 0 (v % 65536)) &&
      readN m 4 (wAt a (o + 8)) == some nopW && readN m 4 (wAt a (o + 12)) == some nopW
    | none => false
  | .tlsDescLd64Lo12 =>
    a.fb.relocs.any fun r' => decide (r'.type = .tlsDescAdrPage21) && r'.offset + 4 == o
  | .tlsDescAddLo12 =>
    a.fb.relocs.any fun r' => decide (r'.type = .tlsDescAdrPage21) && r'.offset + 8 == o
  | .tlsDescCall =>
    a.fb.relocs.any fun r' => decide (r'.type = .tlsDescAdrPage21) && r'.offset + 12 == o

theorem relocB_sound {I : LinkInput} {file : ByteArray} {ex : Excerpt} (hA : Agrees file ex)
    {phs : List Phdr} (hp : phdrs (exRd ex) = some phs) {a : Art} {r : Reloc}
    (h : relocB I (memIn (exRd ex) phs) phs a r = true) : RelocOk I file a r := by
  have hm := memIn_ext hA hp
  have hph : phdrs (fileRd file) = some phs := phdrs_ext (agrees_ext hA) hp
  obtain ⟨o, ty, sym, add⟩ := r
  cases ty with
  | call26 =>
    simp only [relocB, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1, h.2.1.1, h.2.1.2, readN_ext hm h.2.2⟩
  | adrGotPage | adrPrelPgHi21 =>
    simp only [relocB, Bool.and_eq_true, beq_iff_eq, List.any_eq_true, decide_eq_true_eq] at h
    obtain ⟨ho, ⟨⟨h1, h2⟩, ⟨r', hr', hr'2⟩⟩, h4⟩ := h
    refine ⟨by simpa using ho, ?_⟩
    split at h4
    · rename_i x0 x1 e0 e1
      exact ⟨_, x0, x1, h1, h2, ⟨r', hr', hr'2.1.1.1, hr'2.1.1.2, hr'2.1.2, hr'2.2⟩,
        readN_ext hm e0, readN_ext hm e1, pairB_sound hm h4⟩
    · cases h4
  | ld64GotLo12Nc | addAbsLo12Nc =>
    simp only [relocB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨ho, r', hr', h1, h2⟩ := h
    exact ⟨by simpa using ho, r', hr', h1, h2⟩
  | tlsDescAdrPage21 =>
    simp only [relocB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨ho, h⟩ := h
    refine ⟨by simpa using ho, ?_⟩
    split at h
    · rename_i v hv
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
      exact ⟨v, by simp [TpOff, hph, hv], h1, readN_ext hm h2, readN_ext hm h3,
        readN_ext hm h4, readN_ext hm h5⟩
    · cases h
  | tlsDescLd64Lo12 | tlsDescAddLo12 | tlsDescCall =>
    simp only [relocB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨ho, r', hr', h1, h2⟩ := h
    exact ⟨by simpa using ho, r', hr', h1, h2⟩

/-- **The compiled function `a` is in the file**: its code is not writable, every word without
a relocation is the compiled word, every relocation is resolved (`RelocOk`). -/
structure ArtOk (I : LinkInput) (file : ByteArray) (a : Art) : Prop where
  ro : ∀ k < a.fb.words.size, ∀ i < 4, Elf.ro file (wAt a (4 * k + i))
  plain : ∀ k w, a.fb.words[k]? = some w → (∀ r ∈ a.fb.relocs, r.offset ≠ 4 * k) →
    readN (loadMem file) 4 (wAt a (4 * k)) = some w
  reloc : ∀ r ∈ a.fb.relocs, RelocOk I file a r

/-- The check of `ArtOk`. -/
def artB (I : LinkInput) (r : Rd) (phs : List Phdr) (a : Art) : Bool :=
  let m := memIn r phs
  (List.range a.fb.words.size).all (fun k =>
    (List.range 4).all (fun i => roB phs (wAt a (4 * k + i))) &&
    (a.fb.relocs.any (·.offset == 4 * k) ||
      readN m 4 (wAt a (4 * k)) == some (a.fb.words[k]?.getD 0))) &&
  a.fb.relocs.all (relocB I m phs a)

theorem artB_sound {I : LinkInput} {file : ByteArray} {ex : Excerpt} (hA : Agrees file ex)
    {phs : List Phdr} (hp : phdrs (exRd ex) = some phs) {a : Art}
    (h : artB I (exRd ex) phs a = true) : ArtOk I file a := by
  simp only [artB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hw, hr⟩ := h
  refine ⟨fun k hk i hi => roB_sound hA hp ((hw k hk).1 i hi),
    fun k w hk hno => ?_, fun r hr' => relocB_sound hA hp (hr r hr')⟩
  have hk' : k < a.fb.words.size := (Array.getElem?_eq_some_iff.1 hk).1
  have := (hw k hk').2
  simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq, hk, Option.getD_some] at this
  rcases this with ⟨r, hr', hro⟩ | h
  · exact absurd hro (hno r hr')
  · exact readN_ext (memIn_ext hA hp) h

/-- The compiled image of a function of the input (`I.results`' entry for it). -/
def artIn (I : LinkInput) (fi : FnInput) : Art :=
  getOk (pipe fi.func fi.k (BitVec.ofNat 64 (I.baseOf fi.func.name)) (raJ fi.ra fi.j))

/-- **The code check of the functions `fs`** (a slice of the input's) on an excerpt. -/
def codeB (I : LinkInput) (ex : Excerpt) (fs : List FnInput) : Bool :=
  match phdrs (exRd ex) with
  | some phs => fs.all fun fi => artB I (exRd ex) phs (artIn I fi)
  | none => false

/-- `ArtOk` for the functions `fs`. -/
def ArtsOk (I : LinkInput) (file : ByteArray) (fs : List FnInput) : Prop :=
  ∀ fi ∈ fs, ArtOk I file (artIn I fi)

theorem artsOk_append {I : LinkInput} {file : ByteArray} {l₁ l₂ : List FnInput}
    (h₁ : ArtsOk I file l₁) (h₂ : ArtsOk I file l₂) : ArtsOk I file (l₁ ++ l₂) := by
  intro fi hfi
  rcases List.mem_append.1 hfi with h | h
  · exact h₁ fi h
  · exact h₂ fi h

theorem codeB_sound {I : LinkInput} {ex : Excerpt} {fs : List FnInput}
    (h : codeB I ex fs = true) {file : ByteArray} (hA : Agrees file ex) : ArtsOk I file fs := by
  unfold codeB at h
  split at h
  · rename_i phs hp
    exact fun fi hfi => artB_sound hA hp (List.all_eq_true.1 h fi hfi)
  · cases h

/-! ## Data objects -/

/-- The bytes of a data item: a byte, or the 8 little-endian bytes of `I.addrOf n + off`. -/
def itemBytes (I : LinkInput) : Clif.DataItem → List (BitVec 8)
  | .byte b => [b]
  | .addr n off =>
    let v := BitVec.ofInt 64 ((I.addrOf n : Int) + off)
    (List.range 8).map fun j => v.extractLsb' (8 * j) 8

/-- **The resolved bytes of a data object.** -/
def objBytes (I : LinkInput) (o : Clif.DataObject) : List (BitVec 8) := o.items.flatMap (itemBytes I)

/-- The address of a data object: its link-map address. -/
def objAt (I : LinkInput) (o : Clif.DataObject) : BitVec 64 := BitVec.ofNat 64 (I.addrOf o.name)

/-- **The data object `o` is in the file** at its link-map address, with its resolved bytes;
a read-only object is not writable (or in `PT_GNU_RELRO`). -/
structure DataOk (I : LinkInput) (file : ByteArray) (o : Clif.DataObject) : Prop where
  addr : (I.addrs.lookup o.name).isSome = true
  bytes : ∀ i b, (objBytes I o)[i]? = some b →
    loadMem file (objAt I o + BitVec.ofNat 64 i) = some b
  ro : o.writable = false → ∀ i < (objBytes I o).length,
    Elf.ro file (objAt I o + BitVec.ofNat 64 i) ∨ Elf.relro file (objAt I o + BitVec.ofNat 64 i)

def objB (I : LinkInput) (r : Rd) (phs : List Phdr) (o : Clif.DataObject) : Bool :=
  let bs := objBytes I o
  (I.addrs.lookup o.name).isSome &&
    (List.range bs.length).all fun i =>
      let x := objAt I o + BitVec.ofNat 64 i
      loadIn r phs x.toNat == some (bs[i]?.getD 0) && (o.writable || roB phs x || relroB phs x)

/-- **The data check** of the objects `D` on an excerpt. -/
def dataB (I : LinkInput) (D : List Clif.DataObject) (ex : Excerpt) : Bool :=
  match phdrs (exRd ex) with
  | some phs => D.all (objB I (exRd ex) phs)
  | none => false

theorem objB_sound {I : LinkInput} {file : ByteArray} {ex : Excerpt} (hA : Agrees file ex)
    {phs : List Phdr} (hp : phdrs (exRd ex) = some phs) {o : Clif.DataObject}
    (h : objB I (exRd ex) phs o = true) : DataOk I file o := by
  simp only [objB, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq] at h
  obtain ⟨ha, hb⟩ := h
  refine ⟨ha, fun i b hi => ?_, fun hw i hi => ?_⟩
  · have hl : i < (objBytes I o).length := (List.getElem?_eq_some_iff.1 hi).1
    have := (hb i hl).1
    rw [hi, Option.getD_some] at this
    exact memIn_ext hA hp _ _ this
  · rcases (hb i hi).2 with (h | h) | h
    · rw [hw] at h; cases h
    · exact .inl (roB_sound hA hp h)
    · exact .inr (relroB_sound hA hp h)

theorem dataB_sound {I : LinkInput} {D : List Clif.DataObject} {ex : Excerpt}
    (h : dataB I D ex = true) {file : ByteArray} (hA : Agrees file ex) :
    ∀ o ∈ D, DataOk I file o := by
  unfold dataB at h
  split at h
  · rename_i phs hp
    exact fun o ho => objB_sound hA hp (List.all_eq_true.1 h o ho)
  · cases h

/-- The resolved byte at `a` of the first object of `D` containing it. -/
def objByte (I : LinkInput) (D : List Clif.DataObject) (a : BitVec 64) : Option (BitVec 8) :=
  D.findSome? fun o => (objBytes I o)[(a - objAt I o).toNat]?

/-- **The resolved byte at `a` of a CLIF data object** (`none`: no object there). -/
def dataByte (I : LinkInput) (D : List Clif.DataObject) (a : BitVec 64) : Option (BitVec 8) :=
  objByte I D a

/-- **The resolved byte at `a` of a read-only CLIF data object.** -/
def roByte (I : LinkInput) (D : List Clif.DataObject) (a : BitVec 64) : Option (BitVec 8) :=
  objByte I (D.filter (!·.writable)) a

theorem objByte_spec {I : LinkInput} {D : List Clif.DataObject} {a : BitVec 64} {b : BitVec 8}
    (h : objByte I D a = some b) : ∃ o ∈ D, (objBytes I o)[(a - objAt I o).toNat]? = some b := by
  obtain ⟨o, ho, hb⟩ := List.exists_of_findSome?_eq_some h
  exact ⟨o, ho, hb⟩

theorem objAt_add (I : LinkInput) (o : Clif.DataObject) (a : BitVec 64) :
    objAt I o + BitVec.ofNat 64 (a - objAt I o).toNat = a := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

/-- **The loaded image holds the resolved bytes of the data objects.** -/
theorem dataByte_sound {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hD : ∀ o ∈ D, DataOk I file o) {a : BitVec 64} {b : BitVec 8} (h : dataByte I D a = some b) :
    loadMem file a = some b := by
  obtain ⟨o, ho, hb⟩ := objByte_spec h
  have := (hD o ho).bytes _ _ hb
  rwa [objAt_add] at this

/-- **The loaded image holds the resolved bytes of the read-only data objects**, in a
segment without `PF_W` or in `PT_GNU_RELRO`. -/
theorem roByte_sound {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hD : ∀ o ∈ D, DataOk I file o) {a : BitVec 64} {b : BitVec 8} (h : roByte I D a = some b) :
    loadMem file a = some b ∧ (Elf.ro file a ∨ Elf.relro file a) := by
  obtain ⟨o, ho, hb⟩ := objByte_spec h
  obtain ⟨ho, hw⟩ := List.mem_filter.1 ho
  have h1 := (hD o ho).bytes _ _ hb
  have h2 := (hD o ho).ro (by simpa using hw) _ (List.getElem?_eq_some_iff.1 hb).1
  rw [objAt_add] at h1 h2
  exact ⟨h1, h2⟩

/-- The data objects of `; data:` directive lines (as `cargo fv link-proof` exports them;
malformed lines dropped). -/
def parseData (ls : List String) : List Clif.DataObject :=
  ls.filterMap fun l => match Clif.dataDirective l with
    | some (.ok o) => some o
    | _ => none

/-! ## Symbols -/

/-- The symbol of a link-map name: a data object the merge left local is named
`.LdataN@<unit>` (`cargo fv link-proof`: the assembler's `.LdataN` repeats across codegen units,
the link map tells them apart), its symbol is `.LdataN`; other names are their symbol. -/
def symName (n : String) : String := (n.splitOn "@").headD n

/-- **The link map is the file's symbol table**: every entry `(n, v)` of `I.addrs` (but the
self-call aliases, whose addresses are fresh) is a defined symbol `symName n` of value `v`. -/
def SymsOk (I : LinkInput) (file : ByteArray) : Prop :=
  ∀ p ∈ I.addrs, (I.aliases.lookup p.1).isNone = true → SymHas file (symName p.1) p.2

/-- The check of `SymsOk`; `cert` gives, per name, its symbol table section and entry. -/
def symsB (I : LinkInput) (ex : Excerpt) (cert : List (String × Nat × Nat)) : Bool :=
  let r := exRd ex
  I.addrs.all fun p => (I.aliases.lookup p.1).isSome ||
    match cert.lookup p.1 with
    | some (s, i) => match symEntry r s i with
      | some (o, v) => v == p.2 && cstrB r o (symName p.1)
      | none => false
    | none => false

theorem symsB_sound {I : LinkInput} {ex : Excerpt} {cert : List (String × Nat × Nat)}
    (h : symsB I ex cert = true) {file : ByteArray} (hA : Agrees file ex) : SymsOk I file := by
  intro p hp hal
  have := List.all_eq_true.1 h p hp
  simp only [Bool.or_eq_true] at this
  rcases this with h1 | h1
  · rw [Option.isNone_iff_eq_none] at hal; rw [hal] at h1; cases h1
  · split at h1
    · rename_i s i _
      split at h1
      · rename_i o v he
        simp only [Bool.and_eq_true, beq_iff_eq] at h1
        exact ⟨s, i, o, h1.1 ▸ symEntry_ext (agrees_ext hA) he, cstrB_ext (agrees_ext hA) h1.2⟩
      · cases h1
    · cases h1

/-! ## The executable -/

/-- **The headers check**: a static AArch64 executable (`Static`). -/
def hdrB (ex : Excerpt) : Bool :=
  match ehdr (exRd ex), phdrs (exRd ex) with
  | some e, some phs => staticB e phs
  | _, _ => false

theorem hdrB_sound {ex : Excerpt} (h : hdrB ex = true) {file : ByteArray} (hA : Agrees file ex) :
    Static file := by
  unfold hdrB at h
  split at h
  · rename_i e phs he hp
    exact ⟨e, phs, ehdr_ext (agrees_ext hA) he, phdrs_ext (agrees_ext hA) hp, h⟩
  · cases h

/-- **The file is the linked program `I` with data objects `D`.** -/
structure BinOk (I : LinkInput) (D : List Clif.DataObject) (file : ByteArray) : Prop where
  static : Static file
  code : ∀ e ∈ tabOf I.results, ArtOk I file e.2
  data : ∀ o ∈ D, DataOk I file o
  syms : SymsOk I file

theorem binOk_of {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hs : Static file) (hc : ArtsOk I file I.funcs) (hd : ∀ o ∈ D, DataOk I file o)
    (hy : SymsOk I file) : BinOk I D file := by
  refine ⟨hs, fun e he => ?_, hd, hy⟩
  simp only [tabOf, LinkInput.results, List.map_map, List.mem_map, Function.comp] at he
  obtain ⟨fi, hfi, rfl⟩ := he
  exact hc fi hfi

/-! ## Consequences -/

/-- `a` is a byte of a relocated word of the image. -/
def RelocAt (I : LinkInput) (a : BitVec 64) : Prop :=
  ∃ e ∈ tabOf I.results, ∃ r ∈ e.2.fb.relocs, ∃ i < 4, a = wAt e.2 (r.offset + i)

theorem mem_wordsAt {base : BitVec 64} :
    ∀ {ws : List (BitVec 32)} {k : Nat} {p : BitVec 64 × BitVec 32}, List.Mem p (wordsAt base k ws) →
      ∃ j, ws[j]? = some p.2 ∧ p.1 = base + BitVec.ofNat 64 (4 * (k + j))
  | [], _, _, h => by cases h
  | w :: ws, k, p, h => by
    cases h with
    | head => exact ⟨0, rfl, by simp⟩
    | tail _ h =>
      obtain ⟨j, hj, hp⟩ := mem_wordsAt h
      exact ⟨j + 1, by simpa using hj, by rw [hp]; congr 2; omega⟩

/-- **The code image in the file**: with `okB I` (the image reads back, `imgB`), every code
address of the image is not writable and holds the image's byte, unless it is a byte of a
relocated word (whose resolved form `RelocOk` gives). -/
theorem img_bytes {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hB : BinOk I D file) (hI : okB I = true) {a : BitVec 64} (ha : ImgT (tabOf I.results) a) :
    Elf.ro file a ∧ (loadMem file a = some (memT (tabOf I.results) a) ∨ RelocAt I a) := by
  obtain ⟨e, he, p, hp, hlt⟩ := ha
  obtain ⟨j, hj, hp1⟩ := mem_wordsAt (k := 0) hp
  rw [Nat.zero_add] at hp1
  have hjl : j < e.2.fb.words.size := by
    have := (List.getElem?_eq_some_iff.1 hj).1; simpa using this
  have hj' : e.2.fb.words[j]? = some p.2 := by simpa using hj
  have hA := hB.code e he
  obtain ⟨i, hi⟩ : ∃ i, i = (a - p.1).toNat := ⟨_, rfl⟩
  rw [← hi] at hlt
  have ha' : a = wAt e.2 (4 * j + i) := by
    simp only [wAt]
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, ← hp1, hi, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.add_comm, BitVec.sub_add_cancel]
  refine ⟨ha' ▸ hA.ro j hjl i hlt, ?_⟩
  by_cases hr : ∃ r ∈ e.2.fb.relocs, r.offset = 4 * j
  · obtain ⟨r, hr, hro⟩ := hr
    exact .inr ⟨e, he, r, hr, i, hlt, by rw [hro]; exact ha'⟩
  · left
    have hpl := hA.plain j p.2 hj' fun r hr' hro => hr ⟨r, hr', hro⟩
    have himg : imgB (tabOf I.results) = true := by
      have := okB_global hI ("imgCode: the image reads back", imgB (tabOf I.results))
        (by simp [globalChks])
      exact this
    have hw := imgCode_of himg he (setMem Arm.ArmState.default (memT (tabOf I.results)))
      (fun _ _ => rfl) j p.2 hj'
    obtain ⟨hr1, hb⟩ := readN_bytes hpl
    have heq := read_mem_bytes_bytes 4 _ _ _ (hr1.trans hw.symm) i hlt
    obtain ⟨b, hb1, hb2⟩ := hb i hlt
    have hwa : wAt e.2 (4 * j) + BitVec.ofNat 64 i = a := by
      rw [ha']; simp only [wAt, BitVec.ofNat_add, BitVec.add_assoc]
    rw [hwa] at hb1 hb2 heq
    rw [hb1, ← hb2, heq]
    rfl

end E2E.BinCheck
