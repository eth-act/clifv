import FV.Link.Layout
import FV.E2E.BinCheck

/-! # Relocation of the program part (L2b)

The executable's words of a compiled function `a` loaded at `a.base`, every relocation resolved
against the link map of the input `I`, in the forms `E2E.BinCheck.RelocOk` names:

* `R_AARCH64_CALL26`: `bl` with the offset to `I.baseOf sym`;
* a page pair (`ADR_PREL_PG_HI21`+`ADD_ABS_LO12_NC`, or the GOT pair
  `ADR_GOT_PAGE`+`LD64_GOT_LO12_NC`): `adrp`+`add` of `T = I.symAddr sym addend`. The GOT pair is
  resolved directly too (`PairOk.adrpAdd` accepts it for a GOT access), so the program part
  needs no GOT;
* the TLS descriptor sequence: the local-exec form `movz x0`/`movk x0`/`nop`/`nop` of the
  symbol's thread-pointer offset `tp (I.addrOf sym)` (`tp`: `Elf.tpOff` of the executable's
  program headers).

`resolveWord I tp a k` is word `k`, a function of the word's own relocation (at most one per
offset, `relocsOkB`) and, for the second word of a pair or of the TLS sequence, its partner
four bytes before. `relocsOkB` is the linker's check of the compiled code's relocation shapes
(the compiled words the relocations patch, the partners, the ranges): a rejection is a link
error, never a wrong executable.
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck Backend

/-- The relocation at byte offset `o` of `a` (the first; `relocsOkB` makes it the only one). -/
def relocAt? (a : Art) (o : Nat) : Option Reloc := a.fb.relocs.find? (·.offset == o)

/-- Compiled word `k` of `a` (`0` past the end). -/
def wordOf (a : Art) (k : Nat) : BitVec 32 := a.fb.words[k]?.getD 0

/-- The target address of a relocation. -/
def target (I : LinkInput) (r : Reloc) : Nat := (I.symAddr r.sym r.addend).toNat

/-- **Word `k` of `a` in the executable**: the compiled word, or its resolved form if a
relocation is at its offset. -/
def resolveWord (I : LinkInput) (tp : Nat → Option Nat) (a : Art) (k : Nat) : BitVec 32 :=
  let w := wordOf a k
  let P := (wAt a (4 * k)).toNat
  match relocAt? a (4 * k) with
  | none => w
  | some r => match r.type with
    | .call26 => blW ((I.baseOf r.sym : Int) - P)
    | .adrGotPage | .adrPrelPgHi21 => adrpW (rd5 w) (pageOf (target I r) - pageOf P)
    | .ld64GotLo12Nc | .addAbsLo12Nc =>
      match relocAt? a (4 * k - 4) with
      | some r' => let rd := rd5 (wordOf a (k - 1)); addW rd rd (target I r' % 4096)
      | none => w
    | .tlsDescAdrPage21 => movzW 0 ((tp (I.addrOf r.sym)).getD 0 / 65536)
    | .tlsDescLd64Lo12 =>
      match relocAt? a (4 * k - 4) with
      | some r' => movkW 0 ((tp (I.addrOf r'.sym)).getD 0 % 65536)
      | none => w
    | .tlsDescAddLo12 | .tlsDescCall => nopW

/-- A relocation of type `t` is at offset `o` of `a`. -/
def hasAt (a : Art) (o : Nat) (t : RelocType) : Bool :=
  a.fb.relocs.any fun r => r.offset == o && decide (r.type = t)

/-- **The linker's check of one relocation** of `a`: the compiled words it patches have the
shape the relocation's resolved form assumes (zero immediates), its partners are there, the
target is in range, and the TLS offset is known and fits. -/
def relocOkB (I : LinkInput) (tp : Nat → Option Nat) (a : Art) (r : Reloc) : Bool :=
  let o := r.offset
  let n := a.fb.words.size
  o % 4 == 0 && decide (o / 4 < n) && match r.type with
  | .call26 =>
    wordOf a (o / 4) == blW 0 && blRange ((I.baseOf r.sym : Int) - (wAt a o).toNat)
  | .adrGotPage | .adrPrelPgHi21 =>
    let got := decide (r.type = .adrGotPage)
    let rd := rd5 (wordOf a (o / 4))
    decide (rd < 31) && decide (o / 4 + 1 < n) && wordOf a (o / 4) == adrpW rd 0 &&
      wordOf a (o / 4 + 1) == (if got then ldrW rd rd 0 else addW rd rd 0) &&
      a.fb.relocs.any (fun r' => r'.offset == o + 4 && decide (r'.type = loOf r.type) &&
        r'.sym == r.sym && r'.addend == r.addend) &&
      inR (-2 ^ 20) (2 ^ 20) (pageOf (target I r) - pageOf (wAt a o).toNat)
  | .ld64GotLo12Nc | .addAbsLo12Nc =>
    a.fb.relocs.any fun r' => r'.offset + 4 == o &&
      decide (r'.type = .adrGotPage ∨ r'.type = .adrPrelPgHi21)
  | .tlsDescAdrPage21 =>
    decide (o / 4 + 3 < n) && hasAt a (o + 4) .tlsDescLd64Lo12 && hasAt a (o + 8) .tlsDescAddLo12 &&
      hasAt a (o + 12) .tlsDescCall &&
      match tp (I.addrOf r.sym) with
      | some v => decide (v < 2 ^ 32)
      | none => false
  | .tlsDescLd64Lo12 => hasAt a (o - 4) .tlsDescAdrPage21 && decide (4 ≤ o)
  | .tlsDescAddLo12 => hasAt a (o - 8) .tlsDescAdrPage21 && decide (8 ≤ o)
  | .tlsDescCall => hasAt a (o - 12) .tlsDescAdrPage21 && decide (12 ≤ o)

/-- **The linker's check of `a`'s relocations**: one per offset, each `relocOkB`. -/
def relocsOkB (I : LinkInput) (tp : Nat → Option Nat) (a : Art) : Bool :=
  decide (a.fb.relocs.map (·.offset)).Nodup && a.fb.relocs.all (relocOkB I tp a)

/-- The little-endian bytes of a word. -/
def wordBytes (w : BitVec 32) : List UInt8 :=
  [UInt8.ofNat w.toNat, UInt8.ofNat (w.toNat >>> 8), UInt8.ofNat (w.toNat >>> 16),
    UInt8.ofNat (w.toNat >>> 24)]

/-- The bytes of `a` in the region: its resolved words, then the gap word (`0`, `udf #0`). -/
def artImage (I : LinkInput) (tp : Nat → Option Nat) (a : Art) : List UInt8 :=
  (List.range a.fb.words.size).flatMap (fun k => wordBytes (resolveWord I tp a k)) ++ [0, 0, 0, 0]

/-- **The region's bytes**: the placed functions' images, consecutive. -/
def regionBytes (I : LinkInput) (tp : Nat → Option Nat) (T : List Art) : List UInt8 :=
  T.flatMap (artImage I tp)

end Link
