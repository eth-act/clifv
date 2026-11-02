/-! # Lean static linker: AArch64 relocations (ELF for the Arm 64-bit Architecture, §5.7)

`relocVal ty r old`: the new value of the `relocWidth ty` bytes a relocation of type `ty`
patches, from their old value `old` and the relocation's inputs `r` (`S` the symbol's value,
`A` the addend, `P` the place, `G` the GOT slot's address, `tp` the thread-pointer offset of
`S + A`). The types: the survey's (docs/research/lean-linker.md §2) and the other static ones
a std link may meet. TLS descriptors and initial-exec GOT loads are relaxed to local exec as
lld does in a static executable (`movz`/`movk` of the offset, `nop`s).
-/

namespace Link.Ld

/-- The inputs of one relocation. -/
structure RelIn where
  S : Int
  A : Int
  P : Int
  G : Int := 0
  tp : Int := 0
  deriving Inhabited, Repr

/-- `old` with bits `[lo, lo + len)` replaced by `v mod 2 ^ len`. -/
def setBits (old : Nat) (v : Int) (lo len : Nat) : Nat :=
  let m := 2 ^ len
  old - (old >>> lo % m) <<< lo + ((v % (m : Int)).toNat) <<< lo

/-- The 4 KiB page of `x`. -/
def page (x : Int) : Int := x - x % 4096

/-- The number of bytes a relocation type patches. -/
def relocWidth : Nat → Nat
  | 0 => 0
  | 257 | 260 => 8
  | 259 | 262 => 2
  | _ => 4

/-- `lo ≤ v < hi`, or an error naming the type. -/
def inRange (ty : Nat) (v lo hi : Int) : Except String Unit :=
  if lo ≤ v ∧ v < hi then pure () else throw s!"relocation type {ty}: value {v} out of range"

/-- The `adr`/`adrp` immediate `imm` (21 bits) in instruction `old`. -/
def setAdr (old : Nat) (imm : Int) : Nat :=
  let n := (imm % 2 ^ 21).toNat
  setBits (setBits old (n % 4) 29 2) (n / 4) 5 19

/-- **The relocated value** of the patched bytes (`old`: their value). -/
def relocVal (ty : Nat) (r : RelIn) (old : Nat) : Except String Nat := do
  let x := r.S + r.A
  match ty with
  | 0 => return old
  | 257 => return (x % 2 ^ 64).toNat                                     -- ABS64
  | 258 => inRange ty x (-2 ^ 31) (2 ^ 32); return (x % 2 ^ 32).toNat     -- ABS32
  | 259 => inRange ty x (-2 ^ 15) (2 ^ 16); return (x % 2 ^ 16).toNat     -- ABS16
  | 260 => return ((x - r.P) % 2 ^ 64).toNat                              -- PREL64
  | 261 => inRange ty (x - r.P) (-2 ^ 31) (2 ^ 32); return ((x - r.P) % 2 ^ 32).toNat
  | 262 => inRange ty (x - r.P) (-2 ^ 15) (2 ^ 16); return ((x - r.P) % 2 ^ 16).toNat
  | 263 | 264 => return setBits old x 5 16                                -- MOVW_UABS_G0(_NC)
  | 265 | 266 => return setBits old (x / 2 ^ 16) 5 16
  | 267 | 268 => return setBits old (x / 2 ^ 32) 5 16
  | 269 => return setBits old (x / 2 ^ 48) 5 16
  | 274 =>                                                                -- ADR_PREL_LO21
    inRange ty (x - r.P) (-2 ^ 20) (2 ^ 20); return setAdr old (x - r.P)
  | 275 =>                                                                -- ADR_PREL_PG_HI21
    let d := (page x - page r.P) / 4096
    inRange ty d (-2 ^ 20) (2 ^ 20); return setAdr old d
  | 276 => return setAdr old ((page x - page r.P) / 4096)                 -- ADR_PREL_PG_HI21_NC
  | 277 | 278 => return setBits old (x % 4096) 10 12                       -- ADD_ABS_LO12_NC, LDST8
  | 284 => return setBits old (x % 4096 / 2) 10 12                        -- LDST16
  | 285 => return setBits old (x % 4096 / 4) 10 12                        -- LDST32
  | 286 => return setBits old (x % 4096 / 8) 10 12                        -- LDST64
  | 299 => return setBits old (x % 4096 / 16) 10 12                       -- LDST128
  | 279 =>                                                                -- TSTBR14
    inRange ty (x - r.P) (-2 ^ 15) (2 ^ 15); return setBits old ((x - r.P) / 4) 5 14
  | 280 =>                                                                -- CONDBR19
    inRange ty (x - r.P) (-2 ^ 20) (2 ^ 20); return setBits old ((x - r.P) / 4) 5 19
  | 282 | 283 =>                                                          -- JUMP26, CALL26
    inRange ty (x - r.P) (-2 ^ 27) (2 ^ 27)
    if (x - r.P) % 4 != 0 then throw s!"relocation type {ty}: unaligned target"
    return setBits old ((x - r.P) / 4) 0 26
  | 311 =>                                                                -- ADR_GOT_PAGE
    let d := (page (r.G + r.A) - page r.P) / 4096
    inRange ty d (-2 ^ 20) (2 ^ 20); return setAdr old d
  | 312 => return setBits old ((r.G + r.A) % 4096 / 8) 10 12               -- LD64_GOT_LO12_NC
  | 541 =>                                                                -- TLSIE_ADR_GOTTPREL_PAGE21
    inRange ty r.tp 0 (2 ^ 32); return 0xd2a00000 + old % 32 + ((r.tp / 2 ^ 16) % 2 ^ 16).toNat * 32
  | 542 =>                                                                -- TLSIE_LD64_GOTTPREL_LO12_NC
    return 0xf2800000 + old % 32 + (r.tp % 2 ^ 16).toNat * 32
  | 549 =>                                                                -- TLSLE_ADD_TPREL_HI12
    inRange ty r.tp 0 (2 ^ 24); return setBits old (r.tp / 4096) 10 12
  | 550 => inRange ty r.tp 0 4096; return setBits old r.tp 10 12          -- TLSLE_ADD_TPREL_LO12
  | 551 => return setBits old (r.tp % 4096) 10 12                         -- TLSLE_ADD_TPREL_LO12_NC
  | 562 =>                                                                -- TLSDESC_ADR_PAGE21
    inRange ty r.tp 0 (2 ^ 32); return 0xd2a00000 + ((r.tp / 2 ^ 16) % 2 ^ 16).toNat * 32
  | 563 => return 0xf2800000 + (r.tp % 2 ^ 16).toNat * 32                 -- TLSDESC_LD64_LO12
  | 564 | 569 => return 0xd503201f                                       -- TLSDESC_ADD_LO12, _CALL
  | _ => throw s!"unsupported relocation type {ty}"

/-- The types whose value goes through a GOT slot. -/
def gotType (ty : Nat) : Bool := ty == 311 || ty == 312

/-- The TLS types (`S` is a thread-local symbol; `tp` is used). -/
def tlsType (ty : Nat) : Bool := (541 ≤ ty ∧ ty ≤ 569)

/-- Branches whose undefined weak target becomes the next instruction (lld). -/
def branchType (ty : Nat) : Bool := ty == 279 || ty == 280 || ty == 282 || ty == 283

end Link.Ld
