module

public section

/-!
# What the unwinder reads: DWARF call frame information and the LSDA (S10c/S10d)

A model, **generic over the bytes it reads** (not over the compiler), of how libgcc's /
libunwind's DWARF unwinder and the Itanium personality routine read the unwind tables
(`docs/plans/unwinding.md`, "The outside contract"). Trusted by design, like std: it states
what the outside code does with the tables; the compiler's tables are proven to make it do the
right thing (`FV/Backend/Proof/UnwindTables.lean`).

* LEB128 (`uleb?`, `sleb?`): DWARF 5 §7.6.
* Call frame instructions (DWARF 5 §6.4.2) for code alignment 4 and data alignment −8 (the
  CIE's, `Backend.ehFrame`): `decodeCfa?` reads `DW_CFA_advance_loc[1|2|4]`, `def_cfa`,
  `def_cfa_offset`, `def_cfa_register`, `offset`, `offset_extended`, `offset_extended_sf`,
  `nop`; any other opcode is `none` (outside the model, not wrong).
* Rows (`Row`, `Row.exec`, `rowAt`): DWARF 5 §6.4.1: the instructions in order, each
  `advance` moving the location; the row at code offset `pc` is the state after the
  instructions whose location is at most `pc`.
* The LSDA (`decodeLsda?`, `lookup`): the Itanium C++ ABI §1.6 / GCC's `.gcc_except_table`
  layout for `lpStart` omitted, a `udata4` type table and a `uleb128` call-site table; the
  personality uses the first call-site entry whose range contains `pc − 1`.
-/

namespace Unw

/-! ## LEB128 -/

/-- Decode an unsigned LEB128 number at the head of a byte list. -/
@[expose] def uleb? : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bs =>
    if b.toNat < 128 then some (b.toNat, bs)
    else (uleb? bs).map fun (n, r) => (b.toNat - 128 + 128 * n, r)

/-- Decode a signed LEB128 number at the head of a byte list (the last byte's bit 6 is the
sign). -/
@[expose] def sleb? : List UInt8 → Option (Int × List UInt8)
  | [] => none
  | b :: bs =>
    if b.toNat < 128 then some (if b.toNat < 64 then (b.toNat : Int) else b.toNat - 128, bs)
    else (sleb? bs).map fun (n, r) => ((b.toNat - 128 : Nat) + 128 * n, r)

/-! ## Call frame instructions -/

@[expose] section
@[expose] section
/-- A decoded call frame instruction (data alignment −8 applied to `offset`s: `off` is the
byte offset from the CFA). -/
inductive CfaInsn where
  /-- Advance the location by `delta` bytes. -/
  | advance (delta : Nat)
  | defCfa (reg : Nat) (off : Nat)
  | defCfaOffset (off : Nat)
  | defCfaRegister (reg : Nat)
  /-- Register `reg` is saved at CFA + `off`. -/
  | offset (reg : Nat) (off : Int)
  | nop
  deriving DecidableEq, Repr, Inhabited
end
end

/-- Little-endian unsigned number of a byte list. -/
@[expose] def leNat : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs

/-- Decode one call frame instruction (code alignment 4, data alignment −8). -/
@[expose] def decodeCfa1? : List UInt8 → Option (CfaInsn × List UInt8)
  | [] => none
  | b :: bs =>
    let n := b.toNat
    if n / 64 = 1 then some (.advance (4 * (n % 64)), bs)
    else if n / 64 = 2 then (uleb? bs).map fun (f, r) => (.offset (n % 64) (-8 * f), r)
    else if n = 0x00 then some (.nop, bs)
    else if n = 0x02 then match bs with
      | d :: r => some (.advance (4 * d.toNat), r)
      | [] => none
    else if n = 0x03 then match bs with
      | d0 :: d1 :: r => some (.advance (4 * leNat [d0, d1]), r)
      | _ => none
    else if n = 0x04 then match bs with
      | d0 :: d1 :: d2 :: d3 :: r => some (.advance (4 * leNat [d0, d1, d2, d3]), r)
      | _ => none
    else if n = 0x05 then do
      let (reg, r) ← uleb? bs
      let (f, r) ← uleb? r
      pure (.offset reg (-8 * f), r)
    else if n = 0x0c then do
      let (reg, r) ← uleb? bs
      let (o, r) ← uleb? r
      pure (.defCfa reg o, r)
    else if n = 0x0d then (uleb? bs).map fun (reg, r) => (.defCfaRegister reg, r)
    else if n = 0x0e then (uleb? bs).map fun (o, r) => (.defCfaOffset o, r)
    else if n = 0x11 then do
      let (reg, r) ← uleb? bs
      let (f, r) ← sleb? r
      pure (.offset reg (-8 * f), r)
    else none

/-- Decode a whole instruction sequence (`fuel` bounds the steps; every instruction takes at
least one byte, so the length suffices). -/
@[expose] def decodeCfaN? : Nat → List UInt8 → Option (List CfaInsn)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, bs@(_ :: _) => do
    let (i, r) ← decodeCfa1? bs
    let is ← decodeCfaN? fuel r
    pure (i :: is)

@[expose] def decodeCfa? (bs : List UInt8) : Option (List CfaInsn) := decodeCfaN? bs.length bs

/-! ## Rows -/

@[expose] section
@[expose] section
/-- An unwind row: the CFA is `cfaReg + cfaOff`; `saved` lists the registers saved at
CFA-relative offsets (DWARF numbers; latest rule first); every other register has its
initial rule (`same value` for callee-saved registers in the AArch64 ABI). -/
structure Row where
  cfaReg : Nat
  cfaOff : Nat
  saved : List (Nat × Int) := []
  deriving DecidableEq, Repr, Inhabited
end
end

/-- The rule of register `r` in a row: `some off` = saved at CFA + `off`. -/
@[expose] def Row.rule (row : Row) (r : Nat) : Option Int := row.saved.lookup r

/-- Execute one non-advance instruction on a row. -/
@[expose] def Row.exec (row : Row) : CfaInsn → Row
  | .defCfa reg off => { row with cfaReg := reg, cfaOff := off }
  | .defCfaOffset off => { row with cfaOff := off }
  | .defCfaRegister reg => { row with cfaReg := reg }
  | .offset reg off => { row with saved := (reg, off) :: row.saved }
  | .advance _ | .nop => row

/-- The row at code offset `pc` (from the function start): run the instructions from `row`
at location `loc`, stopping at the first `advance` past `pc`. -/
@[expose] def rowAtFrom (pc : Nat) : Row → Nat → List CfaInsn → Row
  | row, _, [] => row
  | row, loc, .advance d :: is => if loc + d ≤ pc then rowAtFrom pc row (loc + d) is else row
  | row, loc, i :: is => rowAtFrom pc (row.exec i) loc is

/-- The row at code offset `pc` of a function whose CIE's initial instructions are `cie` and
whose FDE's are `fde`. -/
@[expose] def rowAt (cie fde : List CfaInsn) (pc : Nat) : Row :=
  rowAtFrom pc (rowAtFrom 0 { cfaReg := 31, cfaOff := 0 } 0 cie) 0 fde

/-! ## The LSDA -/

@[expose] section
@[expose] section
/-- One call-site table entry: `[start, start + len)` → landing pad `pad` (0 = none) and
action-table offset + 1 `action` (0 = cleanup only). Offsets from the function start. -/
structure CallSiteEntry where
  start : Nat
  len : Nat
  pad : Nat
  action : Nat
  deriving DecidableEq, Repr, Inhabited
end
end

/-- Decode `n` bytes worth of call-site entries (four ULEB128s each). -/
@[expose] def decodeSitesN? : Nat → List UInt8 → Option (List CallSiteEntry)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, bs@(_ :: _) => do
    let (s, r) ← uleb? bs
    let (l, r) ← uleb? r
    let (p, r) ← uleb? r
    let (a, r) ← uleb? r
    let es ← decodeSitesN? fuel r
    pure (⟨s, l, p, a⟩ :: es)

/-- The call-site table of an LSDA with `lpStart` omitted (`0xff`), a `udata4` type table
(`0x03`, its offset a ULEB128) and a `uleb128` call-site table (`0x01`, its byte length a
ULEB128). Other encodings: `none`. -/
@[expose] def decodeLsda? : List UInt8 → Option (List CallSiteEntry)
  | 0xff :: 0x03 :: bs => do
    let (_, r) ← uleb? bs
    match r with
    | 0x01 :: r => do
      let (len, r) ← uleb? r
      if len ≤ r.length then decodeSitesN? len (r.take len) else none
    | _ => none
  | _ => none

/-- The personality's lookup: the first entry whose range contains `off` (the call's return
offset − 1). -/
@[expose] def lookup (sites : List CallSiteEntry) (off : Nat) : Option CallSiteEntry :=
  sites.find? fun e => decide (e.start ≤ off ∧ off < e.start + e.len)

end Unw
