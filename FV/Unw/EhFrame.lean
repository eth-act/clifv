module

public import FV.Unw.Model

@[expose] public section

/-!
# What the unwinder reads from the linked image: `.eh_frame` and `.gcc_except_table` (S10f)

A model, **generic over the bytes it reads** (like `FV/Unw/Dwarf.lean`), of how libgcc's /
libunwind's unwinder finds and reads a function's unwind tables in the linked image: the
`.eh_frame` section (LSB 5.0 "Exception Frames", §10.6.1; DWARF 5 §6.4.1) with its Common
Information Entries (CIEs) and Frame Description Entries (FDEs), and the LSDA an FDE points at
(in `.gcc_except_table`). The result is the function's `Unw.FnTables`, what `Unw.ArmStepU`'s
unwinder reads (`FV/Unw/Model.lean`). Trusted by design, like std.

The subset (anything else ⇒ `none`: outside the model, not wrong):
* entries with a 32-bit length (a zero length ends the section; `0xffffffff`, the 64-bit
  form, is outside the model);
* CIEs of version 1 with augmentation `zR` or `zLPR`, code alignment 4, data alignment −8 and
  return address register 30 (what `decodeCfa?` assumes), the FDE pointer encoding
  `DW_EH_PE_pcrel | DW_EH_PE_sdata4` (`0x1b`), for `zLPR` the LSDA encoding `0x1b` and the
  personality encoding `DW_EH_PE_indirect | pcrel | sdata8` (`0x9c`, its 8-byte pointer is
  skipped: the model's personality is Rust's, `Unw.personality`);
* FDEs whose CIE pointer points back at a CIE of the section, with `pc_begin` (`0x1b`, relative
  to the field's address), a 4-byte `pc_range`, and augmentation data that is the LSDA pointer
  (`0x1b`, 4 bytes) if the CIE has `L`, else empty;
* the call frame instructions of `decodeCfa?`; `DW_CFA_nop` (padding) is dropped;
* the LSDA at the FDE's LSDA pointer, decoded by `decodeLsda?` from the `.gcc_except_table`
  bytes at that address.

`tablesAt eh ehAddr gcc gccAddr pc`: the tables of the first FDE whose range contains `pc`,
with its `pc_begin` (the function start the unwinder's offsets are relative to).
-/

namespace Unw

/-- Split off the first `n` bytes. -/
def take? (n : Nat) (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  if n ≤ bs.length then some (bs.take n, bs.drop n) else none

/-- A 4-byte little-endian field as a signed 32-bit number. -/
def sdata4 (bs : List UInt8) : Int :=
  if leNat bs < 2 ^ 31 then (leNat bs : Int) else (leNat bs : Int) - 2 ^ 32

/-- A `DW_EH_PE_pcrel | DW_EH_PE_sdata4` pointer read at address `at_`: the address it denotes
(modulo `2 ^ 64`). -/
def pcrel4 (at_ : Nat) (bs : List UInt8) : Nat :=
  (((at_ : Int) + sdata4 bs) % 2 ^ 64).toNat

/-- A NUL-terminated string. -/
def cstr? : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | b :: r => if b = 0 then some ([], r) else (cstr? r).map fun (s, r') => (b :: s, r')

/-- The call frame instructions without the `DW_CFA_nop` padding. -/
def noNops (is : List CfaInsn) : List CfaInsn := is.filter (· != .nop)

/-- A decoded CIE: whether its augmentation has `L` (its FDEs carry an LSDA pointer), and its
initial instructions. -/
structure Cie where
  lsda : Bool
  insns : List CfaInsn
  deriving DecidableEq, Repr

/-- The augmentation strings of the model: `zR`, `zLPR`. -/
def augZR : List UInt8 := [0x7a, 0x52]
def augZLPR : List UInt8 := [0x7a, 0x4c, 0x50, 0x52]

/-- The augmentation data of a CIE: `zR`: the FDE encoding; `zLPR`: the LSDA encoding, the
personality encoding and pointer, the FDE encoding. -/
def augLsda? (aug data : List UInt8) : Option Bool :=
  if aug = augZR then (if data = [0x1b] then some false else none)
  else if aug = augZLPR then
    match data with
    | [0x1b, 0x9c, _, _, _, _, _, _, _, _, 0x1b] => some true
    | _ => none
  else none

/-- A CIE's body after its CIE id. -/
def parseCie (body : List UInt8) : Option Cie := do
  let (v, r) ← take? 1 body
  guard (v = [1])
  let (aug, r) ← cstr? r
  let (ca, r) ← uleb? r
  let (da, r) ← sleb? r
  let (ra, r) ← take? 1 r
  guard (ca = 4 ∧ da = -8 ∧ ra = [30])
  let (alen, r) ← uleb? r
  let (ad, r) ← take? alen r
  let l ← augLsda? aug ad
  let is ← decodeCfa? r
  pure ⟨l, noNops is⟩

/-- A decoded FDE: the code range it covers, its LSDA's address, its instructions and its
CIE's initial instructions. -/
structure Fde where
  pcBegin : Nat
  pcRange : Nat
  lsda : Option Nat
  insns : List CfaInsn
  cieInsns : List CfaInsn
  deriving DecidableEq, Repr

/-- An FDE's body after its CIE pointer, the body starting at address `a` (its `pc_begin`
field). -/
def parseFde (cie : Cie) (a : Nat) (body : List UInt8) : Option Fde := do
  let (pb, r) ← take? 4 body
  let (pr, r) ← take? 4 r
  let (alen, r') ← uleb? r
  let (ad, r'') ← take? alen r'
  let lsda ← if cie.lsda then
      (if alen = 4 then some (some (pcrel4 (a + 8 + (r.length - r'.length)) ad)) else none)
    else (if alen = 0 then some none else none)
  let is ← decodeCfa? r''
  pure ⟨pcrel4 a pb, leNat pr, lsda, noNops is, cie.insns⟩

/-- The entries of an `.eh_frame` section from offset `off`: each entry's offset and its bytes
after the length field. -/
def entriesN : Nat → Nat → List UInt8 → Option (List (Nat × List UInt8))
  | _, _, [] => some []
  | 0, _, _ :: _ => none
  | fuel + 1, off, bs@(_ :: _) => do
    let (lf, r) ← take? 4 bs
    let len := leNat lf
    if len = 0 then pure []
    else if len = 0xffffffff then none
    else do
      let (body, r) ← take? len r
      let es ← entriesN fuel (off + 4 + len) r
      pure ((off, body) :: es)

def entries (bs : List UInt8) : Option (List (Nat × List UInt8)) := entriesN bs.length 0 bs

/-- The FDE of an entry at offset `off` of a section at address `addr` (`none` for a CIE). -/
def fdeOf (es : List (Nat × List UInt8)) (addr off : Nat) (body : List UInt8) :
    Option (Option Fde) := do
  let (idf, r) ← take? 4 body
  let id := leNat idf
  if id = 0 then pure none
  else do
    guard (id ≤ off + 4)
    let cbody ← es.lookup (off + 4 - id)
    let (cid, cr) ← take? 4 cbody
    guard (leNat cid = 0)
    let cie ← parseCie cr
    let f ← parseFde cie (addr + off + 8) r
    pure (some f)

/-- The FDEs of an `.eh_frame` section at address `addr`. -/
def ehFdes (bs : List UInt8) (addr : Nat) : Option (List Fde) := do
  let es ← entries bs
  let fs ← es.mapM fun (off, body) => fdeOf es addr off body
  pure fs.reduceOption

/-- **The tables of the function covering `pc`**: the first FDE whose range contains `pc`, its
`pc_begin`, and the tables the unwinder reads from it (the LSDA from `.gcc_except_table` at
address `gccAddr`). -/
def tablesAt (eh : List UInt8) (ehAddr : Nat) (gcc : List UInt8) (gccAddr : Nat) (pc : Nat) :
    Option (Nat × FnTables) := do
  let fs ← ehFdes eh ehAddr
  let f ← fs.find? fun f => decide (f.pcBegin ≤ pc ∧ pc < f.pcBegin + f.pcRange)
  let lsda ← match f.lsda with
    | none => some none
    | some a => if gccAddr ≤ a then (decodeLsda? (gcc.drop (a - gccAddr))).map some else none
  pure (f.pcBegin, ⟨f.cieInsns, f.insns, lsda⟩)

end Unw
