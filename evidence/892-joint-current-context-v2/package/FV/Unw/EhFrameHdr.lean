import FV.Unw.EhFrame

/-!
# How the unwinder finds a function's FDE: `.eh_frame_hdr` (S10f)

A model, **generic over the memory it reads** (like `FV/Unw/EhFrame.lean`), of how LLVM's
libunwind — the unwinder Rust links on `aarch64-unknown-linux-musl`, the target of
`cargo fv --lean-link` — finds the FDE of a code address `pc` in a static executable. Trusted by
design, like std; transcribed from libunwind's sources:

* `findUnwindSections` (`AddressSpace.hpp`, the `dl_iterate_phdr` callback): the
  `PT_GNU_EH_FRAME` program header gives the address `hdr` of `.eh_frame_hdr` (the ELF side is
  `Link.EhCheck.ehHdrOf`; a static executable's load bias is 0).
* `EHHeaderParser::decodeEHHdr`: version 1, the `eh_frame_ptr` encoding
  `DW_EH_PE_pcrel | sdata4` (`0x1b`), the FDE count encoding `udata4` (`0x03`), the table
  encoding `DW_EH_PE_datarel | sdata4` (`0x3b`, relative to `hdr`) — other encodings are
  outside the model; the table starts at `hdr + 12`, 8 bytes per entry (initial location, FDE
  address).
* `EHHeaderParser::findFDE`: the binary search `search` (its `low`/`len` loop, verbatim), then
  the FDE at the entry `low`'s address (`CFI_Parser::decodeFDE`, `fdeAt`: its CIE at the CIE
  pointer field's address minus the pointer, `parseCie`; the FDE body `parseFdeU`) is accepted
  iff `pcStart ≤ pc < pcStart + pcRange` (`hdrFde`).
* `decodeFDE` reads an LSDA pointer whose raw value is 0 as "no LSDA" (`parseFdeU`; otherwise as
  `EhFrame.lean`'s `parseFde`).

`hdrTables rd hdr pc`: the found FDE's `pc_begin` and the tables the unwinder reads from it, the
LSDA decoded from the memory at the LSDA pointer. Only the direction "`hdrTables … = some x` ⇒
libunwind uses `x`" is claimed: `none` (not found, or outside the model) says nothing — in
particular libunwind's fallback (a linear scan of `.eh_frame`, `Unw.tablesAt`'s model), taken
only when this search fails, is not modelled here.

The memory: `rd a n` is the `n` bytes at address `a` (fewer where the image's file-backed bytes
end); `rdAll rd a` all of them from `a`.
-/

namespace Unw

/-- Every byte of the memory from `a` on. -/
def rdAll (rd : Nat → Nat → List UInt8) (a : Nat) : List UInt8 := rd a (2 ^ 64 - a)

/-- The decoded `.eh_frame_hdr` header: the `.eh_frame` address and the number of table
entries. -/
structure Hdr where
  ehFrame : Nat
  count : Nat
  deriving DecidableEq, Repr

/-- `decodeEHHdr` for the model's encodings, the header at address `hdr`. -/
def parseHdr (hdr : Nat) (bs : List UInt8) : Option Hdr := do
  let (h, r) ← take? 4 bs
  guard (h = [1, 0x1b, 0x03, 0x3b])
  let (ep, r) ← take? 4 r
  let (cnt, _) ← take? 4 r
  pure ⟨pcrel4 (hdr + 4) ep, leNat cnt⟩

/-- Table entry `i` (`DW_EH_PE_datarel | sdata4`, relative to `hdr`): the initial location and
the FDE address. -/
def hdrEntry (rd : Nat → Nat → List UInt8) (hdr i : Nat) : Option (Nat × Nat) := do
  let (lb, r) ← take? 4 (rd (hdr + 12 + 8 * i) 8)
  let (fb, _) ← take? 4 r
  pure (pcrel4 hdr lb, pcrel4 hdr fb)

/-- **`findFDE`'s binary search**, verbatim: `low = 0; for (len = fde_count; len > 1;) { mid =
low + len / 2; start = table[mid].initial_loc; if (start == pc) { low = mid; break; } else if
(start < pc) { low = mid; len -= len / 2; } else len /= 2; }` (`loc i`: entry `i`'s initial
location; `none`: unreadable). -/
def search (loc : Nat → Option Nat) (pc : Nat) (low len : Nat) : Option Nat :=
  if len ≤ 1 then some low
  else match loc (low + len / 2) with
    | none => none
    | some s =>
      if s = pc then some (low + len / 2)
      else if s < pc then search loc pc (low + len / 2) (len - len / 2)
      else search loc pc low (len / 2)
termination_by len
decreasing_by all_goals omega

/-- `decodeFDE`'s FDE body after the CIE pointer, the body starting at address `a` (its
`pc_begin` field): as `parseFde`, with a zero raw LSDA pointer read as no LSDA. -/
def parseFdeU (cie : Cie) (a : Nat) (body : List UInt8) : Option Fde := do
  let (pb, r) ← take? 4 body
  let (pr, r) ← take? 4 r
  let (alen, r') ← uleb? r
  let (ad, r'') ← take? alen r'
  let lsda ← if cie.lsda then
      (if alen = 4 then
        some (if leNat ad = 0 then none else some (pcrel4 (a + 8 + (r.length - r'.length)) ad))
      else none)
    else (if alen = 0 then some none else none)
  let is ← decodeCfa? r''
  pure ⟨pcrel4 a pb, leNat pr, lsda, noNops is, cie.insns⟩

/-- An entry (CIE or FDE) at address `x` with a 32-bit length: its bytes after the length
field. -/
def entryAt (rd : Nat → Nat → List UInt8) (x : Nat) : Option (List UInt8) := do
  let (lf, _) ← take? 4 (rd x 4)
  let len := leNat lf
  guard (len ≠ 0 ∧ len ≠ 0xffffffff)
  let (body, _) ← take? len (rd (x + 4) len)
  pure body

/-- **`CFI_Parser::decodeFDE` at address `x`**: the FDE's CIE is at its CIE pointer field's
address minus the pointer. -/
def fdeAt (rd : Nat → Nat → List UInt8) (x : Nat) : Option Fde := do
  let body ← entryAt rd x
  let (idf, r) ← take? 4 body
  let id := leNat idf
  guard (id ≠ 0 ∧ id ≤ x + 4)
  let cbody ← entryAt rd (x + 4 - id)
  let (cid, cr) ← take? 4 cbody
  guard (leNat cid = 0)
  let cie ← parseCie cr
  parseFdeU cie (x + 8) r

/-- **`EHHeaderParser::findFDE`**: the FDE the binary search lands on, if its range contains
`pc` (`pcStart + pcRange` not wrapping). -/
def hdrFde (rd : Nat → Nat → List UInt8) (hdr pc : Nat) : Option Fde := do
  let h ← parseHdr hdr (rd hdr 12)
  guard (h.count ≠ 0)
  let low ← search (fun i => (hdrEntry rd hdr i).map (·.1)) pc 0 h.count
  let (_, fx) ← hdrEntry rd hdr low
  let f ← fdeAt rd fx
  guard (f.pcBegin ≤ pc ∧ pc < f.pcBegin + f.pcRange ∧ f.pcBegin + f.pcRange < 2 ^ 64)
  pure f

/-- The tables an FDE gives the unwinder: its CIE's and its instructions, the LSDA decoded from
the memory at its LSDA pointer. -/
def fdeTables (rd : Nat → Nat → List UInt8) (f : Fde) : Option FnTables := do
  let lsda ← match f.lsda with
    | none => some none
    | some a => (decodeLsda? (rdAll rd a)).map some
  pure ⟨f.cieInsns, f.insns, lsda⟩

/-- **The function start and tables the unwinder uses at `pc`** (found through
`.eh_frame_hdr` at `hdr`). -/
def hdrTables (rd : Nat → Nat → List UInt8) (hdr pc : Nat) : Option (Nat × FnTables) := do
  let f ← hdrFde rd hdr pc
  let T ← fdeTables rd f
  pure (f.pcBegin, T)

end Unw
