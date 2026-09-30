import FV.Backend.Asm
import FV.Backend.RegallocOps
import Std.Data.HashMap

/-!
# Unwind information (DWARF call frame information for `.eh_frame`)

**Not verified** and outside every theorem: the unwind tables only describe the frame to an
unwinder (a Rust panic unwinding through Lean-compiled code, a debugger, a profiler); the code
does not read them. `Backend.elfObject` writes them as `.eh_frame` (`FV/Backend/Obj.lean`).

The rows mirror what Cranelift emits for aarch64 SystemV (`isa/aarch64/abi.rs`
`gen_prologue_frame_setup` / `gen_clobber_save` and `isa/unwind/systemv.rs`
`create_unwind_info_from_insts`), for the backend's own frame (`FV/Backend/Regalloc.lean`):

| after | rows | Cranelift's `UnwindInst` |
| --- | --- | --- |
| `stp x29, x30, [sp, #-16]!` | `def_cfa_offset 16`, x29 at CFA-16, x30 at CFA-8 | `PushFrameRegs` |
| `mov x29, sp` | `def_cfa_register x29` (CFA = x29+16 from here on) | `DefineNewFrame` |
| each callee-save store `str r, [sp, #o]` | r at CFA + o - 16 - frameSize | `SaveReg` |

The CIE's initial rule is CFA = sp+0 (return address in x30), so a function without a frame
(`AFunc.frame = false`) has an FDE without rows. The frame's `sub sp` needs no row: the CFA
is x29-based by then (Cranelift's `StackAlloc` adds a row only without a frame pointer). The
epilogue has no rows either, as in Cranelift: unwinding starts only at call sites (Rust panics
are synchronous), and no call follows the restores. The callee-saved registers are saved in
block 0 before any other instruction (`buildRFunc`, `ctlCheck`), so their rows cover every call.
For v8–v15 the frame saves all 128 bits (`str q`); the unwinder restores the callee-saved low
64 bits (d8–d15, DWARF 72–79) from the slot's first 8 bytes.

`unwindRows` reads the saves from `AFunc`'s block 0 and checks that the function's final code
starts with exactly the prologue and those stores (so the byte offsets are the code's).
-/

namespace Backend

/-- The DWARF call frame instructions the backend's unwind rows use. -/
inductive Cfi where
  /-- `DW_CFA_def_cfa_offset`. -/
  | defCfaOffset (off : Nat)
  /-- `DW_CFA_def_cfa_register`. -/
  | defCfaRegister (reg : Nat)
  /-- `DW_CFA_offset`: register `reg` is saved at CFA + `off`. -/
  | offset (reg : Nat) (off : Int)
  deriving Repr, BEq, Inhabited

/-- DWARF register number ("DWARF for the Arm 64-bit Architecture": x0–x30 = 0–30, sp = 31,
v0–v31 = 64–95). -/
def Reg.dwarf? : Reg → Option Nat
  | .x n => some n
  | .sp => some 31
  | .v n => some (64 + n)
  | _ => none

/-- A callee-save store of block 0: `(register, sp offset)`. -/
def AInst.calleeSave? : AInst → Option (Reg × Int)
  | .inst (.store op r (.spOffset off) _) =>
    if (op == .store64 || op == .fpuStore128) && calleeSaved.contains r then some (r, off) else none
  | _ => none

/-- The instruction of a line (none for labels and jump-table words). -/
def Line.insn? : Line → Option Insn
  | .ins i _ => some i
  | _ => none

/-- Unwind rows `(code offset, instruction)` of an allocated function `af` whose final code
is `fa`, in code order. -/
def unwindRows (af : AFunc) (fa : FnAsm) : Except String (List (Nat × Cfi)) := do
  if !af.frame then return []
  let some (_, code) := af.blocks[0]? | throw "unwind: no entry block"
  let code := code.toList
  if code.head? != some .prologue then throw "unwind: the entry block does not start with the prologue"
  let saves := (code.drop 1).takeWhile (·.calleeSave?.isSome)
  let pro := prologueLines af.frameSize
  let c : FnCtx := { k := fa.k, slotBase := af.slotBase }
  let mut expect : Array Line := pro.toArray
  let mut off := 4 * pro.length
  let mut rows : Array (Nat × Cfi) :=
    #[(4, .defCfaOffset 16), (4, .offset 29 (-16)), (4, .offset 30 (-8)), (8, .defCfaRegister 29)]
  for s in saves do
    let some (r, o) := s.calleeSave? | throw "unwind: not a save"
    let .inst m := s | throw "unwind: not a save"
    let (ls, _) ← m.lines c {}
    expect := expect ++ ls.toArray
    off := off + 4 * ls.length
    let some dr := r.dwarf? | throw "unwind: register without a DWARF number"
    let cfaOff : Int := o - 16 - af.frameSize
    if cfaOff ≥ 0 || cfaOff % 8 != 0 then throw s!"unwind: save slot at CFA{cfaOff}"
    rows := rows.push (off, .offset dr cfaOff)
  -- the final code starts with the entry label, then exactly these instructions
  let got := (fa.lines.toList.drop 1).take expect.size
  unless (match fa.lines[0]? with | some (Line.label _) => true | _ => false) &&
      got.map Line.insn? == expect.toList.map Line.insn? && got.all (·.insn?.isSome) do
    throw "unwind: the code does not start with the prologue and the callee-save stores"
  return rows.toList

/-- Unsigned LEB128. -/
partial def uleb (n : Nat) : ByteArray :=
  if n < 128 then ⟨#[UInt8.ofNat n]⟩ else ⟨#[UInt8.ofNat (n % 128 + 128)]⟩ ++ uleb (n / 128)

/-- Signed LEB128. -/
partial def sleb (n : Int) : ByteArray :=
  let b := (n % 128).toNat  -- `Int` `/` and `%` are Euclidean: `b ∈ [0, 128)`, `rest` = ⌊n/128⌋
  let rest := n / 128
  let sign := b ≥ 64
  if (rest == 0 && !sign) || (rest == -1 && sign) then ⟨#[UInt8.ofNat b]⟩
  else ⟨#[UInt8.ofNat (b + 128)]⟩ ++ sleb rest

/-- Code alignment factor 4 and data alignment factor -8 (the CIE's, as Cranelift's). -/
def Cfi.bytes : Cfi → ByteArray
  | .defCfaOffset o => ⟨#[0x0e]⟩ ++ uleb o
  | .defCfaRegister r => ⟨#[0x0d]⟩ ++ uleb r
  | .offset r off =>
    if off ≤ 0 && off % 8 == 0 then
      let f := (-off / 8).toNat
      if r < 64 then ⟨#[UInt8.ofNat (0x80 + r)]⟩ ++ uleb f  -- DW_CFA_offset
      else ⟨#[0x05]⟩ ++ uleb r ++ uleb f                     -- DW_CFA_offset_extended
    else ⟨#[0x11]⟩ ++ uleb r ++ sleb (off / (-8))            -- DW_CFA_offset_extended_sf

/-- `DW_CFA_advance_loc*` by `delta` bytes (a multiple of 4). -/
def cfiAdvance (delta : Nat) : ByteArray :=
  let d := delta / 4
  if d == 0 then .empty
  else if d < 64 then ⟨#[UInt8.ofNat (0x40 + d)]⟩
  else if d < 256 then ⟨#[0x02, UInt8.ofNat d]⟩
  else if d < 65536 then ⟨#[0x03, UInt8.ofNat d, UInt8.ofNat (d / 256)]⟩
  else ⟨#[0x04, UInt8.ofNat d, UInt8.ofNat (d / 256), UInt8.ofNat (d / 65536), UInt8.ofNat (d / 16777216)]⟩

/-- An FDE's instruction bytes for rows in code order. -/
def cfiProgram (rows : List (Nat × Cfi)) : ByteArray := Id.run do
  let mut b : ByteArray := .empty
  let mut at_ := 0
  for (o, i) in rows do
    b := b ++ cfiAdvance (o - at_)
    at_ := o
    b := b ++ i.bytes
  return b

/-! ## Call sites and landing pads (the LSDA, `.gcc_except_table`)

Cranelift records every call's return address and, for a `try_call`, its handlers with the
landing pads' code offsets (`MachBuffer::call_sites`, `FinalizedMachExceptionHandler`); the
embedder writes the LSDA. `callSites` recovers the same data from the final code, and
`Backend.lsdaBytes` (`FV/Backend/Obj.lean`) writes cg_clif's LSDA
(`rustc_codegen_cranelift/src/debuginfo/unwind.rs` `add_function`): one call-site entry per
call (`[ret - 1, ret)`), landing pad 0 and no action for a call without handlers, for a
handler with tag 0 (`EXCEPTION_HANDLER_CLEANUP`) its landing pad and no action, for tag 1
(`EXCEPTION_HANDLER_CATCH`) its landing pad and the catch-all action (type 0). -/

/-- One entry of the LSDA's call-site table (offsets from the function start); `action` is
the action-table offset + 1 (0 = no action: cleanup, or no landing pad). -/
structure CallSite where
  start : Nat
  len : Nat
  pad : Nat
  action : Nat
  deriving Repr, BEq, Inhabited

/-- The call-site table of an allocated function `af` whose final code is `fa` (every `bl`/
`blr` is a call, in code order, and `af`'s calls are in the same order), or `none` if the
function has no `try_call` (it needs no LSDA). -/
def callSites (af : AFunc) (fa : FnAsm) : Except String (Option (List CallSite)) := do
  let calls : List (Option TryInfo) := af.blocks.toList.flatMap fun (_, code) =>
    code.toList.filterMap fun
      | .inst (.call _) => some none
      | .inst (.tryCall _ ti) => some (some ti)
      | _ => none
  if !calls.any (·.isSome) then return none
  let mut off := 0
  let mut labels : Std.HashMap Label Nat := {}
  let mut rets : Array Nat := #[]
  for ln in fa.lines do
    match ln with
    | .label (.block l) => labels := labels.insert l off
    | .ins (.bl _) _ | .ins (.blr _) _ => rets := rets.push (off + 4)
    | _ => pure ()
    off := off + ln.size
  if rets.size != calls.length then throw "LSDA: the code's calls differ from the function's"
  let mut sites : Array CallSite := #[]
  for (c, ret) in calls.zip rets.toList do
    let handlers := match c with
      | some ti => ti.handlers
      | none => []
    if handlers.isEmpty then sites := sites.push ⟨ret - 1, 1, 0, 0⟩
    for h in handlers do
      let some pad := labels[h.label]? | throw s!"LSDA: no landing pad label {h.label}"
      match h with
      | .tag 0 _ => sites := sites.push ⟨ret - 1, 1, pad, 0⟩
      | .tag 1 _ => sites := sites.push ⟨ret - 1, 1, pad, 1⟩
      | .tag n _ => throw s!"LSDA: exception tag {n} (cg_clif uses 0 = cleanup, 1 = catch)"
      | .default _ => throw "LSDA: a `default` handler (cg_clif uses tags 0 and 1)"
  return some sites.toList

end Backend
