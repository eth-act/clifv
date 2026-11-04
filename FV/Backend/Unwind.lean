import FV.Backend.Asm

/-!
# Unwind information (DWARF call frame information for `.eh_frame`)

The code does not read these tables; they describe the frame to an unwinder (a Rust panic
unwinding through Lean-compiled code, a debugger, a profiler). `Backend.elfObject` writes them
as `.eh_frame` and `.gcc_except_table` (`FV/Backend/Obj.lean`). They are correct by
construction against the unwinder's model (`FV/Unw/Dwarf.lean`):
`FV/Backend/Proof/UnwindTables.lean` (`unwindRows_frame`, `callSites_ok`, the byte round
trips). Using them in the per-function and linking theorems is S10d–S10f
(`docs/plans/unwinding.md`).

The rows are what Cranelift emits for aarch64 SystemV (`isa/aarch64/abi.rs`
`gen_prologue_frame_setup` / `gen_clobber_save` and `isa/unwind/systemv.rs`
`create_unwind_info_from_insts`), for the backend's frame (`FV/Backend/Regalloc.lean`,
`prologueLines` in `FV/Backend/Asm.lean`):

| after | rows | Cranelift's `UnwindInst` |
| --- | --- | --- |
| `stp x29, x30, [sp, #-16]!` | `def_cfa_offset 16`, x29 at CFA-16, x30 at CFA-8 | `PushFrameRegs` |
| `mov x29, sp` | `def_cfa_register x29` (CFA = x29+16) | `DefineNewFrame` |
| each push `str r`/`stp r, r2` (`[sp, #-16]!`) | r (and r2) at CFA - 16 - `clobberBytes` + its `clobberOff` | `SaveReg` |

The CFA stays x29-based; the `sub sp` of the fixed frame has no row (Cranelift's `StackAlloc`
gives one only without a frame pointer). The body keeps x29 = CFA - 16 (x29 is not allocatable
and every callee preserves it).

The CIE's initial rule is CFA = sp+0 (return address in x30), so a function without a frame
(`AFunc.frame = false`) has an FDE without rows. The epilogue has no rows, as in Cranelift:
unwinding starts only at call sites (Rust panics are synchronous), and no call follows the
pops. For v8–v15 the prologue saves the callee-saved low 64 bits (`str d`/`stp d`, d8–d15 =
DWARF 72–79), as Cranelift does.

`unwindRows` reads the saves from `AFunc.saves` and checks that the function's final code
starts with exactly the prologue (so the byte offsets are the code's).
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
  deriving Repr, BEq, DecidableEq, Inhabited

/-- DWARF register number ("DWARF for the Arm 64-bit Architecture": x0–x30 = 0–30, sp = 31,
v0–v31 = 64–95). -/
def Reg.dwarf? : Reg → Option Nat
  | .x n => some n
  | .sp => some 31
  | .v n => some (64 + n)
  | _ => none

/-- The instruction of a line (none for labels and jump-table words). -/
def Line.insn? : Line → Option Insn
  | .ins i _ => some i
  | _ => none

/-- The registers of each push of `pushLines int rs`, in code order. -/
def pushGroups (rs : List Reg) : List (List Reg) :=
  let (ps, o) := pairsOf rs
  o.toList.map (fun r => [r]) ++ ps.reverse.map fun (a, b) => [a, b]

/-- The rows of the pushes of `saves` (`SaveReg`), the first push at byte offset `start`: after
each push, a row per register it saves, at CFA - 16 - `clobberBytes saves` + `clobberOff`. -/
def pushRows (saves : List Reg) (start : Nat) : List (Nat × Cfi) :=
  ((pushGroups (savesInt saves) ++ pushGroups (savesFloat saves)).zipIdx).flatMap fun (g, i) =>
    g.filterMap fun r => r.dwarf?.map fun dr =>
      (start + 4 * (i + 1), Cfi.offset dr ((clobberOff saves r : Int) - clobberBytes saves - 16))

/-- The rows of the prologue `stp x29, x30, [sp, #-16]!; mov x29, sp`. -/
def prologueRows : List (Nat × Cfi) :=
  [(4, .defCfaOffset 16), (4, .offset 29 (-16)), (4, .offset 30 (-8)), (8, .defCfaRegister 29)]

/-- Unwind rows `(code offset, instruction)` of an allocated function `af` whose final code
is `fa`, in code order. -/
def unwindRows (af : AFunc) (fa : FnAsm) : Except String (List (Nat × Cfi)) := do
  if !af.frame then return []
  let some (_, code) := af.blocks[0]? | throw "unwind: no entry block"
  if code.toList.head? != some .prologue then throw "unwind: the entry block does not start with the prologue"
  let pro := prologueLines af.saves af.frameSize af.isCaller
  if 4 * pro.length ≥ 2 ^ 32 then throw "unwind: the prologue exceeds the FDE's 32-bit range"
  -- the final code starts with the entry label, then exactly the prologue
  let got := (fa.lines.toList.drop 1).take pro.length
  unless (match fa.lines[0]? with | some (Line.label _) => true | _ => false) &&
      decide (got.map Line.insn? = pro.map Line.insn?) && got.all (·.insn?.isSome) do
    throw "unwind: the code does not start with the prologue"
  return prologueRows ++ pushRows af.saves 8

/-- Unsigned LEB128. -/
def uleb (n : Nat) : ByteArray :=
  if n < 128 then ⟨#[UInt8.ofNat n]⟩ else ⟨#[UInt8.ofNat (n % 128 + 128)]⟩ ++ uleb (n / 128)
termination_by n
decreasing_by omega

/-- Signed LEB128. -/
def sleb (n : Int) : ByteArray :=
  let b := (n % 128).toNat  -- `Int` `/` and `%` are Euclidean: `b ∈ [0, 128)`, `rest` = ⌊n/128⌋
  let rest := n / 128
  let sign := b ≥ 64
  if (rest == 0 && !sign) || (rest == -1 && sign) then ⟨#[UInt8.ofNat b]⟩
  else ⟨#[UInt8.ofNat (b + 128)]⟩ ++ sleb rest
termination_by n.natAbs
decreasing_by
  -- not a last byte: `n ∉ [-64, 64)`, so `|⌊n/128⌋| < |n|`
  rename_i h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not, decide_eq_true_eq, not_or, not_and] at h
  omega

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

/-- An FDE's instruction bytes for rows in code order, the location being at `at_`. -/
def cfiProgramFrom : Nat → List (Nat × Cfi) → ByteArray
  | _, [] => .empty
  | at_, (o, i) :: rows => cfiAdvance (o - at_) ++ i.bytes ++ cfiProgramFrom o rows

/-- An FDE's instruction bytes for rows in code order. -/
def cfiProgram (rows : List (Nat × Cfi)) : ByteArray := cfiProgramFrom 0 rows

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
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The labels after line `ln` at byte offset `off` (latest first). -/
def labsAfter (ln : Line) (off : Nat) (labs : List (Label × Nat)) : List (Label × Nat) :=
  match ln with
  | .label (.block l) => (l, off) :: labs
  | _ => labs

/-- The return offsets after line `ln` at byte offset `off` (latest first). -/
def retsAfter (ln : Line) (off : Nat) (rets : List Nat) : List Nat :=
  match ln with
  | .ins (.bl _) _ | .ins (.blr _) _ => (off + 4) :: rets
  | _ => rets

/-- The block labels of `lines` with their byte offsets (latest first: `lookup` finds a
label's last definition) and the return offsets of its calls (`bl`/`blr`, in code order),
the lines starting at byte offset `off`. -/
def scanLines : List Line → Nat → List (Label × Nat) → List Nat → List (Label × Nat) × List Nat
  | [], _, labs, rets => (labs, rets.reverse)
  | ln :: rest, off, labs, rets =>
    scanLines rest (off + ln.size) (labsAfter ln off labs) (retsAfter ln off rets)

/-- The handlers of a call (`some ti` for a `tryCall`). -/
def handlersOf : Option TryInfo → List TryHandler
  | some ti => ti.handlers
  | none => []

/-- The call-site entry of handler `h` of a call returning to `ret`. -/
def handlerEntry (labs : List (Label × Nat)) (ret : Nat) (h : TryHandler) :
    Except String CallSite := do
  let some pad := labs.lookup h.label | throw s!"LSDA: no landing pad label {h.label}"
  match h with
  | .tag 0 _ => pure ⟨ret - 1, 1, pad, 0⟩
  | .tag 1 _ => pure ⟨ret - 1, 1, pad, 1⟩
  | .tag n _ => throw s!"LSDA: exception tag {n} (cg_clif uses 0 = cleanup, 1 = catch)"
  | .default _ => throw "LSDA: a `default` handler (cg_clif uses tags 0 and 1)"

/-- The call-site entries of one call (`some ti` for a `tryCall`) returning to `ret`. -/
def siteEntries (labs : List (Label × Nat)) : Option TryInfo × Nat → Except String (List CallSite)
  | (c, ret) =>
    let handlers := handlersOf c
    if handlers.isEmpty then pure [⟨ret - 1, 1, 0, 0⟩]
    else handlers.mapM (handlerEntry labs ret)

/-- The calls of an allocated function in code order (`some ti` for a `tryCall`). -/
def AFunc.calls (af : AFunc) : List (Option TryInfo) :=
  af.blocks.toList.flatMap fun (_, code) =>
    code.toList.filterMap fun
      | .inst (.call _) => some none
      | .inst (.tryCall _ ti) => some (some ti)
      | _ => none

/-- The call-site table of an allocated function `af` whose final code is `fa` (every `bl`/
`blr` is a call, in code order, and `af`'s calls are in the same order), or `none` if the
function has no `try_call` (it needs no LSDA). -/
def callSites (af : AFunc) (fa : FnAsm) : Except String (Option (List CallSite)) := do
  let calls := af.calls
  if !calls.any (·.isSome) then return none
  let (labs, rets) := scanLines fa.lines.toList 0 [] []
  if rets.length != calls.length then throw "LSDA: the code's calls differ from the function's"
  let sites ← (calls.zip rets).mapM (siteEntries labs)
  return some sites.flatten

end Backend
