import FV.Backend.StackAlloc

/-!
# Assembly text output (GNU/LLVM syntax for `llvm-mc`)

Each allocated instruction is printed as the instruction sequence Cranelift's
`isa/aarch64/inst/emit.rs` produces for it (including `mem_finalize` for pseudo addressing
modes, and the expansions of `Extend`, `CSet`, `CondBr`, `TrapIf`, `JTSequence`,
`LoadExtNameGot`, `LoadAddr`). Every printed line is one 4-byte instruction or data word, so
byte offsets (for the trap table) are computed here; the assembler checks them (`.ifne`
guards after every function and at every trap site).

* Labels: `.L<k>_b<label>` for blocks, `.L<k>_t<n>` for out-of-line traps (Cranelift's
  deferred traps, emitted after the function body), `.L<k>_jt<n>` for jump tables.
* Calls: `bl sym` for colocated callees, and for others (`is_pic`) `adrp x, :got:sym` /
  `ldr x, [x, :got_lo12:sym]` / `blr x` — exactly the sequences the ISLE rules select. The
  static linker resolves both (it builds a GOT for the `:got:` relocations).
* Traps: `udf #0xc11f` (Cranelift's `TRAP_OPCODE`); the code is in the trap table.
-/

namespace Backend

/-- One output line: an instruction (4 bytes, optionally a trap site), a data word (4 bytes),
a label, or a 0-byte directive. -/
inductive Line where
  | ins (text : String) (trap : Option Clif.TrapCode := none)
  | word (text : String)
  | label (name : String)
  | dir (text : String)
  deriving Repr, Inhabited

def Line.size : Line → Nat
  | .ins .. | .word _ => 4
  | _ => 0

/-! ## Registers and operands -/

/-- A general-purpose register at 64 (`x`) or 32 (`w`) bits. -/
def Reg.gpr (r : Reg) (is64 : Bool := true) : String :=
  match r with
  | .x n => (if is64 then "x" else "w") ++ toString n
  | .xzr => if is64 then "xzr" else "wzr"
  | .sp => if is64 then "sp" else "wsp"
  | .v n => s!"<v{n}?>"
  | .vreg n _ => s!"<vreg{n}?>"

def Reg.vnum (r : Reg) : String :=
  match r with
  | .v n => toString n
  | _ => "<not-v>"

def OperandSize.is64 (s : OperandSize) : Bool := s == .size64

def Cond.asm : Cond → String
  | .eq => "eq" | .ne => "ne" | .hs => "hs" | .lo => "lo" | .mi => "mi" | .pl => "pl"
  | .vs => "vs" | .vc => "vc" | .hi => "hi" | .ls => "ls" | .ge => "ge" | .lt => "lt"
  | .gt => "gt" | .le => "le" | .al => "al" | .nv => "nv"

def ExtendOp.asm : ExtendOp → String
  | .uxtb => "uxtb" | .uxth => "uxth" | .uxtw => "uxtw" | .uxtx => "uxtx"
  | .sxtb => "sxtb" | .sxth => "sxth" | .sxtw => "sxtw" | .sxtx => "sxtx"

/-- Register width of the index in an extended operand (`w` for byte/half/word extends). -/
def ExtendOp.is64 : ExtendOp → Bool
  | .uxtx | .sxtx => true
  | _ => false

def ShiftOp.asm : ShiftOp → String
  | .lsl => "lsl" | .lsr => "lsr" | .asr => "asr" | .ror => "ror"

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def imm (i : Int) : String := "#" ++ toString i

/-! ## `mem_finalize` and constants -/

/-- `movz`/`movk` sequence for a 64-bit constant (a correct, not necessarily minimal,
replacement of `Inst::load_constant`; used only for address offsets). -/
def loadConst64 (rd : String) (value : Nat) : List Line :=
  let value := mask64 value
  let chunk (i : Nat) := (value / 2 ^ (16 * i)) % 2 ^ 16
  let first := .ins s!"movz {rd}, #{hex (chunk 0)}"
  first :: ((List.range 3).filterMap fun j =>
    let i := j + 1
    if chunk i != 0 then some (.ins s!"movk {rd}, #{hex (chunk i)}, lsl #{16 * i}") else none)

/-- Context for printing one function. -/
structure FnCtx where
  /-- Function index in the file (for local label names). -/
  k : Nat
  slotBase : Nat
  deriving Inhabited

def FnCtx.blockLabel (c : FnCtx) (l : Label) : String := s!".L{c.k}_b{l}"

/-- `mem_finalize`: turn pseudo addressing modes into real ones (`x16` holds large
offsets). Returns the extra instructions and the final mode. -/
def memFinalize (c : FnCtx) (m : AMode) (accessBytes : Nat) : List Line × AMode :=
  let fin (base : Reg) (off : Int) : List Line × AMode :=
    match simm9? off with
    | some s => ([], .unscaled base s)
    | none => match uimm12Scaled? off accessBytes with
      | some o => ([], .unsignedOffset base o)
      | none => (loadConst64 "x16" (u64 off), .regExtended base (.x 16) .sxtx)
  match m with
  | .regOffset rn off => fin rn off
  | .spOffset off => fin .sp off
  | .fpOffset off => fin Reg.fp off
  | .slotOffset off => fin .sp (off + c.slotBase)
  | .incomingArg _ => ([.ins "<incomingArg unsupported>"], m)
  | m => ([], m)

def log2 (n : Nat) : Nat := match n with
  | 1 => 0 | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0

/-- Print a final addressing mode. -/
def AMode.asm (m : AMode) (accessBytes : Nat) : String :=
  match m with
  | .unscaled rn s => s!"[{rn.gpr}, #{s}]"
  | .unsignedOffset rn o => s!"[{rn.gpr}, #{o}]"
  | .regReg rn rm => s!"[{rn.gpr}, {rm.gpr}]"
  | .regScaled rn rm => s!"[{rn.gpr}, {rm.gpr}, lsl #{log2 accessBytes}]"
  | .regScaledExtended rn rm e => s!"[{rn.gpr}, {rm.gpr e.is64}, {e.asm} #{log2 accessBytes}]"
  | .regExtended rn rm e => s!"[{rn.gpr}, {rm.gpr e.is64}, {e.asm}]"
  | .spPreIndexed s => s!"[sp, #{s}]!"
  | .spPostIndexed s => s!"[sp], #{s}"
  | _ => "<unfinalized amode>"

def AMode.isUnscaled : AMode → Bool
  | .unscaled .. => true
  | _ => false

/-- Mnemonic and destination register text of a load. -/
def LoadOp.asm (op : LoadOp) (rd : Reg) (unscaled : Bool) : String × String :=
  let u := if unscaled then "ldur" else "ldr"
  match op with
  | .uload8 => (u ++ "b", rd.gpr false)
  | .sload8 => (u ++ "sb", rd.gpr true)
  | .uload16 => (u ++ "h", rd.gpr false)
  | .sload16 => (u ++ "sh", rd.gpr true)
  | .uload32 => (u, rd.gpr false)
  | .sload32 => (u ++ "sw", rd.gpr true)
  | .uload64 => (u, rd.gpr true)
  | .fpuLoad128 => (u, "q" ++ rd.vnum)

def StoreOp.asm (op : StoreOp) (rd : Reg) (unscaled : Bool) : String × String :=
  let s := if unscaled then "stur" else "str"
  match op with
  | .store8 => (s ++ "b", rd.gpr false)
  | .store16 => (s ++ "h", rd.gpr false)
  | .store32 => (s, rd.gpr false)
  | .store64 => (s, rd.gpr true)
  | .fpuStore128 => (s, "q" ++ rd.vnum)

/-! ## Instructions -/

def ALUOp.rrr : ALUOp → String
  | .add => "add" | .sub => "sub" | .orr => "orr" | .orrNot => "orn" | .and => "and"
  | .andS => "ands" | .andNot => "bic" | .eor => "eor" | .eorNot => "eon" | .addS => "adds"
  | .subS => "subs" | .sMulH => "smulh" | .uMulH => "umulh" | .sDiv => "sdiv"
  | .uDiv => "udiv" | .extr => "rorv" | .lsr => "lsrv" | .asr => "asrv" | .lsl => "lslv"
  | .adc => "adc" | .adcS => "adcs" | .sbc => "sbc" | .sbcS => "sbcs"

def CondBrKind.branch (k : CondBrKind) (target : String) : String :=
  match k with
  | .zero r s => s!"cbz {r.gpr s.is64}, {target}"
  | .notZero r s => s!"cbnz {r.gpr s.is64}, {target}"
  | .cond c => s!"b.{c.asm} {target}"

def ScalarSize.fpreg (s : ScalarSize) (n : String) : String :=
  match s with
  | .size8 => "b" ++ n | .size16 => "h" ++ n | .size32 => "s" ++ n | .size64 => "d" ++ n
  | .size128 => "q" ++ n

def VectorSize.arr : VectorSize → String
  | .size8x8 => "8b" | .size8x16 => "16b" | .size16x4 => "4h" | .size16x8 => "8h"
  | .size32x2 => "2s" | .size32x4 => "4s" | .size64x2 => "2d"

/-- The lane-size letter of a vector size (for `addv`'s scalar destination). -/
def VectorSize.lane : VectorSize → String
  | .size8x8 | .size8x16 => "b" | .size16x4 | .size16x8 => "h"
  | .size32x2 | .size32x4 => "s" | .size64x2 => "d"

/-- State while printing a function: counters for local labels and the deferred traps. -/
structure PState where
  jt : Nat := 0
  traps : Array (String × Clif.TrapCode) := #[]

/-- Print one instruction (real registers only). -/
def MInst.asm (c : FnCtx) (m : MInst) (ps : PState) : Except String (List Line × PState) := do
  let one (s : String) : Except String (List Line × PState) := pure ([.ins s], ps)
  match m with
  | .aluRRR op s rd rn rm =>
    let is64 := s.is64 || op == .sMulH || op == .uMulH
    one s!"{op.rrr} {rd.gpr is64}, {rn.gpr is64}, {rm.gpr is64}"
  | .aluRRRR op s rd rn rm ra =>
    match op with
    | .mAdd => one s!"madd {rd.gpr s.is64}, {rn.gpr s.is64}, {rm.gpr s.is64}, {ra.gpr s.is64}"
    | .mSub => one s!"msub {rd.gpr s.is64}, {rn.gpr s.is64}, {rm.gpr s.is64}, {ra.gpr s.is64}"
    | .uMAddL => one s!"umaddl {rd.gpr}, {rn.gpr false}, {rm.gpr false}, {ra.gpr}"
    | .sMAddL => one s!"smaddl {rd.gpr}, {rn.gpr false}, {rm.gpr false}, {ra.gpr}"
  | .aluRRImm12 op s rd rn i =>
    let mn ← match op with
      | .add => pure "add" | .sub => pure "sub" | .addS => pure "adds" | .subS => pure "subs"
      | _ => throw s!"AluRRImm12 {repr op}"
    let sh := if i.shift12 then ", lsl #12" else ""
    one s!"{mn} {rd.gpr s.is64}, {rn.gpr s.is64}, #{i.bits}{sh}"
  | .aluRRImmLogic op s rd rn i =>
    let (mn, i) ← match op with
      | .orr => pure ("orr", i) | .and => pure ("and", i) | .andS => pure ("ands", i)
      | .eor => pure ("eor", i) | .orrNot => pure ("orr", i.invert)
      | .andNot => pure ("and", i.invert) | .eorNot => pure ("eor", i.invert)
      | _ => throw s!"AluRRImmLogic {repr op}"
    let v := match s with
      | .size32 => mask64 i.value % 2 ^ 32
      | .size64 => mask64 i.value
    one s!"{mn} {rd.gpr s.is64}, {rn.gpr s.is64}, #{hex v}"
  | .aluRRImmShift op s rd rn amt =>
    let mn ← match op with
      | .lsr => pure "lsr" | .asr => pure "asr" | .lsl => pure "lsl" | .extr => pure "ror"
      | _ => throw s!"AluRRImmShift {repr op}"
    one s!"{mn} {rd.gpr s.is64}, {rn.gpr s.is64}, #{amt}"
  | .aluRRRShift op s rd rn rm sh =>
    match op with
    | .extr => one s!"extr {rd.gpr s.is64}, {rn.gpr s.is64}, {rm.gpr s.is64}, #{sh.amt}"
    | _ => one s!"{op.rrr} {rd.gpr s.is64}, {rn.gpr s.is64}, {rm.gpr s.is64}, {sh.op.asm} #{sh.amt}"
  | .aluRRRExtend op s rd rn rm e =>
    let mn ← match op with
      | .add => pure "add" | .sub => pure "sub" | .addS => pure "adds" | .subS => pure "subs"
      | _ => throw s!"AluRRRExtend {repr op}"
    one s!"{mn} {rd.gpr s.is64}, {rn.gpr s.is64}, {rm.gpr (e.is64 && s.is64)}, {e.asm}"
  | .bitRR op s rd rn =>
    let mn := match op with
      | .rbit => "rbit" | .clz => "clz" | .cls => "cls" | .rev16 => "rev16" | .rev32 => "rev32"
      | .rev64 => "rev"
    one s!"{mn} {rd.gpr s.is64}, {rn.gpr s.is64}"
  | .load op rd mem fl =>
    let (pre, mem) := memFinalize c mem op.bytes
    let (mn, r) := op.asm rd mem.isUnscaled
    pure (pre ++ [.ins s!"{mn} {r}, {mem.asm op.bytes}" fl.trapCode], ps)
  | .store op rd mem fl =>
    let (pre, mem) := memFinalize c mem op.bytes
    let (mn, r) := op.asm rd mem.isUnscaled
    pure (pre ++ [.ins s!"{mn} {r}, {mem.asm op.bytes}" fl.trapCode], ps)
  | .mov s rd rm =>
    if rm == .sp then one s!"mov {rd.gpr}, sp"
    else one s!"mov {rd.gpr s.is64}, {rm.gpr s.is64}"
  | .movWide op rd i s =>
    let mn := if op == .movZ then "movz" else "movn"
    one s!"{mn} {rd.gpr s.is64}, #{hex i.bits}, lsl #{16 * i.shift}"
  | .movK rd _ i s => one s!"movk {rd.gpr s.is64}, #{hex i.bits}, lsl #{16 * i.shift}"
  | .extend rd rn signed fromBits toBits =>
    if !signed && fromBits == 1 then one s!"and {rd.gpr false}, {rn.gpr false}, #0x1"
    else if !signed && fromBits == 32 && toBits == 64 then one s!"mov {rd.gpr false}, {rn.gpr false}"
    else if signed then
      let is64 := toBits > 32
      one s!"sbfm {rd.gpr is64}, {rn.gpr is64}, #0, #{fromBits - 1}"
    else one s!"ubfm {rd.gpr false}, {rn.gpr false}, #0, #{fromBits - 1}"
  | .bitfieldMove s op rd rn immr imms =>
    let mn := if op == .sBfm then "sbfm" else "ubfm"
    one s!"{mn} {rd.gpr s.is64}, {rn.gpr s.is64}, #{immr}, #{imms}"
  | .cset rd cond => one s!"cset {rd.gpr}, {cond.asm}"
  | .ccmp s rn rm f cond => one s!"ccmp {rn.gpr s.is64}, {rm.gpr s.is64}, #{f.bits}, {cond.asm}"
  | .ccmpImm s rn i f cond => one s!"ccmp {rn.gpr s.is64}, #{i}, #{f.bits}, {cond.asm}"
  | .movToFpu rd rn s =>
    match s with
    | .size16 => one s!"fmov h{rd.vnum}, {rn.gpr false}"
    | .size32 => one s!"fmov s{rd.vnum}, {rn.gpr false}"
    | .size64 => one s!"fmov d{rd.vnum}, {rn.gpr}"
    | _ => throw "MovToFpu size"
  | .movFromVec rd rn idx s =>
    match s with
    | .size8 => one s!"umov {rd.gpr false}, v{rn.vnum}.b[{idx}]"
    | .size16 => one s!"umov {rd.gpr false}, v{rn.vnum}.h[{idx}]"
    | .size32 => one s!"umov {rd.gpr false}, v{rn.vnum}.s[{idx}]"
    | .size64 => one s!"umov {rd.gpr}, v{rn.vnum}.d[{idx}]"
    | _ => throw "MovFromVec size"
  | .vecMisc .cnt rd rn s => one s!"cnt v{rd.vnum}.{s.arr}, v{rn.vnum}.{s.arr}"
  | .vecLanes op rd rn s =>
    let mn := if op == .addv then "addv" else "uaddlv"
    one s!"{mn} {s.lane}{rd.vnum}, v{rn.vnum}.{s.arr}"
  | .vecRRR .addp rd rn rm s => one s!"addp v{rd.vnum}.{s.arr}, v{rn.vnum}.{s.arr}, v{rm.vnum}.{s.arr}"
  | .call info =>
    match info.dest with
    | .sym n => one s!"bl {n}"
    | .reg r => one s!"blr {r.gpr}"
  | .args _ | .rets _ => throw "args/rets after allocation"
  | .jump l => one s!"b {c.blockLabel l}"
  | .condBr t e k => pure ([.ins (k.branch (c.blockLabel t)), .ins s!"b {c.blockLabel e}"], ps)
  | .testBitAndBranch k t e rn bit =>
    let mn := if k == .z then "tbz" else "tbnz"
    pure ([.ins s!"{mn} {rn.gpr}, #{bit}, {c.blockLabel t}", .ins s!"b {c.blockLabel e}"], ps)
  | .trapIf k code =>
    let l := s!".L{c.k}_t{ps.traps.size}"
    pure ([.ins (k.branch l)], { ps with traps := ps.traps.push (l, code) })
  | .udf code => pure ([.ins "udf #0xc11f" (some code)], ps)
  | .jtSequence dflt targets ridx t1 t2 =>
    let jt := s!".L{c.k}_jt{ps.jt}"
    let body : List Line :=
      [.ins s!"b.hs {c.blockLabel dflt}", .ins s!"csel {t2.gpr}, xzr, {ridx.gpr}, hs",
       .ins s!"adr {t1.gpr}, {jt}", .ins s!"ldrsw {t2.gpr}, [{t1.gpr}, {t2.gpr false}, uxtw #2]",
       .ins s!"add {t1.gpr}, {t1.gpr}, {t2.gpr}", .ins s!"br {t1.gpr}", .label jt] ++
      targets.map fun l => .word s!".word {c.blockLabel l} - {jt}"
    pure (body, { ps with jt := ps.jt + 1 })
  | .loadExtNameGot rd n =>
    pure ([.ins s!"adrp {rd.gpr}, :got:{n}", .ins s!"ldr {rd.gpr}, [{rd.gpr}, :got_lo12:{n}]"], ps)
  | .loadExtNameNear rd n off =>
    let sym := if off == 0 then n else if off > 0 then s!"{n}+{off}" else s!"{n}{off}"
    pure ([.ins s!"adrp {rd.gpr}, {sym}", .ins s!"add {rd.gpr}, {rd.gpr}, :lo12:{sym}"], ps)
  | .loadAddr rd mem =>
    let (pre, mem) := memFinalize c mem 1
    let tail : List Line ← match mem with
      | .regExtended rn rm e => pure [.ins s!"add {rd.gpr}, {rn.gpr}, {rm.gpr e.is64}, {e.asm}"]
      | .unscaled rn off => pure (addOff rd rn off)
      | .unsignedOffset rn off => pure (addOff rd rn off)
      | _ => throw "LoadAddr amode"
    pure (pre ++ tail, ps)
  | .emitIsland _ => pure ([], ps)
where
  /-- `LoadAddr` with an immediate offset (`emit.rs`). -/
  addOff (rd rn : Reg) (off : Int) : List Line :=
    if off == 0 then
      if rn == rd then []
      else if rn == .sp then [.ins s!"mov {rd.gpr}, sp"]
      else [.ins s!"mov {rd.gpr}, {rn.gpr}"]
    else if off > 0 then [.ins s!"add {rd.gpr}, {rn.gpr}, #{off}"]
    else [.ins s!"sub {rd.gpr}, {rn.gpr}, #{-off}"]

/-- Prologue and epilogue (frame size a multiple of 16). -/
def prologueLines (size : Nat) : List Line :=
  [.ins "stp x29, x30, [sp, #-16]!", .ins "mov x29, sp"] ++
  (if size == 0 then []
   else match Imm12.ofNat? size with
     | some i => [.ins s!"sub sp, sp, #{i.bits}{if i.shift12 then ", lsl #12" else ""}"]
     | none => loadConst64 "x16" size ++ [.ins "sub sp, sp, x16, uxtx"])

def epilogueLines : List Line :=
  [.ins "mov sp, x29", .ins "ldp x29, x30, [sp], #16", .ins "ret"]

/-- A trap site: byte offset from the function start and trap code. -/
structure TrapSite where
  offset : Nat
  code : Clif.TrapCode
  deriving Repr, Inhabited

/-- Printed function: text, size in bytes, trap table. -/
structure FnAsm where
  name : String
  text : String
  size : Nat
  traps : List TrapSite
  deriving Inhabited

/-- Print an allocated function (`k` = its index in the file). -/
def printFunc (k : Nat) (af : AFunc) : Except String FnAsm := do
  let c : FnCtx := { k, slotBase := af.slotBase }
  let mut ps : PState := {}
  let mut lines : Array Line := #[]
  for (l, code) in af.blocks do
    lines := lines.push (.label (c.blockLabel l))
    for i in code do
      match i with
      | .prologue => lines := lines ++ (prologueLines af.frameSize).toArray
      | .epilogueRet => lines := lines ++ epilogueLines.toArray
      | .inst m =>
        let (ls, ps') ← m.asm c ps
        ps := ps'
        lines := lines ++ ls.toArray
  -- deferred traps (Cranelift emits them after the body)
  for (l, code) in ps.traps do
    lines := lines.push (.label l)
    lines := lines.push (.ins "udf #0xc11f" (some code))
  -- offsets, trap table and text
  let mut off := 0
  let mut traps : Array TrapSite := #[]
  let mut out : Array String := #[]
  let n := af.name
  out := out ++ #[s!"  .globl {n}", s!"  .type {n}, %function", "  .p2align 2", s!"{n}:"]
  for ln in lines do
    match ln with
    | .ins t tr =>
      if let some code := tr then
        traps := traps.push ⟨off, code⟩
        out := out.push s!"  .ifne . - {n} - {off}\n  .error \"trap offset mismatch\"\n  .endif"
      out := out.push s!"  {t}"
    | .word t => out := out.push s!"  {t}"
    | .label l => out := out.push s!"{l}:"
    | .dir t => out := out.push s!"  {t}"
    off := off + ln.size
  out := out ++ #[s!"  .ifne . - {n} - {off}\n  .error \"function size mismatch\"\n  .endif",
                  s!"  .size {n}, . - {n}"]
  pure { name := n, text := "\n".intercalate out.toList ++ "\n", size := off, traps := traps.toList }

end Backend
