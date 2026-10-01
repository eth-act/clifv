import FV.Backend.StackAlloc

/-!
# Final instruction list and assembly text

`MInst.lines` expands each allocated instruction into the instruction sequence Cranelift's
`isa/aarch64/inst/emit.rs` produces for it (including `mem_finalize` for pseudo addressing
modes, and the expansions of `Extend`, `CSet`, `CondBr`, `TrapIf`, `JTSequence`,
`LoadExtNameGot`, `LoadAddr`). The result is a list of `Line`s over one structured
instruction type, `Insn`: one `Insn` is exactly one line of assembly and one 4-byte machine
word. Both outputs consume it:

* `FnAsm.text` prints GNU/LLVM assembly (for `llvm-mc`, now only a test oracle);
* `FV/Backend/Encode.lean` encodes it to machine words (`Insn.encode`), lays functions out
  (labels, relocations, trap table) and `FV/Backend/Obj.lean` writes the ELF object.

So comparing `llvm-mc`'s bytes for `FnAsm.text` with the encoder's bytes checks the encoder
against the assembler's reading of the same instruction list.

* Labels (`Lbl`): blocks `.L<k>_b<label>`, out-of-line traps `.L<k>_t<n>` (Cranelift's
  deferred traps, emitted after the function body), jump tables `.L<k>_jt<n>`.
* Calls: `bl sym` for colocated callees, and for others (`is_pic`) `adrp x, :got:sym` /
  `ldr x, [x, :got_lo12:sym]` / `blr x` — exactly the sequences the ISLE rules select.
* Traps: `udf #0xc11f` (Cranelift's `TRAP_OPCODE`); the code is in the trap table.
-/

namespace Backend

/-! ## Labels and instructions -/

/-- A function-local label. -/
inductive Lbl where
  | block (l : Label)
  | trap (n : Nat)
  | jt (n : Nat)
  /-- An emit-time label of an atomic LL/SC loop expansion (not a block label). -/
  | loop (n : Nat)
  -- `BEq` is the lawful one from `DecidableEq` (the layout proof uses `Std.HashMap` lemmas)
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Assembly name of a label of function `k` (its index in the file). -/
def Lbl.name (k : Nat) : Lbl → String
  | .block l => s!".L{k}_b{l}"
  | .trap n => s!".L{k}_t{n}"
  | .jt n => s!".L{k}_jt{n}"
  | .loop n => s!".L{k}_a{n}"

/-- One AArch64 instruction over real registers: one line of assembly, one 4-byte word.
Constructors follow the assembly the backend prints (including the aliases `mov`, `cset`,
`lsl`/`lsr`/`asr`/`ror #imm`), so that `llvm-mc` checks the alias translation the encoder does.
`is64` selects `x` (true) or `w` registers. Branch targets are local labels; symbol operands
become relocations. -/
inductive Insn where
  /-- Three-register ALU op: `add/sub/adds/subs/and/orr/eor/ands/orn/bic/eon` (shifted
  register, `lsl #0`), `sdiv/udiv/lslv/lsrv/asrv/rorv`, `smulh/umulh`, `adc/adcs/sbc/sbcs`. -/
  | aluRRR (op : ALUOp) (is64 : Bool) (rd rn rm : Reg)
  /-- `madd/msub` (`is64`), `smaddl/umaddl` (always `x rd, w rn, w rm, x ra`). -/
  | aluRRRR (op : ALUOp3) (is64 : Bool) (rd rn rm ra : Reg)
  /-- `add/sub/adds/subs rd, rn, #imm12{, lsl #12}`. -/
  | aluImm12 (op : ALUOp) (is64 : Bool) (rd rn : Reg) (imm : Imm12)
  /-- `and/orr/eor/ands rd, rn, #value` with a bitmask immediate (`value < 2^size`). -/
  | logicImm (op : ALUOp) (is64 : Bool) (rd rn : Reg) (value : Nat)
  /-- `lsl/lsr/asr/ror rd, rn, #amt` (aliases of `ubfm`/`sbfm`/`extr`). -/
  | shiftImm (op : ShiftOp) (is64 : Bool) (rd rn : Reg) (amt : Nat)
  /-- `op rd, rn, rm, shift #amt` (add/sub/logical, shifted register). -/
  | aluRRRShift (op : ALUOp) (is64 : Bool) (rd rn rm : Reg) (sh : ShiftOpAndAmt)
  /-- `extr rd, rn, rm, #lsb`. -/
  | extr (is64 : Bool) (rd rn rm : Reg) (lsb : Nat)
  /-- `add/sub/adds/subs rd, rn, rm, ext` (extended register, amount 0). -/
  | aluRRRExtend (op : ALUOp) (is64 : Bool) (rd rn rm : Reg) (e : ExtendOp)
  /-- `rbit/clz/cls/rev16/rev32/rev rd, rn`. -/
  | bitRR (op : BitOp) (is64 : Bool) (rd rn : Reg)
  /-- Single-register load; `m` is a final mode (`unscaled` prints `ldur*`). -/
  | load (op : LoadOp) (rt : Reg) (m : AMode)
  /-- Single-register store; `m` is a final mode (`unscaled` prints `stur*`). -/
  | store (op : StoreOp) (rt : Reg) (m : AMode)
  /-- `ldp xt, xt2, m` (`m` = `spPostIndexed`/`spPreIndexed`, byte offset). -/
  | ldp (rt rt2 : Reg) (m : AMode)
  /-- `stp xt, xt2, m`. -/
  | stp (rt rt2 : Reg) (m : AMode)
  /-- `mov rd, rm`: `orr rd, zr, rm`, or `add rd, rn, #0` when either is `sp`. -/
  | mov (is64 : Bool) (rd rm : Reg)
  /-- `movz/movn rd, #bits, lsl #16*shift`. -/
  | movWide (op : MoveWideOp) (is64 : Bool) (rd : Reg) (imm : MoveWideConst)
  /-- `movk rd, #bits, lsl #16*shift`. -/
  | movk (is64 : Bool) (rd : Reg) (imm : MoveWideConst)
  /-- `sbfm/ubfm rd, rn, #immr, #imms`. -/
  | bfm (op : BfmOp) (is64 : Bool) (rd rn : Reg) (immr imms : Nat)
  /-- `cset xd, cond` (`csinc xd, xzr, xzr, !cond`). -/
  | cset (rd : Reg) (c : Cond)
  /-- `csel xd, xn, xm, cond`. -/
  | csel (rd rn rm : Reg) (c : Cond)
  /-- `ccmp rn, rm, #nzcv, cond`. -/
  | ccmp (is64 : Bool) (rn rm : Reg) (nzcv : NZCV) (c : Cond)
  /-- `ccmp rn, #imm5, #nzcv, cond`. -/
  | ccmpImm (is64 : Bool) (rn : Reg) (imm : Nat) (nzcv : NZCV) (c : Cond)
  /-- `fmov h/s/d rd, w/w/x rn`. -/
  | fmovToFp (size : ScalarSize) (rd rn : Reg)
  /-- `umov w/x rd, vn.<T>[idx]`. -/
  | umov (size : ScalarSize) (rd rn : Reg) (idx : Nat)
  /-- `cnt vd.<T>, vn.<T>` (8b/16b). -/
  | cnt (size : VectorSize) (rd rn : Reg)
  /-- `addv/uaddlv <lane>d, vn.<T>`. -/
  | vecLanes (op : VecLanesOp) (size : VectorSize) (rd rn : Reg)
  /-- `addp vd.<T>, vn.<T>, vm.<T>`. -/
  | addp (size : VectorSize) (rd rn rm : Reg)
  | b (target : Lbl)
  | bcond (c : Cond) (target : Lbl)
  /-- `cbz` (`nz = false`) / `cbnz` (`nz = true`). -/
  | cbz (nz : Bool) (is64 : Bool) (rt : Reg) (target : Lbl)
  /-- `tbz` (`nz = false`) / `tbnz` (`nz = true`) `xt, #bit, target`. -/
  | tbz (nz : Bool) (rt : Reg) (bit : Nat) (target : Lbl)
  /-- `bl sym` (relocation `R_AARCH64_CALL26`). -/
  | bl (sym : String)
  | blr (rn : Reg)
  | br (rn : Reg)
  /-- `ret` (x30). -/
  | ret
  | udf (imm : Nat)
  /-- `adr xd, target`. -/
  | adr (rd : Reg) (target : Lbl)
  /-- `adrp xd, :got:sym` (`R_AARCH64_ADR_GOT_PAGE`). -/
  | adrpGot (rd : Reg) (sym : String)
  /-- `ldr xd, [xn, :got_lo12:sym]` (`R_AARCH64_LD64_GOT_LO12_NC`). -/
  | ldrGotLo12 (rd rn : Reg) (sym : String)
  /-- `adrp xd, sym+addend` (`R_AARCH64_ADR_PREL_PG_HI21`). -/
  | adrp (rd : Reg) (sym : String) (addend : Int)
  /-- `add xd, xn, :lo12:sym+addend` (`R_AARCH64_ADD_ABS_LO12_NC`). -/
  | addLo12 (rd rn : Reg) (sym : String) (addend : Int)
  /-- `ldar{b,h,}` (`bits` ∈ {8, 16, 32, 64}; `ldar w..`/`ldar x..` at 32/64). -/
  | ldar (bits : Nat) (rt rn : Reg)
  /-- `stlr{b,h,}`. -/
  | stlr (bits : Nat) (rt rn : Reg)
  /-- `ldaxr{b,h,}` (acquire exclusive load). -/
  | ldaxr (bits : Nat) (rt rn : Reg)
  /-- `stlxr{b,h,} w/rs, x/wt, [xn]` (`rs` is the success-flag register, always `w`). -/
  | stlxr (bits : Nat) (rs rt rn : Reg)
  /-- `dmb ish` (`MInst.Fence`). -/
  | dmbish
  /-- `csetm xd, cond` = `csinv xd, xzr, xzr, invert(cond)`. -/
  | csetm (rd : Reg) (c : Cond)
  /-- `adrp xd, :tlsdesc:sym` (`R_AARCH64_TLSDESC_ADR_PAGE21`). -/
  | adrpTlsDesc (rd : Reg) (sym : String)
  /-- `ldr xt, [xn, :tlsdesc_lo12:sym]` (`R_AARCH64_TLSDESC_LD64_LO12`). -/
  | ldrTlsDescLo12 (rt rn : Reg) (sym : String)
  /-- `add xd, xn, :tlsdesc_lo12:sym` (`R_AARCH64_TLSDESC_ADD_LO12`). -/
  | addTlsDescLo12 (rd rn : Reg) (sym : String)
  /-- `blr xn` marked `.tlsdesccall sym` (`R_AARCH64_TLSDESC_CALL`, for linker relaxation). -/
  | blrTlsDesc (rn : Reg) (sym : String)
  /-- `mrs xt, tpidr_el0` (the thread pointer). -/
  | mrsTpidrEl0 (rt : Reg)
  deriving DecidableEq, Repr, Inhabited, BEq

/-- One element of a function's code: an instruction (4 bytes, optionally a trap site), a
jump-table word `target - base` (4 bytes of data), or a label (0 bytes). -/
inductive Line where
  | ins (i : Insn) (trap : Option Clif.TrapCode := none)
  | word (target base : Lbl)
  | label (l : Lbl)
  deriving Repr, Inhabited

def Line.size : Line → Nat
  | .ins .. | .word .. => 4
  | .label _ => 0

/-! ## Expansion of allocated instructions (`emit.rs`) -/

def OperandSize.is64 (s : OperandSize) : Bool := s == .size64

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- `movz`/`movk` sequence for a 64-bit constant (a correct, not necessarily minimal,
replacement of `Inst::load_constant`; used only for address offsets). -/
def loadConst64 (rd : Reg) (value : Nat) : List Line :=
  let value := mask64 value
  let chunk (i : Nat) := (value / 2 ^ (16 * i)) % 2 ^ 16
  let first := .ins (.movWide .movZ true rd ⟨chunk 0, 0⟩)
  first :: ((List.range 3).filterMap fun j =>
    let i := j + 1
    if chunk i != 0 then some (.ins (.movk true rd ⟨chunk i, i⟩)) else none)

/-- Context for expanding one function. -/
structure FnCtx where
  /-- Function index in the file (for local label names). -/
  k : Nat
  slotBase : Nat
  deriving Inhabited

/-- `mem_finalize`: turn pseudo addressing modes into real ones (`x16` holds large
offsets). Returns the extra instructions and the final mode. -/
def memFinalize (c : FnCtx) (m : AMode) (accessBytes : Nat) : Except String (List Line × AMode) :=
  let fin (base : Reg) (off : Int) : List Line × AMode :=
    match simm9? off with
    | some s => ([], .unscaled base s)
    | none => match uimm12Scaled? off accessBytes with
      | some o => ([], .unsignedOffset base o)
      | none => (loadConst64 (.x 16) (u64 off), .regExtended base (.x 16) .sxtx)
  match m with
  | .regOffset rn off => pure (fin rn off)
  | .spOffset off => pure (fin .sp off)
  | .fpOffset off => pure (fin Reg.fp off)
  | .slotOffset off => pure (fin .sp (off + c.slotBase))
  | .incomingArg _ => throw "memFinalize: IncomingArg is not supported"
  | m => pure ([], m)

/-- State while expanding a function: counters for local labels and the deferred traps. -/
structure PState where
  jt : Nat := 0
  /-- Emit-time labels of the atomic LL/SC loop expansions. -/
  aloop : Nat := 0
  traps : Array (Lbl × Clif.TrapCode) := #[]

/-- The branch of a `CondBrKind` to `target`. -/
def CondBrKind.insn (k : CondBrKind) (target : Lbl) : Insn :=
  match k with
  | .zero r s => .cbz false s.is64 r target
  | .notZero r s => .cbz true s.is64 r target
  | .cond c => .bcond c target

/-! ### The LL/SC loops (`emit.rs` `AtomicRMWLoop`, `AtomicCASLoop`) -/

/-- The min/max comparison of the `atomic_rmw` loop: `subs xzr, x27, x26` at the operation size
(`OperandSize::from_ty`: 32-bit below `i64`), with the operand register extended to the access
size for `i8`/`i16` (`sxt{b,h}` for `smin`/`smax`, whose loaded value is sign-extended first,
`uxt{b,h}` for `umin`/`umax`). -/
def rmwLoopCmp (op : AtomicRmwLoopOp) (bits : Nat) : Insn :=
  match op, bits with
  | .smin, 8 | .smax, 8 => .aluRRRExtend .subS false .xzr (.x 27) (.x 26) .sxtb
  | .smin, 16 | .smax, 16 => .aluRRRExtend .subS false .xzr (.x 27) (.x 26) .sxth
  | .umin, 8 | .umax, 8 => .aluRRRExtend .subS false .xzr (.x 27) (.x 26) .uxtb
  | .umin, 16 | .umax, 16 => .aluRRRExtend .subS false .xzr (.x 27) (.x 26) .uxth
  | _, b => .aluRRR .subS (b == 64) .xzr (.x 27) (.x 26)

/-- `sxt{b,h} w27, w27` before the `smin`/`smax` comparison of a subword (`Inst::Extend` to 32
bits). -/
def rmwLoopSext (bits : Nat) : List Insn :=
  match bits with
  | 8 => [.bfm .sBfm false (.x 27) (.x 27) 0 7]
  | 16 => [.bfm .sBfm false (.x 27) (.x 27) 0 15]
  | _ => []

/-- The instructions of the `atomic_rmw` loop between `ldaxr x27, [x25]` and `stlxr`: the new
value in x28 from the old value x27 and the operand x26, at the operation size (`xchg`: none,
it stores x26). -/
def rmwLoopMid (op : AtomicRmwLoopOp) (bits : Nat) : List Insn :=
  let w := bits == 64
  match op with
  | .xchg => []
  | .nand => [.aluRRR .and w (.x 28) (.x 27) (.x 26), .aluRRR .orrNot w (.x 28) .xzr (.x 28)]
  | .add => [.aluRRR .add w (.x 28) (.x 27) (.x 26)]
  | .sub => [.aluRRR .sub w (.x 28) (.x 27) (.x 26)]
  | .and => [.aluRRR .and w (.x 28) (.x 27) (.x 26)]
  | .or => [.aluRRR .orr w (.x 28) (.x 27) (.x 26)]
  | .xor => [.aluRRR .eor w (.x 28) (.x 27) (.x 26)]
  | .smin => rmwLoopSext bits ++ [rmwLoopCmp .smin bits, .csel (.x 28) (.x 27) (.x 26) .lt]
  | .smax => rmwLoopSext bits ++ [rmwLoopCmp .smax bits, .csel (.x 28) (.x 27) (.x 26) .gt]
  | .umin => [rmwLoopCmp .umin bits, .csel (.x 28) (.x 27) (.x 26) .lo]
  | .umax => [rmwLoopCmp .umax bits, .csel (.x 28) (.x 27) (.x 26) .hi]

/-- The register `stlxr` stores: the new value x28, or the operand x26 for `xchg`. -/
def rmwLoopStored (op : AtomicRmwLoopOp) : Reg := if op == .xchg then .x 26 else .x 28

/-- The body of the `atomic_rmw` loop: `ldaxr x27, [x25]; …; stlxr w24, x28, [x25]`. -/
def rmwLoopBody (bits : Nat) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags) : List Line :=
  [.ins (.ldaxr bits (.x 27) (.x 25)) fl.trapCode] ++
    (rmwLoopMid op bits).map (fun i => .ins i) ++
    [.ins (.stlxr bits (.x 24) (rmwLoopStored op) (.x 25)) fl.trapCode]

/-- The lines of the `atomic_rmw` loop at label `l`: `l: <body>; cbnz x24, l`. -/
def rmwLoopLines (bits : Nat) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags) (l : Lbl) : List Line :=
  .label l :: rmwLoopBody bits op fl ++ [.ins (.cbz true true (.x 24) l)]

/-- The comparison of the `atomic_cas` loop: the zero-extended loaded value x27 against the
expected value x26 extended to the access size. Deviation from Cranelift 0.136.1 at `i32`:
Cranelift compares all 64 bits of x26 (`cmp x27, x26`), whose upper half is unspecified for an
`i32` value (e.g. an `ireduce`), so a CAS whose expected value has nonzero upper register bits
fails although the low 32 bits match (observed with `clif-native`); the backend compares
`x27` with `w26, uxtw`. -/
def casLoopCmp (bits : Nat) : Insn :=
  match bits with
  | 8 => .aluRRRExtend .subS true .xzr (.x 27) (.x 26) .uxtb
  | 16 => .aluRRRExtend .subS true .xzr (.x 27) (.x 26) .uxth
  | 32 => .aluRRRExtend .subS true .xzr (.x 27) (.x 26) .uxtw
  | _ => .aluRRR .subS true .xzr (.x 27) (.x 26)

/-- The head of the `atomic_cas` loop: `ldaxr x27, [x25]; cmp …`. -/
def casLoopHead (bits : Nat) (fl : Clif.MemFlags) : List Line :=
  [.ins (.ldaxr bits (.x 27) (.x 25)) fl.trapCode, .ins (casLoopCmp bits)]

/-- The lines of the `atomic_cas` loop at labels `again`, `out`:
`again: ldaxr x27, [x25]; cmp …; b.ne out; stlxr w24, x28, [x25]; cbnz x24, again; out:`. -/
def casLoopLines (bits : Nat) (fl : Clif.MemFlags) (again out : Lbl) : List Line :=
  .label again :: casLoopHead bits fl ++
    [.ins (.bcond .ne out), .ins (.stlxr bits (.x 24) (.x 28) (.x 25)) fl.trapCode,
     .ins (.cbz true true (.x 24) again), .label out]

/-- Expand one allocated instruction (real registers only). -/
def MInst.lines (c : FnCtx) (m : MInst) (ps : PState) : Except String (List Line × PState) := do
  let one (i : Insn) : Except String (List Line × PState) := pure ([.ins i], ps)
  match m with
  | .aluRRR op s rd rn rm => one (.aluRRR op (s.is64 || op == .sMulH || op == .uMulH) rd rn rm)
  | .aluRRRR op s rd rn rm ra => one (.aluRRRR op s.is64 rd rn rm ra)
  | .aluRRImm12 op s rd rn i => one (.aluImm12 op s.is64 rd rn i)
  | .aluRRImmLogic op s rd rn i =>
    let (op, i) ← match op with
      | .orr | .and | .andS | .eor => pure (op, i)
      | .orrNot => pure (.orr, i.invert) | .andNot => pure (.and, i.invert)
      | .eorNot => pure (.eor, i.invert)
      | _ => throw s!"AluRRImmLogic {repr op}"
    let v := match s with
      | .size32 => mask64 i.value % 2 ^ 32
      | .size64 => mask64 i.value
    one (.logicImm op s.is64 rd rn v)
  | .aluRRImmShift op s rd rn amt =>
    let sop ← match op with
      | .lsr => pure ShiftOp.lsr | .asr => pure .asr | .lsl => pure .lsl | .extr => pure .ror
      | _ => throw s!"AluRRImmShift {repr op}"
    one (.shiftImm sop s.is64 rd rn amt)
  | .aluRRRShift op s rd rn rm sh =>
    match op with
    | .extr => one (.extr s.is64 rd rn rm sh.amt)
    | _ => one (.aluRRRShift op s.is64 rd rn rm sh)
  | .aluRRRExtend op s rd rn rm e => one (.aluRRRExtend op s.is64 rd rn rm e)
  | .bitRR op s rd rn => one (.bitRR op s.is64 rd rn)
  | .load op rd mem fl =>
    let (pre, mem) ← memFinalize c mem op.bytes
    pure (pre ++ [.ins (.load op rd mem) fl.trapCode], ps)
  | .store op rd mem fl =>
    let (pre, mem) ← memFinalize c mem op.bytes
    pure (pre ++ [.ins (.store op rd mem) fl.trapCode], ps)
  | .mov s rd rm => one (if rm == .sp then .mov true rd rm else .mov s.is64 rd rm)
  | .movWide op rd i s => one (.movWide op s.is64 rd i)
  | .movK rd _ i s => one (.movk s.is64 rd i)
  | .extend rd rn signed fromBits toBits =>
    if !signed && fromBits == 1 then one (.logicImm .and false rd rn 1)
    else if !signed && fromBits == 32 && toBits == 64 then one (.mov false rd rn)
    else if signed then one (.bfm .sBfm (toBits > 32) rd rn 0 (fromBits - 1))
    else one (.bfm .uBfm false rd rn 0 (fromBits - 1))
  | .bitfieldMove s op rd rn immr imms => one (.bfm op s.is64 rd rn immr imms)
  | .cset rd cond => one (.cset rd cond)
  | .csel rd rn rm cond => one (.csel rd rn rm cond)
  | .ccmp s rn rm f cond => one (.ccmp s.is64 rn rm f cond)
  | .ccmpImm s rn i f cond => one (.ccmpImm s.is64 rn i f cond)
  | .movToFpu rd rn s => one (.fmovToFp s rd rn)
  | .movFromVec rd rn idx s => one (.umov s rd rn idx)
  | .vecMisc .cnt rd rn s => one (.cnt s rd rn)
  | .vecLanes op rd rn s => one (.vecLanes op s rd rn)
  | .vecRRR .addp rd rn rm s => one (.addp s rd rn rm)
  | .call info =>
    match info.dest with
    | .sym n => one (.bl n)
    | .reg r => one (.blr r)
  | .args _ | .rets _ => throw "args/rets after allocation"
  -- `emit.rs` `Inst::Call`/`CallInd` with `try_call_info`: the call, then `b continuation`
  -- (dropped by `fallthrough` when the continuation is the next block); the landing pads
  -- are recorded in the LSDA (`Backend.Unwind`, `callSites`)
  | .tryCall info ti =>
    let call : Insn := match info.dest with
      | .sym n => .bl n
      | .reg r => .blr r
    pure ([.ins call, .ins (.b (.block ti.continuation))], ps)
  | .jump l => one (.b (.block l))
  | .condBr t e k => pure ([.ins (k.insn (.block t)), .ins (.b (.block e))], ps)
  | .testBitAndBranch k t e rn bit =>
    pure ([.ins (.tbz (k == .nz) rn bit (.block t)), .ins (.b (.block e))], ps)
  | .trapIf k code =>
    let l := Lbl.trap ps.traps.size
    pure ([.ins (k.insn l)], { ps with traps := ps.traps.push (l, code) })
  | .udf code => pure ([.ins (.udf 0xc11f) (some code)], ps)
  | .jtSequence dflt targets ridx t1 t2 =>
    let jt := Lbl.jt ps.jt
    let body : List Line :=
      [.ins (.bcond .hs (.block dflt)), .ins (.csel t2 .xzr ridx .hs), .ins (.adr t1 jt),
       .ins (.load .sload32 t2 (.regScaledExtended t1 t2 .uxtw)),
       .ins (.aluRRR .add true t1 t1 t2), .ins (.br t1), .label jt] ++
      targets.map fun l => .word (.block l) jt
    pure (body, { ps with jt := ps.jt + 1 })
  | .loadExtNameGot rd n => pure ([.ins (.adrpGot rd n), .ins (.ldrGotLo12 rd rd n)], ps)
  | .loadExtNameNear rd n off => pure ([.ins (.adrp rd n off), .ins (.addLo12 rd rd n off)], ps)
  | .loadAddr rd mem =>
    let (pre, mem) ← memFinalize c mem 1
    let tail : List Line ← match mem with
      | .regExtended rn rm e => pure [.ins (.aluRRRExtend .add true rd rn rm e)]
      | .unscaled rn off => pure (addOff rd rn off)
      | .unsignedOffset rn off => pure (addOff rd rn off)
      | _ => throw "LoadAddr amode"
    pure (pre ++ tail, ps)
  | .emitIsland _ => pure ([], ps)
  | .loadAcquire ty rt rn fl => pure ([.ins (.ldar ty.bits rt rn) fl.trapCode], ps)
  | .storeRelease ty rt rn fl => pure ([.ins (.stlr ty.bits rt rn) fl.trapCode], ps)
  | .csetm rd c => one (.csetm rd c)
  | .fence => one .dmbish
  -- The LL/SC loop expansions, transcribed from Cranelift's `inst/emit.rs`
  -- (`AtomicRMWLoop`, `AtomicCASLoop`; the fixed registers are `aarch64_get_operands`'
  -- fixed operands, which regalloc2 assigned).
  | .atomicRmwLoop ty op fl addr operand oldval s1 s2 =>
    if addr != .x 25 || operand != .x 26 || oldval != .x 27 || s1 != .x 24
        || (op != .xchg && s2 != .x 28) then
      throw s!"atomic_rmw_loop with unexpected fixed registers {repr addr} {repr operand} \
        {repr oldval} {repr s1} {repr s2}"
    else
      let l := Lbl.loop ps.aloop
      pure (rmwLoopLines ty.bits op fl l, { ps with aloop := ps.aloop + 1 })
  | .atomicCasLoop ty fl addr expect replace oldval scratch =>
    if addr != .x 25 || expect != .x 26 || replace != .x 28 || oldval != .x 27
        || scratch != .x 24 then
      throw s!"atomic_cas_loop with unexpected fixed registers {repr addr} {repr expect} \
        {repr replace} {repr oldval} {repr scratch}"
    else
      pure (casLoopLines ty.bits fl (.loop ps.aloop) (.loop (ps.aloop + 1)),
        { ps with aloop := ps.aloop + 2 })
  -- `emit.rs` `ElfTlsGetAddr`: the TLSDESC sequence (the resolver returns the variable's
  -- offset from the thread pointer in x0), then the thread pointer is added
  | .elfTlsGetAddr sym rd tmp =>
    if rd != .x 0 || tmp == .x 0 then
      throw s!"elf_tls_get_addr with unexpected registers {repr rd} {repr tmp}"
    else
      pure ([.ins (.adrpTlsDesc (.x 0) sym), .ins (.ldrTlsDescLo12 tmp (.x 0) sym),
             .ins (.addTlsDescLo12 (.x 0) (.x 0) sym), .ins (.blrTlsDesc tmp sym),
             .ins (.mrsTpidrEl0 tmp), .ins (.aluRRR .add true (.x 0) (.x 0) tmp)], ps)
where
  /-- `LoadAddr` with an immediate offset (`emit.rs`). -/
  addOff (rd rn : Reg) (off : Int) : List Line :=
    if off == 0 then
      if rn == rd then [] else [.ins (.mov true rd rn)]
    else if off > 0 then [.ins (.aluImm12 .add true rd rn ⟨off.toNat, false⟩)]
    else [.ins (.aluImm12 .sub true rd rn ⟨(-off).toNat, false⟩)]

/-- Prologue and epilogue (frame size a multiple of 16). -/
def prologueLines (size : Nat) : List Line :=
  [.ins (.stp Reg.fp Reg.lr (.spPreIndexed (-16))), .ins (.mov true Reg.fp .sp)] ++
  (if size == 0 then []
   else match Imm12.ofNat? size with
     | some i => [.ins (.aluImm12 .sub true .sp .sp i)]
     | none => loadConst64 (.x 16) size ++ [.ins (.aluRRRExtend .sub true .sp .sp (.x 16) .uxtx)])

/-- The epilogue frees the frame by adjusting `sp` (as the prologue allocated it; `x16` holds
large sizes), then pops fp/lr and returns. It does not read `fp`: the body keeps `sp`
(`FrameKeep`), which is what the register-level proof tracks. -/
def epilogueLines (size : Nat) : List Line :=
  (if size == 0 then []
   else match Imm12.ofNat? size with
     | some i => [.ins (.aluImm12 .add true .sp .sp i)]
     | none => loadConst64 (.x 16) size ++ [.ins (.aluRRRExtend .add true .sp .sp (.x 16) .uxtx)]) ++
  [.ins (.ldp Reg.fp Reg.lr (.spPostIndexed 16)), .ins .ret]

/-- A trap site: byte offset from the function start and trap code. -/
structure TrapSite where
  offset : Nat
  code : Clif.TrapCode
  deriving DecidableEq, Repr, Inhabited

/-- A function's final code: the line list, its size in bytes and trap table. -/
structure FnAsm where
  name : String
  /-- Index of the function in its file (local label names). -/
  k : Nat
  lines : Array Line
  size : Nat
  traps : List TrapSite
  deriving Inhabited

/-- The target of a conditional branch. -/
def Insn.condTarget? : Insn → Option Lbl
  | .bcond c t => if c == .al || c == .nv then none else some t
  | .cbz _ _ _ t | .tbz _ _ _ t => some t
  | _ => none

/-- The conditional branch with the opposite condition, to `target`. -/
def Insn.invertTo (target : Lbl) : Insn → Insn
  | .bcond c _ => .bcond c.invert target
  | .cbz nz w r _ => .cbz (!nz) w r target
  | .tbz nz r bit _ => .tbz (!nz) r bit target
  | i => i

/-- Branches to the next block fall through (as Cranelift's `MachBuffer` does): `b L` right
before `L:` is dropped, and `b.c T; b E; T:` becomes `b.!c E; T:`. -/
def fallthrough (lines : Array Line) : Array Line := Id.run do
  let mut out : Array Line := #[]
  let mut i := 0
  for _ in [0:lines.size] do
    if i ≥ lines.size then break
    match lines[i]!, lines[i + 1]?, lines[i + 2]? with
    | .ins c none, some (.ins (.b e) none), some (.label l) =>
      if c.condTarget? == some l then
        out := out.push (.ins (c.invertTo e) none)
        i := i + 2
        continue
    | _, _, _ => pure ()
    match lines[i]!, lines[i + 1]? with
    | .ins (.b x) none, some (.label l) =>
      if x == l then
        i := i + 1
        continue
    | _, _ => pure ()
    out := out.push lines[i]!
    i := i + 1
  return out

/-- Expand an allocated function (`k` = its index in the file) into its final line list,
with byte offsets of the trap sites. -/
def emitFunc (k : Nat) (af : AFunc) : Except String FnAsm := do
  let c : FnCtx := { k, slotBase := af.slotBase }
  let mut ps : PState := {}
  let mut lines : Array Line := #[]
  for (l, code) in af.blocks do
    lines := lines.push (.label (.block l))
    for i in code do
      match i with
      | .prologue => if af.frame then lines := lines ++ (prologueLines af.frameSize).toArray
      | .epilogueRet =>
        lines := lines ++ (if af.frame then (epilogueLines af.frameSize).toArray else #[.ins .ret])
      | .inst m =>
        let (ls, ps') ← m.lines c ps
        ps := ps'
        lines := lines ++ ls.toArray
  lines := fallthrough lines
  -- deferred traps (Cranelift emits them after the body)
  for (l, code) in ps.traps do
    lines := lines.push (.label l)
    lines := lines.push (.ins (.udf 0xc11f) (some code))
  let mut off := 0
  let mut traps : Array TrapSite := #[]
  for ln in lines do
    if let .ins _ (some code) := ln then traps := traps.push ⟨off, code⟩
    off := off + ln.size
  pure { name := af.name, k, lines, size := off, traps := traps.toList }

/-! ## Assembly text (GNU/LLVM syntax) -/

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

def ALUOp.rrr : ALUOp → String
  | .add => "add" | .sub => "sub" | .orr => "orr" | .orrNot => "orn" | .and => "and"
  | .andS => "ands" | .andNot => "bic" | .eor => "eor" | .eorNot => "eon" | .addS => "adds"
  | .subS => "subs" | .sMulH => "smulh" | .uMulH => "umulh" | .sDiv => "sdiv"
  | .uDiv => "udiv" | .extr => "rorv" | .lsr => "lsrv" | .asr => "asrv" | .lsl => "lslv"
  | .adc => "adc" | .adcS => "adcs" | .sbc => "sbc" | .sbcS => "sbcs"

def ALUOp3.asm : ALUOp3 → String
  | .mAdd => "madd" | .mSub => "msub" | .uMAddL => "umaddl" | .sMAddL => "smaddl"

/-- Mnemonic at width `is64`: `Rev32` at `Size32` is Cranelift's opcode `0b000010` with
`sf = 0` (`emit.rs:971`), i.e. `rev wd, wn` (A64 has no 32-bit `rev32`). -/
def BitOp.asm (is64 : Bool) : BitOp → String
  | .rbit => "rbit" | .clz => "clz" | .cls => "cls" | .rev16 => "rev16"
  | .rev32 => if is64 then "rev32" else "rev"
  | .rev64 => "rev"

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

/-- The destination lane letter of `uaddlv` (twice the source lane width). -/
def VectorSize.wideLane : VectorSize → String
  | .size8x8 | .size8x16 => "h" | .size16x4 | .size16x8 => "s"
  | .size32x2 | .size32x4 | .size64x2 => "d"

def symOff (sym : String) (off : Int) : String :=
  if off == 0 then sym else if off > 0 then s!"{sym}+{off}" else s!"{sym}{off}"

/-- One instruction as assembly text (`k` = function index, for label names). -/
def Insn.asm (k : Nat) : Insn → String
  | .aluRRR op w rd rn rm => s!"{op.rrr} {rd.gpr w}, {rn.gpr w}, {rm.gpr w}"
  | .aluRRRR op w rd rn rm ra =>
    match op with
    | .mAdd | .mSub => s!"{op.asm} {rd.gpr w}, {rn.gpr w}, {rm.gpr w}, {ra.gpr w}"
    | .uMAddL | .sMAddL => s!"{op.asm} {rd.gpr}, {rn.gpr false}, {rm.gpr false}, {ra.gpr}"
  | .aluImm12 op w rd rn i =>
    let sh := if i.shift12 then ", lsl #12" else ""
    s!"{op.rrr} {rd.gpr w}, {rn.gpr w}, #{i.bits}{sh}"
  | .logicImm op w rd rn v => s!"{op.rrr} {rd.gpr w}, {rn.gpr w}, #{hex v}"
  | .shiftImm op w rd rn amt => s!"{op.asm} {rd.gpr w}, {rn.gpr w}, #{amt}"
  | .aluRRRShift op w rd rn rm sh =>
    s!"{op.rrr} {rd.gpr w}, {rn.gpr w}, {rm.gpr w}, {sh.op.asm} #{sh.amt}"
  | .extr w rd rn rm lsb => s!"extr {rd.gpr w}, {rn.gpr w}, {rm.gpr w}, #{lsb}"
  | .aluRRRExtend op w rd rn rm e =>
    s!"{op.rrr} {rd.gpr w}, {rn.gpr w}, {rm.gpr (e.is64 && w)}, {e.asm}"
  | .bitRR op w rd rn => s!"{op.asm w} {rd.gpr w}, {rn.gpr w}"
  | .load op rt m =>
    let (mn, r) := op.asm rt m.isUnscaled
    s!"{mn} {r}, {m.asm op.bytes}"
  | .store op rt m =>
    let (mn, r) := op.asm rt m.isUnscaled
    s!"{mn} {r}, {m.asm op.bytes}"
  | .ldp rt rt2 m => s!"ldp {rt.gpr}, {rt2.gpr}, {m.asm 8}"
  | .stp rt rt2 m => s!"stp {rt.gpr}, {rt2.gpr}, {m.asm 8}"
  | .mov w rd rm => s!"mov {rd.gpr w}, {rm.gpr w}"
  | .movWide op w rd i =>
    s!"{if op == .movZ then "movz" else "movn"} {rd.gpr w}, #{hex i.bits}, lsl #{16 * i.shift}"
  | .movk w rd i => s!"movk {rd.gpr w}, #{hex i.bits}, lsl #{16 * i.shift}"
  | .bfm op w rd rn immr imms =>
    s!"{if op == .sBfm then "sbfm" else "ubfm"} {rd.gpr w}, {rn.gpr w}, #{immr}, #{imms}"
  | .cset rd c => s!"cset {rd.gpr}, {c.asm}"
  | .csel rd rn rm c => s!"csel {rd.gpr}, {rn.gpr}, {rm.gpr}, {c.asm}"
  | .ccmp w rn rm f c => s!"ccmp {rn.gpr w}, {rm.gpr w}, #{f.bits}, {c.asm}"
  | .ccmpImm w rn i f c => s!"ccmp {rn.gpr w}, #{i}, #{f.bits}, {c.asm}"
  | .fmovToFp s rd rn => s!"fmov {s.fpreg rd.vnum}, {rn.gpr (s == .size64)}"
  | .umov s rd rn idx => s!"umov {rd.gpr (s == .size64)}, v{rn.vnum}.{s.fpreg ""}[{idx}]"
  | .cnt s rd rn => s!"cnt v{rd.vnum}.{s.arr}, v{rn.vnum}.{s.arr}"
  | .vecLanes op s rd rn =>
    if op == .addv then s!"addv {s.lane}{rd.vnum}, v{rn.vnum}.{s.arr}"
    else s!"uaddlv {s.wideLane}{rd.vnum}, v{rn.vnum}.{s.arr}"
  | .addp s rd rn rm => s!"addp v{rd.vnum}.{s.arr}, v{rn.vnum}.{s.arr}, v{rm.vnum}.{s.arr}"
  | .b t => s!"b {t.name k}"
  | .bcond c t => s!"b.{c.asm} {t.name k}"
  | .cbz nz w rt t => s!"{if nz then "cbnz" else "cbz"} {rt.gpr w}, {t.name k}"
  | .tbz nz rt bit t => s!"{if nz then "tbnz" else "tbz"} {rt.gpr}, #{bit}, {t.name k}"
  | .bl sym => s!"bl {sym}"
  | .blr rn => s!"blr {rn.gpr}"
  | .br rn => s!"br {rn.gpr}"
  | .ret => "ret"
  | .udf i => s!"udf #{hex i}"
  | .adr rd t => s!"adr {rd.gpr}, {t.name k}"
  | .adrpGot rd sym => s!"adrp {rd.gpr}, :got:{sym}"
  | .ldrGotLo12 rd rn sym => s!"ldr {rd.gpr}, [{rn.gpr}, :got_lo12:{sym}]"
  | .adrp rd sym off => s!"adrp {rd.gpr}, {symOff sym off}"
  | .addLo12 rd rn sym off => s!"add {rd.gpr}, {rn.gpr}, :lo12:{symOff sym off}"
  | .ldar bits rt rn => s!"ldar{sizeSfx bits} {rt.gpr (bits == 64)}, [{rn.gpr}]"
  | .stlr bits rt rn => s!"stlr{sizeSfx bits} {rt.gpr (bits == 64)}, [{rn.gpr}]"
  | .ldaxr bits rt rn => s!"ldaxr{sizeSfx bits} {rt.gpr (bits == 64)}, [{rn.gpr}]"
  | .stlxr bits rs rt rn =>
    s!"stlxr{sizeSfx bits} {rs.gpr false}, {rt.gpr (bits == 64)}, [{rn.gpr}]"
  | .dmbish => "dmb ish"
  | .csetm rd c => s!"csetm {rd.gpr}, {c.asm}"
  | .adrpTlsDesc rd sym => s!"adrp {rd.gpr}, :tlsdesc:{sym}"
  | .ldrTlsDescLo12 rt rn sym => s!"ldr {rt.gpr}, [{rn.gpr}, :tlsdesc_lo12:{sym}]"
  | .addTlsDescLo12 rd rn sym => s!"add {rd.gpr}, {rn.gpr}, :tlsdesc_lo12:{sym}"
  | .blrTlsDesc rn sym => s!".tlsdesccall {sym}\n  blr {rn.gpr}"
  | .mrsTpidrEl0 rt => s!"mrs {rt.gpr}, tpidr_el0"
where
  /-- The `b`/`h`/`` size suffix of the exclusive and acquire-release loads/stores. -/
  sizeSfx : Nat → String
    | 8 => "b" | 16 => "h" | _ => ""

/-- Assembly text of a function. Every line is 4 bytes, so offsets are computed here;
`.ifne . - f - N / .error` guards make `llvm-mc` reject the file if a trap offset or the
function size differ from the assembler's. -/
def FnAsm.text (f : FnAsm) : String := Id.run do
  let n := f.name
  let mut out : Array String := #[s!"  .globl {n}", s!"  .type {n}, %function", "  .p2align 2", s!"{n}:"]
  let mut off := 0
  for ln in f.lines do
    match ln with
    | .ins i tr =>
      if tr.isSome then
        out := out.push s!"  .ifne . - {n} - {off}\n  .error \"trap offset mismatch\"\n  .endif"
      out := out.push s!"  {i.asm f.k}"
    | .word t b => out := out.push s!"  .word {t.name f.k} - {b.name f.k}"
    | .label l => out := out.push s!"{l.name f.k}:"
    off := off + ln.size
  out := out ++ #[s!"  .ifne . - {n} - {off}\n  .error \"function size mismatch\"\n  .endif",
                  s!"  .size {n}, . - {n}"]
  return "\n".intercalate out.toList ++ "\n"

end Backend
