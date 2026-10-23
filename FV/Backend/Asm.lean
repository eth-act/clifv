import FV.Backend.StackAlloc
import Std.Data.HashMap
import Std.Data.HashSet

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
  /-- The instruction after the next one (`pc + 8`): the target of the inverted short branch of
  a relaxed branch (`relaxLine`); never defined by a label line. -/
  | skip
  -- `BEq` is the lawful one from `DecidableEq` (the layout proof uses `Std.HashMap` lemmas)
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Assembly name of a label of function `k` (its index in the file). -/
def Lbl.name (k : Nat) : Lbl → String
  | .block l => s!".L{k}_b{l}"
  | .trap n => s!".L{k}_t{n}"
  | .jt n => s!".L{k}_jt{n}"
  | .loop n => s!".L{k}_a{n}"
  | .skip => ".+8"

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
  /-- `fmov sd, sn` / `fmov dd, dn` (FMOV (register); Cranelift `FpuMove32`/`FpuMove64`). -/
  | fpuMove (size : ScalarSize) (rd rn : Reg)
  /-- `mov vd.16b, vn.16b` (ORR (vector, register) with `Rm = Rn`; Cranelift `FpuMove128`, the
  register move of the float class). -/
  | fpuMove128 (rd rn : Reg)
  /-- `fabs/fneg/fsqrt sd, sn` / `… dd, dn`, `fcvt dd, sn` (`cvt32To64`, `size` 32) and
  `fcvt sd, dn` (`cvt64To32`, `size` 64) (Cranelift `FpuRR`). -/
  | fpuRR (op : FPUOp1) (size : ScalarSize) (rd rn : Reg)
  /-- `fadd/fsub/fmul/fdiv/fmax/fmin sd, sn, sm` / `… dd, dn, dm` (Cranelift `FpuRRR`). -/
  | fpuRRR (op : FPUOp2) (size : ScalarSize) (rd rn rm : Reg)
  /-- `fmadd/fmsub/fnmadd/fnmsub sd, sn, sm, sa` / `… dd, dn, dm, da` (Cranelift `FpuRRRR`). -/
  | fpuRRRR (op : FPUOp3) (size : ScalarSize) (rd rn rm ra : Reg)
  /-- `fcmp sn, sm` / `fcmp dn, dm` (Cranelift `FpuCmp`; writes NZCV). -/
  | fpuCmp (size : ScalarSize) (rn rm : Reg)
  /-- `frintm/frintp/frintz/frintn sd, sn` / `… dd, dn` (Cranelift `FpuRound`). -/
  | fpuRound (op : FpuRoundMode) (rd rn : Reg)
  /-- `fcvtzs/fcvtzu wd/xd, sn/dn` (Cranelift `FpuToInt`). -/
  | fpuToInt (op : FpuToIntOp) (rd rn : Reg)
  /-- `scvtf/ucvtf sd/dd, wn/xn` (Cranelift `IntToFpu`). -/
  | intToFpu (op : IntToFpuOp) (rd rn : Reg)
  /-- `fcsel sd, sn, sm, cond` / `… dd, dn, dm, cond` (Cranelift `FpuCSel32/64`). -/
  | fpuCSel (size : ScalarSize) (rd rn rm : Reg) (c : Cond)
  /-- `fmov sd/dd, #imm` with the 8-bit encoded immediate `imm8` (`VFPExpandImm`; Cranelift
  `FpuMoveFPImm`, `ASIMDFPModImm::enc_bits`). -/
  | fpuMoveFPImm (size : ScalarSize) (rd : Reg) (imm8 : Nat)
  /-- `movi vd.<T>, #imm8` for 8-, 16- and 32-bit lanes, `lsl #0` (Cranelift `VecDupImm` without
  shift or inversion; `movi vd.2s, #0` is its zero `f32const`/`f64const`). -/
  | movi (size : VectorSize) (rd : Reg) (imm8 : Nat)
  /-- Single-register SIMD&FP load `ldr/ldur st/dt, m` (`size` 32/64; `m` a final mode;
  Cranelift `FpuLoad32/64`). The 128-bit load is `load .fpuLoad128`. -/
  | fpuLoad (size : ScalarSize) (rt : Reg) (m : AMode)
  /-- Single-register SIMD&FP store `str/stur st/dt, m` (Cranelift `FpuStore32/64`). -/
  | fpuStore (size : ScalarSize) (rt : Reg) (m : AMode)
  /-- `ldp st/dt/qt, st2/dt2/qt2, m` (`m` = `spPreIndexed`/`spPostIndexed`, byte offset;
  Cranelift `FpuLoadP64/128`). -/
  | fpuLoadP (size : ScalarSize) (rt rt2 : Reg) (m : AMode)
  /-- `stp st/dt/qt, st2/dt2/qt2, m` (Cranelift `FpuStoreP64/128`). -/
  | fpuStoreP (size : ScalarSize) (rt rt2 : Reg) (m : AMode)
  /-- `ldr st/dt/qt, target` (LDR (literal, SIMD&FP), ±1 MiB; Cranelift `FpuLoad32/64/128` with
  `AMode::Label`, the constant pool). -/
  | fpuLoadLit (size : ScalarSize) (rt : Reg) (target : Lbl)
  deriving DecidableEq, Repr, Inhabited, BEq

/-- One element of a function's code: an instruction (4 bytes, optionally a trap site), a
jump-table word `target - base` (4 bytes of data), or a label (0 bytes). -/
inductive Line where
  | ins (i : Insn) (trap : Option Clif.TrapCode := none)
  | word (target base : Lbl)
  | label (l : Lbl)
  deriving Repr, Inhabited, DecidableEq

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
  -- `emit.rs` `FpuLoad32/64`, `FpuStore32/64` (`mem_finalize` as for the integer accesses),
  -- `FpuCSel32/64`, `FpuMoveFPImm` (`enc_bits` of the immediate)
  | .fpuLoad s rd mem fl =>
    let (pre, mem) ← memFinalize c mem s.bytes
    pure (pre ++ [.ins (.fpuLoad s rd mem) fl.trapCode], ps)
  | .fpuStore s rd mem fl =>
    let (pre, mem) ← memFinalize c mem s.bytes
    pure (pre ++ [.ins (.fpuStore s rd mem) fl.trapCode], ps)
  | .fpuCSel s rd rn rm cond => one (.fpuCSel s rd rn rm cond)
  | .fpuMoveFPImm rd imm s => one (.fpuMoveFPImm s rd imm.imm.toNat)
  -- `emit.rs` `VecDupImm`: the plain `movi vd.<T>, #imm8` (no inversion, no shift, not the
  -- 64-bit byte mask); the other forms are not expanded
  | .vecDupImm rd imm invert s =>
    if invert || imm.shift != 0 || imm.shiftOnes || imm.is64 then
      throw s!"VecDupImm {repr imm} invert={invert}"
    else one (.movi s rd imm.imm.toNat)
  -- S11f: `emit.rs` `FpuRR`, `FpuRRR`, `FpuRRRR`, `FpuCmp`, `FpuRound`, `FpuToInt`, `IntToFpu`:
  -- one instruction each
  | .fpuRR op s rd rn => one (.fpuRR op s rd rn)
  | .fpuRRR op s rd rn rm => one (.fpuRRR op s rd rn rm)
  | .fpuRRRR op s rd rn rm ra => one (.fpuRRRR op s rd rn rm ra)
  | .fpuCmp s rn rm => one (.fpuCmp s rn rm)
  | .fpuRound op rd rn => one (.fpuRound op rd rn)
  | .fpuToInt op rd rn => one (.fpuToInt op rd rn)
  | .intToFpu op rd rn => one (.intToFpu op rd rn)
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
  /-- The block labels `MachBuffer` aliased, with the block label each resolves to (the
  landing pads of the LSDA resolve through them, as `resolve_label_offset`). -/
  alias : List (Label × Label) := []
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

/-! ## Emission order and branch simplification (Cranelift's `MachBuffer`)

Cranelift emits a function's blocks in lowering order with the cold ones moved after all others
(`machinst/vcode.rs:759-770`; `AFunc.cold`, `emitOrder`). Its `MachBuffer` simplifies the
branches at the tail of the buffer whenever a label is bound (`machinst/buffer.rs:726-748`) and
once after the last block (`vcode.rs:1130-1132`), `optimize_branches` (`buffer.rs:999-1271`),
on the branches registered with `add_uncond_branch`/`add_cond_branch` (`aarch64/inst/emit.rs`
`Jump`, `CondBr`, `TestBitAndBranch`, and the `Jump` after a call with `try_call_info`; not
`TrapIf`, `JTSequence`'s `b.hs` or the LL/SC loops' branches), repeating until none applies:

1. a branch whose target resolves to the current offset is removed (`buffer.rs:1057`);
2. the labels bound at the start of a last `b X` become aliases of `X` unless `X` resolves
   there (`buffer.rs:1170-1196`): references to them resolve to `X`'s offset;
3. a `b` right after another `b`, with no label at it, is removed (`buffer.rs:1207-1214`);
4. a `b E` right after a conditional branch to the current offset is removed and the
   conditional branch inverted to `E` (`buffer.rs:1222-1257`);

with no change once more than `LABEL_LIST_THRESHOLD` = 100 labels are at a branch
(`buffer.rs:1041`). Label references resolve through the aliases at the end
(`resolve_label_offset`, `buffer.rs:766`); deferred traps follow the body, emitted after
`latest_branches` is cleared (`buffer.rs:1378`).

`machBuf` emulates this on the line list (aliased labels keep their zero-size line but are
no labels of the tail any more). The emitter keeps the result only if it splits into the
blocks' segments (label, unchanged body, simplified last instruction) that `segsOk` accepts;
otherwise the same with only block labels aliased (`machBuf`'s `allLabels := false`), otherwise
the unsimplified lines. -/

/-- The lines of one `AInst`. -/
def ainstLines (c : FnCtx) (af : AFunc) : AInst → PState → Except String (List Line × PState)
  | .prologue, ps => pure (if af.frame then prologueLines af.frameSize else [], ps)
  | .epilogueRet, ps => pure (if af.frame then epilogueLines af.frameSize else [.ins .ret], ps)
  | .inst m, ps => m.lines c ps

/-- The lines of a block's code. -/
def codeLinesE (c : FnCtx) (af : AFunc) : List AInst → PState → Except String (List Line × PState)
  | [], ps => pure ([], ps)
  | a :: as, ps => do
    let (l1, ps1) ← ainstLines c af a ps
    let (l2, ps2) ← codeLinesE c af as ps1
    pure (l1 ++ l2, ps2)

/-- Cranelift's emission order (`vcode.rs:759-770`): the blocks (with their indices) in
lowering order, the cold ones (`AFunc.cold`) after all others; the entry block stays first. -/
def emitOrder (af : AFunc) : List ((Label × Array AInst) × Nat) :=
  let cold (x : (Label × Array AInst) × Nat) : Bool := x.2 != 0 && af.cold[x.2]?.getD false
  af.blocks.toList.zipIdx.filter (!cold ·) ++ af.blocks.toList.zipIdx.filter cold

/-- A block in emission order before branch simplification: its index and label, the lines of
its code but the last instruction (`body`) and the last instruction's lines (`term`). -/
structure Seg where
  idx : Nat
  label : Label
  body : List Line
  term : List Line
  deriving Inhabited

/-- The segments of the blocks `bs`, emitted from state `ps`. -/
def segsOf (c : FnCtx) (af : AFunc) :
    List ((Label × Array AInst) × Nat) → PState → Except String (List Seg × PState)
  | [], ps => pure ([], ps)
  | ((l, code), i) :: bs, ps => do
    let (body, ps1) ← codeLinesE c af code.toList.dropLast ps
    let (term, ps2) ← codeLinesE c af code.toList.getLast?.toList ps1
    let (ss, ps3) ← segsOf c af bs ps2
    pure (⟨i, l, body, term⟩ :: ss, ps3)

/-- The lines of the segments `ss`, block `s` ending in the lines `o` (paired in order). -/
def segLines : List Seg → List (List Line) → List Line
  | s :: ss, o :: os => .label (.block s.label) :: (s.body ++ o) ++ segLines ss os
  | _, _ => []

/-- The label of a line. -/
def Line.label? : Line → Option Lbl
  | .label l => some l
  | _ => none

/-- Replace a branch's target. -/
def Insn.setTarget (t : Lbl) : Insn → Insn
  | .b _ => .b t
  | .bcond c _ => .bcond c t
  | .cbz nz w r _ => .cbz nz w r t
  | .tbz nz r bit _ => .tbz nz r bit t
  | i => i

/-- The label a line refers to as a branch target or jump-table entry (not `adr`/literal
loads, whose labels are never bound at a branch). -/
def Line.target? : Line → Option Lbl
  | .ins (.b t) _ | .ins (.bcond _ t) _ | .ins (.cbz _ _ _ t) _ | .ins (.tbz _ _ _ t) _ => some t
  | .word t _ => some t
  | _ => none

/-- Resolve the line's target through `f`. -/
def Line.relabel (f : Lbl → Lbl) : Line → Line
  | .ins i tc => match Line.target? (.ins i tc) with
    | some t => .ins (i.setTarget (f t)) tc
    | none => .ins i tc
  | .word t b => .word (f t) b
  | l => l

/-- A branch `add_uncond_branch` registers: `b` to a block label (`Jump`, and the jumps of
`CondBr`, `TestBitAndBranch` and of a call with `try_call_info`). -/
def Line.ubr? : Line → Option Lbl
  | .ins (.b (.block l)) none => some (.block l)
  | _ => none

/-- A branch `add_cond_branch` registers: a conditional branch to a block label (`CondBr`,
`TestBitAndBranch`; `JTSequence`'s `b.hs` is always followed by code). -/
def Line.cbr? : Line → Option Lbl
  | .ins c none => match c.condTarget? with
    | some (.block l) => some (.block l)
    | _ => none
  | _ => none

/-- `MachBuffer`'s state over the line list: the lines so far and the label aliases. -/
structure MBuf where
  out : Array Line := #[]
  alias : Std.HashMap Lbl Lbl := {}
  deriving Inhabited

/-- Resolve a label through the aliases (`resolve_label_offset`; aliases are acyclic). -/
def MBuf.res (m : MBuf) (l : Lbl) : Lbl := Id.run do
  let mut l := l
  for _ in [0:m.alias.size + 1] do
    match m.alias[l]? with
    | some l' => l := l'
    | none => break
  return l

/-- Is line `ln` a bound label (a label line whose label is no alias)? -/
def MBuf.bound (m : MBuf) (ln : Line) : Option Lbl :=
  match ln with
  | .label l => if m.alias.contains l then none else some l
  | _ => none

/-- The index of the last line before `n` that is not a label line. -/
def lastCode (out : Array Line) : Nat → Option Nat
  | 0 => none
  | n + 1 => match out[n]? with
    | some (.label _) => lastCode out n
    | some _ => some n
    | none => none

/-- The bound labels among the lines `out[i, j)`. -/
def MBuf.boundIn (m : MBuf) (i j : Nat) : List Lbl :=
  (m.out.extract i j).toList.filterMap m.bound

/-- One round of `optimize_branches` (`buffer.rs:1016-1262`); `none`: no rule applies.
`allLabels`: alias every label at a `b`, else only block labels. -/
def MBuf.step (allLabels : Bool) (m : MBuf) : Option MBuf := do
  let k ← lastCode m.out m.out.size
  let ln := m.out[k]!
  let t ← (ln.ubr?).orElse fun _ => ln.cbr?
  let tail := m.boundIn (k + 1) m.out.size
  let p := lastCode m.out k
  let atBr := m.boundIn ((p.map (· + 1)).getD 0) k
  if atBr.length > 100 then none
  let rt := m.res t
  if tail.contains rt then return { m with out := m.out.eraseIdx! k }
  if ln.ubr?.isSome then
    if atBr.contains rt then none
    let als := if allLabels then atBr else atBr.filter (· matches .block _)
    if !als.isEmpty then
      return { m with alias := als.foldl (fun a l => a.insert l t) m.alias }
    if !atBr.isEmpty then none
    let p ← p
    if m.out[p]!.ubr?.isSome then return { m with out := m.out.eraseIdx! k }
    let ct ← m.out[p]!.cbr?
    if !tail.contains (m.res ct) then none
    match m.out[p]! with
    | .ins c tc => return { m with out := (m.out.eraseIdx! k).set! p (.ins (c.invertTo t) tc) }
    | _ => none
  none

/-- `optimize_branches`: the rounds until none applies (each removes a line or aliases a
label). -/
def MBuf.optimize (allLabels : Bool) (m : MBuf) : MBuf := Id.run do
  let mut m := m
  for _ in [0:m.out.size + m.out.size + 1] do
    match m.step allLabels with
    | some m' => m := m'
    | none => break
  return m

/-- `MachBuffer` on the lines `ls` (optimizing at every label and at the end), then the
references resolved; the block-label aliases. -/
def machBuf (allLabels : Bool) (ls : List Line) : List Line × List (Label × Label) :=
  let m := ls.foldl (fun m ln =>
    let m := { m with out := m.out.push ln }
    if ln matches .label _ then m.optimize allLabels else m) ({} : MBuf)
  let m := m.optimize allLabels
  (m.out.toList.map (Line.relabel m.res),
    m.alias.toList.filterMap fun
      | (.block l, _) => match m.res (.block l) with
        | .block x => some (l, x)
        | _ => none
      | _ => none)

/-- Split simplified lines into the segments' final last-instruction lines: each segment's
label line, its unchanged body, then the lines up to the next block label line. -/
def splitSegs : List Seg → List Line → Option (List (List Line))
  | [], [] => some []
  | [], _ :: _ => none
  | s :: ss, .label (.block l) :: rest =>
    if l != s.label then none
    else if rest.take s.body.length != s.body then none
    else
      let r := rest.drop s.body.length
      let o := r.takeWhile (fun ln => !(ln matches .label (.block _)))
      (splitSegs ss (r.drop o.length)).map (o :: ·)
  | _ :: _, _ => none

/-- The block label `s` forwards to: a block other than the entry whose code is a single
`jump` (its label resolves to the jump's target). -/
def AFunc.fwd? (af : AFunc) (s : Label) : Option Label :=
  match af.blocks.toList.zipIdx.find? (·.1.1 == s) with
  | some ((_, code), i) => if i == 0 then none else match code.toList with
    | [.inst (.jump x)] => some x
    | _ => none
  | none => none

/-- The first line defining each block label of `L`. -/
def blockLabelIdx (L : List Line) : Std.HashMap Label Nat :=
  L.zipIdx.foldr (fun (ln, j) m => match ln with
    | .label (.block l) => m.insert l j
    | _ => m) {}

/-- Line `j` of `L` represents block `s` (`fuel` bounds the search): the label lines from `j`
on include `s`'s own, or `s` forwards to a block line `j` represents. -/
def repAt (af : AFunc) (L : Array Line) : Nat → Label → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, s, j =>
    (match L[j]? with
     | some (.label (.block l)) => l == s || repAt af L fuel s (j + 1)
     | some (.label _) => repAt af L fuel s (j + 1)
     | _ => false) ||
    (match af.fwd? s with
     | some x => repAt af L fuel x j
     | none => false)

/-- The checks of `segsOk` for one segment: the final lines `o` of the block's last
instruction `a` (lines `t`) reach the successors `a` names; `rep s j`: line `j` represents
block `s`, `nxt`: the line after `o`. A branch to a block label `l'` reaches `s` if `l'`'s line
represents `s`; a removed branch falls through to `nxt`. -/
def termOk (rep : Label → Nat → Bool) (idx : Std.HashMap Label Nat) (a : Option AInst)
    (t o : List Line) (nxt : Nat) : Bool :=
  let repL (s : Label) (l' : Lbl) : Bool := match l' with
    | .block l => match idx[l]? with
      | some j => rep s j
      | none => false
    | _ => false
  -- a line kept but for a target resolved to another block label representing the old one
  let lineOk (x y : Line) : Bool :=
    x == y || match x.target?, y.target? with
      | some (.block l), some l' => y == x.relabel (fun _ => l') && repL l l'
      | _, _ => false
  let keptOk : Bool := o.length == t.length && (t.zip o).all fun (x, y) => lineOk x y
  let condOk (s1 s2 : Label) (ci : Insn) : Bool :=
    match o with
    | [.ins c none, .ins (.b e') none] =>
      (match c.condTarget? with
       | some t' => c == ci.setTarget t' && repL s1 t'
       | none => false) && repL s2 e'
    | [.ins c none] =>
      (match c.condTarget? with
       | some t' => (c == ci.setTarget t' && repL s1 t' && rep s2 nxt) ||
           (c == ci.invertTo t' && repL s2 t' && rep s1 nxt)
       | none => false)
    | [] => rep s1 nxt && rep s2 nxt
    | _ => false
  match a with
  | some (.inst (.jump x)) =>
    (match o with
     | [.ins (.b l') none] => repL x l'
     | [] => rep x nxt
     | _ => false)
  | some (.inst (.condBr tl el k)) => condOk tl el (k.insn (.block tl))
  | some (.inst (.testBitAndBranch k tl el rn bit)) =>
    condOk tl el (.tbz (k == .nz) rn bit (.block tl))
  | some (.inst (.tryCall _ ti)) =>
    (match t, o with
     | [call, _], [call', .ins (.b l') none] => call == call' && repL ti.continuation l'
     | [call, _], [call'] => call == call' && rep ti.continuation nxt
     | _, _ => false)
  | _ => keptOk

/-- `repAt` on the lines `L` with enough fuel. -/
def repOn (af : AFunc) (L : List Line) : Label → Nat → Bool :=
  repAt af L.toArray (L.length + af.blocks.size + 1)

/-- An alias `l ↦ x` whose resolution the lines `L` justify: `x`'s label line represents `l`. -/
def aliasOk (af : AFunc) (L : List Line) (a : Label × Label) : Bool :=
  match (blockLabelIdx L)[a.2]? with
  | some j => repOn af L a.1 j
  | none => false

/-- The segments `ss` ending in the lines `os` laid out as `L` (`segLines ss os`, then the
traps) are a correct simplification: entry first, every segment's final lines `termOk`. -/
def segsOk (af : AFunc) (ss : List Seg) (os : List (List Line)) (L : List Line) : Bool :=
  let idx := blockLabelIdx L
  let rep := repOn af L
  let rec go : List Seg → List (List Line) → Nat → Bool
    | s :: ss, o :: os, j =>
      let nxt := j + 1 + s.body.length + o.length
      termOk rep idx (af.blocks[s.idx]?.bind (·.2.back?)) s.term o nxt && go ss os nxt
    | [], [], _ => true
    | _, _, _ => false
  (ss.head?.map (·.idx)) == some 0 && go ss os 0

/-- An emission plan: the segments in emission order, their final last-instruction lines, the
emitter's final state (deferred traps) and the block-label aliases (each `aliasOk`). -/
structure Plan where
  segs : List Seg
  outs : List (List Line)
  ps : PState
  alias : List (Label × Label)

/-- The deferred traps' lines (Cranelift emits them after the body). -/
def trapLines (ps : PState) : List Line :=
  ps.traps.toList.flatMap fun p => [.label p.1, .ins (.udf 0xc11f) (some p.2)]

/-- The lines of a plan before branch relaxation. -/
def Plan.lines (p : Plan) : List Line := segLines p.segs p.outs ++ trapLines p.ps

/-- The `MachBuffer` simplification of the segments `ss` (`allLabels` as in `machBuf`), if it
splits into them and `segsOk` accepts it. -/
def machPlan (af : AFunc) (allLabels : Bool) (ss : List Seg) (ps : PState) : Option Plan := do
  let (L, al) := machBuf allLabels (segLines ss (ss.map (·.term)))
  let os ← splitSegs ss L
  let L' := segLines ss os ++ trapLines ps
  if segsOk af ss os L' then some ⟨ss, os, ps, al.filter (aliasOk af L')⟩ else none

/-- The emission plan of an allocated function (`k` = its index in the file): the blocks in
`emitOrder`, `MachBuffer`'s branch simplification (`machPlan`), else the unsimplified lines. -/
def emitPlan (k : Nat) (af : AFunc) : Except String Plan := do
  let (ss, ps) ← segsOf { k, slotBase := af.slotBase } af (emitOrder af) {}
  pure <| ((machPlan af true ss ps).orElse fun _ => machPlan af false ss ps).getD
    ⟨ss, ss.map (·.term), ps, []⟩

/-- The block-label aliases of the emission plan. -/
def emitAlias (k : Nat) (af : AFunc) : List (Label × Label) :=
  match emitPlan k af with
  | .ok p => p.alias
  | .error _ => []

/-- The lines of an allocated function before branch relaxation. -/
def emitPre (k : Nat) (af : AFunc) : Except String (Array Line) :=
  (·.lines.toArray) <$> emitPlan k af

/-! ## Branch relaxation

A short conditional branch (`b.cond`, `cbz`/`cbnz`: ±1 MiB; `tbz`/`tbnz`: ±32 KiB) whose label is
out of reach becomes the inverted branch over an unconditional `b` (±128 MiB):
`b.c T` ⟶ `b.!c .+8; b T` (`cbz`↔`cbnz`, `tbz`↔`tbnz`), as Cranelift's `MachBuffer` does with
veneers. The decision is per target label (`far`): every relaxable branch to a far label is
relaxed. `relaxOf` iterates layout to a fixpoint: relaxing only lengthens the code, so the set
of far labels only grows; when the fuel (more than the number of lines, hence of labels) runs
out, every relaxable branch is relaxed. With no far label the lines are unchanged. -/

/-- Byte offsets of the labels from byte offset `off` with the labels found so far in `m`. -/
def labelOffsets.go : List Line → Nat → Std.HashMap Lbl Nat → Except String (Std.HashMap Lbl Nat)
  | [], _, m => pure m
  | ln :: rest, off, m =>
    match ln with
    | .label l =>
      if m.contains l then throw s!"label {repr l} is defined twice"
      else go rest off (m.insert l off)
    | _ => go rest (off + ln.size) m

/-- Byte offsets of the labels of a line list (every label defined once, else an error). -/
def labelOffsets (lines : Array Line) : Except String (Std.HashMap Lbl Nat) :=
  labelOffsets.go lines.toList 0 {}

/-- The label operand of a PC-relative form, its reach in bytes (`-reach ≤ target - pc <
reach`) and its alignment (Arm ARM C6.2: B `imm26:'00'`, B.cond/CBZ/CBNZ `imm19:'00'`,
TBZ/TBNZ `imm14:'00'`, ADR `immhi:immlo`; C7.2 LDR (literal, SIMD&FP) `imm19:'00'`). -/
def Insn.pcRelSpec? : Insn → Option (Lbl × Int × Int)
  | .b t => some (t, 128 * 2 ^ 20, 4)
  | .bcond _ t | .cbz _ _ _ t => some (t, 2 ^ 20, 4)
  | .tbz _ _ _ t => some (t, 32 * 2 ^ 10, 4)
  | .adr _ t => some (t, 2 ^ 20, 1)
  | .fpuLoadLit _ _ t => some (t, 2 ^ 20, 4)
  | _ => none

/-- Whether the PC-relative operand of `i` at byte offset `pc` reaches byte offset `o`. -/
def Insn.reaches (i : Insn) (pc o : Nat) : Bool :=
  match i.pcRelSpec? with
  | some (_, reach, _) => decide (-reach ≤ (o : Int) - pc ∧ (o : Int) - pc < reach)
  | none => true

/-- The target of a conditional branch relaxation may rewrite: a block or trap label (the
atomic loops' and jump tables' labels are a few instructions away). -/
def Insn.relaxTarget? (i : Insn) : Option Lbl :=
  match i.condTarget? with
  | some (.block l) => some (.block l)
  | some (.trap n) => some (.trap n)
  | _ => none

/-- A relaxable line: a conditional branch (no trap code) with its relaxable target. -/
def Line.relaxable? : Line → Option (Insn × Lbl)
  | .ins c none => c.relaxTarget?.map (c, ·)
  | _ => none

/-- Relax one line: a relaxable branch to a far label becomes `b.!c .+8; b T`. -/
def relaxLine (far : Lbl → Bool) (ln : Line) : List Line :=
  match ln.relaxable? with
  | some (c, t) => if far t then [.ins (c.invertTo .skip) none, .ins (.b t) none] else [ln]
  | none => [ln]

def relaxLines (far : Lbl → Bool) (ls : List Line) : List Line := ls.flatMap (relaxLine far)

/-- `farTargets` at byte offset `pc` with the far labels found so far in `acc`. -/
def farTargets.go (m : Std.HashMap Lbl Nat) : List Line → Nat → List Lbl → List Lbl
  | [], _, acc => acc
  | ln :: rest, pc, acc =>
    let acc := match ln.relaxable? with
      | some (c, t) => match m[t]? with
        | some o => if c.reaches pc o then acc else t :: acc
        | none => acc
      | none => acc
    go m rest (pc + ln.size) acc

/-- The targets of the relaxable branches of `lines` that do not reach their label at the
offsets `lines` is laid out at (none if a label is defined twice: `layout` rejects that). -/
def farTargets (lines : List Line) : List Lbl :=
  match labelOffsets.go lines 0 {} with
  | .ok m => farTargets.go m lines 0 []
  | .error _ => []

/-- The far labels: iterate until every relaxable branch that is left reaches its label. -/
def relaxFar (pre : List Line) : Nat → Std.HashSet Lbl → Lbl → Bool
  | 0, _ => fun _ => true
  | n + 1, far =>
    match farTargets (relaxLines (far.contains ·) pre) with
    | [] => (far.contains ·)
    | ts => relaxFar pre n (far.insertMany ts)

def relaxOf (pre : List Line) : Lbl → Bool := relaxFar pre (pre.length + 1) {}

/-- Expand an allocated function (`k` = its index in the file) into its final line list
(`emitPre`, then branch relaxation), with byte offsets of the trap sites. -/
def emitFunc (k : Nat) (af : AFunc) : Except String FnAsm := do
  let pre := (← emitPre k af).toList
  let lines := (relaxLines (relaxOf pre) pre).toArray
  let mut off := 0
  let mut traps : Array TrapSite := #[]
  for ln in lines do
    if let .ins _ (some code) := ln then traps := traps.push ⟨off, code⟩
    off := off + ln.size
  pure { name := af.name, k, lines, size := off, traps := traps.toList, alias := emitAlias k af }

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

def FPUOp1.asm : FPUOp1 → String
  | .abs => "fabs" | .neg => "fneg" | .sqrt => "fsqrt" | .cvt32To64 | .cvt64To32 => "fcvt"

/-- The destination size of `fpuRR op s`: the other precision for FCVT, else `s`. -/
def FPUOp1.dstSize (op : FPUOp1) (s : ScalarSize) : ScalarSize :=
  match op with | .cvt32To64 => .size64 | .cvt64To32 => .size32 | _ => s

def FPUOp2.asm : FPUOp2 → String
  | .add => "fadd" | .sub => "fsub" | .mul => "fmul" | .div => "fdiv" | .max => "fmax"
  | .min => "fmin"

def FPUOp3.asm : FPUOp3 → String
  | .mAdd => "fmadd" | .mSub => "fmsub" | .nMAdd => "fnmadd" | .nMSub => "fnmsub"

def FpuRoundMode.asm : FpuRoundMode → String
  | .minus32 | .minus64 => "frintm" | .plus32 | .plus64 => "frintp"
  | .zero32 | .zero64 => "frintz" | .nearest32 | .nearest64 => "frintn"

/-- The operand precision of a rounding mode. -/
def FpuRoundMode.size : FpuRoundMode → ScalarSize
  | .minus32 | .plus32 | .zero32 | .nearest32 => .size32
  | .minus64 | .plus64 | .zero64 | .nearest64 => .size64

/-- `(signed, float size, 64-bit integer)` of a float → integer conversion. -/
def FpuToIntOp.parts : FpuToIntOp → Bool × ScalarSize × Bool
  | .f32ToU32 => (false, .size32, false) | .f32ToI32 => (true, .size32, false)
  | .f32ToU64 => (false, .size32, true) | .f32ToI64 => (true, .size32, true)
  | .f64ToU32 => (false, .size64, false) | .f64ToI32 => (true, .size64, false)
  | .f64ToU64 => (false, .size64, true) | .f64ToI64 => (true, .size64, true)

/-- `(signed, 64-bit integer, float size)` of an integer → float conversion. -/
def IntToFpuOp.parts : IntToFpuOp → Bool × Bool × ScalarSize
  | .u32ToF32 => (false, false, .size32) | .i32ToF32 => (true, false, .size32)
  | .u32ToF64 => (false, false, .size64) | .i32ToF64 => (true, false, .size64)
  | .u64ToF32 => (false, true, .size32) | .i64ToF32 => (true, true, .size32)
  | .u64ToF64 => (false, true, .size64) | .i64ToF64 => (true, true, .size64)

/-- The value of an 8-bit floating-point immediate (`VFPExpandImm`) as exact decimal text:
`±(16 + imm8<3:0>) · 2^(e - 4)` with `e = imm8<6> ? imm8<5:4> - 3 : imm8<5:4> + 1`, i.e.
`n / 2^k` for `k = 4 - e ∈ [0, 7]`, which is `n · 5^k / 10^k`. -/
def fpImm8Text (imm8 : Nat) : String :=
  let sign := if imm8 / 128 % 2 == 1 then "-" else ""
  let b54 := imm8 / 16 % 4
  let k := if imm8 / 64 % 2 == 1 then 7 - b54 else 3 - b54
  let num := (16 + imm8 % 16) * 5 ^ k
  let frac := toString (num % 10 ^ k)
  let frac := if k == 0 then "0" else "".pushn '0' (k - frac.length) ++ frac
  s!"{sign}{num / 10 ^ k}.{frac}"

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
  | .fpuMove s rd rn => s!"fmov {s.fpreg rd.vnum}, {s.fpreg rn.vnum}"
  | .fpuMove128 rd rn => s!"mov v{rd.vnum}.16b, v{rn.vnum}.16b"
  | .fpuRR op s rd rn => s!"{op.asm} {(op.dstSize s).fpreg rd.vnum}, {s.fpreg rn.vnum}"
  | .fpuRRR op s rd rn rm =>
    s!"{op.asm} {s.fpreg rd.vnum}, {s.fpreg rn.vnum}, {s.fpreg rm.vnum}"
  | .fpuRRRR op s rd rn rm ra =>
    s!"{op.asm} {s.fpreg rd.vnum}, {s.fpreg rn.vnum}, {s.fpreg rm.vnum}, {s.fpreg ra.vnum}"
  | .fpuCmp s rn rm => s!"fcmp {s.fpreg rn.vnum}, {s.fpreg rm.vnum}"
  | .fpuRound op rd rn => s!"{op.asm} {op.size.fpreg rd.vnum}, {op.size.fpreg rn.vnum}"
  | .fpuToInt op rd rn =>
    let (sg, fs, w) := op.parts
    s!"{if sg then "fcvtzs" else "fcvtzu"} {rd.gpr w}, {fs.fpreg rn.vnum}"
  | .intToFpu op rd rn =>
    let (sg, w, fs) := op.parts
    s!"{if sg then "scvtf" else "ucvtf"} {fs.fpreg rd.vnum}, {rn.gpr w}"
  | .fpuCSel s rd rn rm c =>
    s!"fcsel {s.fpreg rd.vnum}, {s.fpreg rn.vnum}, {s.fpreg rm.vnum}, {c.asm}"
  | .fpuMoveFPImm s rd imm8 => s!"fmov {s.fpreg rd.vnum}, #{fpImm8Text imm8}"
  | .movi s rd imm8 => s!"movi v{rd.vnum}.{s.arr}, #{imm8}"
  | .fpuLoad s rt m =>
    s!"{if m.isUnscaled then "ldur" else "ldr"} {s.fpreg rt.vnum}, {m.asm s.bytes}"
  | .fpuStore s rt m =>
    s!"{if m.isUnscaled then "stur" else "str"} {s.fpreg rt.vnum}, {m.asm s.bytes}"
  | .fpuLoadP s rt rt2 m => s!"ldp {s.fpreg rt.vnum}, {s.fpreg rt2.vnum}, {m.asm s.bytes}"
  | .fpuStoreP s rt rt2 m => s!"stp {s.fpreg rt.vnum}, {s.fpreg rt2.vnum}, {m.asm s.bytes}"
  | .fpuLoadLit s rt t => s!"ldr {s.fpreg rt.vnum}, {t.name k}"
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
