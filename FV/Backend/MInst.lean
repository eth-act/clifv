import FV.Clif
import FV.Isle

/-!
# Typed view of the aarch64 `MInst` subset (M4 backend)

The instruction selector (`FV/Backend/Isel.lean`) runs Cranelift's exported ISLE rules
(`FV/Isle`) with the generic interpreter. The rules build values of the ISLE enum `MInst`
(and of its operand types); this module gives

* the Lean operand types (`ALUOp`, `OperandSize`, `Imm12`, `ImmLogic`, `AMode`, `Cond`, ...)
  for the part of `MInst` that the emitter-subset closure (`Isle.Aarch64.Closure`) produces,
  plus the instructions the lowering driver and the ABI code add themselves
  (`Mov`, `MovK`, `LoadAddr`, `Args`, `Rets`, `Call`);
* the typed `MInst` over registers `Reg` (virtual or real);
* the interpreter's value domain `V` and the conversion `V → MInst` (`MInst.ofV`);
* Lean transcriptions of the immediate constructors of `isa/aarch64/inst/imms.rs` and
  `args.rs` (`Imm12::maybe_from_u64`, `ImmLogic::maybe_from_u64`, `MoveWideConst`, `SImm9`,
  `UImm12Scaled`, `ShiftOpShiftImm`), which both the ISLE extern helpers and the frame code
  use.

Everything is total; no `partial`.
-/

namespace Backend

open Isle

/-! ## Registers -/

inductive RegClass where
  | int | float
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

/-- A register operand: a virtual register (before stack allocation) or a real one.
`xzr` and `sp` are the two meanings of encoding 31 (Cranelift's `zero_reg` / `stack_reg`). -/
inductive Reg where
  | vreg (n : Nat) (cls : RegClass)
  | x (n : Nat)
  | xzr
  | sp
  | v (n : Nat)
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

def Reg.isVirtual : Reg → Bool
  | .vreg .. => true
  | _ => false

def Reg.fp : Reg := .x 29
def Reg.lr : Reg := .x 30

/-- `Reg::invalid_sentinel()` (`machinst/valueregs.rs:54`) = `VReg::invalid()`, the virtual
register with regalloc2's maximal index `VReg::MAX = 2^21 - 1`. Only the `nop` lowering
(`invalid_reg`) produces it; the driver drops the outputs of result-less instructions, so it
never reaches VCode. -/
def Reg.invalid : Reg := .vreg (2 ^ 21 - 1) .int

/-! ## CLIF types as seen by the ISLE rules (`Type` values) -/

/-- A Cranelift `Type`: scalar integers `I8..I128`, floats, fixed vectors and `INVALID` (the
type of an instruction without results). Only what the rules mention. -/
inductive CTy where
  | invalid
  | int (bits : Nat)
  | float (bits : Nat)
  | vec (laneBits lanes : Nat) (isFloat : Bool)
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

namespace CTy
def ofClif : Clif.Ty → CTy
  | .i8 => .int 8 | .i16 => .int 16 | .i32 => .int 32 | .i64 => .int 64 | .i128 => .int 128
/-- `Type::bits`. -/
def bits : CTy → Nat
  | .invalid => 0 | .int b => b | .float b => b | .vec lb n _ => lb * n
/-- `Type::lane_bits`. -/
def laneBits : CTy → Nat
  | .invalid => 0 | .int b => b | .float b => b | .vec lb _ _ => lb
def bytes (t : CTy) : Nat := t.bits / 8
def isInt : CTy → Bool
  | .int _ => true | _ => false
def isFloat : CTy → Bool
  | .float _ => true | _ => false
def isVector : CTy → Bool
  | .vec .. => true | _ => false
def laneCount : CTy → Nat
  | .vec _ n _ => n | .invalid => 0 | _ => 1
/-- The `$NAME` type constants of the ISLE prelude that the aarch64 rules mention. -/
def ofName? : String → Option CTy
  | "I8" => some (.int 8) | "I16" => some (.int 16) | "I32" => some (.int 32)
  | "I64" => some (.int 64) | "I128" => some (.int 128)
  | "F16" => some (.float 16) | "F32" => some (.float 32) | "F64" => some (.float 64)
  | "F128" => some (.float 128)
  | "I8X8" => some (.vec 8 8 false) | "I8X16" => some (.vec 8 16 false)
  | "I16X4" => some (.vec 16 4 false) | "I16X8" => some (.vec 16 8 false)
  | "I32X2" => some (.vec 32 2 false) | "I32X4" => some (.vec 32 4 false)
  | "I64X2" => some (.vec 64 2 false)
  | "F32X2" => some (.vec 32 2 true) | "F32X4" => some (.vec 32 4 true)
  | "F64X2" => some (.vec 64 2 true)
  | "INVALID" => some .invalid
  | _ => none
/-- Register class of a type (`Inst::rc_for_type`, single-register types only). -/
def regClass? : CTy → Option RegClass
  | .int b => if b ≤ 64 then some .int else none
  | .float _ => some .float
  | .vec .. => some .float
  | .invalid => none
end CTy

/-! ## Operand types (ISLE `inst.isle`) -/

inductive OperandSize where
  | size32 | size64
  deriving DecidableEq, Repr, Inhabited, BEq

def OperandSize.bits : OperandSize → Nat
  | .size32 => 32 | .size64 => 64

/-- `OperandSize::from_ty` / `from_bits`: 64 for 64-bit types, else 32. -/
def OperandSize.ofBits (b : Nat) : OperandSize := if b > 32 then .size64 else .size32

inductive ALUOp where
  | add | sub | orr | orrNot | and | andS | andNot | eor | eorNot | addS | subS
  | sMulH | uMulH | sDiv | uDiv | extr | lsr | asr | lsl | adc | adcS | sbc | sbcS
  deriving DecidableEq, Repr, Inhabited, BEq

inductive ALUOp3 where
  | mAdd | mSub | uMAddL | sMAddL
  deriving DecidableEq, Repr, Inhabited, BEq

inductive MoveWideOp where
  | movZ | movN
  deriving DecidableEq, Repr, Inhabited, BEq

inductive BfmOp where
  | uBfm | sBfm
  deriving DecidableEq, Repr, Inhabited, BEq

inductive BitOp where
  | rbit | clz | cls | rev16 | rev32 | rev64
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Condition codes, in the order of the ISLE `Cond` enum (= the hardware encoding). -/
inductive Cond where
  | eq | ne | hs | lo | mi | pl | vs | vc | hi | ls | ge | lt | gt | le | al | nv
  deriving DecidableEq, Repr, Inhabited, BEq

/-- `Cond::invert`. -/
def Cond.invert : Cond → Cond
  | .eq => .ne | .ne => .eq | .hs => .lo | .lo => .hs | .mi => .pl | .pl => .mi
  | .vs => .vc | .vc => .vs | .hi => .ls | .ls => .hi | .ge => .lt | .lt => .ge
  | .gt => .le | .le => .gt | .al => .nv | .nv => .al

inductive ExtendOp where
  | uxtb | uxth | uxtw | uxtx | sxtb | sxth | sxtw | sxtx
  deriving DecidableEq, Repr, Inhabited, BEq

inductive ShiftOp where
  | lsl | lsr | asr | ror
  deriving DecidableEq, Repr, Inhabited, BEq

/-- `ShiftOpAndAmt` (amount `< 64`). -/
structure ShiftOpAndAmt where
  op : ShiftOp
  amt : Nat
  deriving DecidableEq, Repr, Inhabited, BEq

/-- `Imm12`: 12 bits, optionally shifted left by 12. -/
structure Imm12 where
  bits : Nat
  shift12 : Bool
  deriving DecidableEq, Repr, Inhabited, BEq

def Imm12.value (i : Imm12) : Nat := if i.shift12 then i.bits * 4096 else i.bits

/-- `ImmLogic`: the value (as given to `maybe_from_u64`) and the operand size it was built
for. The `N:immr:imms` encoding is left to the assembler. -/
structure ImmLogic where
  value : Nat
  size : OperandSize
  deriving DecidableEq, Repr, Inhabited, BEq

/-- `MoveWideConst`: `bits << (16 * shift)`. -/
structure MoveWideConst where
  bits : Nat
  shift : Nat
  deriving DecidableEq, Repr, Inhabited, BEq

structure NZCV where
  n : Bool
  z : Bool
  c : Bool
  v : Bool
  deriving DecidableEq, Repr, Inhabited, BEq

def NZCV.bits (f : NZCV) : Nat :=
  (if f.n then 8 else 0) + (if f.z then 4 else 0) + (if f.c then 2 else 0) + (if f.v then 1 else 0)

inductive ScalarSize where
  | size8 | size16 | size32 | size64 | size128
  deriving DecidableEq, Repr, Inhabited, BEq

inductive VectorSize where
  | size8x8 | size8x16 | size16x4 | size16x8 | size32x2 | size32x4 | size64x2
  deriving DecidableEq, Repr, Inhabited, BEq

inductive VecMisc2 where
  | cnt
  deriving DecidableEq, Repr, Inhabited, BEq

inductive VecLanesOp where
  | addv | uaddlv
  deriving DecidableEq, Repr, Inhabited, BEq

inductive VecALUOp where
  | addp
  deriving DecidableEq, Repr, Inhabited, BEq

inductive TestBitAndBranchKind where
  | z | nz
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Addressing modes (`AMode`). `unsignedOffset` carries the byte offset (already scaled). -/
inductive AMode where
  | spPostIndexed (simm9 : Int)
  | spPreIndexed (simm9 : Int)
  | regReg (rn rm : Reg)
  | regScaled (rn rm : Reg)
  | regScaledExtended (rn rm : Reg) (e : ExtendOp)
  | regExtended (rn rm : Reg) (e : ExtendOp)
  | unscaled (rn : Reg) (simm9 : Int)
  | unsignedOffset (rn : Reg) (off : Nat)
  | regOffset (rn : Reg) (off : Int)
  | spOffset (off : Int)
  | fpOffset (off : Int)
  | incomingArg (off : Int)
  | slotOffset (off : Int)
  deriving DecidableEq, Repr, Inhabited, BEq

inductive CondBrKind where
  | zero (r : Reg) (size : OperandSize)
  | notZero (r : Reg) (size : OperandSize)
  | cond (c : Cond)
  deriving DecidableEq, Repr, Inhabited, BEq

/-- `CondBrKind::invert`. -/
def CondBrKind.invert : CondBrKind → CondBrKind
  | .zero r s => .notZero r s
  | .notZero r s => .zero r s
  | .cond c => .cond c.invert

abbrev Label := Nat

inductive CallDest where
  | sym (name : String)
  | reg (r : Reg)
  deriving DecidableEq, Repr, Inhabited, BEq

/-- `CallInfo`: argument registers (vreg used, real register), return registers (real
register, vreg defined). -/
structure CallInfo where
  dest : CallDest
  uses : List (Reg × Reg)
  defs : List (Reg × Reg)
  deriving DecidableEq, Repr, Inhabited, BEq

/-- A handler of a `try_call` (`TryCallHandler` without `Context`): an exception tag or the
default, with its landing pad (the label of the handler successor). -/
inductive TryHandler where
  | tag (n : Nat) (l : Label)
  | default (l : Label)
  deriving DecidableEq, Repr, Inhabited, BEq

def TryHandler.label : TryHandler → Label
  | .tag _ l | .default l => l

/-- `TryCallInfo`: the normal-return continuation and the handlers (exception-table order).
`clobberAll`: the callee's exceptional ABI restores no register (`tail`/`preserve_all`
callees, `get_regs_clobbered_by_call(_, true) = ALL_CLOBBERS`); for `system_v` the unwinder
restores the callee-saved registers, so the clobbers are the normal call's. -/
structure TryInfo where
  continuation : Label
  handlers : List TryHandler
  clobberAll : Bool := false
  deriving DecidableEq, Repr, Inhabited, BEq

inductive LoadOp where
  | uload8 | sload8 | uload16 | sload16 | uload32 | sload32 | uload64 | fpuLoad128
  deriving DecidableEq, Repr, Inhabited, BEq

inductive StoreOp where
  | store8 | store16 | store32 | store64 | fpuStore128
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Access size in bytes (`Inst::mem_type`), used by `mem_finalize`. -/
def LoadOp.bytes : LoadOp → Nat
  | .uload8 | .sload8 => 1 | .uload16 | .sload16 => 2 | .uload32 | .sload32 => 4
  | .uload64 => 8 | .fpuLoad128 => 16
def StoreOp.bytes : StoreOp → Nat
  | .store8 => 1 | .store16 => 2 | .store32 => 4 | .store64 => 8 | .fpuStore128 => 16

/-! ## Machine instructions -/

/-- The `op` of an `atomicRmwLoop` (`AtomicRMWLoopOp`; the constructor order is the generated
ISLE type's, so `VIdx.AtomicRMWLoopOp.*` indices are `all`'s indices). -/
inductive AtomicRmwLoopOp where
  | add | sub | and | nand | xor | or | smax | smin | umax | umin | xchg
  deriving DecidableEq, Repr, Inhabited

def AtomicRmwLoopOp.all : List AtomicRmwLoopOp :=
  [.add, .sub, .and, .nand, .xor, .or, .smax, .smin, .umax, .umin, .xchg]

/-- The variant name of an `AtomicRMWLoopOp` in the generated ISLE types. -/
def AtomicRmwLoopOp.name : AtomicRmwLoopOp → String
  | .add => "Add" | .sub => "Sub" | .and => "And" | .nand => "Nand" | .xor => "Eor"
  | .or => "Orr" | .smax => "Smax" | .smin => "Smin" | .umax => "Umax" | .umin => "Umin"
  | .xchg => "Xchg"

/-- The aarch64 `MInst` subset. Field order follows `inst.isle`. `args`/`rets` are Cranelift's
`Args`/`Rets` pseudo-instructions: `(vreg, real register)` pairs defined at entry / used at
return. -/
inductive MInst where
  | aluRRR (op : ALUOp) (size : OperandSize) (rd rn rm : Reg)
  | aluRRRR (op : ALUOp3) (size : OperandSize) (rd rn rm ra : Reg)
  | aluRRImm12 (op : ALUOp) (size : OperandSize) (rd rn : Reg) (imm : Imm12)
  | aluRRImmLogic (op : ALUOp) (size : OperandSize) (rd rn : Reg) (imm : ImmLogic)
  | aluRRImmShift (op : ALUOp) (size : OperandSize) (rd rn : Reg) (imm : Nat)
  | aluRRRShift (op : ALUOp) (size : OperandSize) (rd rn rm : Reg) (sh : ShiftOpAndAmt)
  | aluRRRExtend (op : ALUOp) (size : OperandSize) (rd rn rm : Reg) (e : ExtendOp)
  | bitRR (op : BitOp) (size : OperandSize) (rd rn : Reg)
  | load (op : LoadOp) (rd : Reg) (mem : AMode) (flags : Clif.MemFlags)
  | store (op : StoreOp) (rd : Reg) (mem : AMode) (flags : Clif.MemFlags)
  | mov (size : OperandSize) (rd rm : Reg)
  | movWide (op : MoveWideOp) (rd : Reg) (imm : MoveWideConst) (size : OperandSize)
  | movK (rd rn : Reg) (imm : MoveWideConst) (size : OperandSize)
  | extend (rd rn : Reg) (signed : Bool) (fromBits toBits : Nat)
  | bitfieldMove (size : OperandSize) (op : BfmOp) (rd rn : Reg) (immr imms : Nat)
  | cset (rd : Reg) (c : Cond)
  /-- `csel xd, xn, xm, cond` (always 64-bit, `emit.rs:1438`). -/
  | csel (rd rn rm : Reg) (c : Cond)
  | ccmp (size : OperandSize) (rn rm : Reg) (nzcv : NZCV) (c : Cond)
  | ccmpImm (size : OperandSize) (rn : Reg) (imm : Nat) (nzcv : NZCV) (c : Cond)
  | movToFpu (rd rn : Reg) (size : ScalarSize)
  | movFromVec (rd rn : Reg) (idx : Nat) (size : ScalarSize)
  | vecMisc (op : VecMisc2) (rd rn : Reg) (size : VectorSize)
  | vecLanes (op : VecLanesOp) (rd rn : Reg) (size : VectorSize)
  | vecRRR (op : VecALUOp) (rd rn rm : Reg) (size : VectorSize)
  | call (info : CallInfo)
  | args (defs : List (Reg × Reg))
  | rets (uses : List (Reg × Reg))
  | jump (target : Label)
  | condBr (taken notTaken : Label) (kind : CondBrKind)
  | testBitAndBranch (kind : TestBitAndBranchKind) (taken notTaken : Label) (rn : Reg) (bit : Nat)
  | trapIf (kind : CondBrKind) (code : Clif.TrapCode)
  | udf (code : Clif.TrapCode)
  | jtSequence (default : Label) (targets : List Label) (ridx rtmp1 rtmp2 : Reg)
  | loadExtNameGot (rd : Reg) (name : String)
  | loadExtNameNear (rd : Reg) (name : String) (offset : Int)
  | loadAddr (rd : Reg) (mem : AMode)
  | emitIsland (needed : Nat)
  /-- `ldar{b,h,}`: acquire load (`MInst.LoadAcquire`; the address is a register, as
  Cranelift's `load_acquire` helper passes it). -/
  | loadAcquire (ty : CTy) (rt : Reg) (rn : Reg) (flags : Clif.MemFlags)
  /-- `stlr{b,h,}`: release store (`MInst.StoreRelease`). -/
  | storeRelease (ty : CTy) (rt rn : Reg) (flags : Clif.MemFlags)
  /-- `atomic_rmw` as Cranelift's LL/SC pseudo-instruction `MInst.AtomicRMWLoop` (cg_clif's
  flags have `has_lse = 0`), expanded at emit time into the `ldaxr`/`stlxr` loop: fixed uses
  x25 (addr) and x26 (operand), fixed defs x27 (old value) and x24 (and x28 unless
  `xchg`), as `aarch64_get_operands` collects them. -/
  | atomicRmwLoop (ty : CTy) (op : AtomicRmwLoopOp) (flags : Clif.MemFlags)
      (addr operand oldval scratch1 scratch2 : Reg)
  /-- `atomic_cas` as Cranelift's LL/SC pseudo-instruction `MInst.AtomicCASLoop`: fixed uses
  x25 (addr), x26 (expected), x28 (replacement); fixed defs x27 (old value), x24. -/
  | atomicCasLoop (ty : CTy) (flags : Clif.MemFlags) (addr expect replace oldval scratch : Reg)
  /-- `csetm xd, cond` = `csinv xd, xzr, xzr, invert(cond)`. -/
  | csetm (rd : Reg) (c : Cond)
  /-- `dmb ish` (`MInst.Fence`). -/
  | fence
  /-- `Call`/`CallInd` with a `try_call_info` (`try_call`/`try_call_indirect`): a block
  terminator (`MachTerminator::Branch`) whose successors are the handlers' landing pads and
  the continuation; emitted as `bl`/`blr` then `b continuation`. Its defs (return values and
  exception payloads, fixed registers) are live into every successor. Unverified. -/
  | tryCall (info : CallInfo) (ti : TryInfo)
  deriving DecidableEq, Repr, Inhabited, BEq

/-! ### Operands -/

/-- Register occurrences of an addressing mode (all are uses). -/
def AMode.regs : AMode → List Reg
  | .regReg a b | .regScaled a b | .regScaledExtended a b _ | .regExtended a b _ => [a, b]
  | .unscaled a _ | .unsignedOffset a _ | .regOffset a _ => [a]
  | _ => []

def AMode.mapRegs (f : Reg → Reg) : AMode → AMode
  | .regReg a b => .regReg (f a) (f b)
  | .regScaled a b => .regScaled (f a) (f b)
  | .regScaledExtended a b e => .regScaledExtended (f a) (f b) e
  | .regExtended a b e => .regExtended (f a) (f b) e
  | .unscaled a i => .unscaled (f a) i
  | .unsignedOffset a i => .unsignedOffset (f a) i
  | .regOffset a i => .regOffset (f a) i
  | m => m

def CondBrKind.regs : CondBrKind → List Reg
  | .zero r _ | .notZero r _ => [r]
  | .cond _ => []

def CondBrKind.mapRegs (f : Reg → Reg) : CondBrKind → CondBrKind
  | .zero r s => .zero (f r) s
  | .notZero r s => .notZero (f r) s
  | .cond c => .cond c

/-- Registers read by an instruction (`get_operands` uses), excluding the fixed-register
pairs of `call`/`args`/`rets`, which the allocator handles separately. -/
def MInst.uses : MInst → List Reg
  | .aluRRR _ _ _ rn rm => [rn, rm]
  | .aluRRRR _ _ _ rn rm ra => [rn, rm, ra]
  | .aluRRImm12 _ _ _ rn _ | .aluRRImmLogic _ _ _ rn _ | .aluRRImmShift _ _ _ rn _ => [rn]
  | .aluRRRShift _ _ _ rn rm _ | .aluRRRExtend _ _ _ rn rm _ => [rn, rm]
  | .bitRR _ _ _ rn => [rn]
  | .load _ _ mem _ => mem.regs
  | .store _ rd mem _ => rd :: mem.regs
  | .mov _ _ rm => [rm]
  | .movWide .. => []
  | .movK _ rn _ _ => [rn]
  | .extend _ rn _ _ _ => [rn]
  | .bitfieldMove _ _ _ rn _ _ => [rn]
  | .cset .. => []
  | .csel _ rn rm _ => [rn, rm]
  | .ccmp _ rn rm _ _ => [rn, rm]
  | .ccmpImm _ rn _ _ _ => [rn]
  | .movToFpu _ rn _ | .movFromVec _ rn _ _ | .vecMisc _ _ rn _ | .vecLanes _ _ rn _ => [rn]
  | .vecRRR _ _ rn rm _ => [rn, rm]
  | .call info => match info.dest with
    | .reg r => [r]
    | .sym _ => []
  | .args _ | .rets _ => []
  | .jump _ => []
  | .condBr _ _ k | .trapIf k _ => k.regs
  | .testBitAndBranch _ _ _ rn _ => [rn]
  | .udf _ => []
  | .jtSequence _ _ ridx _ _ => [ridx]
  | .loadExtNameGot .. | .loadExtNameNear .. => []
  | .loadAddr _ mem => mem.regs
  | .emitIsland _ => []
  | .loadAcquire _ _ rn _ => [rn]
  | .storeRelease _ rt rn _ => [rt, rn]
  | .atomicRmwLoop _ _ _ addr operand _ _ _ => [addr, operand]
  | .atomicCasLoop _ _ addr expect replace _ _ => [addr, expect, replace]
  | .csetm .. | .fence => []
  | .tryCall info _ => match info.dest with
    | .reg r => [r]
    | .sym _ => []

/-- Registers written by an instruction (excluding `call`/`args` fixed pairs). -/
def MInst.defs : MInst → List Reg
  | .aluRRR _ _ rd _ _ | .aluRRRR _ _ rd _ _ _ | .aluRRImm12 _ _ rd _ _
  | .aluRRImmLogic _ _ rd _ _ | .aluRRImmShift _ _ rd _ _ | .aluRRRShift _ _ rd _ _ _
  | .aluRRRExtend _ _ rd _ _ _ | .bitRR _ _ rd _ | .load _ rd _ _ | .mov _ rd _
  | .movWide _ rd _ _ | .movK rd _ _ _ | .extend rd _ _ _ _ | .bitfieldMove _ _ rd _ _ _
  | .cset rd _ | .csel rd _ _ _ | .movToFpu rd _ _ | .movFromVec rd _ _ _ | .vecMisc _ rd _ _
  | .vecLanes _ rd _ _ | .vecRRR _ rd _ _ _ | .loadExtNameGot rd _ | .loadExtNameNear rd _ _
  | .loadAddr rd _ => [rd]
  | .jtSequence _ _ _ t1 t2 => [t1, t2]
  | .loadAcquire _ rt _ _ => [rt]
  | .atomicRmwLoop _ _ _ _ _ oldval _ _ => [oldval]
  | .atomicCasLoop _ _ _ _ _ oldval _ => [oldval]
  | .csetm rd _ => [rd]
  | _ => []

/-- Apply `f` to every register occurrence (uses and defs, not the real registers of the
fixed pairs of `call`/`args`/`rets`, whose vreg side is mapped). -/
def MInst.mapRegs (f : Reg → Reg) : MInst → MInst
  | .aluRRR op s rd rn rm => .aluRRR op s (f rd) (f rn) (f rm)
  | .aluRRRR op s rd rn rm ra => .aluRRRR op s (f rd) (f rn) (f rm) (f ra)
  | .aluRRImm12 op s rd rn i => .aluRRImm12 op s (f rd) (f rn) i
  | .aluRRImmLogic op s rd rn i => .aluRRImmLogic op s (f rd) (f rn) i
  | .aluRRImmShift op s rd rn i => .aluRRImmShift op s (f rd) (f rn) i
  | .aluRRRShift op s rd rn rm sh => .aluRRRShift op s (f rd) (f rn) (f rm) sh
  | .aluRRRExtend op s rd rn rm e => .aluRRRExtend op s (f rd) (f rn) (f rm) e
  | .bitRR op s rd rn => .bitRR op s (f rd) (f rn)
  | .load op rd mem fl => .load op (f rd) (mem.mapRegs f) fl
  | .store op rd mem fl => .store op (f rd) (mem.mapRegs f) fl
  | .mov s rd rm => .mov s (f rd) (f rm)
  | .movWide op rd i s => .movWide op (f rd) i s
  | .movK rd rn i s => .movK (f rd) (f rn) i s
  | .extend rd rn sg a b => .extend (f rd) (f rn) sg a b
  | .bitfieldMove s op rd rn a b => .bitfieldMove s op (f rd) (f rn) a b
  | .cset rd c => .cset (f rd) c
  | .csel rd rn rm c => .csel (f rd) (f rn) (f rm) c
  | .ccmp s rn rm n c => .ccmp s (f rn) (f rm) n c
  | .ccmpImm s rn i n c => .ccmpImm s (f rn) i n c
  | .movToFpu rd rn s => .movToFpu (f rd) (f rn) s
  | .movFromVec rd rn i s => .movFromVec (f rd) (f rn) i s
  | .vecMisc op rd rn s => .vecMisc op (f rd) (f rn) s
  | .vecLanes op rd rn s => .vecLanes op (f rd) (f rn) s
  | .vecRRR op rd rn rm s => .vecRRR op (f rd) (f rn) (f rm) s
  | .call info =>
    .call { info with
      dest := match info.dest with
        | .reg r => .reg (f r)
        | d => d
      uses := info.uses.map fun (v, p) => (f v, p)
      defs := info.defs.map fun (p, v) => (p, f v) }
  | .args ds => .args (ds.map fun (v, p) => (f v, p))
  | .rets us => .rets (us.map fun (v, p) => (f v, p))
  | .jump l => .jump l
  | .condBr a b k => .condBr a b (k.mapRegs f)
  | .testBitAndBranch k a b rn bit => .testBitAndBranch k a b (f rn) bit
  | .trapIf k c => .trapIf (k.mapRegs f) c
  | .udf c => .udf c
  | .jtSequence d ts ridx t1 t2 => .jtSequence d ts (f ridx) (f t1) (f t2)
  | .loadExtNameGot rd n => .loadExtNameGot (f rd) n
  | .loadExtNameNear rd n o => .loadExtNameNear (f rd) n o
  | .loadAddr rd mem => .loadAddr (f rd) (mem.mapRegs f)
  | .emitIsland n => .emitIsland n
  | .loadAcquire ty rt rn fl => .loadAcquire ty (f rt) (f rn) fl
  | .storeRelease ty rt rn fl => .storeRelease ty (f rt) (f rn) fl
  | .atomicRmwLoop ty op fl a o1 o2 s1 s2 =>
    .atomicRmwLoop ty op fl (f a) (f o1) (f o2) (f s1) (f s2)
  | .atomicCasLoop ty fl a e r o s =>
    .atomicCasLoop ty fl (f a) (f e) (f r) (f o) (f s)
  | .csetm rd c => .csetm (f rd) c
  | .fence => .fence
  | .tryCall info ti =>
    .tryCall { info with
      dest := match info.dest with
        | .reg r => .reg (f r)
        | d => d
      uses := info.uses.map fun (v, p) => (f v, p)
      defs := info.defs.map fun (p, v) => (p, f v) } ti

/-- Is this a block terminator (`is_term`)? -/
def MInst.isTerm : MInst → Bool
  | .rets _ | .jump _ | .condBr .. | .testBitAndBranch .. | .jtSequence .. | .tryCall .. => true
  | _ => false

/-! ## Immediates (transcriptions of `imms.rs` / `args.rs`) -/

def mask64 (n : Nat) : Nat := n % 2 ^ 64

/-- `Imm12::maybe_from_u64`. -/
def Imm12.ofNat? (val : Nat) : Option Imm12 :=
  let val := mask64 val
  if val < 0x1000 then some ⟨val, false⟩
  else if val % 0x1000 == 0 && val < 0x1000000 then some ⟨val / 0x1000, true⟩
  else none

/-- Rotate the `e`-bit value `x` right by one bit. -/
def rotr1 (e x : Nat) : Nat := x / 2 + (x % 2) * 2 ^ (e - 1)

/-- Is the `e`-bit element `x` a rotation of a contiguous non-empty, non-full run of ones?
(exactly two bit transitions around the circle). -/
def isRotatedRun (e x : Nat) : Bool :=
  let t := Nat.xor x (rotr1 e x)
  x != 0 && x != 2 ^ e - 1 &&
    (List.range e).foldl (fun c i => if t.testBit i then c + 1 else c) 0 == 2

/-- `ImmLogic::maybe_from_u64(value, ty)` for `ty ∈ {I32, I64}`: `some` iff the (for `I32`:
low 32 bits, replicated) 64-bit pattern is an AArch64 bitmask immediate, i.e. a replication
of an element of size 2, 4, ..., 64 that is a rotated run of ones. This is the set of values
VIXL's `IsImmLogical` (ported in `imms.rs`) accepts; the `N:immr:imms` encoding is computed by
the assembler. -/
def ImmLogic.ofNat? (value : Nat) (size : OperandSize) : Option ImmLogic :=
  let v := mask64 value
  let v := match size with
    | .size32 => (v % 2 ^ 32) * 2 ^ 32 + v % 2 ^ 32
    | .size64 => v
  let ok := [2, 4, 8, 16, 32, 64].any fun e =>
    let x := v % 2 ^ e
    -- periodic with period e
    (List.range (64 / e)).all (fun k => (v / 2 ^ (k * e)) % 2 ^ e == x) && isRotatedRun e x
  if ok then some ⟨value, size⟩ else none

/-- The bits the immediate stands for at its operand size. -/
def ImmLogic.bitsAtSize (i : ImmLogic) : Nat :=
  match i.size with
  | .size32 => i.value % 2 ^ 32
  | .size64 => mask64 i.value

/-- `ImmLogic::invert`. -/
def ImmLogic.invert (i : ImmLogic) : ImmLogic :=
  ⟨2 ^ 64 - 1 - mask64 i.value, i.size⟩

/-- `MoveWideConst::maybe_from_u64`. -/
def MoveWideConst.ofNat? (value : Nat) : Option MoveWideConst :=
  let value := mask64 value
  if value < 2 ^ 16 then some ⟨value, 0⟩
  else if value % 2 ^ 16 == 0 && value < 2 ^ 32 then some ⟨value / 2 ^ 16, 1⟩
  else if value % 2 ^ 32 == 0 && value < 2 ^ 48 then some ⟨value / 2 ^ 32, 2⟩
  else if value % 2 ^ 48 == 0 then some ⟨value / 2 ^ 48, 3⟩
  else none

/-- `SImm9::maybe_from_i64`. -/
def simm9? (v : Int) : Option Int := if -256 ≤ v ∧ v ≤ 255 then some v else none

/-- `UImm12Scaled::maybe_from_i64(value, scale_ty)` with `scale = scale_ty.bytes()`. -/
def uimm12Scaled? (v : Int) (scale : Nat) : Option Nat :=
  if 0 ≤ v ∧ v ≤ 4095 * scale ∧ v.toNat % scale == 0 then some v.toNat else none

/-- `ShiftOpShiftImm::maybe_from_shift`. -/
def shiftImm? (n : Nat) : Option Nat := if n ≤ 63 then some n else none

/-! ## The interpreter's value domain -/

/-- Opaque (ISLE `primitive` / extern) values that are not CLIF entities or registers. -/
inductive Opnd where
  | imm12 (i : Imm12)
  | immLogic (i : ImmLogic)
  | immShift (n : Nat)
  | uimm5 (n : Nat)
  | uimm6 (n : Nat)
  | simm9 (i : Int)
  | uimm12Scaled (off : Nat)
  | shiftOpAndAmt (s : ShiftOpAndAmt)
  | moveWideConst (m : MoveWideConst)
  | nzcv (f : NZCV)
  | memFlags (f : Clif.MemFlags)
  | trapCode (c : Clif.TrapCode)
  | stackSlot (n : Nat)
  | funcRef (n : Nat)
  /-- `GlobalValue` (`gvN`). -/
  | globalValue (n : Nat)
  /-- `SigRef`/`Sig`: the callee signature itself. -/
  | sig (s : Clif.Signature)
  | extName (name : String)
  | callArgs (uses : List (Reg × Reg))
  | callRets (defs : List (Reg × Reg))
  | callInfo (c : CallInfo)
  /-- `ExtendedValue`: a CLIF value and the extend op that `get_as_extended_value` found. -/
  | extended (value : Nat) (e : ExtendOp)
  /-- `JumpTable`: indices of the `br_table` targets. -/
  | jumpTable (n : Nat)
  | tryCallNone
  /-- `ExceptionTable`: the table's signature and item kinds (tag number, or `none` for
  `default`), in item order (`context` items are rejected when the data is built). -/
  | exnTable (sig : Clif.Signature) (items : List (Option Nat))
  /-- `OptionTryCallInfo` = `Some(TryCallInfo)` (`try_call_info`). -/
  | tryCallInfo (ti : TryInfo)
  | unit
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Values of the ISLE interpreter (`Isle.Sem V σ`). ISLE integers of every width are `int`
(kept in the range of their ISLE type by the helpers that make them); enums and structs
defined in ISLE (and extern enums such as `Cond`, `Opcode`, `InstructionData`) are `data`. -/
inductive V where
  | int (i : Int)
  | bool (b : Bool)
  | ty (t : CTy)
  /-- A CLIF instruction (index into the lowering context's instruction table). -/
  | inst (n : Nat)
  /-- A CLIF value `vN`. -/
  | value (n : Nat)
  /-- `Reg` / `WritableReg`. -/
  | reg (r : Reg)
  /-- `ValueRegs`. -/
  | regs (rs : List Reg)
  /-- `ValueRegsVec` / `InstOutput`. -/
  | regsVec (rss : List (List Reg))
  | label (l : Label)
  /-- `MachLabelSlice` / `BoxVecMachLabel`. -/
  | labels (ls : List Label)
  /-- `ValueList` / `ValueSlice` / `ValueArray2`. -/
  | values (vs : List Nat)
  /-- `BlockCall` (opaque index) / `BlockArray2`. -/
  | blockCalls (bs : List Nat)
  | data (ty : TypeId) (k : Nat) (fields : List V)
  | op (o : Opnd)
  deriving Repr, Inhabited

mutual
/-- Structural equality of ISLE values (hand-written: `deriving BEq` on this nested inductive
gives an opaque function, about which proofs can learn nothing). -/
def V.beq : V → V → Bool
  | .int a, .int b => decide (a = b)
  | .bool a, .bool b => decide (a = b)
  | .ty a, .ty b => decide (a = b)
  | .inst a, .inst b => decide (a = b)
  | .value a, .value b => decide (a = b)
  | .reg a, .reg b => decide (a = b)
  | .regs a, .regs b => decide (a = b)
  | .regsVec a, .regsVec b => decide (a = b)
  | .label a, .label b => decide (a = b)
  | .labels a, .labels b => decide (a = b)
  | .values a, .values b => decide (a = b)
  | .blockCalls a, .blockCalls b => decide (a = b)
  | .data t k fs, .data t' k' fs' => decide (t = t') && decide (k = k') && V.beqList fs fs'
  | .op a, .op b => decide (a = b)
  | _, _ => false
/-- `V.beq` on lists. -/
def V.beqList : List V → List V → Bool
  | [], [] => true
  | a :: as, b :: bs => V.beq a b && V.beqList as bs
  | _, _ => false
end

instance : BEq V := ⟨V.beq⟩

theorem V.beq_iff (a : V) : ∀ b : V, V.beq a b = true ↔ a = b := by
  induction a using V.rec (motive_2 := fun l => ∀ l', V.beqList l l' = true ↔ l = l') with
  | data t k fs ih =>
    intro b
    cases b <;> simp only [V.beq, Bool.and_eq_true, decide_eq_true_eq, ih, V.data.injEq, and_assoc,
      reduceCtorEq, Bool.false_eq_true]
  | nil => rename_i l'; cases l' <;> simp [V.beqList]
  | cons a as iha ihas => rename_i l'; cases l' <;> simp [V.beqList, iha, ihas]
  | _ => intro b; cases b <;> simp [V.beq]

instance : LawfulBEq V where
  eq_of_beq h := (V.beq_iff _ _).1 h
  rfl := (V.beq_iff _ _).2 rfl

/-! ### ISLE type ids and enum variants

Type ids and variant indices are the generated constants `Isle.Aarch64.TyId.*` and
`Isle.Aarch64.VIdx.*` (`FV/Isle/Generated/Ids.lean`): decoding matches on them (a `Nat`-literal
match, which proofs reduce by `rfl`), and a Cranelift upgrade that renames a type or variant
the backend uses is a compile error here. Values the backend builds from CLIF by *name*
(`mkVariant`, used for `Opcode`/`InstructionData`) go through `variantIdx`;
`FVTest/Backend/Names.lean` checks those names. -/

open Isle.Aarch64 in
/-- Variant names of the enum type `ty` (messages and by-name construction). -/
def variantNames (ty : TypeId) : List String :=
  match program.type? ty with
  | some ⟨_, _, .enum _ vs, _⟩ => vs.map (·.name)
  | _ => []

/-- Index of variant `name` of enum `ty`. -/
def variantIdx (ty : TypeId) (name : String) : Option Nat := (variantNames ty).idxOf? name

/-- Build the field-less or fielded variant `name` of the enum `ty`. -/
def mkVariant (ty : TypeId) (name : String) (fs : List V := []) : V :=
  match variantIdx ty name with
  | some k => .data ty k fs
  | none => .op .unit   -- unreachable for the names the backend uses (`FVTest/Backend/Names.lean`)

open Isle.Aarch64

abbrev tyMInst : TypeId := TyId.MInst
abbrev tyAtomicRmwOp : TypeId := TyId.AtomicRmwOp
abbrev tyALUOp : TypeId := TyId.ALUOp
abbrev tyALUOp3 : TypeId := TyId.ALUOp3
abbrev tyOperandSize : TypeId := TyId.OperandSize
abbrev tyCond : TypeId := TyId.Cond
abbrev tyExtendOp : TypeId := TyId.ExtendOp
abbrev tyAMode : TypeId := TyId.AMode
abbrev tyAtomicRmwLoopOp : TypeId := TyId.AtomicRMWLoopOp
abbrev tyCondBrKind : TypeId := TyId.CondBrKind
abbrev tyMoveWideOp : TypeId := TyId.MoveWideOp
abbrev tyBfmOp : TypeId := TyId.BfmOp
abbrev tyBitOp : TypeId := TyId.BitOp
abbrev tyScalarSize : TypeId := TyId.ScalarSize
abbrev tyVectorSize : TypeId := TyId.VectorSize
abbrev tyVecMisc2 : TypeId := TyId.VecMisc2
abbrev tyVecLanesOp : TypeId := TyId.VecLanesOp
abbrev tyVecALUOp : TypeId := TyId.VecALUOp
abbrev tyTBKind : TypeId := TyId.TestBitAndBranchKind
abbrev tyIntCC : TypeId := TyId.IntCC
abbrev tyOpcode : TypeId := TyId.Opcode
abbrev tyInstData : TypeId := TyId.InstructionData
abbrev tyRelocDistance : TypeId := TyId.RelocDistance
abbrev tyTlsModel : TypeId := TyId.TlsModel
abbrev tyImmExtend : TypeId := TyId.ImmExtend

/-- The variant name of an enum value (messages only). -/
def V.variant? : V → Option (TypeId × String × List V)
  | .data t k fs => ((variantNames t)[k]?).map fun n => (t, n, fs)
  | _ => none

/-- Variant index and fields of a value of the enum type `ty`. -/
def V.enumOf? (ty : TypeId) : V → Option (Nat × List V)
  | .data t k fs => if t = ty then some (k, fs) else none
  | _ => none

/-! ### Conversion to the typed view (`V → MInst`) -/

def ALUOp.ofIdx? : Nat → Option ALUOp
  | VIdx.ALUOp.Add => some .add | VIdx.ALUOp.Sub => some .sub | VIdx.ALUOp.Orr => some .orr
  | VIdx.ALUOp.OrrNot => some .orrNot | VIdx.ALUOp.And => some .and
  | VIdx.ALUOp.AndS => some .andS | VIdx.ALUOp.AndNot => some .andNot
  | VIdx.ALUOp.Eor => some .eor | VIdx.ALUOp.EorNot => some .eorNot
  | VIdx.ALUOp.AddS => some .addS | VIdx.ALUOp.SubS => some .subS
  | VIdx.ALUOp.SMulH => some .sMulH | VIdx.ALUOp.UMulH => some .uMulH
  | VIdx.ALUOp.SDiv => some .sDiv | VIdx.ALUOp.UDiv => some .uDiv
  | VIdx.ALUOp.Extr => some .extr | VIdx.ALUOp.Lsr => some .lsr | VIdx.ALUOp.Asr => some .asr
  | VIdx.ALUOp.Lsl => some .lsl | VIdx.ALUOp.Adc => some .adc | VIdx.ALUOp.AdcS => some .adcS
  | VIdx.ALUOp.Sbc => some .sbc | VIdx.ALUOp.SbcS => some .sbcS | _ => none

def ALUOp3.ofIdx? : Nat → Option ALUOp3
  | VIdx.ALUOp3.MAdd => some .mAdd | VIdx.ALUOp3.MSub => some .mSub
  | VIdx.ALUOp3.UMAddL => some .uMAddL | VIdx.ALUOp3.SMAddL => some .sMAddL | _ => none

def Cond.all : List Cond :=
  [.eq, .ne, .hs, .lo, .mi, .pl, .vs, .vc, .hi, .ls, .ge, .lt, .gt, .le, .al, .nv]

def Cond.name : Cond → String
  | .eq => "Eq" | .ne => "Ne" | .hs => "Hs" | .lo => "Lo" | .mi => "Mi" | .pl => "Pl"
  | .vs => "Vs" | .vc => "Vc" | .hi => "Hi" | .ls => "Ls" | .ge => "Ge" | .lt => "Lt"
  | .gt => "Gt" | .le => "Le" | .al => "Al" | .nv => "Nv"

/-- Variant index of a condition in the ISLE enum `Cond`. -/
def Cond.idx : Cond → Nat
  | .eq => VIdx.Cond.Eq | .ne => VIdx.Cond.Ne | .hs => VIdx.Cond.Hs | .lo => VIdx.Cond.Lo
  | .mi => VIdx.Cond.Mi | .pl => VIdx.Cond.Pl | .vs => VIdx.Cond.Vs | .vc => VIdx.Cond.Vc
  | .hi => VIdx.Cond.Hi | .ls => VIdx.Cond.Ls | .ge => VIdx.Cond.Ge | .lt => VIdx.Cond.Lt
  | .gt => VIdx.Cond.Gt | .le => VIdx.Cond.Le | .al => VIdx.Cond.Al | .nv => VIdx.Cond.Nv

def Cond.ofIdx? : Nat → Option Cond
  | VIdx.Cond.Eq => some .eq | VIdx.Cond.Ne => some .ne | VIdx.Cond.Hs => some .hs
  | VIdx.Cond.Lo => some .lo | VIdx.Cond.Mi => some .mi | VIdx.Cond.Pl => some .pl
  | VIdx.Cond.Vs => some .vs | VIdx.Cond.Vc => some .vc | VIdx.Cond.Hi => some .hi
  | VIdx.Cond.Ls => some .ls | VIdx.Cond.Ge => some .ge | VIdx.Cond.Lt => some .lt
  | VIdx.Cond.Gt => some .gt | VIdx.Cond.Le => some .le | VIdx.Cond.Al => some .al
  | VIdx.Cond.Nv => some .nv | _ => none

def ExtendOp.all : List ExtendOp := [.uxtb, .uxth, .uxtw, .uxtx, .sxtb, .sxth, .sxtw, .sxtx]

def ExtendOp.name : ExtendOp → String
  | .uxtb => "UXTB" | .uxth => "UXTH" | .uxtw => "UXTW" | .uxtx => "UXTX"
  | .sxtb => "SXTB" | .sxth => "SXTH" | .sxtw => "SXTW" | .sxtx => "SXTX"

/-- Variant index of an extend op in the ISLE enum `ExtendOp`. -/
def ExtendOp.idx : ExtendOp → Nat
  | .uxtb => VIdx.ExtendOp.UXTB | .uxth => VIdx.ExtendOp.UXTH | .uxtw => VIdx.ExtendOp.UXTW
  | .uxtx => VIdx.ExtendOp.UXTX | .sxtb => VIdx.ExtendOp.SXTB | .sxth => VIdx.ExtendOp.SXTH
  | .sxtw => VIdx.ExtendOp.SXTW | .sxtx => VIdx.ExtendOp.SXTX

def ExtendOp.ofIdx? : Nat → Option ExtendOp
  | VIdx.ExtendOp.UXTB => some .uxtb | VIdx.ExtendOp.UXTH => some .uxth
  | VIdx.ExtendOp.UXTW => some .uxtw | VIdx.ExtendOp.UXTX => some .uxtx
  | VIdx.ExtendOp.SXTB => some .sxtb | VIdx.ExtendOp.SXTH => some .sxth
  | VIdx.ExtendOp.SXTW => some .sxtw | VIdx.ExtendOp.SXTX => some .sxtx | _ => none

def OperandSize.name : OperandSize → String
  | .size32 => "Size32" | .size64 => "Size64"

def OperandSize.ofIdx? : Nat → Option OperandSize
  | VIdx.OperandSize.Size32 => some .size32 | VIdx.OperandSize.Size64 => some .size64 | _ => none

def ScalarSize.ofIdx? : Nat → Option ScalarSize
  | VIdx.ScalarSize.Size8 => some .size8 | VIdx.ScalarSize.Size16 => some .size16
  | VIdx.ScalarSize.Size32 => some .size32 | VIdx.ScalarSize.Size64 => some .size64
  | VIdx.ScalarSize.Size128 => some .size128 | _ => none

def VectorSize.ofIdx? : Nat → Option VectorSize
  | VIdx.VectorSize.Size8x8 => some .size8x8 | VIdx.VectorSize.Size8x16 => some .size8x16
  | VIdx.VectorSize.Size16x4 => some .size16x4 | VIdx.VectorSize.Size16x8 => some .size16x8
  | VIdx.VectorSize.Size32x2 => some .size32x2 | VIdx.VectorSize.Size32x4 => some .size32x4
  | VIdx.VectorSize.Size64x2 => some .size64x2 | _ => none

def BitOp.ofIdx? : Nat → Option BitOp
  | VIdx.BitOp.RBit => some .rbit | VIdx.BitOp.Clz => some .clz | VIdx.BitOp.Cls => some .cls
  | VIdx.BitOp.Rev16 => some .rev16 | VIdx.BitOp.Rev32 => some .rev32
  | VIdx.BitOp.Rev64 => some .rev64 | _ => none

/-- Decode an enum value of type `ty` through `f` on its variant index. -/
def V.enum? (ty : TypeId) (f : Nat → Option α) (v : V) : Option α := do
  let (k, _) ← v.enumOf? ty
  f k

def V.aluOp? := V.enum? tyALUOp ALUOp.ofIdx?
def V.aluOp3? := V.enum? tyALUOp3 ALUOp3.ofIdx?
def V.size? := V.enum? tyOperandSize OperandSize.ofIdx?
def V.cond? := V.enum? tyCond Cond.ofIdx?
def V.extendOp? := V.enum? tyExtendOp ExtendOp.ofIdx?
def V.scalarSize? := V.enum? tyScalarSize ScalarSize.ofIdx?
def V.vectorSize? := V.enum? tyVectorSize VectorSize.ofIdx?
def V.bitOp? := V.enum? tyBitOp BitOp.ofIdx?
def V.moveWideOp? := V.enum? tyMoveWideOp fun
  | VIdx.MoveWideOp.MovZ => some MoveWideOp.movZ | VIdx.MoveWideOp.MovN => some .movN | _ => none
def V.bfmOp? := V.enum? tyBfmOp fun
  | VIdx.BfmOp.UBfm => some BfmOp.uBfm | VIdx.BfmOp.SBfm => some .sBfm | _ => none
def V.tbKind? := V.enum? tyTBKind fun
  | VIdx.TestBitAndBranchKind.Z => some TestBitAndBranchKind.z
  | VIdx.TestBitAndBranchKind.NZ => some .nz | _ => none
def V.vecMisc2? := V.enum? tyVecMisc2 fun
  | VIdx.VecMisc2.Cnt => some VecMisc2.cnt | _ => none
def V.vecLanesOp? := V.enum? tyVecLanesOp fun
  | VIdx.VecLanesOp.Addv => some VecLanesOp.addv | _ => none
def V.vecALUOp? := V.enum? tyVecALUOp fun
  | VIdx.VecALUOp.Addp => some VecALUOp.addp | _ => none

def V.reg? : V → Option Reg
  | .reg r => some r
  | _ => none

def V.nat? : V → Option Nat
  | .int i => if 0 ≤ i then some i.toNat else none
  | _ => none

def V.bool? : V → Option Bool
  | .bool b => some b
  | _ => none

def V.label? : V → Option Label
  | .label l => some l
  | _ => none

def V.labels? : V → Option (List Label)
  | .labels l => some l
  | _ => none

def V.opnd? : V → Option Opnd
  | .op o => some o
  | _ => none

def V.imm12? : V → Option Imm12
  | .op (.imm12 i) => some i
  | _ => none
def V.immLogic? : V → Option ImmLogic
  | .op (.immLogic i) => some i
  | _ => none
def V.immShift? : V → Option Nat
  | .op (.immShift i) => some i
  | _ => none
def V.uimm5? : V → Option Nat
  | .op (.uimm5 i) => some i
  | _ => none
def V.uimm6? : V → Option Nat
  | .op (.uimm6 i) => some i
  | _ => none
def V.shiftOpAndAmt? : V → Option ShiftOpAndAmt
  | .op (.shiftOpAndAmt i) => some i
  | _ => none
def V.moveWideConst? : V → Option MoveWideConst
  | .op (.moveWideConst i) => some i
  | _ => none
def V.nzcv? : V → Option NZCV
  | .op (.nzcv i) => some i
  | _ => none
def V.memFlags? : V → Option Clif.MemFlags
  | .op (.memFlags i) => some i
  | _ => none
def V.trapCode? : V → Option Clif.TrapCode
  | .op (.trapCode i) => some i
  | _ => none
def V.callInfo? : V → Option CallInfo
  | .op (.callInfo i) => some i
  | _ => none
def V.extName? : V → Option String
  | .op (.extName i) => some i
  | _ => none
def V.int? : V → Option Int
  | .int i => some i
  | _ => none
def V.ty? : V → Option CTy
  | .ty t => some t
  | _ => none
/-- `AtomicRmwLoopOp` from its ISLE value (index into `all`). -/
def V.atomicRmwLoopOp? : V → Option AtomicRmwLoopOp
  | v => (v.enumOf? tyAtomicRmwLoopOp).bind fun (k, _) => AtomicRmwLoopOp.all[k]?

/-- `AMode` from its ISLE value. -/
def V.amode? (v : V) : Option AMode := do
  let (k, fs) ← v.enumOf? tyAMode
  match k, fs with
  | VIdx.AMode.RegReg, [a, b] => return .regReg (← a.reg?) (← b.reg?)
  | VIdx.AMode.RegScaled, [a, b] => return .regScaled (← a.reg?) (← b.reg?)
  | VIdx.AMode.RegScaledExtended, [a, b, e] =>
    return .regScaledExtended (← a.reg?) (← b.reg?) (← e.extendOp?)
  | VIdx.AMode.RegExtended, [a, b, e] => return .regExtended (← a.reg?) (← b.reg?) (← e.extendOp?)
  | VIdx.AMode.Unscaled, [a, .op (.simm9 i)] => return .unscaled (← a.reg?) i
  | VIdx.AMode.UnsignedOffset, [a, .op (.uimm12Scaled o)] => return .unsignedOffset (← a.reg?) o
  | VIdx.AMode.RegOffset, [a, o] => return .regOffset (← a.reg?) (← o.int?)
  | VIdx.AMode.SPOffset, [o] => return .spOffset (← o.int?)
  | VIdx.AMode.FPOffset, [o] => return .fpOffset (← o.int?)
  | VIdx.AMode.IncomingArg, [o] => return .incomingArg (← o.int?)
  | VIdx.AMode.SlotOffset, [o] => return .slotOffset (← o.int?)
  | VIdx.AMode.SPPreIndexed, [.op (.simm9 i)] => return .spPreIndexed i
  | VIdx.AMode.SPPostIndexed, [.op (.simm9 i)] => return .spPostIndexed i
  | _, _ => none

/-- `CondBrKind` from its ISLE value. -/
def V.condBrKind? (v : V) : Option CondBrKind := do
  let (k, fs) ← v.enumOf? tyCondBrKind
  match k, fs with
  | VIdx.CondBrKind.Zero, [r, s] => return .zero (← r.reg?) (← s.size?)
  | VIdx.CondBrKind.NotZero, [r, s] => return .notZero (← r.reg?) (← s.size?)
  | VIdx.CondBrKind.Cond, [c] => return .cond (← c.cond?)
  | _, _ => none

def loadOpOfIdx? : Nat → Option LoadOp
  | VIdx.MInst.ULoad8 => some .uload8 | VIdx.MInst.SLoad8 => some .sload8
  | VIdx.MInst.ULoad16 => some .uload16 | VIdx.MInst.SLoad16 => some .sload16
  | VIdx.MInst.ULoad32 => some .uload32 | VIdx.MInst.SLoad32 => some .sload32
  | VIdx.MInst.ULoad64 => some .uload64 | _ => none

def storeOpOfIdx? : Nat → Option StoreOp
  | VIdx.MInst.Store8 => some .store8 | VIdx.MInst.Store16 => some .store16
  | VIdx.MInst.Store32 => some .store32 | VIdx.MInst.Store64 => some .store64 | _ => none

/-- The typed instruction of an ISLE `MInst` value (`none`: not in the modelled subset).
`BranchTarget` values are labels (`branch_target` is the identity on labels). -/
def MInst.ofV (v : V) : Option MInst := do
  let (k, fs) ← v.enumOf? tyMInst
  match k, fs with
  | VIdx.MInst.AluRRR, [op, s, rd, rn, rm] =>
    return .aluRRR (← op.aluOp?) (← s.size?) (← rd.reg?) (← rn.reg?) (← rm.reg?)
  | VIdx.MInst.AluRRRR, [op, s, rd, rn, rm, ra] =>
    return .aluRRRR (← op.aluOp3?) (← s.size?) (← rd.reg?) (← rn.reg?) (← rm.reg?) (← ra.reg?)
  | VIdx.MInst.AluRRImm12, [op, s, rd, rn, i] =>
    return .aluRRImm12 (← op.aluOp?) (← s.size?) (← rd.reg?) (← rn.reg?) (← i.imm12?)
  | VIdx.MInst.AluRRImmLogic, [op, s, rd, rn, i] =>
    return .aluRRImmLogic (← op.aluOp?) (← s.size?) (← rd.reg?) (← rn.reg?) (← i.immLogic?)
  | VIdx.MInst.AluRRImmShift, [op, s, rd, rn, i] =>
    return .aluRRImmShift (← op.aluOp?) (← s.size?) (← rd.reg?) (← rn.reg?) (← i.immShift?)
  | VIdx.MInst.AluRRRShift, [op, s, rd, rn, rm, sh] =>
    return .aluRRRShift (← op.aluOp?) (← s.size?) (← rd.reg?) (← rn.reg?) (← rm.reg?)
      (← sh.shiftOpAndAmt?)
  | VIdx.MInst.AluRRRExtend, [op, s, rd, rn, rm, e] =>
    return .aluRRRExtend (← op.aluOp?) (← s.size?) (← rd.reg?) (← rn.reg?) (← rm.reg?)
      (← e.extendOp?)
  | VIdx.MInst.BitRR, [op, s, rd, rn] =>
    return .bitRR (← op.bitOp?) (← s.size?) (← rd.reg?) (← rn.reg?)
  | VIdx.MInst.Mov, [s, rd, rm] => return .mov (← s.size?) (← rd.reg?) (← rm.reg?)
  | VIdx.MInst.MovWide, [op, rd, i, s] =>
    return .movWide (← op.moveWideOp?) (← rd.reg?) (← i.moveWideConst?) (← s.size?)
  | VIdx.MInst.MovK, [rd, rn, i, s] =>
    return .movK (← rd.reg?) (← rn.reg?) (← i.moveWideConst?) (← s.size?)
  | VIdx.MInst.Extend, [rd, rn, sg, a, b] =>
    return .extend (← rd.reg?) (← rn.reg?) (← sg.bool?) (← a.nat?) (← b.nat?)
  | VIdx.MInst.BitfieldMove, [s, op, rd, rn, a, b] =>
    return .bitfieldMove (← s.size?) (← op.bfmOp?) (← rd.reg?) (← rn.reg?) (← a.uimm6?) (← b.uimm6?)
  | VIdx.MInst.CSet, [rd, c] => return .cset (← rd.reg?) (← c.cond?)
  | VIdx.MInst.CSel, [rd, c, rn, rm] => return .csel (← rd.reg?) (← rn.reg?) (← rm.reg?) (← c.cond?)
  | VIdx.MInst.CCmp, [s, rn, rm, f, c] =>
    return .ccmp (← s.size?) (← rn.reg?) (← rm.reg?) (← f.nzcv?) (← c.cond?)
  | VIdx.MInst.CCmpImm, [s, rn, i, f, c] =>
    return .ccmpImm (← s.size?) (← rn.reg?) (← i.uimm5?) (← f.nzcv?) (← c.cond?)
  | VIdx.MInst.MovToFpu, [rd, rn, s] => return .movToFpu (← rd.reg?) (← rn.reg?) (← s.scalarSize?)
  | VIdx.MInst.MovFromVec, [rd, rn, i, s] =>
    return .movFromVec (← rd.reg?) (← rn.reg?) (← i.nat?) (← s.scalarSize?)
  | VIdx.MInst.VecMisc, [op, rd, rn, s] =>
    return .vecMisc (← op.vecMisc2?) (← rd.reg?) (← rn.reg?) (← s.vectorSize?)
  | VIdx.MInst.VecLanes, [op, rd, rn, s] =>
    return .vecLanes (← op.vecLanesOp?) (← rd.reg?) (← rn.reg?) (← s.vectorSize?)
  | VIdx.MInst.VecRRR, [op, rd, rn, rm, s] =>
    return .vecRRR (← op.vecALUOp?) (← rd.reg?) (← rn.reg?) (← rm.reg?) (← s.vectorSize?)
  | VIdx.MInst.Call, [i] => return .call (← i.callInfo?)
  | VIdx.MInst.CallInd, [i] => return .call (← i.callInfo?)
  | VIdx.MInst.Jump, [t] => return .jump (← t.label?)
  | VIdx.MInst.CondBr, [t, e, k] => return .condBr (← t.label?) (← e.label?) (← k.condBrKind?)
  | VIdx.MInst.TestBitAndBranch, [k, t, e, rn, b] =>
    return .testBitAndBranch (← k.tbKind?) (← t.label?) (← e.label?) (← rn.reg?) (← b.nat?)
  | VIdx.MInst.TrapIf, [k, c] => return .trapIf (← k.condBrKind?) (← c.trapCode?)
  | VIdx.MInst.Udf, [c] => return .udf (← c.trapCode?)
  | VIdx.MInst.JTSequence, [d, ts, ridx, t1, t2] =>
    return .jtSequence (← d.label?) (← ts.labels?) (← ridx.reg?) (← t1.reg?) (← t2.reg?)
  | VIdx.MInst.LoadExtNameGot, [rd, nm] => return .loadExtNameGot (← rd.reg?) (← nm.extName?)
  | VIdx.MInst.LoadExtNameNear, [rd, nm, o] =>
    return .loadExtNameNear (← rd.reg?) (← nm.extName?) (← o.int?)
  | VIdx.MInst.LoadAddr, [rd, m] => return .loadAddr (← rd.reg?) (← m.amode?)
  | VIdx.MInst.EmitIsland, [n] => return .emitIsland (← n.nat?)
  | VIdx.MInst.LoadAcquire, [ty, rt, rn, fl] =>
    return .loadAcquire (← ty.ty?) (← rt.reg?) (← rn.reg?) (← fl.memFlags?)
  | VIdx.MInst.StoreRelease, [ty, rt, rn, fl] =>
    return .storeRelease (← ty.ty?) (← rt.reg?) (← rn.reg?) (← fl.memFlags?)
  | VIdx.MInst.AtomicRMWLoop, [ty, op, fl, addr, operand, oldval, s1, s2] =>
    return .atomicRmwLoop (← ty.ty?) (← op.atomicRmwLoopOp?) (← fl.memFlags?)
      (← addr.reg?) (← operand.reg?) (← oldval.reg?) (← s1.reg?) (← s2.reg?)
  | VIdx.MInst.AtomicCASLoop, [ty, fl, addr, expect, replace, oldval, scratch] =>
    return .atomicCasLoop (← ty.ty?) (← fl.memFlags?) (← addr.reg?) (← expect.reg?)
      (← replace.reg?) (← oldval.reg?) (← scratch.reg?)
  | VIdx.MInst.CSetm, [rd, c] => return .csetm (← rd.reg?) (← c.cond?)
  | VIdx.MInst.Fence, [] => return .fence
  | k, [rd, m, fl] =>
    match loadOpOfIdx? k, storeOpOfIdx? k with
    | some op, _ => return .load op (← rd.reg?) (← m.amode?) (← fl.memFlags?)
    | none, some op => return .store op (← rd.reg?) (← m.amode?) (← fl.memFlags?)
    | none, none => none
  | _, _ => none

end Backend
