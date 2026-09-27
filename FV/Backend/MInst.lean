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

/-- Registers written by an instruction (excluding `call`/`args` fixed pairs). -/
def MInst.defs : MInst → List Reg
  | .aluRRR _ _ rd _ _ | .aluRRRR _ _ rd _ _ _ | .aluRRImm12 _ _ rd _ _
  | .aluRRImmLogic _ _ rd _ _ | .aluRRImmShift _ _ rd _ _ | .aluRRRShift _ _ rd _ _ _
  | .aluRRRExtend _ _ rd _ _ _ | .bitRR _ _ rd _ | .load _ rd _ _ | .mov _ rd _
  | .movWide _ rd _ _ | .movK rd _ _ _ | .extend rd _ _ _ _ | .bitfieldMove _ _ rd _ _ _
  | .cset rd _ | .movToFpu rd _ _ | .movFromVec rd _ _ _ | .vecMisc _ rd _ _
  | .vecLanes _ rd _ _ | .vecRRR _ rd _ _ _ | .loadExtNameGot rd _ | .loadExtNameNear rd _ _
  | .loadAddr rd _ => [rd]
  | .jtSequence _ _ _ t1 t2 => [t1, t2]
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

/-- Is this a block terminator (`is_term`)? -/
def MInst.isTerm : MInst → Bool
  | .rets _ | .jump _ | .condBr .. | .testBitAndBranch .. | .jtSequence .. => true
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
  deriving Repr, Inhabited, BEq

/-! ### ISLE enum names -/

open Isle.Aarch64 in
/-- The ISLE program's type named `name` (types are looked up once, at initialisation). -/
def islTy (name : String) : TypeId :=
  ((program.types.find? (·.name == name)).map (·.id)).getD 0

open Isle.Aarch64 in
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

def tyMInst : TypeId := islTy "MInst"
def tyALUOp : TypeId := islTy "ALUOp"
def tyALUOp3 : TypeId := islTy "ALUOp3"
def tyOperandSize : TypeId := islTy "OperandSize"
def tyCond : TypeId := islTy "Cond"
def tyExtendOp : TypeId := islTy "ExtendOp"
def tyAMode : TypeId := islTy "AMode"
def tyCondBrKind : TypeId := islTy "CondBrKind"
def tyMoveWideOp : TypeId := islTy "MoveWideOp"
def tyBfmOp : TypeId := islTy "BfmOp"
def tyBitOp : TypeId := islTy "BitOp"
def tyScalarSize : TypeId := islTy "ScalarSize"
def tyVectorSize : TypeId := islTy "VectorSize"
def tyVecMisc2 : TypeId := islTy "VecMisc2"
def tyVecLanesOp : TypeId := islTy "VecLanesOp"
def tyVecALUOp : TypeId := islTy "VecALUOp"
def tyTBKind : TypeId := islTy "TestBitAndBranchKind"
def tyIntCC : TypeId := islTy "IntCC"
def tyOpcode : TypeId := islTy "Opcode"
def tyInstData : TypeId := islTy "InstructionData"
def tyRelocDistance : TypeId := islTy "RelocDistance"

/-- The variant name of an enum value. -/
def V.variant? : V → Option (TypeId × String × List V)
  | .data t k fs => ((variantNames t)[k]?).map fun n => (t, n, fs)
  | _ => none

/-! ### Conversion to the typed view (`V → MInst`) -/

def ALUOp.ofName? : String → Option ALUOp
  | "Add" => some .add | "Sub" => some .sub | "Orr" => some .orr | "OrrNot" => some .orrNot
  | "And" => some .and | "AndS" => some .andS | "AndNot" => some .andNot | "Eor" => some .eor
  | "EorNot" => some .eorNot | "AddS" => some .addS | "SubS" => some .subS
  | "SMulH" => some .sMulH | "UMulH" => some .uMulH | "SDiv" => some .sDiv
  | "UDiv" => some .uDiv | "Extr" => some .extr | "Lsr" => some .lsr | "Asr" => some .asr
  | "Lsl" => some .lsl | "Adc" => some .adc | "AdcS" => some .adcS | "Sbc" => some .sbc
  | "SbcS" => some .sbcS | _ => none

def ALUOp3.ofName? : String → Option ALUOp3
  | "MAdd" => some .mAdd | "MSub" => some .mSub | "UMAddL" => some .uMAddL
  | "SMAddL" => some .sMAddL | _ => none

def Cond.all : List Cond :=
  [.eq, .ne, .hs, .lo, .mi, .pl, .vs, .vc, .hi, .ls, .ge, .lt, .gt, .le, .al, .nv]

def Cond.name : Cond → String
  | .eq => "Eq" | .ne => "Ne" | .hs => "Hs" | .lo => "Lo" | .mi => "Mi" | .pl => "Pl"
  | .vs => "Vs" | .vc => "Vc" | .hi => "Hi" | .ls => "Ls" | .ge => "Ge" | .lt => "Lt"
  | .gt => "Gt" | .le => "Le" | .al => "Al" | .nv => "Nv"

def Cond.ofName? (s : String) : Option Cond := Cond.all.find? (·.name == s)

def ExtendOp.all : List ExtendOp := [.uxtb, .uxth, .uxtw, .uxtx, .sxtb, .sxth, .sxtw, .sxtx]

def ExtendOp.name : ExtendOp → String
  | .uxtb => "UXTB" | .uxth => "UXTH" | .uxtw => "UXTW" | .uxtx => "UXTX"
  | .sxtb => "SXTB" | .sxth => "SXTH" | .sxtw => "SXTW" | .sxtx => "SXTX"

def ExtendOp.ofName? (s : String) : Option ExtendOp := ExtendOp.all.find? (·.name == s)

def OperandSize.name : OperandSize → String
  | .size32 => "Size32" | .size64 => "Size64"

def OperandSize.ofName? : String → Option OperandSize
  | "Size32" => some .size32 | "Size64" => some .size64 | _ => none

def ScalarSize.ofName? : String → Option ScalarSize
  | "Size8" => some .size8 | "Size16" => some .size16 | "Size32" => some .size32
  | "Size64" => some .size64 | "Size128" => some .size128 | _ => none

def VectorSize.ofName? : String → Option VectorSize
  | "Size8x8" => some .size8x8 | "Size8x16" => some .size8x16 | "Size16x4" => some .size16x4
  | "Size16x8" => some .size16x8 | "Size32x2" => some .size32x2
  | "Size32x4" => some .size32x4 | "Size64x2" => some .size64x2 | _ => none

def BitOp.ofName? : String → Option BitOp
  | "RBit" => some .rbit | "Clz" => some .clz | "Cls" => some .cls | "Rev16" => some .rev16
  | "Rev32" => some .rev32 | "Rev64" => some .rev64 | _ => none

/-- Decode an enum value of type `ty` through `f` on its variant name. -/
def V.enum? (ty : TypeId) (f : String → Option α) (v : V) : Option α := do
  let (ty', n, _) ← v.variant?
  if ty' == ty then f n else none

def V.aluOp? := V.enum? tyALUOp ALUOp.ofName?
def V.aluOp3? := V.enum? tyALUOp3 ALUOp3.ofName?
def V.size? := V.enum? tyOperandSize OperandSize.ofName?
def V.cond? := V.enum? tyCond Cond.ofName?
def V.extendOp? := V.enum? tyExtendOp ExtendOp.ofName?
def V.scalarSize? := V.enum? tyScalarSize ScalarSize.ofName?
def V.vectorSize? := V.enum? tyVectorSize VectorSize.ofName?
def V.bitOp? := V.enum? tyBitOp BitOp.ofName?
def V.moveWideOp? := V.enum? tyMoveWideOp fun
  | "MovZ" => some MoveWideOp.movZ | "MovN" => some .movN | _ => none
def V.bfmOp? := V.enum? tyBfmOp fun
  | "UBfm" => some BfmOp.uBfm | "SBfm" => some .sBfm | _ => none
def V.tbKind? := V.enum? tyTBKind fun
  | "Z" => some TestBitAndBranchKind.z | "NZ" => some .nz | _ => none
def V.vecMisc2? := V.enum? tyVecMisc2 fun
  | "Cnt" => some VecMisc2.cnt | _ => none
def V.vecLanesOp? := V.enum? tyVecLanesOp fun
  | "Addv" => some VecLanesOp.addv | "Uaddlv" => some .uaddlv | _ => none
def V.vecALUOp? := V.enum? tyVecALUOp fun
  | "Addp" => some VecALUOp.addp | _ => none

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

/-- `AMode` from its ISLE value. -/
def V.amode? (v : V) : Option AMode := do
  let (t, n, fs) ← v.variant?
  if t != tyAMode then none
  match n, fs with
  | "RegReg", [a, b] => return .regReg (← a.reg?) (← b.reg?)
  | "RegScaled", [a, b] => return .regScaled (← a.reg?) (← b.reg?)
  | "RegScaledExtended", [a, b, e] => return .regScaledExtended (← a.reg?) (← b.reg?) (← e.extendOp?)
  | "RegExtended", [a, b, e] => return .regExtended (← a.reg?) (← b.reg?) (← e.extendOp?)
  | "Unscaled", [a, .op (.simm9 i)] => return .unscaled (← a.reg?) i
  | "UnsignedOffset", [a, .op (.uimm12Scaled o)] => return .unsignedOffset (← a.reg?) o
  | "RegOffset", [a, o] => return .regOffset (← a.reg?) (← o.int?)
  | "SPOffset", [o] => return .spOffset (← o.int?)
  | "FPOffset", [o] => return .fpOffset (← o.int?)
  | "IncomingArg", [o] => return .incomingArg (← o.int?)
  | "SlotOffset", [o] => return .slotOffset (← o.int?)
  | "SPPreIndexed", [.op (.simm9 i)] => return .spPreIndexed i
  | "SPPostIndexed", [.op (.simm9 i)] => return .spPostIndexed i
  | _, _ => none

/-- `CondBrKind` from its ISLE value. -/
def V.condBrKind? (v : V) : Option CondBrKind := do
  let (t, n, fs) ← v.variant?
  if t != tyCondBrKind then none
  match n, fs with
  | "Zero", [r, s] => return .zero (← r.reg?) (← s.size?)
  | "NotZero", [r, s] => return .notZero (← r.reg?) (← s.size?)
  | "Cond", [c] => return .cond (← c.cond?)
  | _, _ => none

def loadOpOfName? : String → Option LoadOp
  | "ULoad8" => some .uload8 | "SLoad8" => some .sload8 | "ULoad16" => some .uload16
  | "SLoad16" => some .sload16 | "ULoad32" => some .uload32 | "SLoad32" => some .sload32
  | "ULoad64" => some .uload64 | _ => none

def storeOpOfName? : String → Option StoreOp
  | "Store8" => some .store8 | "Store16" => some .store16 | "Store32" => some .store32
  | "Store64" => some .store64 | _ => none

/-- The typed instruction of an ISLE `MInst` value (`none`: not in the modelled subset).
`BranchTarget` values are labels (`branch_target` is the identity on labels). -/
def MInst.ofV (v : V) : Option MInst := do
  let (t, n, fs) ← v.variant?
  if t != tyMInst then none
  match n, fs with
  | "AluRRR", [op, s, rd, rn, rm] =>
    return .aluRRR (← op.aluOp?) (← s.size?) (← rd.reg?) (← rn.reg?) (← rm.reg?)
  | "AluRRRR", [op, s, rd, rn, rm, ra] =>
    return .aluRRRR (← op.aluOp3?) (← s.size?) (← rd.reg?) (← rn.reg?) (← rm.reg?) (← ra.reg?)
  | "AluRRImm12", [op, s, rd, rn, i] =>
    return .aluRRImm12 (← op.aluOp?) (← s.size?) (← rd.reg?) (← rn.reg?) (← i.imm12?)
  | "AluRRImmLogic", [op, s, rd, rn, i] =>
    return .aluRRImmLogic (← op.aluOp?) (← s.size?) (← rd.reg?) (← rn.reg?) (← i.immLogic?)
  | "AluRRImmShift", [op, s, rd, rn, i] =>
    return .aluRRImmShift (← op.aluOp?) (← s.size?) (← rd.reg?) (← rn.reg?) (← i.immShift?)
  | "AluRRRShift", [op, s, rd, rn, rm, sh] =>
    return .aluRRRShift (← op.aluOp?) (← s.size?) (← rd.reg?) (← rn.reg?) (← rm.reg?)
      (← sh.shiftOpAndAmt?)
  | "AluRRRExtend", [op, s, rd, rn, rm, e] =>
    return .aluRRRExtend (← op.aluOp?) (← s.size?) (← rd.reg?) (← rn.reg?) (← rm.reg?)
      (← e.extendOp?)
  | "BitRR", [op, s, rd, rn] => return .bitRR (← op.bitOp?) (← s.size?) (← rd.reg?) (← rn.reg?)
  | "Mov", [s, rd, rm] => return .mov (← s.size?) (← rd.reg?) (← rm.reg?)
  | "MovWide", [op, rd, i, s] =>
    return .movWide (← op.moveWideOp?) (← rd.reg?) (← i.moveWideConst?) (← s.size?)
  | "MovK", [rd, rn, i, s] => return .movK (← rd.reg?) (← rn.reg?) (← i.moveWideConst?) (← s.size?)
  | "Extend", [rd, rn, sg, a, b] =>
    return .extend (← rd.reg?) (← rn.reg?) (← sg.bool?) (← a.nat?) (← b.nat?)
  | "BitfieldMove", [s, op, rd, rn, a, b] =>
    return .bitfieldMove (← s.size?) (← op.bfmOp?) (← rd.reg?) (← rn.reg?) (← a.uimm6?) (← b.uimm6?)
  | "CSet", [rd, c] => return .cset (← rd.reg?) (← c.cond?)
  | "CCmp", [s, rn, rm, f, c] =>
    return .ccmp (← s.size?) (← rn.reg?) (← rm.reg?) (← f.nzcv?) (← c.cond?)
  | "CCmpImm", [s, rn, i, f, c] =>
    return .ccmpImm (← s.size?) (← rn.reg?) (← i.uimm5?) (← f.nzcv?) (← c.cond?)
  | "MovToFpu", [rd, rn, s] => return .movToFpu (← rd.reg?) (← rn.reg?) (← s.scalarSize?)
  | "MovFromVec", [rd, rn, i, s] =>
    return .movFromVec (← rd.reg?) (← rn.reg?) (← i.nat?) (← s.scalarSize?)
  | "VecMisc", [op, rd, rn, s] =>
    return .vecMisc (← op.vecMisc2?) (← rd.reg?) (← rn.reg?) (← s.vectorSize?)
  | "VecLanes", [op, rd, rn, s] =>
    return .vecLanes (← op.vecLanesOp?) (← rd.reg?) (← rn.reg?) (← s.vectorSize?)
  | "VecRRR", [op, rd, rn, rm, s] =>
    return .vecRRR (← op.vecALUOp?) (← rd.reg?) (← rn.reg?) (← rm.reg?) (← s.vectorSize?)
  | "Call", [i] => return .call (← i.callInfo?)
  | "CallInd", [i] => return .call (← i.callInfo?)
  | "Jump", [t] => return .jump (← t.label?)
  | "CondBr", [t, e, k] => return .condBr (← t.label?) (← e.label?) (← k.condBrKind?)
  | "TestBitAndBranch", [k, t, e, rn, b] =>
    return .testBitAndBranch (← k.tbKind?) (← t.label?) (← e.label?) (← rn.reg?) (← b.nat?)
  | "TrapIf", [k, c] => return .trapIf (← k.condBrKind?) (← c.trapCode?)
  | "Udf", [c] => return .udf (← c.trapCode?)
  | "JTSequence", [d, ts, ridx, t1, t2] =>
    return .jtSequence (← d.label?) (← ts.labels?) (← ridx.reg?) (← t1.reg?) (← t2.reg?)
  | "LoadExtNameGot", [rd, nm] => return .loadExtNameGot (← rd.reg?) (← nm.extName?)
  | "LoadExtNameNear", [rd, nm, o] => return .loadExtNameNear (← rd.reg?) (← nm.extName?) (← o.int?)
  | "LoadAddr", [rd, m] => return .loadAddr (← rd.reg?) (← m.amode?)
  | "EmitIsland", [n] => return .emitIsland (← n.nat?)
  | name, [rd, m, fl] =>
    match loadOpOfName? name, storeOpOfName? name with
    | some op, _ => return .load op (← rd.reg?) (← m.amode?) (← fl.memFlags?)
    | none, some op => return .store op (← rd.reg?) (← m.amode?) (← fl.memFlags?)
    | none, none => none
  | _, _ => none

end Backend
