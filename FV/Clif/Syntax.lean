module

public section

/-!
# CLIF syntax (subset `clif-subset-v1`, semantics list S)

Deep embedding of the part of Cranelift IR (0.136.1) that `Clif.run` gives a meaning to.
See `docs/contracts/clif.md` for the public contract and `docs/contracts/clif-subset.md`
for the opcode lists.

Conventions:
* SSA values `vN`, blocks `blockN`, stack slots `ssN`, function references `fnN` are
  represented by their number `N`.
* Every value-producing instruction carries its *controlling type* `ty` explicitly (the
  type that Cranelift's `opcode.ty` suffix denotes). For most opcodes this is the result
  type; the exceptions are documented on the constructor (`icmp`, `store`, `iconcat`,
  `isplit`).
* The first block of `Function.blocks` is the entry block (CLIF layout order).
-/

namespace Clif

@[expose] section
@[expose] section
/-- CLIF scalar types: the integers and the IEEE 754 binary32/binary64 floats (`f32`/`f64`).
A float value is its raw bit pattern (`Val.bits`); its arithmetic is in `FV/Float`. Vectors
and `f16`/`f128` are outside the subset. -/
inductive Ty where
  | i8 | i16 | i32 | i64 | i128
  | f32 | f64
  deriving DecidableEq, Repr, Inhabited, Hashable
end
end

namespace Ty

/-- Bit width of a type. -/
@[expose] def width : Ty → Nat
  | i8 => 8 | i16 => 16 | i32 => 32 | i64 => 64 | i128 => 128 | f32 => 32 | f64 => 64

/-- Byte width of a type. -/
@[expose] def bytes (t : Ty) : Nat := t.width / 8

/-- CLIF spelling of the type. -/
@[expose] def name : Ty → String
  | i8 => "i8" | i16 => "i16" | i32 => "i32" | i64 => "i64" | i128 => "i128"
  | f32 => "f32" | f64 => "f64"

@[expose] def ofName? : String → Option Ty
  | "i8" => some i8 | "i16" => some i16 | "i32" => some i32 | "i64" => some i64
  | "i128" => some i128 | "f32" => some f32 | "f64" => some f64 | _ => none

/-- An integer type (`i8 … i128`). -/
@[expose, simp] def isInt : Ty → Bool
  | i8 | i16 | i32 | i64 | i128 => true
  | f32 | f64 => false

/-- A float type (`f32`, `f64`). -/
@[expose, simp] def isFloat (t : Ty) : Bool := !t.isInt

/-- The integer type of a width. -/
def ofWidth? : Nat → Option Ty
  | 8 => some i8 | 16 => some i16 | 32 => some i32 | 64 => some i64 | 128 => some i128
  | _ => none

/-- The integer type of twice the width (`iconcat` result), if any. -/
@[expose] def double? : Ty → Option Ty
  | i8 => some i16 | i16 => some i32 | i32 => some i64 | i64 => some i128 | i128 => none
  | f32 | f64 => none

/-- The integer type of half the width (`isplit` results), if any. -/
@[expose] def half? : Ty → Option Ty
  | i8 => none | i16 => some i8 | i32 => some i16 | i64 => some i32 | i128 => some i64
  | f32 | f64 => none

/-- The integer type of the same width as a float type (`bitcast` partner); integers map to
themselves. -/
def intOfWidth : Ty → Ty
  | f32 => i32 | f64 => i64 | t => t

@[simp] theorem width_pos (t : Ty) : 0 < t.width := by cases t <;> decide

end Ty

@[expose] section
@[expose] section
/-- A CLIF runtime value: a width-indexed bit vector. -/
structure Val where
  ty : Ty
  bits : BitVec ty.width
  deriving DecidableEq, Repr
end
end

namespace Val

/-- The value of type `ty` whose two's-complement bit pattern represents `i` (mod 2^width). -/
@[expose] def ofInt (ty : Ty) (i : Int) : Val := ⟨ty, BitVec.ofInt ty.width i⟩

/-- The value of type `ty` with bit pattern `n` (mod 2^width). -/
@[expose] def ofNat (ty : Ty) (n : Nat) : Val := ⟨ty, BitVec.ofNat ty.width n⟩

/-- CLIF booleans are `i8` 0/1 (the result of `icmp` and the overflow flags). -/
@[expose] def ofBool (b : Bool) : Val := ⟨.i8, if b then 1#8 else 0#8⟩

/-- Unsigned interpretation. -/
@[expose] def toNat (v : Val) : Nat := v.bits.toNat

/-- Signed interpretation. -/
@[expose] def toInt (v : Val) : Int := v.bits.toInt

/-- The bits of `v` at type `ty`, if `v` has that type. -/
@[expose] def as? (v : Val) (ty : Ty) : Option (BitVec ty.width) :=
  if h : v.ty = ty then some (h ▸ v.bits) else none

@[simp] theorem as?_mk (ty : Ty) (x : BitVec ty.width) : (Val.mk ty x).as? ty = some x := by
  simp [as?]

end Val

@[expose] section
@[expose] section
/-- Trap codes (Cranelift 0.136.1 spelling: `stk_ovf heap_oob int_ovf int_divz bad_toint`
and `user<N>` with `1 ≤ N ≤ 250`). -/
inductive TrapCode where
  | stkOvf | heapOob | intOvf | intDivz | badToint
  | user (n : Nat)
  deriving DecidableEq, Repr, Inhabited
end
end

namespace TrapCode

@[expose] def name : TrapCode → String
  | stkOvf => "stk_ovf" | heapOob => "heap_oob" | intOvf => "int_ovf"
  | intDivz => "int_divz" | badToint => "bad_toint" | user n => s!"user{n}"

@[expose] def ofName? (s : String) : Option TrapCode :=
  match s with
  | "stk_ovf" => some stkOvf | "heap_oob" => some heapOob | "int_ovf" => some intOvf
  | "int_divz" => some intDivz | "bad_toint" => some badToint
  | _ =>
    if s.startsWith "user" then
      match (s.drop 4).toString.toNat? with
      | some n => if 1 ≤ n ∧ n ≤ 250 then some (user n) else none
      | none => none
    else none

end TrapCode

@[expose] section
@[expose] section
inductive Endianness where
  | little | big
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- Memory-operation flags. `trapCode = none` is `notrap`. The default trap code of a
memory access is `heap_oob`. -/
structure MemFlags where
  trapCode : Option TrapCode := some .heapOob
  aligned : Bool := false
  readonly : Bool := false
  canMove : Bool := false
  endianness : Option Endianness := none
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] def MemFlags.notrap (f : MemFlags) : Bool := f.trapCode.isNone

@[expose] section
@[expose] section
/-- Integer condition codes of `icmp`. -/
inductive IntCC where
  | eq | ne | slt | sge | sgt | sle | ult | uge | ugt | ule
  deriving DecidableEq, Repr, Inhabited
end
end

namespace IntCC

@[expose] def name : IntCC → String
  | eq => "eq" | ne => "ne" | slt => "slt" | sge => "sge" | sgt => "sgt" | sle => "sle"
  | ult => "ult" | uge => "uge" | ugt => "ugt" | ule => "ule"

@[expose] def all : List IntCC := [eq, ne, slt, sge, sgt, sle, ult, uge, ugt, ule]

@[expose] def ofName? (s : String) : Option IntCC := all.find? (·.name == s)

end IntCC

@[expose] section
@[expose] section
/-- Unary integer operations `x → x` (same type in and out). -/
inductive UnaryOp where
  | ineg | bnot | iabs | clz | ctz | cls | popcnt | bitrev | bswap
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- Binary integer operations `x, y → x`. For shifts and rotates the amount `y` may have
any integer type; for all other operations both operands have type `ty`. -/
inductive BinaryOp where
  | iadd | isub | imul | umulhi | smulhi
  | band | bor | bxor
  | ishl | ushr | sshr | rotl | rotr
  | smin | smax | umin | umax
  | uaddSat | saddSat | usubSat | ssubSat
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- Trapping division operations. -/
inductive DivOp where
  | udiv | sdiv | urem | srem
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- Operations producing `(result, i8 overflow flag)`. -/
inductive OverflowOp where
  | uaddOverflow | saddOverflow | usubOverflow | ssubOverflow | umulOverflow | smulOverflow
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- Operations with an `i8` carry/borrow input, producing `(result, i8 flag)`. -/
inductive CarryOp where
  | uaddOverflowCin | saddOverflowCin | usubOverflowBin | ssubOverflowBin
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
inductive ExtendOp where
  | uextend | sextend
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- Loads. `load` reads `ty.bytes` bytes; the others read 1/2/4 bytes and extend to `ty`. -/
inductive LoadOp where
  | load | uload8 | sload8 | uload16 | sload16 | uload32 | sload32
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- Stores. `store` writes `ty.bytes` bytes; the others truncate to 1/2/4 bytes. -/
inductive StoreOp where
  | store | istore8 | istore16 | istore32
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- Read-modify-write operations of `atomic_rmw`. -/
inductive AtomicRmwOp where
  | add | sub | and | nand | or | xor | xchg | umin | umax | smin | smax
  deriving DecidableEq, Repr, Inhabited
end
end

namespace AtomicRmwOp

@[expose] def name : AtomicRmwOp → String
  | add => "add" | sub => "sub" | .and => "and" | nand => "nand" | .or => "or"
  | .xor => "xor" | xchg => "xchg" | umin => "umin" | umax => "umax" | smin => "smin"
  | smax => "smax"

@[expose] def all : List AtomicRmwOp := [add, sub, .and, nand, .or, .xor, xchg, umin, umax, smin, smax]

@[expose] def ofName? (s : String) : Option AtomicRmwOp := all.find? (·.name == s)

end AtomicRmwOp

@[expose] section
@[expose] section
/-- Float condition codes of `fcmp` (`FloatCC`). -/
inductive FloatCC where
  | eq | ne | lt | le | gt | ge | ord | uno | one | ueq | ult | ule | ugt | uge
  deriving DecidableEq, Repr, Inhabited
end
end

namespace FloatCC

@[expose] def name : FloatCC → String
  | eq => "eq" | ne => "ne" | lt => "lt" | le => "le" | gt => "gt" | ge => "ge"
  | ord => "ord" | uno => "uno" | one => "one" | ueq => "ueq" | ult => "ult" | ule => "ule"
  | ugt => "ugt" | uge => "uge"

@[expose] def all : List FloatCC := [eq, ne, lt, le, gt, ge, ord, uno, one, ueq, ult, ule, ugt, uge]

@[expose] def ofName? (s : String) : Option FloatCC := all.find? (·.name == s)

end FloatCC

@[expose] section
@[expose] section
/-- Float operations (`Inst.float op ty args`). The operands per operation and the role of
`ty` (Cranelift's controlling type) are listed in `FOp.arity`/`Inst.resultTypes`:
* `fadd fsub fmul fdiv fmin fmax fcopysign`: `x, y : ty → ty`;
* `fneg fabs sqrt ceil floor trunc nearest`: `x : ty → ty`; `fma`: `x, y, z : ty → ty`;
* `fcmp cc`: `x, y : ty → i8`;
* `fpromote` (`ty = f64`), `fdemote` (`ty = f32`): `x → ty`;
* `fcvtToUint fcvtToSint fcvtToUintSat fcvtToSintSat`: float `x` → integer `ty`;
* `fcvtFromUint fcvtFromSint`: integer `x` → float `ty`. -/
inductive FOp where
  | fadd | fsub | fmul | fdiv | fmin | fmax | fcopysign
  | fneg | fabs | sqrt | ceil | floor | trunc | nearest
  | fma
  | fcmp (cc : FloatCC)
  | fpromote | fdemote
  | fcvtToUint | fcvtToSint | fcvtToUintSat | fcvtToSintSat
  | fcvtFromUint | fcvtFromSint
  deriving DecidableEq, Repr, Inhabited
end
end

namespace FOp

/-- The CLIF opcode name. -/
@[expose] def name : FOp → String
  | fadd => "fadd" | fsub => "fsub" | fmul => "fmul" | fdiv => "fdiv" | fmin => "fmin"
  | fmax => "fmax" | fcopysign => "fcopysign" | fneg => "fneg" | fabs => "fabs"
  | sqrt => "sqrt" | ceil => "ceil" | floor => "floor" | trunc => "trunc"
  | nearest => "nearest" | fma => "fma" | fcmp _ => "fcmp" | fpromote => "fpromote"
  | fdemote => "fdemote" | fcvtToUint => "fcvt_to_uint" | fcvtToSint => "fcvt_to_sint"
  | fcvtToUintSat => "fcvt_to_uint_sat" | fcvtToSintSat => "fcvt_to_sint_sat"
  | fcvtFromUint => "fcvt_from_uint" | fcvtFromSint => "fcvt_from_sint"

/-- Number of operands. -/
@[expose] def arity : FOp → Nat
  | fadd | fsub | fmul | fdiv | fmin | fmax | fcopysign | fcmp _ => 2
  | fma => 3
  | _ => 1

/-- The operations without a condition code, by name (`fcmp` is parsed separately). -/
@[expose] def plain : List FOp :=
  [fadd, fsub, fmul, fdiv, fmin, fmax, fcopysign, fneg, fabs, sqrt, ceil, floor, trunc,
    nearest, fma, fpromote, fdemote, fcvtToUint, fcvtToSint, fcvtToUintSat, fcvtToSintSat,
    fcvtFromUint, fcvtFromSint]

@[expose] def ofName? (s : String) : Option FOp := plain.find? (·.name == s)

/-- Is `ty` the type of the operands (`true`: the same-type operations and `fcmp`) rather
than of the result only (conversions)? -/
@[expose] def ctrlIsOperand : FOp → Bool
  | fpromote | fdemote | fcvtToUint | fcvtToSint | fcvtToUintSat | fcvtToSintSat
  | fcvtFromUint | fcvtFromSint => false
  | _ => true

end FOp

abbrev ValueId := Nat
abbrev BlockId := Nat
abbrev SlotId := Nat
abbrev FnRef := Nat

@[expose] section
@[expose] section
/-- A branch target with its block arguments, e.g. `block3(v1, v2)`. -/
structure BlockCall where
  block : BlockId
  args : List ValueId := []
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- Non-terminator instructions of the subset. -/
inductive Inst where
  /-- `iconst.ty imm` (`ty` ∈ i8..i64); at `f32`/`f64` it is `f32const`/`f64const` with the
  literal's bit pattern `imm`. -/
  | iconst (ty : Ty) (imm : BitVec ty.width)
  | unary (op : UnaryOp) (ty : Ty) (x : ValueId)
  | binary (op : BinaryOp) (ty : Ty) (x y : ValueId)
  | div (op : DivOp) (ty : Ty) (x y : ValueId)
  /-- Two results: `ty` and `i8`. -/
  | overflow (op : OverflowOp) (ty : Ty) (x y : ValueId)
  /-- Two results: `ty` and `i8`; `c` is an `i8` carry/borrow in. -/
  | carry (op : CarryOp) (ty : Ty) (x y c : ValueId)
  | uaddOverflowTrap (ty : Ty) (x y : ValueId) (code : TrapCode)
  /-- `ty` is the operand type; the result is `i8`. -/
  | icmp (cc : IntCC) (ty : Ty) (x y : ValueId)
  /-- `ty` is the type of `x`/`y`; `c` may be any integer type. -/
  | select (ty : Ty) (c x y : ValueId)
  | selectSpectreGuard (ty : Ty) (c x y : ValueId)
  | bitselect (ty : Ty) (c x y : ValueId)
  /-- `ty` is the result type; `x` may be any integer type. -/
  | bmask (ty : Ty) (x : ValueId)
  /-- `ty` is the (strictly wider) result type. -/
  | extend (op : ExtendOp) (ty : Ty) (x : ValueId)
  /-- `ty` is the (strictly narrower) result type. -/
  | ireduce (ty : Ty) (x : ValueId)
  /-- `ty` is the operand type; the result has twice the width. -/
  | iconcat (ty : Ty) (lo hi : ValueId)
  /-- `ty` is the operand type; the two results have half the width. -/
  | isplit (ty : Ty) (x : ValueId)
  /-- `ty` is the result type; `p` is an `i32`/`i64` address; `offset` is an `Offset32`. -/
  | load (op : LoadOp) (ty : Ty) (flags : MemFlags) (p : ValueId) (offset : Int)
  /-- `ty` is the type of the stored value `x`. -/
  | store (op : StoreOp) (ty : Ty) (flags : MemFlags) (x p : ValueId) (offset : Int)
  /-- `ty` (i32 or i64) is the address type. -/
  | stackAddr (ty : Ty) (slot : SlotId) (offset : Int)
  | call (fn : FnRef) (args : List ValueId)
  /-- `call_indirect sigN, callee(args)`: an indirect call through the callee address
  `callee` with the declared signature `sigN` (clif-subset S addition, rust-route step 4). -/
  | callIndirect (sig : Nat) (callee : ValueId) (args : List ValueId)
  /-- `func_addr.ty fnN`: the runtime address of the function `fnN` refers to (a program
  function or an extern), resolved through the link-time image's function symbols. -/
  | funcAddr (ty : Ty) (fn : FnRef)
  /-- `v = atomic_rmw.ty flags op p, x`: returns the old value. -/
  | atomicRmw (op : AtomicRmwOp) (ty : Ty) (flags : MemFlags) (p x : ValueId)
  /-- `v = atomic_cas.ty flags p, expected, x`: returns the old value. -/
  | atomicCas (ty : Ty) (flags : MemFlags) (p e x : ValueId)
  | atomicLoad (ty : Ty) (flags : MemFlags) (p : ValueId)
  /-- `ty` is the type of the stored value `x`. -/
  | atomicStore (ty : Ty) (flags : MemFlags) (x p : ValueId)
  | fence
  /-- `bitcast.ty flags x`: `x`'s bits at the type `ty` of the same width (`i32 ↔ f32`,
  `i64 ↔ f64`, or the identity). -/
  | bitcast (ty : Ty) (flags : MemFlags) (x : ValueId)
  | trapz (c : ValueId) (code : TrapCode)
  | trapnz (c : ValueId) (code : TrapCode)
  | nop
  /-- `symbol_value.ty gvN`: the address of the global value `gvN`, which must be a
  `symbol %name[+offset]` declaration; resolved through the link-time image
  (`Clif.Image`, `Mem.symbols`). `ty` is the address type (`i64`, or `i32`). -/
  | symbolValue (ty : Ty) (gv : Nat)
  /-- `tls_value.ty gvN`: the address of the calling thread's instance of the thread-local
  variable `gvN`, which must be a `symbol tls %name` declaration. `Clif.run` has one thread,
  whose instance is the symbol of the link-time image. -/
  | tlsValue (ty : Ty) (gv : Nat)
  /-- A float operation (`FOp`, `FV/Clif/FSem.lean`); `ty` is Cranelift's controlling type:
  the result type, except for `fcmp` (the operand type; the result is `i8`). -/
  | float (op : FOp) (ty : Ty) (args : List ValueId)
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- An argument of a `try_call` successor block call: a value, the `i`-th return value of the
call (`retN`, normal-return successor only) or the `i`-th exception payload (`exnN`, handler
successors only; `x0`/`x1` on aarch64). -/
inductive TryArg where
  | val (v : ValueId)
  | ret (i : Nat)
  | exn (i : Nat)
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- A successor of a `try_call`: a block with `TryArg` arguments. -/
structure TryDest where
  block : BlockId
  args : List TryArg := []
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- An item of an exception table (Cranelift 0.136.1 `ExceptionTableItem`): `tagN: dest`,
`default: dest`, or `context vN` (a dynamic context value for the unwinder). -/
inductive ExnItem where
  | tag (n : Nat) (dest : TryDest)
  | default (dest : TryDest)
  | context (v : ValueId)
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- The exception table of a `try_call`/`try_call_indirect`: the callee signature `sigN`,
the normal-return successor, and the handler items (`sigN, block1(ret0), [ tag0: block2(exn0) ]`). -/
structure ExnTable where
  sig : Nat
  normal : TryDest
  items : List ExnItem := []
  deriving DecidableEq, Repr, Inhabited
end
end

/-- The handler successors of an exception table, in item order (Cranelift's successor order:
handlers first, then the normal return, `ExceptionTableData::all_branches`). -/
@[expose] def ExnTable.handlers (et : ExnTable) : List TryDest :=
  et.items.filterMap fun
    | .tag _ d | .default d => some d
    | .context _ => none

/-- All successors in Cranelift's order: the handlers, then the normal return. -/
@[expose] def ExnTable.dests (et : ExnTable) : List TryDest := et.handlers ++ [et.normal]

@[expose] def TryDest.vals (d : TryDest) : List ValueId :=
  d.args.filterMap fun | .val v => some v | _ => none

def TryDest.mapVals (g : ValueId → ValueId) (d : TryDest) : TryDest :=
  { d with args := d.args.map fun | .val v => .val (g v) | a => a }

/-- The values an exception table reads: successor arguments and context values. -/
@[expose] def ExnTable.vals (et : ExnTable) : List ValueId :=
  et.normal.vals ++ et.items.flatMap fun
    | .tag _ d | .default d => d.vals
    | .context v => [v]

@[expose] def ExnTable.mapVals (g : ValueId → ValueId) (et : ExnTable) : ExnTable :=
  { et with normal := et.normal.mapVals g, items := et.items.map fun
    | .tag n d => .tag n (d.mapVals g)
    | .default d => .default (d.mapVals g)
    | .context v => .context (g v) }

@[expose] section
@[expose] section
/-- Block terminators. -/
inductive Terminator where
  | jump (dest : BlockCall)
  | brif (c : ValueId) (thenDest elseDest : BlockCall)
  /-- `x` is an `i32` index; out-of-range indices go to `default`. -/
  | brTable (x : ValueId) (default : BlockCall) (table : List BlockCall)
  | ret (vals : List ValueId)
  /-- `return_call fnN(args)`: tail call; the callee's results are this function's. -/
  | returnCall (fn : FnRef) (args : List ValueId)
  | trap (code : TrapCode)
  /-- `try_call fnN(args), exception-table`: a call that ends the block. A normal return
  continues at the table's normal-return successor with the call's results as `retN`
  arguments; an unwinding callee resumes at a handler successor with the exception payload
  as `exnN` arguments (not observable in `Clif.run`, which has no unwinding). Outside
  subset E (unverified, rust-route "agent/fv-trycall"). -/
  | tryCall (fn : FnRef) (args : List ValueId) (et : ExnTable)
  /-- `try_call_indirect callee(args), exception-table` (the signature is the table's). -/
  | tryCallIndirect (callee : ValueId) (args : List ValueId) (et : ExnTable)
  deriving DecidableEq, Repr, Inhabited
end
end

/-- A `try_call`/`try_call_indirect` terminator. -/
@[expose] def Terminator.isTry : Terminator → Bool
  | .tryCall .. | .tryCallIndirect .. => true
  | _ => false

@[expose] section
@[expose] section
/-- One instruction with its result values, e.g. `v3, v4 = uadd_overflow v1, v2`. -/
structure Stmt where
  results : List ValueId := []
  inst : Inst
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
structure Block where
  id : BlockId
  params : List (ValueId × Ty) := []
  cold : Bool := false
  body : List Stmt := []
  term : Terminator
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- ABI extension flags on parameters/returns (`uext`/`sext`); no effect on `Clif.run`. -/
inductive ArgExt where
  | none | uext | sext
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- Special purpose of a parameter (`vmctx`, `sret`, `sarg(N)`); in `Clif.run` it only matters
to `call_indirect`, which enters a function of the program only when the call-site signature
has its parameter purposes (`Clif.Signature.abiMatch`). -/
inductive ArgPurpose where
  | normal | vmctx | sret
  | sarg (size : Nat)
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
structure AbiParam where
  ty : Ty
  ext : ArgExt := .none
  purpose : ArgPurpose := .normal
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
inductive CallConv where
  | fast | tail | systemV | windowsFastcall | appleAarch64 | probestack | winch | preserveAll
  deriving DecidableEq, Repr, Inhabited
end
end

namespace CallConv

@[expose] def name : CallConv → String
  | fast => "fast" | tail => "tail" | systemV => "system_v"
  | windowsFastcall => "windows_fastcall" | appleAarch64 => "apple_aarch64"
  | probestack => "probestack" | winch => "winch" | preserveAll => "preserve_all"

@[expose] def all : List CallConv :=
  [fast, tail, systemV, windowsFastcall, appleAarch64, probestack, winch, preserveAll]

@[expose] def ofName? (s : String) : Option CallConv := all.find? (·.name == s)

end CallConv

@[expose] section
@[expose] section
/-- A function signature. `callConv = none` means the reader's default. Calling conventions
have no effect on `Clif.run`. -/
structure Signature where
  params : List AbiParam := []
  returns : List AbiParam := []
  callConv : Option CallConv := none
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- `ssN = explicit_slot size[, align = align]`. -/
structure StackSlot where
  size : Nat
  align : Option Nat := none
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- Global value declarations `gvN = ...`. Only `symbol` declarations have a meaning in
`Clif.run` (through `symbol_value`); the `global_value` instruction is outside subset S. -/
inductive GlobalValue where
  /-- `gvN = vmctx` -/
  | vmctx
  /-- `gvN = load.ty [flags] gvB[+offset]` -/
  | load (ty : Ty) (flags : MemFlags) (base : Nat) (offset : Int)
  /-- `gvN = iadd_imm.ty gvB, offset` -/
  | iaddImm (ty : Ty) (base : Nat) (offset : Int)
  /-- `gvN = [colocated] symbol %name[+offset]` -/
  | symbol (name : String) (offset : Int) (colocated : Bool)
  /-- `gvN = [colocated] symbol tls %name[+offset]`: a thread-local variable (only
  `tls_value` takes it). -/
  | tlsSymbol (name : String) (offset : Int) (colocated : Bool)
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- `fnN = [colocated] %name(sig)`: an external function reference. `name` is resolved at run
time first against the functions of the program, then against the `Env`. -/
structure ExtFunc where
  name : String
  sig : Signature
  colocated : Bool := false
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- How a run command checks its result. -/
inductive Expect where
  /-- `; run: %f(args) == vals` -/
  | eq (vals : List Val)
  /-- `; run: %f(args) != vals` -/
  | ne (vals : List Val)
  /-- Bare `; run`: the function takes no arguments and its single integer result is
  non-zero. -/
  | nonzero
  /-- `; print: %f(args)`: no expectation. -/
  | print
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- A filetest run command (`; run: ...` comment) attached to a function. -/
structure RunCommand where
  func : String
  args : List Val := []
  expect : Expect
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
structure Function where
  name : String
  sig : Signature
  slots : List (SlotId × StackSlot) := []
  globals : List (Nat × GlobalValue) := []
  externs : List (FnRef × ExtFunc) := []
  /-- Signature declarations `sigN = (…)` referenced by `call_indirect` (rust-route
  step 4). -/
  sigDecls : List (Nat × Signature) := []
  blocks : List Block
  /-- Run commands (filetest comments following the function); empty for emitted code. -/
  runs : List RunCommand := []
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- One item of a data object's contents. -/
inductive DataItem where
  /-- One byte. -/
  | byte (b : BitVec 8)
  /-- The 8-byte little-endian absolute address `&name + addend` (an `Abs8` relocation). -/
  | addr (name : String) (addend : Int)
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- A link-time data object (`; data:` directive of a filetest, see `docs/contracts/clif.md`):
a symbol `name` with initial contents, placed at an address aligned to `align`. Read-only
unless `writable`. -/
structure DataObject where
  name : String
  align : Nat := 1
  writable : Bool := false
  items : List DataItem
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- A CLIF file: header lines (`test ...`, `target ...`, `set ...`, kept verbatim), link-time
data objects (`; data:` directives, empty for emitted code) and functions. -/
structure Program where
  header : List String := []
  data : List DataObject := []
  funcs : List Function
  deriving DecidableEq, Repr, Inhabited
end
end

namespace Function

@[expose] def block? (f : Function) (b : BlockId) : Option Block := f.blocks.find? (·.id == b)

def slot? (f : Function) (s : SlotId) : Option StackSlot := (f.slots.lookup s)

@[expose] def extern? (f : Function) (r : FnRef) : Option ExtFunc := f.externs.lookup r

@[expose] def entry? (f : Function) : Option Block := f.blocks.head?

end Function

@[expose] def Program.func? (p : Program) (name : String) : Option Function :=
  p.funcs.find? (·.name == name)

/-! ## Result types -/

/-- Result types of an instruction, given the function's extern declarations (for `call`).
`none` if the instruction is ill-formed (e.g. `iconcat.i128`). -/
@[expose] def Inst.resultTypes (sigOf : FnRef → Option Signature)
    (sigDeclOf : Nat → Option Signature) : Inst → Option (List Ty)
  | .iconst ty _ | .unary _ ty _ | .binary _ ty _ _ | .div _ ty _ _
  | .uaddOverflowTrap ty _ _ _ | .select ty _ _ _ | .selectSpectreGuard ty _ _ _
  | .bitselect ty _ _ _ | .bmask ty _ | .extend _ ty _ | .ireduce ty _
  | .load _ ty _ _ _ | .stackAddr ty _ _ | .atomicRmw _ ty _ _ _ | .atomicCas ty _ _ _ _
  | .atomicLoad ty _ _ | .bitcast ty _ _ | .symbolValue ty _ | .tlsValue ty _ => some [ty]
  | .overflow _ ty _ _ | .carry _ ty _ _ _ => some [ty, .i8]
  | .icmp .. => some [.i8]
  | .iconcat ty _ _ => ty.double?.map fun t => [t]
  | .isplit ty _ => ty.half?.map fun t => [t, t]
  | .store .. | .trapz .. | .trapnz .. | .nop | .atomicStore .. | .fence => some []
  | .call r _ => (sigOf r).map fun s => s.returns.map (·.ty)
  | .callIndirect sig _ _ => (sigDeclOf sig).map fun s => s.returns.map (·.ty)
  | .funcAddr ty _ => some [ty]
  | .float (.fcmp _) _ _ => some [.i8]
  | .float _ ty _ => some [ty]

end Clif
