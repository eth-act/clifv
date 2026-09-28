import FV.Backend.MInst

/-!
# Instruction selection by interpreting Cranelift's ISLE rules (M4, unproven)

`Isle.Interp.run` (the generic ISLE interpreter) is instantiated with

* values `Backend.V` (CLIF instructions/values, registers, ISLE enum data, opaque operands);
* the lowering state `LState` (vreg allocator, instructions emitted for the current CLIF
  instruction, outgoing-argument area size);
* `sem ctx : Isle.Sem V LState`: ISLE constants, and Lean definitions of every Rust extern
  helper the rules reach (`externCtor` / `externExtract`). Each helper is a transcription of
  the Rust function named in `docs/contracts/backend.md` (table "Extern helpers"), from
  cranelift-codegen 0.136.1 (`isle_prelude.rs`, `machinst/isle.rs`, `machinst/lower.rs`,
  `machinst/abi.rs`, `isa/aarch64/lower/isle.rs`, `isa/aarch64/abi.rs`, the generated
  `isle_numerics.rs`).

The driver (`lowerFunction`) plays the part of `machinst/lower.rs`:

* every CLIF value gets a virtual register up front (`value_regs`); the registers `lower`
  returns for an instruction's results become aliases of those (`set_vreg_alias`);
* blocks are lowered in layout order and, within a block, **top-down** (Cranelift goes
  bottom-up so that it can sink loads into their single use and skip dead pure
  instructions). Here `is_sinkable_inst` always fails and `opportunistic_def` is a no-op,
  both of which are valid behaviours of the Rust helpers (they only enable optimisations),
  and every instruction is lowered, dead or not;
* block parameters stay block parameters (`VBlock.params`, the CLIF parameters' vregs) and
  branch arguments are attached to the `jump` that passes them (`VBlock.branchArgs`), as in
  Cranelift's `VCode`; `brif`/`br_table` edges with arguments get their own edge block
  (a `jump` with the arguments). The allocator turns them into parallel moves
  (`StackAlloc.lowerBlockArgs` for the stack-slot allocator, regalloc2 for the other);
* the entry block starts with Cranelift's `Args` pseudo-instruction (register arguments) and
  loads of stack arguments, as `gen_arg_setup` does.

The result is `VCode`: blocks of `MInst` over virtual registers.
-/

namespace Backend

open Isle Isle.Aarch64

/-! ## The lowering context (read-only DFG view) -/

/-- One CLIF instruction of the function being lowered. -/
structure IInfo where
  /-- The `InstructionData` value the rules match. -/
  data : V
  results : List Nat
  resTys : List CTy
  /-- The CLIF instruction (`none` for terminators). -/
  clif : Option Clif.Inst
  deriving Inhabited

/-- Read-only lowering context: the function's DFG and the pre-assigned value registers. -/
structure Ctx where
  func : Clif.Function
  insts : Array IInfo
  valTy : Array (Option CTy)
  valDef : Array (Option Nat)
  valReg : Array (Option Reg)
  /-- Offset of each explicit stack slot in the slot region (`sized_stackslot_offset`). -/
  slotOff : List (Nat × Nat)

/-- The mutable lowering state threaded through extern constructors. -/
structure LState where
  nextVreg : Nat
  classes : Array RegClass
  emitted : Array MInst := #[]
  /-- Size of the outgoing stack-argument area (`accumulate_outgoing_args_size`). -/
  outgoing : Nat := 0
  deriving Inhabited

def LState.fresh (st : LState) (cls : RegClass) : Reg × LState :=
  (.vreg st.nextVreg cls, { st with nextVreg := st.nextVreg + 1, classes := st.classes.push cls })

def LState.emit (st : LState) (i : MInst) : LState := { st with emitted := st.emitted.push i }

/-! ## CLIF → ISLE data -/

def opcodeV (name : String) : V := mkVariant tyOpcode name
def instDataV (fmt : String) (fs : List V) : V := mkVariant tyInstData fmt fs

def intccName : Clif.IntCC → String
  | .eq => "Equal" | .ne => "NotEqual" | .slt => "SignedLessThan"
  | .sge => "SignedGreaterThanOrEqual" | .sgt => "SignedGreaterThan"
  | .sle => "SignedLessThanOrEqual" | .ult => "UnsignedLessThan"
  | .uge => "UnsignedGreaterThanOrEqual" | .ugt => "UnsignedGreaterThan"
  | .ule => "UnsignedLessThanOrEqual"

/-- `lower_condcode`, on the variant index of an ISLE `IntCC` value. -/
def condOfIntCC : Nat → Option Cond
  | VIdx.IntCC.Equal => some .eq | VIdx.IntCC.NotEqual => some .ne
  | VIdx.IntCC.SignedGreaterThanOrEqual => some .ge | VIdx.IntCC.SignedGreaterThan => some .gt
  | VIdx.IntCC.SignedLessThanOrEqual => some .le | VIdx.IntCC.SignedLessThan => some .lt
  | VIdx.IntCC.UnsignedGreaterThanOrEqual => some .hs | VIdx.IntCC.UnsignedGreaterThan => some .hi
  | VIdx.IntCC.UnsignedLessThanOrEqual => some .ls | VIdx.IntCC.UnsignedLessThan => some .lo
  | _ => none

def binaryOpcode : Clif.BinaryOp → Option String
  | .iadd => "Iadd" | .isub => "Isub" | .imul => "Imul" | .umulhi => "Umulhi"
  | .smulhi => "Smulhi" | .band => "Band" | .bor => "Bor" | .bxor => "Bxor"
  | .ishl => "Ishl" | .ushr => "Ushr" | .sshr => "Sshr" | .rotl => "Rotl" | .rotr => "Rotr"
  | .smin => "Smin" | .smax => "Smax" | .umin => "Umin" | .umax => "Umax"
  | _ => none

def unaryOpcode : Clif.UnaryOp → Option String
  | .ineg => "Ineg" | .bnot => "Bnot" | .clz => "Clz" | .ctz => "Ctz" | .popcnt => "Popcnt"
  | .bswap => "Bswap" | .bitrev => "Bitrev"
  | _ => none

def divOpcode : Clif.DivOp → String
  | .udiv => "Udiv" | .sdiv => "Sdiv" | .urem => "Urem" | .srem => "Srem"

def loadOpcode : Clif.LoadOp → String
  | .load => "Load" | .uload8 => "Uload8" | .sload8 => "Sload8" | .uload16 => "Uload16"
  | .sload16 => "Sload16" | .uload32 => "Uload32" | .sload32 => "Sload32"

def storeOpcode : Clif.StoreOp → String
  | .store => "Store" | .istore8 => "Istore8" | .istore16 => "Istore16"
  | .istore32 => "Istore32"

/-- The `Imm64` of `iconst.ty imm`: the reader masks it to the type's width
(`InstructionData::mask_immediates`), so it is the zero-extended value as an `i64`. -/
def imm64OfIconst (ty : Clif.Ty) (imm : BitVec ty.width) : Int :=
  if ty.width < 64 then imm.toNat else imm.toInt

/-- Integer types of E: `i8..i64`. -/
def eTy (ty : Clif.Ty) : Bool := ty != .i128

/-- Calling conventions with the AAPCS64 argument/return locations and clobbers:
`system_v` (also the default of signatures without one) and `fast`, which Cranelift 0.136.1
treats identically on aarch64 (`compute_arg_locs` and `get_regs_clobbered_by_call` only
distinguish `tail`, `winch`, `preserve_all`, `apple_aarch64`). -/
def aapcsConv (c : Option Clif.CallConv) : Bool :=
  c.isNone || c == some .systemV || c == some .fast

/-- Text of an instruction for error messages. -/
def instText (i : Clif.Inst) : String := Clif.Print.inst (fun _ => none) i

/-- `InstructionData` of a non-terminator instruction of E (an error with the reason if the
instruction is outside E). -/
def instData (f : Clif.Function) : Clif.Inst → Except String V
  | .iconst ty imm =>
    if eTy ty then pure (instDataV "UnaryImm" [opcodeV "Iconst", .int (imm64OfIconst ty imm)])
    else throw "iconst.i128"
  | .unary op ty x =>
    match unaryOpcode op with
    | some n =>
      if !eTy ty then throw s!"{n}.i128"
      -- the verifier rejects `bswap.i8` (`clif-subset.md`: `bswap` at i16..i64)
      else if op == .bswap && ty == .i8 then throw "bswap.i8"
      else pure (instDataV "Unary" [opcodeV n, .value x])
    | none => throw s!"`{instText (.unary op ty x)}` is not in E"
  | .binary op ty x y =>
    match binaryOpcode op with
    | some n =>
      if eTy ty then pure (instDataV "Binary" [opcodeV n, .values [x, y]]) else throw s!"{n}.i128"
    | none => throw s!"`{instText (.binary op ty x y)}` is not in E"
  | .div op ty x y =>
    if eTy ty then pure (instDataV "Binary" [opcodeV (divOpcode op), .values [x, y]])
    else throw "division at i128"
  | .icmp cc ty x y =>
    if eTy ty then
      pure (instDataV "IntCompare" [opcodeV "Icmp", .values [x, y], mkVariant tyIntCC (intccName cc)])
    else throw "icmp.i128"
  | .extend op ty x =>
    if eTy ty then
      pure (instDataV "Unary" [opcodeV (if op == .uextend then "Uextend" else "Sextend"), .value x])
    else throw "extend to i128"
  | .ireduce ty x => if eTy ty then pure (instDataV "Unary" [opcodeV "Ireduce", .value x])
    else throw "ireduce.i128"
  | .load op ty flags p off =>
    if !eTy ty then throw "load.i128"
    else if flags.endianness == some .big then throw "big-endian load"
    else pure (instDataV "Load" [opcodeV (loadOpcode op), .value p, .op (.memFlags flags), .int off])
  | .store op ty flags x p off =>
    if !eTy ty then throw "store.i128"
    else if flags.endianness == some .big then throw "big-endian store"
    else pure (instDataV "Store"
      [opcodeV (storeOpcode op), .values [x, p], .op (.memFlags flags), .int off])
  | .select ty c x y =>
    if eTy ty then pure (instDataV "Ternary" [opcodeV "Select", .values [c, x, y]])
    else throw "select.i128"
  | .nop => pure (instDataV "NullAry" [opcodeV "Nop"])
  | .symbolValue ty gv =>
    if ty != .i64 then throw "symbol_value with a non-i64 address type"
    else match f.globals.lookup gv with
      | some (.symbol ..) =>
        pure (instDataV "UnaryGlobalValue" [opcodeV "SymbolValue", .op (.globalValue gv)])
      | some _ => throw s!"symbol_value of gv{gv}, which is not a `symbol`"
      | none => throw s!"unknown gv{gv}"
  | .stackAddr _ slot off =>
    pure (instDataV "StackAddr" [opcodeV "StackAddr", .op (.stackSlot slot), .int off])
  | .call fn args =>
    match f.extern? fn with
    | some ext =>
      if aapcsConv ext.sig.callConv then
        pure (instDataV "Call" [opcodeV "Call", .values args, .op (.funcRef fn)])
      else throw s!"call with calling convention {repr ext.sig.callConv}"
    | none => throw s!"unknown fn{fn}"
  | .callIndirect sig callee args =>
    match f.sigDecls.lookup sig with
    | some s =>
      pure (instDataV "CallIndirect"
        [opcodeV "CallIndirect", .values (callee :: args), .op (.sig s)])
    | none => throw s!"call_indirect of undeclared sig{sig}"
  | .funcAddr ty fn =>
    if ty != .i64 then throw "func_addr with a non-i64 address type"
    else pure (instDataV "FuncAddr" [opcodeV "FuncAddr", .op (.funcRef fn)])
  | i => throw s!"`{instText i}` is not in E"

/-! ## ABI (`isa/aarch64/abi.rs` `compute_arg_locs`, AAPCS64 / `system_v`) -/

inductive ArgLoc where
  | reg (r : Reg)
  | stack (off : Nat)
  deriving Repr, Inhabited, BEq

def alignTo (n a : Nat) : Nat := (n + a - 1) / a * a

/-- Argument locations for integer parameters of the given byte sizes: `x0..x7`, then 8-byte
(at least) naturally aligned stack slots; and the stack-argument space rounded up to 16. -/
def argLocs (bytes : List Nat) : List ArgLoc × Nat :=
  let (locs, _, stack) := bytes.foldl (init := (#[], 0, 0)) fun (acc, nx, st) b =>
    if nx < 8 then (acc.push (.reg (.x nx)), nx + 1, st)
    else
      let size := max b 8
      let off := alignTo st size
      (acc.push (.stack off), nx, off + size)
  (locs.toList, alignTo stack 16)

/-- Return registers: `x0..x7` (more than 8 return values is a Cranelift error without
`enable_multi_ret_implicit_sret`). -/
def retRegs (n : Nat) : Option (List Reg) :=
  if n ≤ 8 then some ((List.range n).map .x) else none

/-- The parameters a call or entry passes in registers/stack slots (`compute_arg_locs`,
AAPCS64): a `normal`/`vmctx` parameter takes the next of x0..x7, then 8-byte-minimum
naturally aligned stack slots; a **`sret`** parameter is the hidden struct-return pointer,
in **x8** (Cranelift's aarch64 `compute_arg_locs`: the sret slot does not consume the
x0..x7 sequence and must be pointer-sized). -/
def sigArgs (s : Clif.Signature) : Except String (List Nat) :=
  s.params.mapM fun p =>
    if p.ty == .i128 then throw "i128 parameter"
    else match p.purpose with
      | .normal | .vmctx => pure p.ty.bytes
      | .sret => if p.ty == .i64 then pure 8 else throw "sret parameter must be i64"
      | _ => throw "special-purpose parameter (sarg)"

/-- The argument locations of a signature: `argLocs` over the normal parameters, with every
`sret` parameter in x8 (in parameter order). -/
def sigArgLocs (s : Clif.Signature) : Except String (List ArgLoc × Nat) := do
  let bytes ← sigArgs s
  let (locs, stack) := argLocs bytes
  if s.params.any (·.purpose == .sret) then
    if s.params.length != locs.length then throw "sigArgLocs: length"
    let locs := s.params.zip locs |>.map fun (p, loc) =>
      if p.purpose == .sret then .reg (.x 8) else loc
    pure (locs, stack)
  else pure (locs, stack)

/-- The returns of a signature as the ABI sees them (`from_func_sig` /
`ensure_struct_return_ptr_is_returned`, which is `keep in sync` in Cranelift's abi.rs): a
signature with an `sret` parameter and no returns returns the struct pointer in x0, i.e.
its only ABI return is the sret parameter itself. -/
def sigRets (s : Clif.Signature) : List Clif.AbiParam :=
  match s.params.find? (·.purpose == .sret) with
  | some p => if s.returns.isEmpty then [p] else s.returns
  | none => s.returns

/-- Parameter types of a signature (only integer `normal`/`vmctx` parameters up to 64 bits). -/
def sigParamBytes (s : Clif.Signature) : Except String (List Nat) := sigArgs s

def storeOpOfBytes : Nat → StoreOp
  | 1 => .store8 | 2 => .store16 | 4 => .store32 | _ => .store64

def loadOpOfBytes : Nat → LoadOp
  | 1 => .uload8 | 2 => .uload16 | 4 => .uload32 | _ => .uload64

/-- `MemFlagsData::trusted()`: `notrap aligned`. -/
def trustedFlags : Clif.MemFlags := { trapCode := none, aligned := true }

/-! ## Extern helpers -/

section Helpers
variable (ctx : Ctx)

def Ctx.valueType? (v : Nat) : Option CTy := (ctx.valTy[v]?).join
def Ctx.defInst? (v : Nat) : Option Nat := (ctx.valDef[v]?).join
def Ctx.defClif? (v : Nat) : Option Clif.Inst := do
  let i ← ctx.defInst? v
  (← ctx.insts[i]?).clif
def Ctx.valueReg? (v : Nat) : Option Reg := (ctx.valReg[v]?).join

end Helpers

/-- Keep an ISLE integer literal in the range of its ISLE type. -/
def normInt (ty : TypeId) (i : Int) : Int :=
  match (program.type? ty).map (·.kind) with
  | some (Isle.TypeKind.int t) =>
    let (w, signed) : Nat × Bool := match t with
      | .u8 => (8, false) | .u16 => (16, false) | .u32 => (32, false) | .u64 => (64, false)
      | .u128 => (128, false) | .usize => (64, false) | .i8 => (8, true) | .i16 => (16, true)
      | .i32 => (32, true) | .i64 => (64, true) | .i128 => (128, true) | .isize => (64, true)
    let m := i % (2 ^ w : Int)
    if signed && m ≥ (2 ^ (w - 1) : Int) then m - 2 ^ w else m
  | _ => i

/-- Sign-extend the low `bits` bits of `i` (`sign_extend_from_width`). -/
def sextFrom (bits : Nat) (i : Int) : Int :=
  if bits = 0 then i else
  let m := i % (2 ^ bits : Int)
  if m ≥ (2 ^ (bits - 1) : Int) then m - 2 ^ bits else m

/-- `u64` view of an `i64`/`Imm64`. -/
def u64 (i : Int) : Nat := (i % (2 ^ 64 : Int)).toNat

/-- Extern `Type → Option Type` predicates of `isle_prelude.rs` / `aarch64/lower/isle.rs`, by
term id (no dynamic vectors exist here: `is_dynamic_vector` is false). -/
def tyPred : TermId → Option (CTy → Bool)
  | TId.fits_in_16 => some fun t => t.bits ≤ 16
  | TId.fits_in_32 => some fun t => t.bits ≤ 32
  | TId.fits_in_64 => some fun t => t.bits ≤ 64
  | TId.ty_int_ref_scalar_64 | TId.ty_int_ref_scalar_64_extract =>
    some fun t => t.bits ≤ 64 && !t.isFloat && !t.isVector
  | TId.ty_32_or_64 => some fun t => t.bits == 32 || t.bits == 64
  | TId.ty_8_or_16 => some fun t => t.bits == 8 || t.bits == 16
  | TId.ty_16_or_32 => some fun t => t.bits == 16 || t.bits == 32
  | TId.ty_16 => some fun t => t.bits == 16
  | TId.ty_32 => some fun t => t.bits == 32
  | TId.ty_64 => some fun t => t.bits == 64
  | TId.ty_128 => some fun t => t.bits == 128
  | TId.ty_int => some CTy.isInt
  | TId.ty_scalar => some fun t => t.laneCount == 1
  | TId.ty_scalar_float => some CTy.isFloat
  | TId.ty_float_or_vec => some fun t => t.isFloat || t.isVector
  | TId.ty_vector_float => some fun t => match t with | .vec _ _ f => f | _ => false
  | TId.ty_vector_not_float => some fun t => match t with | .vec _ _ f => !f | _ => false
  | TId.ty_vec64 => some fun t => t.isVector && t.bits == 64
  | TId.ty_vec128 => some fun t => t.isVector && t.bits == 128
  | TId.ty_vec64_int => some fun t => match t with | .vec _ _ f => !f && t.bits == 64 | _ => false
  | TId.ty_vec128_int => some fun t => match t with | .vec _ _ f => !f && t.bits == 128 | _ => false
  | TId.ty_dyn_vec64 | TId.ty_dyn_vec128 | TId.ty_dyn64_int | TId.ty_dyn128_int => some fun _ => false
  | TId.lane_fits_in_32 => some fun t => t.isVector && t.laneBits ≤ 32
  | TId.int_fits_in_32 => some fun t => t == .int 8 || t == .int 16 || t == .int 32
  | TId.ty_int_ref_64 => some fun t => t == .int 64
  | TId.ty_int_ref_16_to_64 => some fun t => t == .int 16 || t == .int 32 || t == .int 64
  | TId.integral_ty | TId.valid_atomic_transaction =>
    some fun t => t == .int 8 || t == .int 16 || t == .int 32 || t == .int 64
  | _ => none

/-- The variant index of an `IntCC` value. -/
def V.intcc? : V → Option Nat := V.enum? tyIntCC some

open Isle (ExtResult) in
/-- Extern extractors: the input value to the term's argument values. Dispatch is on the term
id (`Isle.Aarch64.TId.*`, generated), a `Nat`-literal match. -/
def externExtract (ctx : Ctx) (t : Term) (v : V) (_st : LState) : ExtResult (List V) :=
  match tyPred t.id, v with
  | some p, .ty ty => if p ty then .ok [.ty ty] else .fail
  | some _, _ => .unmodeled s!"{t.name} on a non-type"
  | none, _ =>
  match t.id, v with
  | TId.def_inst, .value n => match ctx.defInst? n with
    | some i => .ok [.inst i]
    | none => .fail
  | TId.value_type, .value n => match ctx.valueType? n with
    | some ty => .ok [.ty ty]
    | none => .unmodeled s!"value_type of unknown v{n}"
  | TId.inst_data_value, .inst i => match ctx.insts[i]? with
    | some info => .ok [.ty (info.resTys.head?.getD .invalid), info.data]
    | none => .unmodeled s!"inst {i}"
  | TId.first_result, .inst i => match ctx.insts[i]? with
    | some info => match info.results.head? with
      | some r => .ok [.value r]
      | none => .fail
    | none => .unmodeled s!"inst {i}"
  | TId.is_second_result, .value n => match ctx.defInst? n >>= (ctx.insts[·]?) with
    | some info => if info.results[1]? == some n then .ok [.value n] else .fail
    | none => .fail
  | TId.i64_from_iconst, .value n => match ctx.defClif? n with
    | some (.iconst ty imm) => .ok [.int (sextFrom ty.width (imm64OfIconst ty imm))]
    | _ => .fail
  | TId.maybe_uextend, .value n => match ctx.defClif? n with
    | some (.extend .uextend _ x) => .ok [.value x]
    | _ => .ok [.value n]
  | TId.extended_value_from_value, .value n => match ctx.defClif? n with
    | some (.extend op _ x) =>
      match ctx.valueType? x with
      | some (.int b) =>
        let e : Option ExtendOp := match op, b with
          | .sextend, 8 => some .sxtb | .uextend, 8 => some .uxtb
          | .sextend, 16 => some .sxth | .uextend, 16 => some .uxth
          | .sextend, 32 => some .sxtw | .uextend, 32 => some .uxtw
          | _, _ => none
        match e with
        | some e => .ok [.op (.extended x e)]
        | none => .unmodeled "get_as_extended_value: bad width"
      | _ => .unmodeled "get_as_extended_value: operand type"
    | _ => .fail
  | TId.little_or_native_endian, .op (.memFlags f) =>
    if f.endianness == some .big then .fail else .ok [.op (.memFlags f)]
  | TId.u64_from_imm64, .int i => .ok [.int (u64 i)]
  | TId.nonzero_u64_from_imm64, .int i => if i == 0 then .fail else .ok [.int (u64 i)]
  | TId.imm12_from_u64, .int i => match Imm12.ofNat? (u64 i) with
    | some imm => .ok [.op (.imm12 imm)]
    | none => .fail
  | TId.i32_from_i64, .int i => if -(2 ^ 31 : Int) ≤ i ∧ i < 2 ^ 31 then .ok [.int i] else .fail
  | TId.u8_from_u64, .int i => if 0 ≤ i ∧ i < 256 then .ok [.int i] else .fail
  | TId.single_target, .labels [l] => .ok [.label l]
  | TId.single_target, .labels _ => .fail
  | TId.two_targets, .labels [a, b] => .ok [.label a, .label b]
  | TId.two_targets, .labels _ => .fail
  | TId.jump_table_targets, .labels (d :: ts) => .ok [.label d, .labels ts]
  | TId.jump_table_targets, .labels [] => .fail
  | TId.value_list_slice, .values vs => .ok [.values vs]
  | TId.value_slice_unwrap, .values (x :: xs) => .ok [.value x, .values xs]
  | TId.value_slice_unwrap, .values [] => .fail
  | TId.value_array_2, .values [a, b] => .ok [.value a, .value b]
  -- `unpack_value_array_3` (isle_prelude.rs:942)
  | TId.value_array_3, .values [a, b, c] => .ok [.value a, .value b, .value c]
  -- `symbol_value_data` (machinst/isle.rs:397, `Lower::symbol_value_data` lower.rs:1510):
  -- `Symbol { name, offset, colocated }` → `(name, Near iff colocated, offset)`, else `None`
  | TId.symbol_value_data, .op (.globalValue gv) => match ctx.func.globals.lookup gv with
    | some (.symbol name off colocated) =>
      .ok [.op (.extName name),
           .data tyRelocDistance (if colocated then VIdx.RelocDistance.Near else VIdx.RelocDistance.Far) [],
           .int off]
    | _ => .fail
  | TId.block_array_2, .blockCalls [a, b] => .ok [.blockCalls [a], .blockCalls [b]]
  | TId.func_ref_data, .op (.funcRef fn) => match ctx.func.extern? fn with
    | some ext =>
      .ok [.op (.sig ext.sig), .op (.extName ext.name),
           .data tyRelocDistance (if ext.colocated then VIdx.RelocDistance.Near else VIdx.RelocDistance.Far) [],
           .bool false]
    | none => .unmodeled s!"fn{fn}"
  -- `lane_count() > 1` / `is_dynamic_vector()`
  | TId.multi_lane, .ty ty =>
    if ty.laneCount > 1 then .ok [.int ty.laneBits, .int ty.laneCount] else .fail
  | TId.dynamic_lane, .ty _ => .fail
  | TId.not_i64x2, .ty ty => if ty == .vec 64 2 false then .fail else .ok []
  -- aarch64 ISA flags: every extension is off by default (`has_lse`, `has_dotprod`, ...).
  | TId.use_lse, .inst _ | TId.use_dotprod, .inst _ | TId.use_i8mm, .inst _ => .fail
  | TId.sign_return_address_disabled, _ => .ok []
  -- shared flag `tls_model`, default `none`
  | TId.tls_model, .ty _ => .ok [.data tyTlsModel VIdx.TlsModel.None []]
  | _, v => .unmodeled s!"extractor {t.name} on {(repr v).pretty.take 60}"

/-- `load_constant_full` (`aarch64/lower/isle.rs`): a `movz`/`movn` and `movk`s. -/
def loadConstantFull (bits : Nat) (signExt : Bool) (extendTo : OperandSize) (value : Nat)
    (st : LState) : Reg × LState :=
  let value := mask64 value
  let value :=
    match extendTo, signExt with
    | .size32, true => if bits < 32 then u64 (sextFrom bits value) % 2 ^ 32 else value
    | .size32, false => if bits < 32 then value % 2 ^ bits else value
    | .size64, true => if bits < 64 then u64 (sextFrom bits value) else value
    | .size64, false => if bits < 64 then value % 2 ^ bits else value
  let get (v : Nat) (sh : Nat) : Nat := (v / 2 ^ (sh * 16)) % 2 ^ 16
  let replace (old new sh : Nat) : Nat := old - get old sh * 2 ^ (sh * 16) + new * 2 ^ (sh * 16)
  let size : OperandSize := if value / 2 ^ 32 == 0 then .size32 else .size64
  let nslices := size.bits / 16
  let maxv := 2 ^ size.bits - 1
  let cand (op : MoveWideOp) (base : Nat) : Nat × MoveWideOp × Nat :=
    let first := ((List.range nslices).find? fun i => get (Nat.xor base value) i != 0).getD 0
    (replace base (get value first) first, op, first)
  let cz := cand .movZ 0
  let cn := cand .movN maxv
  let cnt (b : Nat) := ((List.range 4).filter fun i => get (Nat.xor b value) i != 0).length
  let (running, op, first) := if cnt cn.1 < cnt cz.1 then cn else cz
  let (rd, st) := st.fresh .int
  let imm : MoveWideConst :=
    ⟨match op with | .movZ => get value first | .movN => 2 ^ 16 - 1 - get value first, first⟩
  let st := st.emit (.movWide op rd imm size)
  let (rd, st, _) := (List.range nslices).foldl (init := (rd, st, running)) fun (rd, st, run) sh =>
    if sh ≤ first then (rd, st, run) else
    let b := get value sh
    if b != get run sh then
      let (rd', st) := st.fresh .int
      (rd', st.emit (.movK rd' rd ⟨b, sh⟩ size), replace run b sh)
    else (rd, st, run)
  (rd, st)

/-- `V` of a `ValueRegsVec` entry list. -/
def regsOf? : V → Option (List (List Reg))
  | .regsVec rss => some rss
  | _ => none

open Isle (ExtResult) in
/-- Extern constructors, dispatched on the term id (`Isle.Aarch64.TId.*`). -/
def externCtor (ctx : Ctx) (t : Term) (args : List V) (st : LState) : ExtResult (V × LState) :=
  let ok (v : V) : ExtResult (V × LState) := .ok (v, st)
  let optOk (o : Option V) : ExtResult (V × LState) := match o with
    | some v => .ok (v, st)
    | none => .fail
  match tyPred t.id, args with
  | some p, [.ty ty] => if p ty then ok (.ty ty) else .fail
  | _, _ =>
  match t.id, args with
  -- prelude.isle / isle_prelude.rs
  | TId.i64_sextend_imm64, [.ty ty, .int x] => ok (.int (sextFrom ty.bits x))
  | TId.ty_bits, [.ty ty] => ok (.int ty.bits)
  | TId.ty_bytes, [.ty ty] => ok (.int ty.bytes)
  | TId.offset32_to_i32, [.int i] => ok (.int i)
  | TId.i32_to_offset32, [.int i] => ok (.int i)
  | TId.signed_cond_code, [cc] => match cc.intcc? with
    | some n => if [VIdx.IntCC.SignedGreaterThanOrEqual, VIdx.IntCC.SignedGreaterThan,
        VIdx.IntCC.SignedLessThanOrEqual, VIdx.IntCC.SignedLessThan].contains n then ok cc else .fail
    | none => .unmodeled "signed_cond_code"
  | TId.unsigned_cond_code, [cc] => match cc.intcc? with
    | some n => if [VIdx.IntCC.Equal, VIdx.IntCC.UnsignedGreaterThanOrEqual,
        VIdx.IntCC.UnsignedGreaterThan, VIdx.IntCC.UnsignedLessThanOrEqual,
        VIdx.IntCC.UnsignedLessThan, VIdx.IntCC.NotEqual].contains n then ok cc else .fail
    | none => .unmodeled "unsigned_cond_code"
  | TId.trap_code_division_by_zero, [] => ok (.op (.trapCode .intDivz))
  | TId.trap_code_integer_overflow, [] => ok (.op (.trapCode .intOvf))
  | TId.safe_divisor_from_imm64, [.ty ty, .int v] =>
    let minusOne : Nat := 2 ^ (ty.bytes * 8) - 1
    let bits := u64 v % 2 ^ (ty.bytes * 8)
    if bits == 0 || bits == minusOne then .fail else ok (.int bits)
  -- prelude_lower.isle / machinst/isle.rs
  | TId.value_reg, [.reg r] => ok (.regs [r])
  | TId.value_regs, [.reg a, .reg b] => ok (.regs [a, b])
  | TId.output_none, [] => ok (.regsVec [])
  | TId.output, [.regs rs] => ok (.regsVec [rs])
  | TId.output_vec, [.regsVec rss] => ok (.regsVec rss)
  | TId.temp_writable_reg, [.ty ty] => match ty.regClass? with
    | some cls => let (r, st) := st.fresh cls; .ok (.reg r, st)
    | none => .unmodeled s!"temp_writable_reg of {repr ty}"
  | TId.opportunistic_def, [_, _] => ok (.op .unit)
  | TId.put_in_reg, [.value n] => match ctx.valueReg? n with
    | some r => ok (.reg r)
    | none => .unmodeled s!"put_in_reg v{n}"
  | TId.put_in_regs, [.value n] => match ctx.valueReg? n with
    | some r => ok (.regs [r])
    | none => .unmodeled s!"put_in_regs v{n}"
  | TId.put_in_regs_vec, [.values vs] => match vs.mapM ctx.valueReg? with
    | some rs => ok (.regsVec (rs.map fun r => [r]))
    | none => .unmodeled "put_in_regs_vec"
  | TId.value_regs_get, [.regs rs, .int i] => match rs[i.toNat]? with
    | some r => ok (.reg r)
    | none => .unmodeled "value_regs_get index"
  | TId.jump_table_size, [.labels ls] => ok (.int ls.length)
  | TId.writable_reg_to_reg, [r] => ok r
  -- `invalid_reg` (machinst/isle.rs:107): `Reg::invalid_sentinel()`
  | TId.invalid_reg, [] => ok (.reg Reg.invalid)
  | TId.is_sinkable_inst, [_] => .fail
  | TId.emit, [i] => match MInst.ofV i with
    | some m => .ok (.op .unit, st.emit m)
    | none => .unmodeled s!"emit of {((i.variant?).map (·.2.1)).getD "?"}"
  | TId.box_external_name, [n] => ok n
  | TId.abi_sig, [s] => ok s
  | TId.abi_stackslot_addr, [rd, .op (.stackSlot s), .int off] =>
    match ctx.slotOff.lookup s with
    | some base =>
      ok (.data tyMInst VIdx.MInst.LoadAddr [rd, .data tyAMode VIdx.AMode.SlotOffset [.int (base + off)]])
    | none => .unmodeled s!"stack slot ss{s}"
  | TId.abi_stackslot_offset_into_slot_region, [.op (.stackSlot s), .int a, .int b] =>
    match ctx.slotOff.lookup s with
    | some base => ok (.int (base + a + b))
    | none => .unmodeled s!"stack slot ss{s}"
  | TId.gen_return, [.regsVec rss] =>
    match retRegs rss.length, rss.mapM (fun | [r] => some r | _ => none) with
    | some ps, some rs => .ok (.op .unit, st.emit (.rets (rs.zip ps)))
    | _, _ => .unmodeled "gen_return: more than 8 return values or multi-register values"
  | TId.gen_call_output, [.op (.sig s)] =>
    let (rs, st) := (sigRets s).foldl (init := (#[], st)) fun (acc, st) _ =>
      let (r, st) := st.fresh .int
      (acc.push [r], st)
    .ok (.regsVec rs.toList, st)
  | TId.gen_call_args, [.op (.sig s), .regsVec rss] =>
    match sigArgLocs s, rss.mapM (fun | [r] => some r | _ => none) with
    | .ok (locs, _), some rs =>
      let bytes := match sigArgs s with | .ok b => b | _ => []
      let (uses, st) := ((locs.zip rs).zip bytes).foldl (init := (#[], st))
        fun (acc, st) ((loc, r), b) => match loc with
          | .reg p => (acc.push (r, p), st)
          | .stack off => (acc, st.emit (.store (storeOpOfBytes b) r (.spOffset off) trustedFlags))
      .ok (.op (.callArgs uses.toList), st)
    | .error e, _ => .unmodeled s!"gen_call_args: {e}"
    | _, none => .unmodeled "gen_call_args: multi-register value"
  | TId.gen_call_rets, [.op (.sig _), .regsVec rss] =>
    match retRegs rss.length, rss.mapM (fun | [r] => some r | _ => none) with
    | some ps, some rs => ok (.op (.callRets (ps.zip rs)))
    | _, _ => .unmodeled "gen_call_rets: more than 8 return values"
  | TId.try_call_none, [] => ok (.op .tryCallNone)
  | TId.gen_call_info, [.op (.sig s), .op (.extName n), .op (.callArgs us), .op (.callRets ds), _, _] =>
    match sigArgLocs s with
    | .ok (_, stack) =>
      .ok (.op (.callInfo ⟨.sym n, us, ds⟩), { st with outgoing := max st.outgoing stack })
    | .error e => .unmodeled s!"gen_call_info: {e}"
  | TId.gen_call_ind_info, [.op (.sig s), .reg r, .op (.callArgs us), .op (.callRets ds), _] =>
    match sigArgLocs s with
    | .ok (_, stack) =>
      .ok (.op (.callInfo ⟨.reg r, us, ds⟩), { st with outgoing := max st.outgoing stack })
    | .error e => .unmodeled s!"gen_call_ind_info: {e}"
  -- aarch64 inst.isle / lower.isle helpers (aarch64/lower/isle.rs)
  | TId.use_fp16, [] => ok (.bool false)
  | TId.is_pic, [] => ok (.bool true)
  | TId.move_wide_const_from_u64, [.ty ty, .int n] =>
    let n := if ty.bits < 64 then u64 n % 2 ^ ty.bits else u64 n
    optOk ((MoveWideConst.ofNat? n).map (.op ∘ .moveWideConst))
  | TId.move_wide_const_from_inverted_u64, [.ty ty, .int n] =>
    let n := 2 ^ 64 - 1 - u64 n
    let n := if ty.bits < 64 then n % 2 ^ ty.bits else n
    optOk ((MoveWideConst.ofNat? n).map (.op ∘ .moveWideConst))
  | TId.imm_logic_from_u64, [.ty ty, .int n] =>
    if ty == .int 32 || ty == .int 64 then
      optOk ((ImmLogic.ofNat? (u64 n) (.ofBits ty.bits)).map (.op ∘ .immLogic))
    else .fail
  | TId.imm_size_from_type, [.ty ty] =>
    if ty == .int 32 then ok (.int 32) else if ty == .int 64 then ok (.int 64) else .fail
  | TId.imm_logic_from_imm64, [.ty ty, .int n] =>
    let ty := if ty.bits < 32 then CTy.int 32 else ty
    if ty == .int 32 || ty == .int 64 then
      optOk ((ImmLogic.ofNat? (u64 n) (.ofBits ty.bits)).map (.op ∘ .immLogic))
    else .fail
  | TId.imm_shift_from_imm64, [.ty ty, .int n] =>
    let v := Nat.land (u64 n) (ty.bits - 1)
    if v < 64 then ok (.op (.immShift v)) else .fail
  | TId.imm_shift_from_u8, [.int n] => if n < 64 then ok (.op (.immShift n.toNat)) else .fail
  | TId.u8_into_uimm5, [.int n] => if n < 32 then ok (.op (.uimm5 n.toNat)) else .fail
  | TId.u8_into_imm12, [.int n] => optOk ((Imm12.ofNat? n.toNat).map (.op ∘ .imm12))
  | TId.u64_into_imm_logic, [.ty ty, .int n] =>
    if ty == .int 32 || ty == .int 64 then
      optOk ((ImmLogic.ofNat? (u64 n) (.ofBits ty.bits)).map (.op ∘ .immLogic))
    else .fail
  | TId.branch_target, [.label l] => ok (.label l)
  | TId.targets_jt_space, [.labels ls] => ok (.int (4 * (8 + ls.length)))
  | TId.lshl_from_imm64, [.ty ty, .int n] =>
    match shiftImm? (u64 n) with
    | some s => if ty.bits ≤ 255 then ok (.op (.shiftOpAndAmt ⟨.lsl, Nat.land s (ty.bits - 1)⟩))
      else .fail
    | none => .fail
  | TId.ashr_from_u64, [.ty ty, .int n] =>
    match shiftImm? n.toNat with
    | some s => if ty.bits ≤ 255 then ok (.op (.shiftOpAndAmt ⟨.asr, Nat.land s (ty.bits - 1)⟩))
      else .fail
    | none => .fail
  | TId.put_extended_in_reg, [.op (.extended x _)] => match ctx.valueReg? x with
    | some r => ok (.reg r)
    | none => .unmodeled "put_extended_in_reg"
  | TId.get_extended_op, [.op (.extended _ e)] => ok (.data tyExtendOp e.idx [])
  | TId.nzcv, [.bool n, .bool z, .bool c, .bool v] => ok (.op (.nzcv ⟨n, z, c, v⟩))
  | TId.cond_br_zero, [r, s] => ok (.data tyCondBrKind VIdx.CondBrKind.Zero [r, s])
  | TId.cond_br_not_zero, [r, s] => ok (.data tyCondBrKind VIdx.CondBrKind.NotZero [r, s])
  | TId.cond_br_cond, [c] => ok (.data tyCondBrKind VIdx.CondBrKind.Cond [c])
  | TId.zero_reg, [] => ok (.reg .xzr)
  | TId.writable_zero_reg, [] => ok (.reg .xzr)
  | TId.a64_extr_imm, [.ty ty, .op (.immShift s)] =>
    if ty == .int 32 then ok (.op (.shiftOpAndAmt ⟨.lsl, s⟩))
    else if ty == .int 64 then ok (.op (.shiftOpAndAmt ⟨.lsr, s⟩))
    else .fail
  | TId.load_constant_full, [.ty ty, ext, sz, .int v] =>
    match ext.enumOf? tyImmExtend, sz.size? with
    | some (e, _), some size =>
      let (r, st) := loadConstantFull ty.bits (e == VIdx.ImmExtend.Sign) size (u64 v) st
      .ok (.reg r, st)
    | _, _ => .unmodeled "load_constant_full"
  | TId.uimm12_scaled_from_i64, [.int v, .ty ty] =>
    optOk ((uimm12Scaled? v ty.bytes).map (.op ∘ .uimm12Scaled))
  | TId.uimm12_scaled_nonzero_from_i64, [.int v, .ty ty] =>
    if v == 0 then .fail else optOk ((uimm12Scaled? v ty.bytes).map (.op ∘ .uimm12Scaled))
  | TId.simm9_from_i64, [.int v] => optOk ((simm9? v).map (.op ∘ .simm9))
  | TId.cond_code, [cc] => match cc.intcc? >>= condOfIntCC with
    | some c => ok (.data tyCond c.idx [])
    | none => .unmodeled "cond_code"
  | TId.invert_cond, [c] => match c.cond? with
    | some c => ok (.data tyCond c.invert.idx [])
    | none => .unmodeled "invert_cond"
  | TId.shift_masked_imm, [.ty ty, .int n] => ok (.int (Nat.land (u64 n % 256) (ty.laneBits - 1)))
  | TId.shift_mask, [.ty ty] => optOk ((ImmLogic.ofNat? (ty.laneBits - 1) .size32).map (.op ∘ .immLogic))
  | TId.bfm_immr, [.ty ty, .int a, .int b] =>
    let w := ty.laneBits
    let a := Nat.land (u64 a % 256) (w - 1)
    let b := Nat.land (u64 b % 256) (w - 1)
    ok (.op (.uimm6 (if a ≤ b then b - a else w - (a - b))))
  | TId.bfm_imms, [.ty ty, .int a, .int _] =>
    let w := ty.laneBits
    let a := Nat.land (u64 a % 256) (w - 1)
    ok (.op (.uimm6 (w - 1 - a)))
  | TId.negate_imm_shift, [.ty ty, .op (.immShift s)] =>
    let size := ty.bits
    ok (.op (.immShift (Nat.land ((size + 256 - s) % 256) (size - 1))))
  | TId.rotr_mask, [.ty ty] => optOk ((ImmLogic.ofNat? (ty.bits - 1) .size32).map (.op ∘ .immLogic))
  | TId.rotr_opposite_amount, [.ty ty, .op (.immShift s)] =>
    let amount := Nat.land s (ty.bits - 1)
    let r := ty.bits - amount
    if r < 64 then ok (.op (.immShift r)) else .fail
  | TId.test_and_compare_bit_const, [.ty ty, .int n] =>
    let n := u64 n
    let ones := (List.range 64).filter (n.testBit ·)
    match ones with
    | [bit] => if bit < ty.bits then ok (.int bit) else .fail
    | _ => .fail
  -- numerics.isle (generated `isle_numerics.rs`)
  | TId.i32_checked_add, [.int a, .int b] =>
    let s := a + b
    if -(2 ^ 31 : Int) ≤ s ∧ s < 2 ^ 31 then ok (.int s) else .fail
  | TId.i64_checked_neg, [.int a] => if a == -(2 ^ 63 : Int) then .fail else ok (.int (-a))
  | TId.u64_eq, [.int a, .int b] => ok (.bool (a == b))
  | TId.u64_gt, [.int a, .int b] => ok (.bool (a > b))
  | TId.u64_wrapping_add, [.int a, .int b] => ok (.int (u64 (a + b)))
  | TId.u64_wrapping_sub, [.int a, .int b] => ok (.int (u64 (a - b)))
  | TId.u64_wrapping_shl, [.int a, .int b] => ok (.int (u64 (a * 2 ^ (b.toNat % 64))))
  | TId.u64_is_odd, [.int a] => ok (.bool (a % 2 == 1))
  | TId.u8_into_u32, [.int a] | TId.u8_into_u64, [.int a] | TId.u16_into_u64, [.int a]
  | TId.i32_into_i64, [.int a] | TId.u32_into_u64, [.int a] => ok (.int a)
  | TId.i64_cast_unsigned, [.int a] => ok (.int (u64 a))
  -- clif_lower.isle
  | TId.value_array_2, [.value a, .value b] => ok (.values [a, b])
  -- `pack_value_array_3` (isle_prelude.rs:948)
  | TId.value_array_3, [.value a, .value b, .value c] => ok (.values [a, b, c])
  | TId.block_array_2, [.blockCalls a, .blockCalls b] => ok (.blockCalls (a ++ b))
  | _, args => .unmodeled s!"constructor {t.name} ({args.length} args)"

/-- The embedding: ISLE constants, data, and the extern helpers. -/
def sem (ctx : Ctx) : Isle.Sem V LState where
  int ty i := .int (normInt ty i)
  bool b := .bool b
  prim ty n := if ty == TyId.Type then (CTy.ofName? n).map .ty else none
  eq a b := a == b
  mkData ty k fs := .data ty k fs
  unData ty v := match v with
    | .data t k fs => if t == ty then some (k, fs) else none
    | _ => none
  ctor := externCtor ctx
  extract := externExtract ctx

/-! ## The lowering driver (`machinst/lower.rs`) -/

/-- A block of VCode. `params` are the block's parameter vregs (empty for the entry block,
whose parameters the `Args` pseudo-instruction and the stack-argument loads define);
`branchArgs` are the arguments of the block's terminating `jump` to its successor's
parameters (empty for every other terminator: branches with arguments to a target go
through an edge block). -/
structure VBlock where
  label : Label
  insts : Array MInst
  params : Array Reg := #[]
  branchArgs : Array Reg := #[]
  deriving Inhabited, Repr

/-- The selected code of one function, over virtual registers. -/
structure VCode where
  name : String
  blocks : Array VBlock
  /-- Class of every virtual register (index = vreg number). -/
  classes : Array RegClass
  /-- Size of the explicit stack-slot region. -/
  slotBytes : Nat
  outgoing : Nat
  /-- Rules fired, in firing order (Cranelift `trace-log` order). -/
  rulesFired : Array RuleId
  deriving Inhabited

/-- Stack-slot layout (`Callee::new`): slots in id order, each aligned to
`max(8, align)`. -/
def slotLayout (slots : List (Nat × Clif.StackSlot)) : List (Nat × Nat) × Nat :=
  let sorted := slots.toArray.qsort (fun a b => a.1 < b.1) |>.toList
  let (offs, end_) := sorted.foldl (init := (#[], 0)) fun (acc, e) (id, s) =>
    let align := max 8 (s.align.getD 1)
    let start := alignTo e align
    (acc.push (id, start), start + s.size)
  (offs.toList, end_)

/-- Build the lowering context of a function: instruction table (statements, then the
terminator, block by block), value types/definitions, and one vreg per value. -/
def buildCtx (f : Clif.Function) : Except String (Ctx × Array (Nat × Nat) × LState) := do
  let sigOf (r : Nat) : Option Clif.Signature := (f.extern? r).map (·.sig)
  -- value ids and types
  let mut maxV := 0
  for b in f.blocks do
    for (v, _) in b.params do maxV := max maxV (v + 1)
    for s in b.body do
      for r in s.results do maxV := max maxV (r + 1)
  let mut valTy : Array (Option CTy) := Array.replicate maxV none
  let mut valDef : Array (Option Nat) := Array.replicate maxV none
  let mut insts : Array IInfo := #[]
  -- (block index → range of instruction indices [start, end))
  let mut ranges : Array (Nat × Nat) := #[]
  for b in f.blocks do
    for (v, ty) in b.params do
      if ty == .i128 then throw s!"block parameter v{v} is i128"
      valTy := valTy.set! v (some (CTy.ofClif ty))
    let start := insts.size
    for s in b.body do
      let data ← instData f s.inst
      let some tys := s.inst.resultTypes sigOf (f.sigDecls.lookup ·) |
        throw "ill-typed instruction"
      if tys.length != s.results.length then throw "result count mismatch"
      for (r, ty) in s.results.zip tys do
        if ty == .i128 then throw s!"value v{r} is i128"
        valTy := valTy.set! r (some (CTy.ofClif ty))
        valDef := valDef.set! r (some insts.size)
      insts := insts.push ⟨data, s.results, tys.map CTy.ofClif, some s.inst⟩
    -- terminator (data filled in by the driver; placeholder here)
    insts := insts.push ⟨.op .unit, [], [], none⟩
    ranges := ranges.push (start, insts.size)
  -- Addresses are `i64` on aarch64 (the Cranelift verifier rejects narrower pointers).
  for info in insts do
    let addr? : Option Nat := match info.clif with
      | some (.load _ _ _ p _) | some (.store _ _ _ _ p _) => some p
      | _ => none
    if let some p := addr? then
      if (valTy[p]?).join != some (.int 64) then
        throw s!"`{instText info.clif.get!}`: address v{p} is not i64 (pointer width 64)"
  -- value registers: vreg n for value n
  let valReg : Array (Option Reg) := (Array.range maxV).map fun v =>
    if (valTy[v]?).join.isSome then some (.vreg v .int) else none
  let (slotOff, _) := slotLayout f.slots
  let ctx : Ctx := { func := f, insts, valTy, valDef, valReg, slotOff }
  let st : LState := { nextVreg := maxV, classes := Array.replicate maxV .int }
  pure (ctx, ranges, st)

/-- Run the ISLE term `term` on `args`. -/
def runTerm (ctx : Ctx) (term : String) (args : List V) (st : LState) :
    Except String (Option V × LState × List RuleId) :=
  match Isle.Interp.run program (sem ctx) {} term args st with
  | .ok r => .ok (r.value, r.state, r.trace)
  | .error e => .error s!"ISLE {term}: {repr e}"

/-- The `InstructionData` of a terminator. -/
def termData (t : Clif.Terminator) : Except String V :=
  match t with
  | .jump _ => pure (instDataV "Jump" [opcodeV "Jump", .blockCalls [0]])
  | .brif c _ _ => pure (instDataV "Brif" [opcodeV "Brif", .value c, .blockCalls [0, 1]])
  | .brTable x _ _ => pure (instDataV "BranchTable" [opcodeV "BrTable", .value x, .op (.jumpTable 0)])
  | .ret vs => pure (instDataV "MultiAry" [opcodeV "Return", .values vs])
  | .trap c => pure (instDataV "Trap" [opcodeV "Trap", .op (.trapCode c)])
  | .returnCall .. => throw "return_call is not in E"

/-- Lowering state of the driver. -/
structure DState where
  st : LState
  /-- Alias of each vreg (`set_vreg_alias`). -/
  alias : Array (Option Reg)
  blocks : Array VBlock := #[]
  /-- Edge blocks to append after the function's blocks. -/
  edges : Array VBlock := #[]
  nextLabel : Nat
  rules : Array RuleId := #[]

/-- The argument vregs of a branch to `bc` (Cranelift's branch block arguments). -/
def blockArgRegs (ctx : Ctx) (f : Clif.Function) (bc : Clif.BlockCall) :
    Except String (Array Reg) := do
  let some tb := f.block? bc.block | throw s!"unknown block{bc.block}"
  if tb.params.length != bc.args.length then throw s!"block{bc.block}: argument count"
  bc.args.toArray.mapM fun a => match ctx.valueReg? a with
    | some r => pure r
    | none => throw s!"unknown value v{a}"

/-- Lower one function to VCode. -/
def lowerFunction (f : Clif.Function) : Except String VCode := do
  if !aapcsConv f.sig.callConv then
    throw s!"calling convention {repr f.sig.callConv}"
  let paramBytes ← sigParamBytes f.sig
  if f.sig.returns.any (·.ty == .i128) then throw "i128 return value"
  if f.sig.params.any (·.purpose == .sret) && !f.sig.returns.isEmpty then
    throw "sret parameter together with return values (Cranelift rejects this)"
  if (retRegs (sigRets f.sig).length).isNone then throw "more than 8 return values"
  let (ctx, ranges, st0) ← buildCtx f
  let blockIdx (b : Nat) : Except String Nat :=
    match f.blocks.findIdx? (·.id == b) with
    | some i => pure i
    | none => throw s!"unknown block{b}"
  let mut d : DState := { st := st0, alias := #[], nextLabel := f.blocks.length }
  for (b, bi) in f.blocks.zipIdx do
    let (start, stop) := ranges[bi]!
    let mut code : Array MInst := #[]
    -- gen_arg_setup
    if bi == 0 then
      let (locs, _) ← sigArgLocs f.sig
      let mut pairs : Array (Reg × Reg) := #[]
      for (((v, _), loc), bytes) in (b.params.zip locs).zip paramBytes do
        let some r := ctx.valueReg? v | throw s!"unknown value v{v}"
        match loc with
        | .reg p => pairs := pairs.push (r, p)
        | .stack off =>
          code := code.push (.load (loadOpOfBytes bytes) r (.fpOffset (16 + off)) trustedFlags)
      code := #[MInst.args pairs.toList] ++ code
    -- body
    for i in [start:stop - 1] do
      let info := ctx.insts[i]!
      let (out, st, n) ← runTerm ctx "lower" [.inst i] { d.st with emitted := #[] }
      let some (.regsVec rss) := out
        | throw s!"no lowering rule for {(repr info.clif).pretty.take 80}"
      -- `lower.rs:953` zips the outputs with the results; only `nop` (no results, one
      -- `invalid_reg` output) has a different count, and its output is dropped.
      if rss.length != info.results.length && !info.results.isEmpty then
        throw "lowering produced a wrong number of results"
      let mut st := st
      let mut extra : Array MInst := #[]
      for (r, rs) in info.results.zip rss do
        let some vr := ctx.valueReg? r | throw s!"unknown value v{r}"
        match rs with
        | [out@(.vreg ..)] =>
          let (.vreg n _) := vr | throw "value register is not virtual"
          let alias := if d.alias.size ≤ n then d.alias ++ Array.replicate (n + 1 - d.alias.size) none
            else d.alias
          d := { d with alias := alias.set! n (some out) }
        | [out] => extra := extra.push (.mov .size64 vr out)
        | _ => throw "multi-register result"
      code := code ++ st.emitted ++ extra
      st := { st with emitted := #[] }
      d := { d with st, rules := d.rules ++ n.toArray }
    -- terminator. An sret signature's only ABI return is the struct pointer in x0
    -- (`sigRets`); the CLIF `return` carries no values, so the legalized return value is
    -- the sret parameter, exactly what Cranelift's legalizer rewrites the terminator to.
    let sretParam : List Clif.ValueId :=
      if sigRets f.sig != f.sig.returns then
        match f.blocks.head?, f.sig.params.findIdx? (·.purpose == .sret) with
        | some b0, some i => (b0.params[i]?.map (·.1)).toList
        | _, _ => []
      else []
    let data ← match b.term with
      | .ret vs => termData (.ret (vs ++ sretParam))
      | _ => termData b.term
    if b.term matches .ret .. && sretParam.isEmpty && (sigRets f.sig != f.sig.returns) then
      throw "sret parameter is not an entry-block parameter"
    let ti := stop - 1
    let ctx' : Ctx := { ctx with insts := ctx.insts.set! ti ⟨data, [], [], none⟩ }
    let mut targets : Array Label := #[]
    let dests : List Clif.BlockCall := match b.term with
      | .jump bc => [bc]
      | .brif _ t e => [t, e]
      | .brTable _ dflt tbl => dflt :: tbl
      | _ => []
    let mut jumpArgs : Array Reg := #[]
    match b.term with
    | .jump bc =>
      jumpArgs ← blockArgRegs ctx f bc
      targets := targets.push (← blockIdx bc.block)
    | _ =>
      for bc in dests do
        let tl ← blockIdx bc.block
        if bc.args.isEmpty then targets := targets.push tl
        else
          let args ← blockArgRegs ctx f bc
          let l := d.nextLabel
          d := { d with nextLabel := l + 1,
                        edges := d.edges.push { label := l, insts := #[MInst.jump tl], branchArgs := args } }
          targets := targets.push l
    let (term, args) : String × List V := match b.term with
      | .ret _ | .trap _ => ("lower", [.inst ti])
      | _ => ("lower_branch", [.inst ti, .labels targets.toList])
    let (out, st, n) ← runTerm ctx' term args { d.st with emitted := #[] }
    if out.isNone then throw s!"no lowering rule for terminator {(repr b.term).pretty.take 80}"
    code := code ++ st.emitted
    let params ← if bi == 0 then pure #[] else
      b.params.toArray.mapM fun (v, _) => match ctx.valueReg? v with
        | some r => pure r
        | none => throw s!"unknown value v{v}"
    d := { d with st := { st with emitted := #[] }, rules := d.rules ++ n.toArray,
                  blocks := d.blocks.push { label := bi, insts := code, params, branchArgs := jumpArgs } }
  -- resolve aliases (chains are acyclic: an alias target is defined by the instruction that
  -- defines the aliased value, which only reads earlier values)
  let alias := d.alias
  let rec resolve (fuel : Nat) (r : Reg) : Reg :=
    match fuel, r with
    | 0, _ => r
    | fuel + 1, .vreg n _ => match (alias[n]?).join with
      | some r' => resolve fuel r'
      | none => r
    | _, _ => r
  let fuel := alias.size + 1
  let fixBlock (vb : VBlock) : VBlock :=
    { vb with insts := vb.insts.map (MInst.mapRegs (resolve fuel)),
              branchArgs := vb.branchArgs.map (resolve fuel) }
  let (_, slotBytes) := slotLayout f.slots
  pure { name := f.name, blocks := (d.blocks ++ d.edges).map fixBlock, classes := d.st.classes,
         slotBytes, outgoing := d.st.outgoing, rulesFired := d.rules }

end Backend
