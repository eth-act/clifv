import FV.Clif.Syntax
import FV.Isle.Interp
import FV.Isle.Generated.Opt.Program
import FV.Isle.Opt.Helpers

/-!
# Cranelift's mid-end `simplify` rules on CLIF e-graph nodes

`Isle.Opt.simplify` runs the exported mid-end rules (`Isle.Opt.program`, Cranelift 0.136.1
`opt` unit) on one e-class, through the multi-term interpreter (`Isle.Interp.runMultiTerm`).
The caller (the mid-end driver) supplies the e-graph as three callbacks:

* `enodes st v`: the pure defining nodes of the e-class `v`, as `Clif.Inst`s whose operands are
  e-class ids, in the order Cranelift's `InstDataEtorIter` would visit them. This is the
  multi-extractor `inst_data_value` (`src/opts.rs`).
* `typeOf st v`: the type of `v` (`DataFlowGraph::value_type`).
* `make st inst`: `make_inst` (`src/opts.rs` `make_inst_ctor` →
  `OptimizeCtx::insert_pure_enode`): insert a pure node, returning its e-class.

The result lists every rewrite candidate (in rule order, see `Isle.Interp.runMulti` for how this
differs from Cranelift's order and `MAX_ISLE_RETURNS` cap), with whether the rule marked it
`subsume` during this call, and the name of the rule that produced it.

**Embedding.** ISLE values are `Isle.Opt.V`. A `Value` is an e-class id. `Opcode`, `IntCC`,
`InstructionData` and the enums defined in ISLE are `V.data` over the generated variant
indices (`Isle.Opt.VIdx`). A node is presented to the rules as Cranelift's `InstructionData`
(`ofInst`): `iconst` as `UnaryImm` with its `Imm64` zero-extended from the type's width (as
Cranelift stores narrow `iconst` immediates), `icmp` as `IntCompare`, `select`/`bitselect` as
`Ternary`, and so on. Nodes without an `InstructionData` form here (loads, calls, `bitcast`,
two-result operations) are not presented; no closure rule matches them.

A node a rule builds that has no `Clif.Inst` form (a float or vector type, an `i128`
`iconst`, an opcode outside `Clif.Inst`) is a `V.poison` value instead of a call of `make`;
a candidate that is poison is dropped. (Cranelift would insert the node; the rules never
depend on it existing, since a poison value has no nodes.)

**Extern helpers.** `ctorFn` / `extractFn` dispatch on the Rust function name
(`Term.externCtor?`, `Term.externExtractor?`) to the transcriptions in `FV/Isle/Opt/Helpers.lean`.
Functions of the skeleton, float and vector paths that E programs never reach
(`zero_constant`, `f32_from_uint`, `inst_data_etor`, `just_trap_block`, ...) are unmodeled:
interpretation aborts with an error rather than guessing.
-/

namespace Isle.Opt
open Isle

/-- A side-effecting (skeleton) instruction, as `simplify_skeleton` sees it: an instruction
(`div`, `trapz`, `trapnz`, ...) or a terminator (`brif`, `br_table`, `jump`). -/
inductive SkelInst where
  | inst (i : Clif.Inst)
  | term (t : Clif.Terminator)
  deriving DecidableEq, Repr, Inhabited

/-- ISLE values of the mid-end embedding. -/
inductive V where
  /-- ISLE integers of every width, in the range of their Rust type; `Imm64` (its `i64`),
  `Offset32`, and the entity indices `StackSlot`, `GlobalValue`, `Block`. -/
  | int (i : Int)
  | bool (b : Bool)
  | ty (t : CTy)
  /-- A CLIF value (e-class id). -/
  | value (id : Nat)
  /-- A value built from a node that has no `Clif.Inst` form (not inserted; no nodes). -/
  | poison (t : CTy)
  /-- `ValueArray2` / `ValueArray3` / `BlockArray2`. -/
  | values (vs : List V)
  /-- `TypeAndInstructionData`. -/
  | pair (t : CTy) (d : V)
  /-- Enum variant `k` (or a struct, `k = 0`) of the ISLE type `ty`. -/
  | data (ty : TypeId) (k : Nat) (fields : List V)
  /-- `Inst`: a skeleton instruction (the one being simplified, or one `make_skeleton_inst`
  built; `none`: built but without a `SkelInst` form). -/
  | inst (i : Option SkelInst)
  | trapCode (c : Clif.TrapCode)
  | blockCall (b : Clif.BlockCall)
  /-- `JumpTable`: the default target and the table of a `br_table`. -/
  | jumpTable (default : Clif.BlockCall) (table : List Clif.BlockCall)
  deriving Repr, Inhabited

mutual
/-- Structural equality. -/
def V.beq : V → V → Bool
  | .int a, .int b => a == b
  | .bool a, .bool b => a == b
  | .ty a, .ty b => a == b
  | .value a, .value b => a == b
  | .poison a, .poison b => a == b
  | .values a, .values b => V.beqList a b
  | .pair t d, .pair t' d' => t == t' && V.beq d d'
  | .data t k fs, .data t' k' fs' => t == t' && k == k' && V.beqList fs fs'
  | .inst a, .inst b => decide (a = b)
  | .trapCode a, .trapCode b => decide (a = b)
  | .blockCall a, .blockCall b => decide (a = b)
  | .jumpTable d t, .jumpTable d' t' => decide (d = d') && decide (t = t')
  | _, _ => false
def V.beqList : List V → List V → Bool
  | [], [] => true
  | a :: as, b :: bs => V.beq a b && V.beqList as bs
  | _, _ => false
end

instance : BEq V := ⟨V.beq⟩

/-- The caller's e-graph (and, for `simplify_skeleton`, the function's blocks). -/
structure EGraph (σ : Type) where
  enodes : σ → Nat → List Clif.Inst
  typeOf : σ → Nat → Option Clif.Ty
  make : σ → Clif.Inst → Nat × σ
  /-- `just_trap_block` (`BranchToTrap::analyze_block`): the trap code if the block is a
  "just trap" block (only pure instructions, then `trap`). -/
  trapBlock : σ → Clif.BlockId → Option Clif.TrapCode := fun _ _ => none

/-- Interpreter state: the caller's state and the values marked by `subsume` / `remat` during
this call (`OptimizeCtx::subsume_values`, `remat_values`). -/
structure St (σ : Type) where
  inner : σ
  subsumed : List Nat := []
  remat : List Nat := []

/-! ## `Opcode`, `IntCC`, `InstructionData` -/

def opcode (k : Nat) : V := .data TyId.«Opcode» k []
def idata (k : Nat) (fs : List V) : V := .data TyId.«InstructionData» k fs

def ccIdx : Clif.IntCC → Nat
  | .eq => VIdx.«IntCC».«Equal» | .ne => VIdx.«IntCC».«NotEqual»
  | .slt => VIdx.«IntCC».«SignedLessThan» | .sge => VIdx.«IntCC».«SignedGreaterThanOrEqual»
  | .sgt => VIdx.«IntCC».«SignedGreaterThan» | .sle => VIdx.«IntCC».«SignedLessThanOrEqual»
  | .ult => VIdx.«IntCC».«UnsignedLessThan» | .uge => VIdx.«IntCC».«UnsignedGreaterThanOrEqual»
  | .ugt => VIdx.«IntCC».«UnsignedGreaterThan»
  | .ule => VIdx.«IntCC».«UnsignedLessThanOrEqual»

def ccOfIdx? : Nat → Option Clif.IntCC
  | VIdx.«IntCC».«Equal» => some .eq | VIdx.«IntCC».«NotEqual» => some .ne
  | VIdx.«IntCC».«SignedLessThan» => some .slt
  | VIdx.«IntCC».«SignedGreaterThanOrEqual» => some .sge
  | VIdx.«IntCC».«SignedGreaterThan» => some .sgt
  | VIdx.«IntCC».«SignedLessThanOrEqual» => some .sle
  | VIdx.«IntCC».«UnsignedLessThan» => some .ult
  | VIdx.«IntCC».«UnsignedGreaterThanOrEqual» => some .uge
  | VIdx.«IntCC».«UnsignedGreaterThan» => some .ugt
  | VIdx.«IntCC».«UnsignedLessThanOrEqual» => some .ule
  | _ => none

def cc (c : Clif.IntCC) : V := .data TyId.«IntCC» (ccIdx c) []

def unaryIdx : Clif.UnaryOp → Nat
  | .ineg => VIdx.«Opcode».«Ineg» | .bnot => VIdx.«Opcode».«Bnot»
  | .iabs => VIdx.«Opcode».«Iabs» | .clz => VIdx.«Opcode».«Clz»
  | .ctz => VIdx.«Opcode».«Ctz» | .cls => VIdx.«Opcode».«Cls»
  | .popcnt => VIdx.«Opcode».«Popcnt» | .bitrev => VIdx.«Opcode».«Bitrev»
  | .bswap => VIdx.«Opcode».«Bswap»

def unaryOfIdx? : Nat → Option Clif.UnaryOp
  | VIdx.«Opcode».«Ineg» => some .ineg | VIdx.«Opcode».«Bnot» => some .bnot
  | VIdx.«Opcode».«Iabs» => some .iabs | VIdx.«Opcode».«Clz» => some .clz
  | VIdx.«Opcode».«Ctz» => some .ctz | VIdx.«Opcode».«Cls» => some .cls
  | VIdx.«Opcode».«Popcnt» => some .popcnt | VIdx.«Opcode».«Bitrev» => some .bitrev
  | VIdx.«Opcode».«Bswap» => some .bswap
  | _ => none

def binaryIdx : Clif.BinaryOp → Nat
  | .iadd => VIdx.«Opcode».«Iadd» | .isub => VIdx.«Opcode».«Isub»
  | .imul => VIdx.«Opcode».«Imul» | .umulhi => VIdx.«Opcode».«Umulhi»
  | .smulhi => VIdx.«Opcode».«Smulhi» | .band => VIdx.«Opcode».«Band»
  | .bor => VIdx.«Opcode».«Bor» | .bxor => VIdx.«Opcode».«Bxor»
  | .ishl => VIdx.«Opcode».«Ishl» | .ushr => VIdx.«Opcode».«Ushr»
  | .sshr => VIdx.«Opcode».«Sshr» | .rotl => VIdx.«Opcode».«Rotl»
  | .rotr => VIdx.«Opcode».«Rotr» | .smin => VIdx.«Opcode».«Smin»
  | .smax => VIdx.«Opcode».«Smax» | .umin => VIdx.«Opcode».«Umin»
  | .umax => VIdx.«Opcode».«Umax» | .uaddSat => VIdx.«Opcode».«UaddSat»
  | .saddSat => VIdx.«Opcode».«SaddSat» | .usubSat => VIdx.«Opcode».«UsubSat»
  | .ssubSat => VIdx.«Opcode».«SsubSat»

def binaryOfIdx? : Nat → Option Clif.BinaryOp
  | VIdx.«Opcode».«Iadd» => some .iadd | VIdx.«Opcode».«Isub» => some .isub
  | VIdx.«Opcode».«Imul» => some .imul | VIdx.«Opcode».«Umulhi» => some .umulhi
  | VIdx.«Opcode».«Smulhi» => some .smulhi | VIdx.«Opcode».«Band» => some .band
  | VIdx.«Opcode».«Bor» => some .bor | VIdx.«Opcode».«Bxor» => some .bxor
  | VIdx.«Opcode».«Ishl» => some .ishl | VIdx.«Opcode».«Ushr» => some .ushr
  | VIdx.«Opcode».«Sshr» => some .sshr | VIdx.«Opcode».«Rotl» => some .rotl
  | VIdx.«Opcode».«Rotr» => some .rotr | VIdx.«Opcode».«Smin» => some .smin
  | VIdx.«Opcode».«Smax» => some .smax | VIdx.«Opcode».«Umin» => some .umin
  | VIdx.«Opcode».«Umax» => some .umax | VIdx.«Opcode».«UaddSat» => some .uaddSat
  | VIdx.«Opcode».«SaddSat» => some .saddSat | VIdx.«Opcode».«UsubSat» => some .usubSat
  | VIdx.«Opcode».«SsubSat» => some .ssubSat
  | _ => none

/-- The `Imm64` Cranelift stores for `iconst.ty imm`: the bits zero-extended from the type's
width (an `i64`). -/
def imm64OfBits {w : Nat} (imm : BitVec w) : Int := Rust.asI64 imm.toNat

/-- A node as Cranelift's `InstructionData` (`none`: no form here; not presented). -/
def ofInst : Clif.Inst → Option V
  | .iconst _ imm =>
    some (idata VIdx.«InstructionData».«UnaryImm» [opcode VIdx.«Opcode».«Iconst», .int (imm64OfBits imm)])
  | .unary op _ x => some (idata VIdx.«InstructionData».«Unary» [opcode (unaryIdx op), .value x])
  | .binary op _ x y =>
    some (idata VIdx.«InstructionData».«Binary» [opcode (binaryIdx op), .values [.value x, .value y]])
  | .icmp c _ x y =>
    some (idata VIdx.«InstructionData».«IntCompare»
      [opcode VIdx.«Opcode».«Icmp», .values [.value x, .value y], cc c])
  | .select _ c x y =>
    some (idata VIdx.«InstructionData».«Ternary»
      [opcode VIdx.«Opcode».«Select», .values [.value c, .value x, .value y]])
  | .selectSpectreGuard _ c x y =>
    some (idata VIdx.«InstructionData».«Ternary»
      [opcode VIdx.«Opcode».«SelectSpectreGuard», .values [.value c, .value x, .value y]])
  | .bitselect _ c x y =>
    some (idata VIdx.«InstructionData».«Ternary»
      [opcode VIdx.«Opcode».«Bitselect», .values [.value c, .value x, .value y]])
  | .bmask _ x => some (idata VIdx.«InstructionData».«Unary» [opcode VIdx.«Opcode».«Bmask», .value x])
  | .extend .uextend _ x =>
    some (idata VIdx.«InstructionData».«Unary» [opcode VIdx.«Opcode».«Uextend», .value x])
  | .extend .sextend _ x =>
    some (idata VIdx.«InstructionData».«Unary» [opcode VIdx.«Opcode».«Sextend», .value x])
  | .ireduce _ x =>
    some (idata VIdx.«InstructionData».«Unary» [opcode VIdx.«Opcode».«Ireduce», .value x])
  | .iconcat _ lo hi =>
    some (idata VIdx.«InstructionData».«Binary»
      [opcode VIdx.«Opcode».«Iconcat», .values [.value lo, .value hi]])
  | .stackAddr _ slot off =>
    some (idata VIdx.«InstructionData».«StackAddr» [opcode VIdx.«Opcode».«StackAddr», .int slot, .int off])
  | .symbolValue _ gv =>
    some (idata VIdx.«InstructionData».«UnaryGlobalValue» [opcode VIdx.«Opcode».«SymbolValue», .int gv])
  | _ => none

/-- `make_inst ty data` as a `Clif.Inst` (`none`: no `Clif.Inst` form). `Clif.Inst` records
the operand type for `icmp`/`iconcat` (Cranelift's `ty` is the result type). -/
def toInst (typeOf : Nat → Option Clif.Ty) (ty : CTy) : V → Option Clif.Inst
  | .data t k fs =>
    if t != TyId.«InstructionData» then none else
    match k, fs, ty.toClif? with
    | VIdx.«InstructionData».«UnaryImm», [.data _ VIdx.«Opcode».«Iconst» [], .int imm], some t =>
      if t == .i128 then none else some (.iconst t (BitVec.ofInt t.width imm))
    | VIdx.«InstructionData».«Unary», [.data _ op [], .value x], some t =>
      match unaryOfIdx? op with
      | some u => some (.unary u t x)
      | none =>
        match op with
        | VIdx.«Opcode».«Bmask» => some (.bmask t x)
        | VIdx.«Opcode».«Uextend» => some (.extend .uextend t x)
        | VIdx.«Opcode».«Sextend» => some (.extend .sextend t x)
        | VIdx.«Opcode».«Ireduce» => some (.ireduce t x)
        | _ => none
    | VIdx.«InstructionData».«Binary», [.data _ op [], .values [.value x, .value y]], some t =>
      match binaryOfIdx? op with
      | some b => some (.binary b t x y)
      | none =>
        if op == VIdx.«Opcode».«Iconcat» then (typeOf x).map (.iconcat · x y) else none
    | VIdx.«InstructionData».«IntCompare»,
      [.data _ VIdx.«Opcode».«Icmp» [], .values [.value x, .value y], .data _ c []], some _ =>
      match ccOfIdx? c, typeOf x with
      | some c, some xt => some (.icmp c xt x y)
      | _, _ => none
    | VIdx.«InstructionData».«Ternary», [.data _ op [], .values [.value c, .value x, .value y]],
      some t =>
      match op with
      | VIdx.«Opcode».«Select» => some (.select t c x y)
      | VIdx.«Opcode».«SelectSpectreGuard» => some (.selectSpectreGuard t c x y)
      | VIdx.«Opcode».«Bitselect» => some (.bitselect t c x y)
      | _ => none
    | VIdx.«InstructionData».«StackAddr», [.data _ VIdx.«Opcode».«StackAddr» [], .int s, .int o],
      some t => if s ≥ 0 then some (.stackAddr t s.toNat o) else none
    | VIdx.«InstructionData».«UnaryGlobalValue»,
      [.data _ VIdx.«Opcode».«SymbolValue» [], .int g], some t =>
      if g ≥ 0 then some (.symbolValue t g.toNat) else none
    | _, _, _ => none
  | _ => none

/-! ## Skeleton instructions (`simplify_skeleton`) -/

def divIdx : Clif.DivOp → Nat
  | .udiv => VIdx.«Opcode».«Udiv» | .sdiv => VIdx.«Opcode».«Sdiv»
  | .urem => VIdx.«Opcode».«Urem» | .srem => VIdx.«Opcode».«Srem»

/-- A skeleton instruction as Cranelift's `InstructionData` (`inst_data_etor`; `none`: no
form here, no rule matches it). -/
def ofSkel : SkelInst → Option V
  | .inst (.div op _ x y) =>
    some (idata VIdx.«InstructionData».«Binary» [opcode (divIdx op), .values [.value x, .value y]])
  | .inst (.trapz c code) =>
    some (idata VIdx.«InstructionData».«CondTrap» [opcode VIdx.«Opcode».«Trapz», .value c, .trapCode code])
  | .inst (.trapnz c code) =>
    some (idata VIdx.«InstructionData».«CondTrap» [opcode VIdx.«Opcode».«Trapnz», .value c, .trapCode code])
  | .term (.brif c t e) =>
    some (idata VIdx.«InstructionData».«Brif»
      [opcode VIdx.«Opcode».«Brif», .value c, .values [.blockCall t, .blockCall e]])
  | .term (.jump d) => some (idata VIdx.«InstructionData».«Jump» [opcode VIdx.«Opcode».«Jump», .blockCall d])
  | .term (.brTable x d tbl) =>
    some (idata VIdx.«InstructionData».«BranchTable» [opcode VIdx.«Opcode».«BrTable», .value x, .jumpTable d tbl])
  | _ => none

/-- `make_skeleton_inst data` as a skeleton instruction (the forms the rules build: `jump`,
`trapz`, `trapnz`, `brif`). -/
def toSkel : V → Option SkelInst
  | .data t k fs =>
    if t != TyId.«InstructionData» then none else
    match k, fs with
    | VIdx.«InstructionData».«Jump», [.data _ VIdx.«Opcode».«Jump» [], .blockCall d] => some (.term (.jump d))
    | VIdx.«InstructionData».«CondTrap», [.data _ VIdx.«Opcode».«Trapz» [], .value c, .trapCode code] =>
      some (.inst (.trapz c code))
    | VIdx.«InstructionData».«CondTrap», [.data _ VIdx.«Opcode».«Trapnz» [], .value c, .trapCode code] =>
      some (.inst (.trapnz c code))
    | VIdx.«InstructionData».«Brif», [.data _ VIdx.«Opcode».«Brif» [], .value c, .values [.blockCall a, .blockCall b]] =>
      some (.term (.brif c a b))
    | _, _ => none
  | _ => none

/-- `SkeletonInstSimplification` (`prelude_opt.isle`) with skeleton instructions as
`SkelInst`. `RemoveDeadStore` is not built by any closure rule. -/
inductive SkelSimp where
  | remove
  | removeWithVal (v : Nat)
  | replace (i : SkelInst)
  | replaceWithVal (i : SkelInst) (v : Nat)
  | replaceBranchCond (c : Nat)
  | replaceWithTwo (first second : SkelInst)
  deriving DecidableEq, Repr, Inhabited

/-- A result of `simplify_skeleton` (`none`: it mentions a poison value or an instruction
without a `SkelInst` form, or is `RemoveDeadStore`; dropped). -/
def skelSimp? : V → Option SkelSimp
  | .data t k fs =>
    if t != TyId.«SkeletonInstSimplification» then none else
    match k, fs with
    | VIdx.«SkeletonInstSimplification».«Remove», [] => some .remove
    | VIdx.«SkeletonInstSimplification».«RemoveWithVal», [.value v] => some (.removeWithVal v)
    | VIdx.«SkeletonInstSimplification».«Replace», [.inst (some i)] => some (.replace i)
    | VIdx.«SkeletonInstSimplification».«ReplaceWithVal», [.inst (some i), .value v] =>
      some (.replaceWithVal i v)
    | VIdx.«SkeletonInstSimplification».«ReplaceBranchCond», [.value c] => some (.replaceBranchCond c)
    | VIdx.«SkeletonInstSimplification».«ReplaceWithTwo», [.inst (some a), .inst (some b)] =>
      some (.replaceWithTwo a b)
    | _, _ => none
  | _ => none

/-! ## Extern helpers -/

/-- Errors: unmodeled helpers and Rust panics. -/
abbrev R := Except String

def V.int? : V → R Int | .int i => pure i | v => throw s!"expected an integer, got {repr v}"
def V.ty? : V → R CTy | .ty t => pure t | v => throw s!"expected a Type, got {repr v}"
def V.bool? : V → R Bool | .bool b => pure b | v => throw s!"expected a bool, got {repr v}"
def V.cc? : V → R Clif.IntCC
  | v@(.data _ k []) => match ccOfIdx? k with
    | some c => pure c
    | none => throw s!"expected an IntCC, got {repr v}"
  | v => throw s!"expected an IntCC, got {repr v}"

def panics {α : Type} (x : Rust.Panics α) : R α :=
  match x with
  | .ok a => pure a
  | .error e => throw s!"panic: {e}"

/-- Normalise an ISLE integer literal to its type (`u8`..`u128` wrap to unsigned, `i8`..`i128`
to signed). -/
def normInt (ty : TypeId) (i : Int) : Int :=
  let u (w : Nat) : Int := (BitVec.ofInt w i).toNat
  let s (w : Nat) : Int := (BitVec.ofInt w i).toInt
  match ty with
  | TyId.«u8» => u 8 | TyId.«u16» => u 16 | TyId.«u32» => u 32 | TyId.«u64» => u 64
  | TyId.«u128» => u 128 | TyId.«usize» => u 64
  | TyId.«i8» => s 8 | TyId.«i16» => s 16 | TyId.«i32» => s 32 | TyId.«i64» => s 64
  | TyId.«i128» => s 128 | TyId.«isize» => s 64
  | _ => i

def dcm (ty : TypeId) (fs : List V) : V := .data ty 0 fs

section
variable {σ : Type} (G : EGraph σ)

/-- Type of a value (`value_type`). -/
def valueType (st : St σ) : V → R CTy
  | .value n => match G.typeOf st.inner n with
    | some t => pure (CTy.ofClif t)
    | none => throw s!"value_type: v{n} has no type"
  | .poison t => pure t
  | v => throw s!"value_type: not a value: {repr v}"

/-- Nodes of a value as `(Type, InstructionData)` (`inst_data_value_etor`). -/
def nodesOf (st : St σ) : V → R (List (CTy × V))
  | .value n => do
    let t ← valueType G st (.value n)
    pure ((G.enodes st.inner n).filterMap fun i => (ofInst i).map (t, ·))
  | .poison _ => pure []
  | v => throw s!"inst_data_value: not a value: {repr v}"

/-- `make_inst ty data`: a poison value if the node has no `Clif.Inst` form. -/
def makeInst (st : St σ) (ty : CTy) (d : V) : V × St σ :=
  match toInst (G.typeOf st.inner) ty d with
  | some i =>
    let (n, s') := G.make st.inner i
    (.value n, { st with inner := s' })
  | none => (.poison ty, st)

/-- Extern constructors, by Rust function name: `none` is a failing `Option`. -/
def ctorFn (fn : String) (args : List V) (st : St σ) : R (Option (V × St σ)) := do
  let ok (v : V) : R (Option (V × St σ)) := pure (some (v, st))
  let int (i : Int) := ok (.int i)
  let bool (b : Bool) := ok (.bool b)
  let opt (o : Option Int) : R (Option (V × St σ)) := pure (o.map fun i => (.int i, st))
  match fn, args with
  -- `src/opts.rs`
  | "make_inst_ctor", [t, d] => do
    let (v, st') := makeInst G st (← t.ty?) d
    pure (some (v, st'))
  | "value_array_2_ctor", [a, b] => ok (.values [a, b])
  | "value_array_3_ctor", [a, b, c] => ok (.values [a, b, c])
  | "remat", [v] =>
    match v with
    | .value n => pure (some (v, { st with remat := n :: st.remat }))
    | _ => ok v
  | "subsume", [v] =>
    match v with
    | .value n => pure (some (v, { st with subsumed := n :: st.subsumed }))
    | _ => ok v
  | "u64_bswap16", [n] => int (Rust.bswap 2 (← n.int?))
  | "u64_bswap32", [n] => int (Rust.bswap 4 (← n.int?))
  | "u64_bswap64", [n] => int (Rust.bswap 8 (← n.int?))
  | "div_const_magic_u32", [d] =>
    let (m, a, s) := Rust.magicU 32 (← d.int?).toNat
    ok (dcm TyId.«DivConstMagicU32» [.int m, .bool a, .int (Rust.asU32 s)])
  | "div_const_magic_u64", [d] =>
    let (m, a, s) := Rust.magicU 64 (← d.int?).toNat
    ok (dcm TyId.«DivConstMagicU64» [.int m, .bool a, .int (Rust.asU32 s)])
  | "div_const_magic_s32", [d] =>
    let (m, s) := Rust.magicS 32 (← d.int?)
    ok (dcm TyId.«DivConstMagicS32» [.int m, .int (Rust.asU32 s)])
  | "div_const_magic_s64", [d] =>
    let (m, s) := Rust.magicS 64 (← d.int?)
    ok (dcm TyId.«DivConstMagicS64» [.int m, .int (Rust.asU32 s)])
  -- `src/isle_prelude.rs`: `Imm64`
  | "imm64_sdiv", [t, x, y] => opt (← panics (Rust.imm64Sdiv (← t.ty?) (← x.int?) (← y.int?)))
  | "imm64_udiv", [t, x, y] => opt (← panics (Rust.imm64Udiv (← t.ty?) (← x.int?) (← y.int?)))
  | "imm64_srem", [t, x, y] => opt (← panics (Rust.imm64Srem (← t.ty?) (← x.int?) (← y.int?)))
  | "imm64_urem", [t, x, y] => opt (← panics (Rust.imm64Urem (← t.ty?) (← x.int?) (← y.int?)))
  | "imm64_add", [t, x, y] => int (← panics (Rust.imm64Add (← t.ty?) (← x.int?) (← y.int?)))
  | "imm64_sub", [t, x, y] => int (← panics (Rust.imm64Sub (← t.ty?) (← x.int?) (← y.int?)))
  | "imm64_mul", [t, x, y] => int (← panics (Rust.imm64Mul (← t.ty?) (← x.int?) (← y.int?)))
  | "imm64_and", [t, x, y] => int (← panics (Rust.imm64And (← t.ty?) (← x.int?) (← y.int?)))
  | "imm64_or", [t, x, y] => int (← panics (Rust.imm64Or (← t.ty?) (← x.int?) (← y.int?)))
  | "imm64_xor", [t, x, y] => int (← panics (Rust.imm64Xor (← t.ty?) (← x.int?) (← y.int?)))
  | "imm64_not", [t, x] => int (← panics (Rust.imm64Not (← t.ty?) (← x.int?)))
  | "imm64_neg", [t, x] => int (← panics (Rust.imm64Neg (← t.ty?) (← x.int?)))
  | "imm64_umin", [t, x, y] => int (← panics (Rust.imm64Umin (← t.ty?) (← x.int?) (← y.int?)))
  | "imm64_umax", [t, x, y] => int (← panics (Rust.imm64Umax (← t.ty?) (← x.int?) (← y.int?)))
  | "imm64_smin", [t, x, y] => int (← panics (Rust.imm64Smin (← t.ty?) (← x.int?) (← y.int?)))
  | "imm64_smax", [t, x, y] => int (← panics (Rust.imm64Smax (← t.ty?) (← x.int?) (← y.int?)))
  | "imm64_shl", [t, x, y] => int (← panics (Rust.imm64Shl (← t.ty?) (← x.int?) (← y.int?)))
  | "imm64_ushr", [t, x, y] => int (← panics (Rust.imm64Ushr (← t.ty?) (← x.int?) (← y.int?)))
  | "imm64_sshr", [t, x, y] => int (← panics (Rust.imm64Sshr (← t.ty?) (← x.int?) (← y.int?)))
  | "imm64_rotl", [t, x, y] => int (← panics (Rust.imm64Rotl (← t.ty?) (← x.int?) (← y.int?)))
  | "imm64_rotr", [t, x, y] => int (← panics (Rust.imm64Rotr (← t.ty?) (← x.int?) (← y.int?)))
  | "imm64_clz", [t, x] => int (← panics (Rust.imm64Clz (← t.ty?) (← x.int?)))
  | "imm64_ctz", [t, x] => int (← panics (Rust.imm64Ctz (← t.ty?) (← x.int?)))
  | "imm64_icmp", [t, c, x, y] =>
    int (← panics (Rust.imm64Icmp (← t.ty?) (← c.cc?) (← x.int?) (← y.int?)))
  | "i64_sextend_u64", [t, x] => int (← panics (Rust.i64SextendU64 (← t.ty?) (← x.int?)))
  | "imm64", [x] => int (Rust.asI64 (← x.int?))
  | "imm64_masked", [t, x] => int (← panics (Rust.imm64Masked (← t.ty?) (← x.int?)))
  -- `src/isle_prelude.rs`: `Type`, `IntCC`
  | "ty_umax", [t] => int (← panics (Rust.tyUmax (← t.ty?)))
  | "ty_mask", [t] => int (← panics (Rust.tyMask (← t.ty?)))
  | "ty_smin", [t] => int (← panics (Rust.tySmin (← t.ty?)))
  | "ty_smax", [t] => int (← panics (Rust.tySmax (← t.ty?)))
  | "ty_bits", [t] => int (← panics (Rust.tyBits (← t.ty?)))
  | "ty_bits_u64", [t] => int (← t.ty?).bits
  | "lane_type", [t] => ok (.ty (← t.ty?).laneType)
  | "ty_half_width", [t] => pure ((← t.ty?).halfWidth?.map fun t => (.ty t, st))
  | "ty_equal", [a, b] => bool ((← a.ty?) == (← b.ty?))
  | "intcc_swap_args", [c] => ok (cc (Rust.intccSwapArgs (← c.cc?)))
  | "intcc_complement", [c] => ok (cc (Rust.intccComplement (← c.cc?)))
  | "signed_cond_code", [c] => pure ((Rust.signedCondCode (← c.cc?)).map fun c => (cc c, st))
  | "u64_uextend_imm64", [t, x] => int (← panics (Rust.u64UextendImm64 (← t.ty?) (← x.int?)))
  | "checked_add_with_type", [t, a, b] =>
    opt (← panics (Rust.checkedAddWithType (← t.ty?) (← a.int?) (← b.int?)))
  | "ty_vector_not_float", [t] => pure ((Rust.tyVectorNotFloat (← t.ty?)).map fun t => (.ty t, st))
  | "pack_value_array_2", [a, b] => ok (.values [a, b])
  | "pack_block_array_2", [a, b] => ok (.values [a, b])
  -- `src/opts.rs`: skeleton instructions
  | "make_skeleton_inst_ctor", [d] => ok (.inst (toSkel d))
  | "resolve_jump_table_entry", [.jumpTable d tbl, i] => do
    let i ← i.int?
    ok (.blockCall (if i ≥ 0 then (tbl[i.toNat]?).getD d else d))
  | "block_call_block", [.blockCall b] => int b.block
  | "just_trap_block", [b] => do
    let b ← b.int?
    pure ((G.trapBlock st.inner b.toNat).map fun c => (.trapCode c, st))
  | "pack_value_array_3", [a, b, c] => ok (.values [a, b, c])
  -- `<OUT_DIR>/isle_numerics.rs`
  | "i32_lt", [a, b] => bool ((← a.int?) < (← b.int?))
  | "i32_gt", [a, b] => bool ((← a.int?) > (← b.int?))
  | "u32_lt", [a, b] => bool ((← a.int?) < (← b.int?))
  | "u32_sub", [a, b] => int (← panics (Rust.checkedSubU "u32_sub" (← a.int?) (← b.int?)))
  | "u32_is_power_of_two", [a] => bool (Rust.isPow2 (← a.int?))
  | "i64_eq", [a, b] => bool ((← a.int?) == (← b.int?))
  | "i64_ne", [a, b] => bool ((← a.int?) != (← b.int?))
  | "i64_lt", [a, b] => bool ((← a.int?) < (← b.int?))
  | "i64_gt", [a, b] => bool ((← a.int?) > (← b.int?))
  | "i64_gt_eq", [a, b] => bool ((← a.int?) ≥ (← b.int?))
  | "i64_shl", [a, b] => int (← panics (Rust.i64Shl (← a.int?) (← b.int?)))
  | "i64_trailing_zeros", [a] => int (Rust.ctz64 (← a.int?))
  | "i64_wrapping_neg", [a] => int (Rust.asI64 (-(← a.int?)))
  | "i64_cast_unsigned", [a] => int (Rust.asU64 (← a.int?))
  | "u64_eq", [a, b] => bool ((← a.int?) == (← b.int?))
  | "u64_lt", [a, b] => bool ((← a.int?) < (← b.int?))
  | "u64_lt_eq", [a, b] => bool ((← a.int?) ≤ (← b.int?))
  | "u64_gt", [a, b] => bool ((← a.int?) > (← b.int?))
  | "u64_wrapping_add", [a, b] => int (Rust.asU64 ((← a.int?) + (← b.int?)))
  | "u64_wrapping_sub", [a, b] => int (Rust.asU64 ((← a.int?) - (← b.int?)))
  | "u64_sub", [a, b] => int (← panics (Rust.checkedSubU "u64_sub" (← a.int?) (← b.int?)))
  | "u64_div", [a, b] => do
    let b ← b.int?
    if b == 0 then throw s!"panic: u64_div: div failure: {← a.int?} / 0"
    int ((← a.int?) / b)
  | "u64_rem", [a, b] => do
    let b ← b.int?
    if b == 0 then throw s!"panic: u64_rem: rem failure: {← a.int?} % 0"
    int ((← a.int?) % b)
  | "u64_checked_rem", [a, b] => do
    let a ← a.int?
    let b ← b.int?
    opt (if b == 0 then none else some (a % b))
  | "u64_and", [a, b] => int (Rust.band64 (← a.int?) (← b.int?))
  | "u64_or", [a, b] => int (Rust.bor64 (← a.int?) (← b.int?))
  | "u64_not", [a] => int (Rust.asU64 (-(← a.int?) - 1))
  | "u64_shl", [a, b] => int (← panics (Rust.u64Shl (← a.int?) (← b.int?)))
  | "u64_ilog2", [a] => int (← panics (Rust.u64Ilog2 (← a.int?)))
  | "u64_trailing_zeros", [a] => int (Rust.ctz64 (← a.int?))
  | "u64_is_power_of_two", [a] => bool (Rust.isPow2 (← a.int?))
  | "u16_into_u64", [a] => ok a
  | "u8_into_u32", [a] => ok a
  | "u8_into_u64", [a] => ok a
  | "i32_into_i64", [a] => ok a
  | "u32_into_i64", [a] => ok a
  | "u32_into_u64", [a] => ok a
  | _, _ => throw s!"unmodeled extern constructor {fn}"

/-- Extern (single) extractors, by Rust function name: `none` is no match. -/
def extractFn (fn : String) (v : V) (st : St σ) : R (Option (List V)) := do
  let ok (vs : List V) : R (Option (List V)) := pure (some vs)
  let tyIf (o : Option CTy) : R (Option (List V)) := pure (o.map fun t => [.ty t])
  match fn with
  | "value_type" => ok [.ty (← valueType G st v)]
  | "fits_in_64" => tyIf (Rust.fitsIn64 (← v.ty?))
  | "ty_int_ref_scalar_64_extract" => tyIf (Rust.tyIntRefScalar64 (← v.ty?))
  | "ty_int" => tyIf (Rust.tyInt (← v.ty?))
  | "ty_vec128" => tyIf (Rust.tyVec128 (← v.ty?))
  | "ty_vector" => tyIf (Rust.tyVector (← v.ty?))
  | "ty_int_vec128" => tyIf (Rust.tyIntVec128 (← v.ty?))
  | "ty_vec128_int" => tyIf (Rust.tyVec128Int (← v.ty?))
  | "multi_lane" =>
    pure ((Rust.multiLane (← v.ty?)).map fun (b, n) => [.int b, .int n])
  | "u64_from_imm64" => ok [.int (Rust.asU64 (← v.int?))]
  | "imm64_power_of_two" => pure ((Rust.imm64PowerOfTwo (← v.int?)).map fun i => [.int i])
  | "inst_data_etor" =>
    match v with
    | .inst (some i) => pure ((ofSkel i).map ([·]))
    | .inst none => pure none
    | _ => throw s!"inst_data_etor: {repr v}"
  | "unpack_block_array_2" =>
    match v with
    | .values [a, b] => ok [a, b]
    | _ => throw s!"unpack_block_array_2: {repr v}"
  | "unpack_value_array_2" =>
    match v with
    | .values [a, b] => ok [a, b]
    | _ => throw s!"unpack_value_array_2: {repr v}"
  | "unpack_value_array_3" =>
    match v with
    | .values [a, b, c] => ok [a, b, c]
    | _ => throw s!"unpack_value_array_3: {repr v}"
  | "iconst_sextend_etor" =>
    match v with
    | .pair t (.data _ VIdx.«InstructionData».«UnaryImm» [.data _ VIdx.«Opcode».«Iconst» [], .int imm]) =>
      ok [.ty t, .int (Rust.i64SextendImm64 t imm)]
    | .pair _ _ => pure none
    | _ => throw s!"iconst_sextend_etor: {repr v}"
  | "all_zero_etor" =>
    -- Only the `iconst` arm can match a node presented here (floats and vectors are not).
    match v with
    | .pair t (.data _ VIdx.«InstructionData».«UnaryImm» [.data _ VIdx.«Opcode».«Iconst» [], .int imm]) =>
      pure (if imm == 0 then some [.ty t] else none)
    | .pair _ _ => pure none
    | _ => throw s!"all_zero_etor: {repr v}"
  -- `<OUT_DIR>/isle_numerics.rs`
  | "u32_matches_non_zero" | "u64_matches_non_zero" | "i64_matches_non_zero" =>
    ok [.bool ((← v.int?) != 0)]
  | "u64_matches_power_of_two" => ok [.bool (Rust.isPow2 (← v.int?))]
  | "i64_from_i32" => let x ← v.int?; pure (if Rust.inI32 x then some [.int x] else none)
  | "i32_from_i64" => ok [v]
  | "u64_from_u32" => let x ← v.int?; pure (if Rust.inU32 x then some [.int x] else none)
  | "u32_from_u64" => ok [v]
  | _ => throw s!"unmodeled extern extractor {fn}"

/-- `MaybeUnaryEtorIter` (`src/opts.rs`): the operand of every `op` node of `v`, else `v`
itself once. -/
def maybeUnary (st : St σ) (op : Nat) (v : V) : R (List (List V)) := do
  let ns ← nodesOf G st v
  let hits := ns.filterMap fun (t, d) =>
    match d with
    | .data _ VIdx.«InstructionData».«Unary» [.data _ o [], x] => if o == op then some [.ty t, x] else none
    | _ => none
  if hits.isEmpty then pure [[.ty (← valueType G st v), v]] else pure hits

/-- Extern multi-extractors. -/
def extractMultiFn (fn : String) (v : V) (st : St σ) : R (List (List V)) := do
  match fn with
  | "inst_data_value_etor" => pure ((← nodesOf G st v).map fun (t, d) => [.ty t, d])
  | "inst_data_value_tupled_etor" => pure ((← nodesOf G st v).map fun (t, d) => [.pair t d])
  | "uextend_maybe_etor" => maybeUnary G st VIdx.«Opcode».«Uextend» v
  | "sextend_maybe_etor" => maybeUnary G st VIdx.«Opcode».«Sextend» v
  | _ => throw s!"unmodeled multi extractor {fn}"

def toExt {α : Type} : R (Option α) → ExtResult α
  | .ok (some a) => .ok a
  | .ok none => .fail
  | .error e => .unmodeled e

/-- The embedding. -/
def sem : MultiSem V (St σ) where
  int ty i := .int (normInt ty i)
  bool b := .bool b
  prim ty n := if ty == TyId.«Type» then (CTy.ofName? n).map .ty else none
  eq := V.beq
  mkData ty k fs := .data ty k fs
  unData ty v := match v with
    | .data ty' k fs => if ty == ty' then some (k, fs) else none
    | _ => none
  ctor t args st := match t.externCtor? with
    | some fn => toExt (ctorFn G fn args st)
    | none => .unmodeled s!"{t.name} has no extern constructor"
  extract t v st := match t.externExtractor? with
    | some fn => toExt (extractFn G fn v st)
    | none => .unmodeled s!"{t.name} has no extern extractor"
  extractMulti t v st := match t.externExtractor? with
    | some fn => match extractMultiFn G fn v st with
      | .ok vs => .ok vs
      | .error e => .unmodeled e
    | none => .unmodeled s!"{t.name} has no extern extractor"

end

/-- Interpreter configuration of `simplify` (fuel per call). -/
def cfg : Config := { fuel := 1000000 }

/-- Run `simplify` on the e-class `v`: the rewrite candidates (e-class, `subsume`d during this
call) in rule order, the names of the rules that produced them (same order), and the caller's
state after the `make` calls. `.error` only for interpreter errors (an unmodeled helper, a
Rust panic, fuel). -/
def simplify {σ : Type} (enodes : σ → Nat → List Clif.Inst) (typeOf : σ → Nat → Option Clif.Ty)
    (make : σ → Clif.Inst → Nat × σ) (st : σ) (v : Nat) :
    Except String (List (Nat × Bool) × List String × σ) :=
  let G : EGraph σ := { enodes, typeOf, make }
  match Interp.runMultiTerm program (sem G) cfg T.«simplify» [.value v] { inner := st } with
  | .error e => .error (reprStr e)
  | .ok r =>
    let cands := r.values.filterMap fun (rid, w) =>
      match w with
      | .value n => some ((n, r.state.subsumed.contains n), (program.rule? rid).elim s!"<rule {rid}>" (·.name))
      | _ => none
    .ok (cands.map (·.1), cands.map (·.2), r.state.inner)

/-- Run `simplify_skeleton` on the side-effecting instruction `i`: the simplifications in rule
order, the names of the rules that produced them (same order), and the caller's state after
the `make` calls. `trapBlock` is `just_trap_block`. -/
def simplifySkeleton {σ : Type} (enodes : σ → Nat → List Clif.Inst)
    (typeOf : σ → Nat → Option Clif.Ty) (make : σ → Clif.Inst → Nat × σ)
    (trapBlock : σ → Clif.BlockId → Option Clif.TrapCode) (st : σ) (i : SkelInst) :
    Except String (List SkelSimp × List String × σ) :=
  let G : EGraph σ := ⟨enodes, typeOf, make, trapBlock⟩
  match Interp.runMultiTerm program (sem G) cfg T.«simplify_skeleton» [.inst (some i)]
      { inner := st } with
  | .error e => .error (reprStr e)
  | .ok r =>
    let res := r.values.filterMap fun (rid, w) =>
      (skelSimp? w).map fun s => (s, (program.rule? rid).elim s!"<rule {rid}>" (·.name))
    .ok (res.map (·.1), res.map (·.2), r.state.inner)

end Isle.Opt
