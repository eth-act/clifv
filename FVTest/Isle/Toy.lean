import FV.Isle

/-!
# A toy embedding for the ISLE interpreter

A minimal model of Cranelift's aarch64 lowering context, enough to run `lower` on single
instructions of small CLIF functions: a data-flow graph (instructions, values, types), a
virtual-register allocator and the list of emitted `MInst`s. Each modelled extern mirrors its
Rust implementation in cranelift-codegen 0.136.1 (`machinst/isle.rs`, `isle_prelude.rs`,
`isa/aarch64/lower/isle.rs`, `isa/aarch64/inst/imms.rs`) on the inputs used here; anything else
is reported as unmodeled, which aborts interpretation (so a missing model can never silently turn
into "rule does not match").

This is test scaffolding for `FVTest/Isle/Interp.lean`, not the M4 lowering context.
-/

namespace Isle.Toy
open Isle Isle.Aarch64

/-- Toy values. ISLE integers of every width are `int`; enums/structs are `data` (type id,
variant, fields); opaque Rust types (`ValueArray2`, `Imm12`, `ValueRegs`, `InstOutput`, ...) are
`prim` with a tag. -/
inductive TV where
  | int (i : Int)
  | bool (b : Bool)
  | ty (name : String)
  | inst (n : Nat)
  | value (n : Nat)
  | reg (n : Nat)
  | data (ty : TypeId) (k : Nat) (fields : List TV)
  | prim (tag : String) (fields : List TV)
  deriving Repr, Inhabited

mutual
def TV.beq : TV → TV → Bool
  | .int a, .int b => a == b
  | .bool a, .bool b => a == b
  | .ty a, .ty b => a == b
  | .inst a, .inst b => a == b
  | .value a, .value b => a == b
  | .reg a, .reg b => a == b
  | .data t k fs, .data t' k' gs => t == t' && k == k' && TV.beqList fs gs
  | .prim a fs, .prim b gs => a == b && TV.beqList fs gs
  | _, _ => false
def TV.beqList : List TV → List TV → Bool
  | [], [] => true
  | a :: as, b :: bs => TV.beq a b && TV.beqList as bs
  | _, _ => false
end

instance : BEq TV := ⟨TV.beq⟩

/-- `(type id, variant number)` of the enum-variant term `full` (e.g. `"Opcode.Iadd"`). -/
def variant? (full : String) : Option (TypeId × Nat) := do
  let t ← program.termByName? full
  match t.kind with
  | .enumVariant k => some (t.ret, k)
  | _ => none

/-- The value of the field-less enum variant `full`. -/
def enumVal (full : String) : TV :=
  match variant? full with
  | some (ty, k) => .data ty k []
  | none => .prim s!"<unknown variant {full}>" []

def dataVal (full : String) (fields : List TV) : TV :=
  match variant? full with
  | some (ty, k) => .data ty k fields
  | none => .prim s!"<unknown variant {full}>" fields

/-- One CLIF instruction: its `InstructionData` and result values. -/
structure InstInfo where
  data : TV
  results : List Nat
  deriving Repr, Inhabited

/-- The lowering context: DFG, vreg allocation, emitted instructions (in emission order). -/
structure St where
  insts : Array InstInfo
  /-- Type name of each value (`"I64"`, ...). -/
  valueTy : Array String
  /-- Defining instruction of each value (`none`: block parameter). -/
  valueDef : Array (Option Nat)
  /-- Virtual register holding each value (Cranelift assigns these before lowering). -/
  valueReg : Array Nat
  nextVreg : Nat
  emitted : Array TV
  deriving Repr, Inhabited

/-! Instruction constructors (the `InstructionData` a CLIF instruction carries). -/

def iconstInst (imm : Int) : TV :=
  dataVal "InstructionData.UnaryImm" [enumVal "Opcode.Iconst", .int imm]

def binaryInst (op : String) (a b : Nat) : TV :=
  dataVal "InstructionData.Binary" [enumVal s!"Opcode.{op}", .prim "ValueArray2" [.value a, .value b]]

def icmpInst (cc : String) (a b : Nat) : TV :=
  dataVal "InstructionData.IntCompare"
    [enumVal "Opcode.Icmp", .prim "ValueArray2" [.value a, .value b], enumVal s!"IntCC.{cc}"]

def returnInst (vs : List Nat) : TV :=
  dataVal "InstructionData.MultiAry" [enumVal "Opcode.Return", .prim "ValueList" (vs.map .value)]

/-- A single-block function: parameter types, then instructions `(data, result type?)` whose
results are numbered after the parameters. Value `n` lives in vreg `n`. -/
def mkFunc (params : List String) (insts : List (TV × Option String)) : St :=
  let (infos, tys, defs) := insts.foldl (init := (#[], params.toArray, params.toArray.map fun _ => none))
    fun (infos, tys, defs) (data, rty) =>
      match rty with
      | some ty => (infos.push ⟨data, [tys.size]⟩, tys.push ty, defs.push (some infos.size))
      | none => (infos.push ⟨data, []⟩, tys, defs)
  { insts := infos, valueTy := tys, valueDef := defs
    valueReg := (List.range tys.size).toArray, nextVreg := tys.size, emitted := #[] }

/-- Scalar CLIF types: bit width and `is_int`. `INVALID` (no result) has 0 bits. -/
def tyInfo : String → Option (Nat × Bool)
  | "I8" => some (8, true)
  | "I16" => some (16, true)
  | "I32" => some (32, true)
  | "I64" => some (64, true)
  | "I128" => some (128, true)
  | "INVALID" => some (0, false)
  | _ => none

/-- Extern `Type → Option Type` predicates (`isle_prelude.rs`) on the non-float, non-vector
types of `tyInfo`. -/
def tyPred : String → Option (String → Nat → Bool → Bool)
  | "fits_in_16" => some fun _ b _ => b ≤ 16
  | "fits_in_32" => some fun _ b _ => b ≤ 32
  | "fits_in_64" => some fun _ b _ => b ≤ 64
  | "ty_int_ref_scalar_64" => some fun _ b _ => b ≤ 64
  | "ty_int_ref_scalar_64_extract" => some fun _ b _ => b ≤ 64
  | "ty_16" => some fun _ b _ => b == 16
  | "ty_32" => some fun _ b _ => b == 32
  | "ty_64" => some fun _ b _ => b == 64
  | "ty_128" => some fun _ b _ => b == 128
  | "ty_32_or_64" => some fun _ b _ => b == 32 || b == 64
  | "ty_8_or_16" => some fun _ b _ => b == 8 || b == 16
  | "ty_16_or_32" => some fun _ b _ => b == 16 || b == 32
  | "int_fits_in_32" => some fun n _ _ => n == "I8" || n == "I16" || n == "I32"
  | "ty_int_ref_64" => some fun n _ _ => n == "I64"
  | "ty_int_ref_16_to_64" => some fun n _ _ => n == "I16" || n == "I32" || n == "I64"
  | "valid_atomic_transaction" | "integral_ty" =>
    some fun n _ _ => n == "I8" || n == "I16" || n == "I32" || n == "I64"
  | "ty_int" => some fun _ _ i => i
  | "ty_int_vec128" => some fun _ _ i => i
  | "ty_scalar_float" | "ty_float_or_vec" | "ty_vector_float" | "ty_vector_not_float"
  | "ty_vec64" | "ty_vec128" | "ty_dyn_vec64" | "ty_dyn_vec128" | "ty_vec64_int"
  | "ty_vec128_int" | "ty_dyn64_int" | "ty_dyn128_int" | "lane_fits_in_32" =>
    some fun _ _ _ => false
  | _ => none

def applyTyPred (name : String) (v : TV) : Option (ExtResult TV) := do
  let f ← tyPred name
  match v with
  | .ty n =>
    match tyInfo n with
    | some (bits, isInt) => some (if f n bits isInt then .ok (.ty n) else .fail)
    | none => some (.unmodeled s!"{name} on type {n}")
  | _ => some (.unmodeled s!"{name} on a non-type")

/-- `Imm12::maybe_from_u64`. -/
def imm12? (n : Nat) : Option TV :=
  if n < 0x1000 then some (.prim "Imm12" [.int n, .bool false])
  else if n % 0x1000 == 0 && n / 0x1000 < 0x1000 then some (.prim "Imm12" [.int (n / 0x1000), .bool true])
  else none

def valTy (st : St) (v : Nat) : String := st.valueTy.getD v "?"

def extract (t : Term) (v : TV) (st : St) : ExtResult (List TV) :=
  match applyTyPred t.name v with
  | some (.ok ty) => .ok [ty]
  | some .fail => .fail
  | some (.unmodeled w) => .unmodeled w
  | none =>
  match t.name, v with
  | "inst_data_value", .inst i =>
    match st.insts[i]? with
    | some info =>
      let ty := match info.results.head? with
        | some r => valTy st r
        | none => "INVALID"
      .ok [.ty ty, info.data]
    | none => .unmodeled s!"inst {i}"
  | "first_result", .inst i =>
    match st.insts[i]? with
    | some info => match info.results.head? with
      | some r => .ok [.value r]
      | none => .fail
    | none => .unmodeled s!"inst {i}"
  | "value_type", .value r => .ok [.ty (valTy st r)]
  | "def_inst", .value r =>
    match st.valueDef[r]? with
    | some (some i) => .ok [.inst i]
    | some none => .fail
    | none => .unmodeled s!"value {r}"
  -- aarch64 ISA-flag extractors: every extension is off in the default flags.
  | "use_lse", .inst _ | "use_dotprod", .inst _ | "use_i8mm", .inst _ => .fail
  -- `lane_count() > 1` / `is_dynamic_vector()`: false for the scalar types of `tyInfo`.
  | "multi_lane", .ty n | "dynamic_lane", .ty n =>
    if (tyInfo n).isSome then .fail else .unmodeled s!"{t.name} on type {n}"
  | "not_i64x2", .ty n => if (tyInfo n).isSome then .ok [] else .unmodeled s!"not_i64x2 on {n}"
  | "tls_model", .ty _ => .ok [enumVal "TlsModel.None"]  -- `tls_model` flag default
  -- `get_as_extended_value`: only values defined by `uextend`/`sextend` (not modelled here).
  | "extended_value_from_value", .value r =>
    match st.valueDef[r]? with
    | some none => .fail
    | some (some i) =>
      match st.insts[i]? with
      | some ⟨.data _ _ (op :: _), _⟩ =>
        if op == enumVal "Opcode.Uextend" || op == enumVal "Opcode.Sextend" then
          .unmodeled "extended_value_from_value on an extend"
        else .fail
      | _ => .unmodeled s!"inst {i}"
    | none => .unmodeled s!"value {r}"
  | "value_array_2", .prim "ValueArray2" [a, b] => .ok [a, b]
  | "value_list_slice", .prim "ValueList" vs => .ok [.prim "ValueSlice" vs]
  | "u64_from_imm64", .int i => .ok [.int (i % 2 ^ 64)]
  | "imm12_from_u64", .int n => match imm12? n.toNat with
    | some imm => if n ≥ 0 then .ok [imm] else .fail
    | none => .fail
  | name, _ => .unmodeled s!"extractor {name}"

def fresh (st : St) : TV × St := (.reg st.nextVreg, { st with nextVreg := st.nextVreg + 1 })

def ctor (t : Term) (args : List TV) (st : St) : ExtResult (TV × St) :=
  match args with
  | [a] =>
    match applyTyPred t.name a with
    | some (.ok ty) => .ok (ty, st)
    | some .fail => .fail
    | some (.unmodeled w) => .unmodeled w
    | none => ctor' t args st
  | _ => ctor' t args st
where
  ctor' (t : Term) (args : List TV) (st : St) : ExtResult (TV × St) :=
    match t.name, args with
    | "put_in_reg", [.value r] =>
      match st.valueReg[r]? with
      | some n => .ok (.reg n, st)
      | none => .unmodeled s!"value {r}"
    | "put_in_regs", [.value r] =>
      match st.valueReg[r]? with
      | some n => .ok (.prim "ValueRegs" [.reg n], st)
      | none => .unmodeled s!"value {r}"
    | "put_in_regs_vec", [.prim "ValueSlice" vs] =>
      let regs := vs.map fun
        | .value r => .prim "ValueRegs" [.reg (st.valueReg.getD r 0)]
        | other => other
      .ok (.prim "ValueRegsVec" regs, st)
    | "use_fp16", [] | "use_csdb", [] => .ok (.bool false, st)
    | "temp_writable_reg", [.ty _] => .ok (fresh st)
    | "writable_reg_to_reg", [r] => .ok (r, st)
    | "writable_zero_reg", [] => .ok (.prim "zero_reg" [], st)
    | "emit", [i] => .ok (.prim "Unit" [], { st with emitted := st.emitted.push i })
    | "gen_return", [rs] =>
      .ok (.prim "Unit" [], { st with emitted := st.emitted.push (.prim "Ret" [rs]) })
    | "value_reg", [r] => .ok (.prim "ValueRegs" [r], st)
    | "value_regs_get", [.prim "ValueRegs" rs, .int i] =>
      match rs[i.toNat]? with
      | some r => .ok (r, st)
      | none => .unmodeled "value_regs_get index"
    | "output", [rs] => .ok (.prim "InstOutput" [rs], st)
    | "output_none", [] => .ok (.prim "InstOutput" [], st)
    | "cond_code", [.data _ k []] =>
      -- `Cond` of an `IntCC`, via the variant *names* (`lower/isle.rs` `cond_code`).
      match condOf k with
      | some c => .ok (enumVal s!"Cond.{c}", st)
      | none => .unmodeled "cond_code"
    | name, _ => .unmodeled s!"constructor {name}"
  /-- `IntCC` variant number to aarch64 `Cond` name (`lower/isle.rs`, `lower_condcode`). -/
  condOf (k : Nat) : Option String :=
    let ccs := ["Equal", "NotEqual", "SignedLessThan", "SignedGreaterThanOrEqual",
      "SignedGreaterThan", "SignedLessThanOrEqual", "UnsignedLessThan",
      "UnsignedGreaterThanOrEqual", "UnsignedGreaterThan", "UnsignedLessThanOrEqual"]
    let conds := ["Eq", "Ne", "Lt", "Ge", "Gt", "Le", "Lo", "Hs", "Hi", "Ls"]
    let name? := ccs.findIdx? fun cc => variant? s!"IntCC.{cc}" == some (intccTy, k)
    name?.bind (conds[·]?)
  intccTy : TypeId := ((variant? "IntCC.Equal").map (·.1)).getD 0

def sem : Sem TV St where
  int _ i := .int i
  bool b := .bool b
  prim ty n := if program.typeName ty == "Type" then some (.ty n) else none
  eq a b := a == b
  mkData ty k fs := .data ty k fs
  unData ty v := match v with
    | .data ty' k fs => if ty == ty' then some (k, fs) else none
    | _ => none
  ctor := ctor
  extract := extract

/-- Run `lower` on each instruction in turn (in the order Cranelift's driver lowers them),
concatenating traces. -/
def lowerInsts (st : St) (insts : List Nat) (cfg : Config := {}) : Except Err (List RuleId × St) :=
  insts.foldlM (init := ([], st)) fun (tr, st) i => do
    let r ← Interp.run program sem cfg "lower" [.inst i] st
    if r.value.isNone then throw (.malformed s!"lower returned none for inst {i}")
    pure (tr ++ r.trace, r.state)

/-- A trace in the format of Cranelift's `trace-log` lines (0-based line numbers). -/
def traceLines (tr : List RuleId) : List String :=
  tr.filterMap fun r => (program.rule? r).map fun r =>
    s!"ISLE {program.termName r.term} {r.pos.file} line {r.pos.line - 1}"

end Isle.Toy
