module

public import FV.Backend.Proof.IselPrgExtT

@[expose] public section

/-!
# Progress of the ISLE lowering over the float scope: the transfer functions (S11f, #35)

`aextG defOuts`: `aextT` (`IselPrgExtT`) with the outputs of `def_inst` (the kinds of instruction
that may define a value) a parameter; `aextT_eq`: `aextT` is `aextG defOutsT`. The float scope
(`Compile.functionETF`: the typed movement scope with the S11f float operations) has the extractors
`aextTF := aextG defOutsTF`, whose `def_inst` may also find a float operation (`fDataTF`: its
`InstructionData`, the operands values of the typed scope (`aVM`), integers (`aV`: the operand of an
`fcvt_from_*`) or floats (`aVF`: the operands of a saturating conversion and of an `fcmp`), an
`fcmp`'s condition one `instData` admits (`fccIdxs`)). Kept apart from `IselPrgExtT` so the typed
scope's table `prgTabT` does not depend on it.
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Aarch64 PA

/-- **Abstract extern extractors over a float-capable context** (`externExtract`), with the
outputs `defOuts` of `def_inst` (the kinds of instruction that may define a value; S11f: the
typed movement scope's `defOutsT`, the float scope's `defOutsTF`). -/
def aextG (defOuts : List (List PA)) (id : TermId) (a : PA) : Option (List (List PA) × Bool) :=
  match tyPred id with
  | some pr =>
    match a with
    | .ty ts =>
      let ok := ts.filter pr
      if ok.isEmpty then noMatch else some ([[.ty ok]], ts.all pr)
    | .bot => noMatch
    | _ => none
  | none =>
  if a.isBot then noMatch else
  match id, a with
  | TId.offset32, .int lo hi => okOne [.int lo hi]
  | TId.def_inst, .val _ => some (defOuts, false)
  | TId.value_type, .val ts => okOne [.ty ts]
  | TId.inst_data_value, .inst t d => okOne [t, d]
  | TId.first_result, .inst _ _ => mayOne [aVM]
  | TId.is_second_result, .val ts => mayOne [.val ts]
  | TId.i64_from_iconst, .val _ => mayOne [.int none none]
  | TId.maybe_uextend, .val ts => okOne [.val (withE ts)]
  | TId.extended_value_from_value, .val _ => mayOne [.op .extended none]
  | TId.little_or_native_endian, .op .memFlags n => okOne [.op .memFlags n]
  | TId.u64_from_imm64, .int lo hi =>
    match (PA.int lo hi).intOf with
    | some i => okOne [exact (u64 i : Int)]
    | none => okOne [.int (some 0) (some (2 ^ 64 - 1))]
  | TId.nonzero_u64_from_imm64, .int lo hi =>
    match (PA.int lo hi).intOf with
    | some i => if i == 0 then noMatch else okOne [exact (u64 i : Int)]
    | none => mayOne [.int (some 0) (some (2 ^ 64 - 1))]
  | TId.imm12_from_u64, a => intTest a (fun i => (Imm12.ofNat? (u64 i)).isSome) [.op .imm12 none]
  | TId.i32_from_i64, .int lo hi =>
    match (PA.int lo hi).intOf with
    | some i => if -(2 ^ 31 : Int) ≤ i ∧ i < 2 ^ 31 then okOne [exact i] else noMatch
    | none => mayOne [range (-(2 ^ 31)) (2 ^ 31 - 1)]
  | TId.u8_from_u64, .int lo hi =>
    match (PA.int lo hi).intOf with
    | some i => if 0 ≤ i ∧ i < 256 then okOne [exact i] else noMatch
    | none => mayOne [range 0 255]
  | TId.single_target, .labels lo n =>
    match n with
    | some 1 => okOne [.label]
    | some _ => noMatch
    | none => if lo ≤ 1 then mayOne [.label] else noMatch
  | TId.two_targets, .labels lo n =>
    match n with
    | some 2 => okOne [.label, .label]
    | some _ => noMatch
    | none => if lo ≤ 2 then mayOne [.label, .label] else noMatch
  | TId.jump_table_targets, .labels lo n =>
    match n with
    | some 0 => noMatch
    | some (k + 1) => okOne [.label, .labels k (some k)]
    | none => if 1 ≤ lo then okOne [.label, .labels (lo - 1) none] else mayOne [.label, .labels 0 none]
  | TId.value_list_slice, .vals as => okOne [.vals as]
  | TId.value_list_slice, .valsMin lo => okOne [.valsMin lo]
  | TId.value_slice_unwrap, .vals as =>
    match as with
    | b :: bs => okOne [b, .vals bs]
    | [] => noMatch
  | TId.value_slice_unwrap, .valsMin lo =>
    if 1 ≤ lo then okOne [aVM, .valsMin (lo - 1)] else mayOne [aVM, .valsMin 0]
  | TId.value_array_2, .vals [x, y] => okOne [x, y]
  | TId.value_array_3, .vals [x, y, z] => okOne [x, y, z]
  | TId.symbol_value_data, .op .globalValue _ => okOne [.op .extName none, aDist, .int none none]
  | TId.symbol_value_data, .op .tlsGlobalValue _ => okOne [.op .extName none, aDist, .int none none]
  | TId.block_array_2, .blockCalls 2 => okOne [.blockCalls 1, .blockCalls 1]
  | TId.func_ref_data, .op .funcRef n => okOne [.op .sig n, .op .extName none, aDist, .bool (some false)]
  | TId.func_ref_data, .op .funcRefTry _ =>
    okOne [.op .sigTry none, .op .extName none, aDist, .bool (some false)]
  | TId.multi_lane, .ty ts =>
    if ts.all (·.laneCount ≤ 1) then noMatch else mayOne [.int none none, .int none none]
  | TId.dynamic_lane, .ty _ => noMatch
  | TId.not_i64x2, .ty ts =>
    if ts.contains (.vec 64 2 false) then mayOne [] else okOne []
  | TId.use_lse, .inst _ _ => noMatch
  | TId.use_dotprod, .inst _ _ => noMatch
  | TId.use_i8mm, .inst _ _ => noMatch
  | TId.sign_return_address_disabled, _ => okOne []
  | TId.tls_model, .ty _ => okOne [.data tyTlsModel VIdx.TlsModel.ElfGd []]
  | TId.exception_sig, .op .exnTable n => okOne [.op .sig n]
  | TId.exception_sig, .op .exnTry _ => okOne [.op .sigTry none]
  | TId.u32_from_ieee32, .int lo hi => okOne [.int lo hi]
  | TId.u64_from_ieee64, .int lo hi => okOne [.int lo hi]
  | TId.u16_from_u32, .int lo hi => rangeTest lo hi 0 (2 ^ 16 - 1)
  | TId.u32_from_u64, .int lo hi => rangeTest lo hi 0 (2 ^ 32 - 1)
  | TId.u64_low32_bits_unset, a => intTest a (fun i => u64 i % 2 ^ 32 == 0) [a]
  | _, _ => none

/-- `aextT` is `aextG` with the typed movement scope's defining instructions. -/
theorem aextT_eq (id : TermId) (a : PA) : aextT id a = aextG defOutsT id a := rfl

/-- A float value: `f32` or `f64`. -/
def aVF : PA := .val [.float 32, .float 64]

/-- The `fcmp` conditions `instData` admits (`Backend.fccOk`): every `FloatCC` but `one` (7) and
`ueq` (9). -/
def fccIdxs : List Nat := [0, 1, 2, 3, 4, 5, 6, 8, 10, 11, 12, 13]

/-- The data of a two-operand float arithmetic instruction. -/
def fDataBin : PA := idat VIdx.InstructionData.Binary [aOps [VIdx.Opcode.Fadd, VIdx.Opcode.Fsub,
  VIdx.Opcode.Fmul, VIdx.Opcode.Fdiv, VIdx.Opcode.Fmin, VIdx.Opcode.Fmax], .vals [aVM, aVM]]

/-- The data of a one-operand float arithmetic or rounding instruction. -/
def fDataUn : PA := idat VIdx.InstructionData.Unary [aOps [VIdx.Opcode.Sqrt, VIdx.Opcode.Fneg,
  VIdx.Opcode.Fabs, VIdx.Opcode.Ceil, VIdx.Opcode.Floor, VIdx.Opcode.Trunc, VIdx.Opcode.Nearest,
  VIdx.Opcode.Fpromote, VIdx.Opcode.Fdemote], aVM]

/-- The data of a conversion from an integer. -/
def fDataFrom : PA :=
  idat VIdx.InstructionData.Unary [aOps [VIdx.Opcode.FcvtFromUint, VIdx.Opcode.FcvtFromSint], aV]

/-- The data of a saturating conversion of a float. -/
def fDataTo : PA :=
  idat VIdx.InstructionData.Unary [aOps [VIdx.Opcode.FcvtToUintSat, VIdx.Opcode.FcvtToSintSat], aVF]

/-- The data of an `fcmp`. -/
def fDataCmp : PA := idat VIdx.InstructionData.FloatCompare [opc VIdx.Opcode.Fcmp, .vals [aVF, aVF],
  enumAlts TyId.FloatCC fccIdxs]

/-- **The `InstructionData` of the float scope's instructions with results outside E**:
`fDataT` and the S11f float operations (`Compile.instETF`): the two-operand arithmetic, the
one-operand arithmetic and rounding, the conversions from an integer, the saturating conversions
of a float, and `fcmp`. -/
def fDataTF : List PA := fDataT ++ [fDataBin, fDataUn, fDataFrom, fDataTo, fDataCmp]

/-- The outputs of `def_inst` on a value of the float scope (`defOutsT` with `fDataTF`). -/
def defOutsTF : List (List PA) := (.idata :: fDataTF).map fun d => [.inst (.ty mCTys) d]

/-- **Abstract extern extractors over the float scope**: `aextG` with `defOutsTF`. -/
def aextTF (id : TermId) (a : PA) : Option (List (List PA) × Bool) := aextG defOutsTF id a

end Backend.Proof.Prg
