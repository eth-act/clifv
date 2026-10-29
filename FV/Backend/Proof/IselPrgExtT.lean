module

public import FV.Backend.Proof.IselPrgRoot

@[expose] public section

/-!
# Progress of the ISLE lowering over the typed scope: the transfer functions

The V7 transfer functions (`IselPrgExt`) for the float-capable lowering context of a function of
the typed scope (`Compile.functionET`; context invariant `PInvT`, `IselPrgInvT`):

* `aextT`: `aext` where values are of the typed scope's types (`aVM`: `mCTys`), the instruction
  defining a value (`def_inst`) is an E instruction (`.idata`) or one of the typed scope's other
  instructions with results (`fDataT`, their `InstructionData` spelled out), and the numeric
  extractors of the float constants (`u32_from_ieee32`, `u64_from_ieee64`, `u16_from_u32`,
  `u32_from_u64`, `u64_low32_bits_unset`);
* `actorT`: `actor` with the float constants' immediates (`asimd_mov_mod_imm_zero`,
  `asimd_fp_mod_imm_from_u64`) and `emit` of the float instructions `MInst.ofV` decodes
  (`ofvOkT`: `minstOk` or `minstOkF`).

`aidata` (the `InstructionData` of an E instruction) is V7's.
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Aarch64 PA

/-- A value of the typed scope: one of `mCTys`. -/
def aVM : PA := .val mCTys

/-- The `f32` bit patterns. -/
def aU32 : PA := .int (some 0) (some (2 ^ 32 - 1))

/-- The `f64` bit patterns. -/
def aU64 : PA := .int (some 0) (some (2 ^ 64 - 1))

/-- **The `InstructionData` of the typed scope's instructions with results outside E**:
`f32const`, `f64const`, a float `load`, a float `select`, `bitcast`. -/
def fDataT : List PA :=
  [idat VIdx.InstructionData.UnaryIeee32 [opc VIdx.Opcode.F32const, aU32],
   idat VIdx.InstructionData.UnaryIeee64 [opc VIdx.Opcode.F64const, aU64],
   idat VIdx.InstructionData.Load [opc VIdx.Opcode.Load, aV, .op .memFlags none, .int none none],
   idat VIdx.InstructionData.Ternary [opc VIdx.Opcode.Select, .vals [aV, aVM, aVM]],
   idat VIdx.InstructionData.LoadNoOffset [opc VIdx.Opcode.Bitcast, aVM, .any]]

/-- The outputs of `def_inst` on a value of the typed scope: its defining instruction, one
output per kind (an E instruction, or one of `fDataT`). -/
def defOutsT : List (List PA) := (.idata :: fDataT).map fun d => [.inst (.ty mCTys) d]

/-- `ts` and the E types. -/
def withE (ts : List CTy) : List CTy := ts ++ eCTys.filter (fun t => !ts.contains t)

/-- An integer test `L ≤ i ≤ H` (a generated `try_into` extractor): exact on known bounds. -/
def rangeTest (lo hi : Option Int) (L H : Int) : Option (List (List PA) × Bool) :=
  match lo, hi with
  | some l, some h =>
    if L ≤ l ∧ h ≤ H then okOne [.int lo hi]
    else if h < L ∨ H < l then noMatch
    else mayOne [.int (some (max l L)) (some (min h H))]
  | _, _ => mayOne [range L H]

/-- **Abstract extern extractors over the typed scope** (`externExtract`). -/
def aextT (id : TermId) (a : PA) : Option (List (List PA) × Bool) :=
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
  | TId.def_inst, .val _ => some (defOutsT, false)
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

/-! ## `MInst.ofV` on the float instructions -/

/-- The `FPUOp1` variants (`V.fpuOp1?`). -/
def fpuOp1Idx? : Nat → Option FPUOp1
  | VIdx.FPUOp1.Abs => some FPUOp1.abs | VIdx.FPUOp1.Neg => some .neg
  | VIdx.FPUOp1.Sqrt => some .sqrt | VIdx.FPUOp1.Cvt32To64 => some .cvt32To64
  | VIdx.FPUOp1.Cvt64To32 => some .cvt64To32 | _ => none
/-- The `FPUOp2` variants (`V.fpuOp2?`). -/
def fpuOp2Idx? : Nat → Option FPUOp2
  | VIdx.FPUOp2.Add => some FPUOp2.add | VIdx.FPUOp2.Sub => some .sub
  | VIdx.FPUOp2.Mul => some .mul | VIdx.FPUOp2.Div => some .div
  | VIdx.FPUOp2.Max => some .max | VIdx.FPUOp2.Min => some .min | _ => none
/-- The `FPUOp3` variants (`V.fpuOp3?`). -/
def fpuOp3Idx? : Nat → Option FPUOp3
  | VIdx.FPUOp3.MAdd => some FPUOp3.mAdd | VIdx.FPUOp3.MSub => some .mSub
  | VIdx.FPUOp3.NMAdd => some .nMAdd | VIdx.FPUOp3.NMSub => some .nMSub | _ => none
/-- The `FpuRoundMode` variants (`V.fpuRoundMode?`). -/
def fpuRoundIdx? : Nat → Option FpuRoundMode
  | VIdx.FpuRoundMode.Minus32 => some FpuRoundMode.minus32
  | VIdx.FpuRoundMode.Minus64 => some .minus64 | VIdx.FpuRoundMode.Plus32 => some .plus32
  | VIdx.FpuRoundMode.Plus64 => some .plus64 | VIdx.FpuRoundMode.Zero32 => some .zero32
  | VIdx.FpuRoundMode.Zero64 => some .zero64 | VIdx.FpuRoundMode.Nearest32 => some .nearest32
  | VIdx.FpuRoundMode.Nearest64 => some .nearest64 | _ => none
/-- The `FpuToIntOp` variants (`V.fpuToIntOp?`). -/
def fpuToIntIdx? : Nat → Option FpuToIntOp
  | VIdx.FpuToIntOp.F32ToU32 => some FpuToIntOp.f32ToU32
  | VIdx.FpuToIntOp.F32ToI32 => some .f32ToI32 | VIdx.FpuToIntOp.F32ToU64 => some .f32ToU64
  | VIdx.FpuToIntOp.F32ToI64 => some .f32ToI64 | VIdx.FpuToIntOp.F64ToU32 => some .f64ToU32
  | VIdx.FpuToIntOp.F64ToI32 => some .f64ToI32 | VIdx.FpuToIntOp.F64ToU64 => some .f64ToU64
  | VIdx.FpuToIntOp.F64ToI64 => some .f64ToI64 | _ => none
/-- The `IntToFpuOp` variants (`V.intToFpuOp?`). -/
def intToFpuIdx? : Nat → Option IntToFpuOp
  | VIdx.IntToFpuOp.U32ToF32 => some IntToFpuOp.u32ToF32
  | VIdx.IntToFpuOp.I32ToF32 => some .i32ToF32 | VIdx.IntToFpuOp.U32ToF64 => some .u32ToF64
  | VIdx.IntToFpuOp.I32ToF64 => some .i32ToF64 | VIdx.IntToFpuOp.U64ToF32 => some .u64ToF32
  | VIdx.IntToFpuOp.I64ToF32 => some .i64ToF32 | VIdx.IntToFpuOp.U64ToF64 => some .u64ToF64
  | VIdx.IntToFpuOp.I64ToF64 => some .i64ToF64 | _ => none

/-- A scalar size. -/
def sSize (s : PA) : Bool := enumOk tyScalarSize ScalarSize.ofIdx? s

/-- **The float instructions `MInst.ofV` decodes**, abstractly (S11e4 movement, S11f arithmetic,
comparison, rounding, conversions). -/
def minstOkF (k : Nat) (fs : List PA) : Bool :=
  match k, fs with
  | VIdx.MInst.FpuLoad32, [rd, m, fl] => isReg rd && amodeOk m && isOp .memFlags fl
  | VIdx.MInst.FpuLoad64, [rd, m, fl] => isReg rd && amodeOk m && isOp .memFlags fl
  | VIdx.MInst.FpuStore32, [rd, m, fl] => isReg rd && amodeOk m && isOp .memFlags fl
  | VIdx.MInst.FpuStore64, [rd, m, fl] => isReg rd && amodeOk m && isOp .memFlags fl
  | VIdx.MInst.FpuCSel32, [rd, rn, rm, c] =>
    isReg rd && isReg rn && isReg rm && enumOk tyCond Cond.ofIdx? c
  | VIdx.MInst.FpuCSel64, [rd, rn, rm, c] =>
    isReg rd && isReg rn && isReg rm && enumOk tyCond Cond.ofIdx? c
  | VIdx.MInst.FpuMoveFPImm, [rd, i, s] => isReg rd && isOp .fpModImm i && sSize s
  | VIdx.MInst.VecDupImm, [rd, i, inv, s] =>
    isReg rd && isOp .movModImm i && isBool inv && enumOk tyVectorSize VectorSize.ofIdx? s
  | VIdx.MInst.FpuRR, [o, s, rd, rn] =>
    enumOk tyFPUOp1 fpuOp1Idx? o && sSize s && isReg rd && isReg rn
  | VIdx.MInst.FpuRRR, [o, s, rd, rn, rm] =>
    enumOk tyFPUOp2 fpuOp2Idx? o && sSize s && isReg rd && isReg rn && isReg rm
  | VIdx.MInst.FpuRRRR, [o, s, rd, rn, rm, ra] =>
    enumOk tyFPUOp3 fpuOp3Idx? o && sSize s && isReg rd && isReg rn && isReg rm && isReg ra
  | VIdx.MInst.FpuCmp, [s, rn, rm] => sSize s && isReg rn && isReg rm
  | VIdx.MInst.FpuRound, [o, rd, rn] => enumOk tyFpuRoundMode fpuRoundIdx? o && isReg rd && isReg rn
  | VIdx.MInst.FpuToInt, [o, rd, rn] => enumOk tyFpuToIntOp fpuToIntIdx? o && isReg rd && isReg rn
  | VIdx.MInst.IntToFpu, [o, rd, rn] => enumOk tyIntToFpuOp intToFpuIdx? o && isReg rd && isReg rn
  | _, _ => false

mutual
/-- Every value decodes as an `MInst` of V7's or a float one (`emit` succeeds). -/
def ofvOkT : PA → Bool
  | .bot => true
  | .data t k fs => t == tyMInst && (minstOk k fs || minstOkF k fs)
  | .alts as => ofvOkTL as
  | _ => false
/-- `ofvOkT` of alternatives. -/
def ofvOkTL : List PA → Bool
  | [] => true
  | a :: as => ofvOkT a && ofvOkTL as
end

/-! ## Constructors -/

/-- **Abstract extern constructors over the typed scope** (`externCtor`): `actor`, with `emit` of
the float instructions and the float constants' immediates. -/
def actorT (id : TermId) (as : List PA) : Option (PA × Bool) :=
  match tyPred id with
  | some _ => actor id as
  | none =>
  match id, as with
  | TId.emit, [i] => if ofvOkT i then cOk (.op .unit none) else none
  | TId.asimd_mov_mod_imm_zero, [s] => if sSize s then cOk (.op .movModImm none) else none
  | TId.asimd_fp_mod_imm_from_u64, [x, s] =>
    if isInt x && sSize s then cMay (.op .fpModImm none) else none
  | _, _ => actor id as

end Backend.Proof.Prg
