import FV.Backend.Proof.IselContract
import FV.Backend.Proof.IselPrgModel

/-!
# Progress of the ISLE lowering (V7): the transfer functions of the extern helpers

The abstract counterparts of `externExtract` (`aext`) and `externCtor` (`actor`) of
`FV/Backend/Isel.lean`, and the fields of the `InstructionData` of an E instruction (`aidata`).
Each mirrors the dispatch of its concrete function: `none` where the helper may throw
(`unmodeled`, or a total helper failing), else the abstract result and whether the helper surely
succeeds. `ofvOk` is the abstract `MInst.ofV` (`emit` decodes its instruction). Their soundness
(`Model`) is `IselPrgExtSound*`.
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Aarch64

namespace PA

mutual
/-- The variant indices of an enum value of type `ty` (`none`: maybe not one). -/
def enumsOf (ty : TypeId) : PA → Option (List Nat)
  | .bot => some []
  | .data t k fs => if t == ty && fs.isEmpty then some [k] else none
  | .alts as => enumsOfL ty as
  | _ => none
/-- `enumsOf` of alternatives. -/
def enumsOfL (ty : TypeId) : List PA → Option (List Nat)
  | [] => some []
  | a :: as => do
    let x ← enumsOf ty a
    let y ← enumsOfL ty as
    pure (x ++ y)
end

/-- Every value is an enum value of `ty` whose variant `g` decodes. -/
def enumOk {α : Type} (ty : TypeId) (g : Nat → Option α) (a : PA) : Bool :=
  match a.enumsOf ty with
  | some ks => ks.all fun k => (g k).isSome
  | none => false

/-- The types of a type value. -/
def tysOf : PA → Option (List CTy)
  | .ty ts => some ts
  | .bot => some []
  | _ => none

/-- Exactly the integer `i`. -/
def exact (i : Int) : PA := .int (some i) (some i)

/-- The integers of `[lo, hi]`. -/
def range (lo hi : Int) : PA := .int (some lo) (some hi)

/-- The exact integer of an integer value. -/
def intOf : PA → Option Int
  | .int (some l) (some h) => if l == h then some l else none
  | _ => none

/-- The upper bound of an integer value. -/
def hiOf : PA → Option Int
  | .int _ (some h) => some h
  | _ => none

/-- The lower bound of an integer value. -/
def loOf : PA → Option Int
  | .int (some l) _ => some l
  | _ => none

/-- A register. -/
def isReg : PA → Bool
  | .reg => true
  | .bot => true
  | _ => false

/-- An integer. -/
def isInt : PA → Bool
  | .int _ _ => true
  | .bot => true
  | _ => false

/-- A boolean. -/
def isBool : PA → Bool
  | .bool _ => true
  | .bot => true
  | _ => false

/-- An operand of kind `k`. -/
def isOp (k : OK) : PA → Bool
  | .op k' _ => k' == k
  | .bot => true
  | _ => false

/-- A non-negative integer (`V.nat?`). -/
def isNat : PA → Bool
  | .int (some l) _ => decide (0 ≤ l)
  | .bot => true
  | _ => false

/-- A label. -/
def isLabel : PA → Bool
  | .label => true
  | .bot => true
  | _ => false

/-- A type. -/
def isTy : PA → Bool
  | .ty _ => true
  | .bot => true
  | _ => false

/-- Enum values of the listed variants of `ty`. -/
def enumAlts (ty : TypeId) (ks : List Nat) : PA := .alts (ks.map fun k => .data ty k [])

end PA

open PA

/-! ## `MInst.ofV`, abstractly -/

mutual
/-- Every value decodes as an `AMode` (`V.amode?`). -/
def amodeOk : PA → Bool
  | .bot => true
  | .alts as => amodeOkL as
  | .data t k fs =>
    t == tyAMode &&
    match k, fs with
    | VIdx.AMode.RegReg, [a, b] => isReg a && isReg b
    | VIdx.AMode.RegScaled, [a, b] => isReg a && isReg b
    | VIdx.AMode.RegScaledExtended, [a, b, e] =>
      isReg a && isReg b && enumOk tyExtendOp ExtendOp.ofIdx? e
    | VIdx.AMode.RegExtended, [a, b, e] => isReg a && isReg b && enumOk tyExtendOp ExtendOp.ofIdx? e
    | VIdx.AMode.Unscaled, [a, .op .simm9 _] => isReg a
    | VIdx.AMode.UnsignedOffset, [a, .op .uimm12Scaled _] => isReg a
    | VIdx.AMode.RegOffset, [a, o] => isReg a && isInt o
    | VIdx.AMode.SPOffset, [o] => isInt o
    | VIdx.AMode.FPOffset, [o] => isInt o
    | VIdx.AMode.IncomingArg, [o] => isInt o
    | VIdx.AMode.SlotOffset, [o] => isInt o
    | VIdx.AMode.SPPreIndexed, [.op .simm9 _] => true
    | VIdx.AMode.SPPostIndexed, [.op .simm9 _] => true
    | _, _ => false
  | _ => false
/-- `amodeOk` of alternatives. -/
def amodeOkL : List PA → Bool
  | [] => true
  | a :: as => amodeOk a && amodeOkL as
end

mutual
/-- Every value decodes as a `CondBrKind` (`V.condBrKind?`). -/
def condBrOk : PA → Bool
  | .bot => true
  | .alts as => condBrOkL as
  | .data t k fs =>
    t == tyCondBrKind &&
    match k, fs with
    | VIdx.CondBrKind.Zero, [r, s] => isReg r && enumOk tyOperandSize OperandSize.ofIdx? s
    | VIdx.CondBrKind.NotZero, [r, s] => isReg r && enumOk tyOperandSize OperandSize.ofIdx? s
    | VIdx.CondBrKind.Cond, [c] => enumOk tyCond Cond.ofIdx? c
    | _, _ => false
  | _ => false
/-- `condBrOk` of alternatives. -/
def condBrOkL : List PA → Bool
  | [] => true
  | a :: as => condBrOk a && condBrOkL as
end

/-- The `MoveWideOp` variants (`V.moveWideOp?`). -/
def mwOp? : Nat → Option MoveWideOp
  | VIdx.MoveWideOp.MovZ => some .movZ | VIdx.MoveWideOp.MovN => some .movN | _ => none
/-- The `BfmOp` variants (`V.bfmOp?`). -/
def bfmOp? : Nat → Option BfmOp
  | VIdx.BfmOp.UBfm => some .uBfm | VIdx.BfmOp.SBfm => some .sBfm | _ => none
/-- The `TestBitAndBranchKind` variants (`V.tbKind?`). -/
def tbKind? : Nat → Option TestBitAndBranchKind
  | VIdx.TestBitAndBranchKind.Z => some .z | VIdx.TestBitAndBranchKind.NZ => some .nz | _ => none
/-- The `VecMisc2` variants (`V.vecMisc2?`). -/
def vecMisc2? : Nat → Option VecMisc2
  | VIdx.VecMisc2.Cnt => some .cnt | _ => none
/-- The `VecLanesOp` variants (`V.vecLanesOp?`). -/
def vecLanesOp? : Nat → Option VecLanesOp
  | VIdx.VecLanesOp.Addv => some .addv | _ => none
/-- The `VecALUOp` variants (`V.vecALUOp?`). -/
def vecALUOp? : Nat → Option VecALUOp
  | VIdx.VecALUOp.Addp => some .addp | _ => none

/-- **`MInst.ofV` decodes every value of variant `k` with fields `fs`.** -/
def minstOk (k : Nat) (fs : List PA) : Bool :=
  match k, fs with
  | VIdx.MInst.AluRRR, [o, s, rd, rn, rm] =>
    enumOk tyALUOp ALUOp.ofIdx? o && enumOk tyOperandSize OperandSize.ofIdx? s &&
      isReg rd && isReg rn && isReg rm
  | VIdx.MInst.AluRRRR, [o, s, rd, rn, rm, ra] =>
    enumOk tyALUOp3 ALUOp3.ofIdx? o && enumOk tyOperandSize OperandSize.ofIdx? s &&
      isReg rd && isReg rn && isReg rm && isReg ra
  | VIdx.MInst.AluRRImm12, [o, s, rd, rn, i] =>
    enumOk tyALUOp ALUOp.ofIdx? o && enumOk tyOperandSize OperandSize.ofIdx? s &&
      isReg rd && isReg rn && isOp .imm12 i
  | VIdx.MInst.AluRRImmLogic, [o, s, rd, rn, i] =>
    enumOk tyALUOp ALUOp.ofIdx? o && enumOk tyOperandSize OperandSize.ofIdx? s &&
      isReg rd && isReg rn && isOp .immLogic i
  | VIdx.MInst.AluRRImmShift, [o, s, rd, rn, i] =>
    enumOk tyALUOp ALUOp.ofIdx? o && enumOk tyOperandSize OperandSize.ofIdx? s &&
      isReg rd && isReg rn && isOp .immShift i
  | VIdx.MInst.AluRRRShift, [o, s, rd, rn, rm, sh] =>
    enumOk tyALUOp ALUOp.ofIdx? o && enumOk tyOperandSize OperandSize.ofIdx? s &&
      isReg rd && isReg rn && isReg rm && isOp .shiftAmt sh
  | VIdx.MInst.AluRRRExtend, [o, s, rd, rn, rm, e] =>
    enumOk tyALUOp ALUOp.ofIdx? o && enumOk tyOperandSize OperandSize.ofIdx? s &&
      isReg rd && isReg rn && isReg rm && enumOk tyExtendOp ExtendOp.ofIdx? e
  | VIdx.MInst.BitRR, [o, s, rd, rn] =>
    enumOk tyBitOp BitOp.ofIdx? o && enumOk tyOperandSize OperandSize.ofIdx? s &&
      isReg rd && isReg rn
  | VIdx.MInst.Mov, [s, rd, rm] => enumOk tyOperandSize OperandSize.ofIdx? s && isReg rd && isReg rm
  | VIdx.MInst.MovWide, [o, rd, i, s] =>
    enumOk tyMoveWideOp mwOp? o && isReg rd && isOp .mwc i && enumOk tyOperandSize OperandSize.ofIdx? s
  | VIdx.MInst.MovK, [rd, rn, i, s] =>
    isReg rd && isReg rn && isOp .mwc i && enumOk tyOperandSize OperandSize.ofIdx? s
  | VIdx.MInst.Extend, [rd, rn, sg, a, b] => isReg rd && isReg rn && isBool sg && isNat a && isNat b
  | VIdx.MInst.BitfieldMove, [s, o, rd, rn, a, b] =>
    enumOk tyOperandSize OperandSize.ofIdx? s && enumOk tyBfmOp bfmOp? o && isReg rd && isReg rn &&
      isOp .uimm6 a && isOp .uimm6 b
  | VIdx.MInst.CSet, [rd, c] => isReg rd && enumOk tyCond Cond.ofIdx? c
  | VIdx.MInst.CSel, [rd, c, rn, rm] => isReg rd && enumOk tyCond Cond.ofIdx? c && isReg rn && isReg rm
  | VIdx.MInst.CCmp, [s, rn, rm, fl, c] =>
    enumOk tyOperandSize OperandSize.ofIdx? s && isReg rn && isReg rm && isOp .nzcv fl &&
      enumOk tyCond Cond.ofIdx? c
  | VIdx.MInst.CCmpImm, [s, rn, i, fl, c] =>
    enumOk tyOperandSize OperandSize.ofIdx? s && isReg rn && isOp .uimm5 i && isOp .nzcv fl &&
      enumOk tyCond Cond.ofIdx? c
  | VIdx.MInst.MovToFpu, [rd, rn, s] =>
    isReg rd && isReg rn && enumOk tyScalarSize ScalarSize.ofIdx? s
  | VIdx.MInst.MovFromVec, [rd, rn, i, s] =>
    isReg rd && isReg rn && isNat i && enumOk tyScalarSize ScalarSize.ofIdx? s
  | VIdx.MInst.VecMisc, [o, rd, rn, s] =>
    enumOk tyVecMisc2 vecMisc2? o && isReg rd && isReg rn && enumOk tyVectorSize VectorSize.ofIdx? s
  | VIdx.MInst.VecLanes, [o, rd, rn, s] =>
    enumOk tyVecLanesOp vecLanesOp? o && isReg rd && isReg rn &&
      enumOk tyVectorSize VectorSize.ofIdx? s
  | VIdx.MInst.VecRRR, [o, rd, rn, rm, s] =>
    enumOk tyVecALUOp vecALUOp? o && isReg rd && isReg rn && isReg rm &&
      enumOk tyVectorSize VectorSize.ofIdx? s
  | VIdx.MInst.Call, [i] => isOp .callInfo i
  | VIdx.MInst.CallInd, [i] => isOp .callInfo i
  | VIdx.MInst.Jump, [t] => isLabel t
  | VIdx.MInst.CondBr, [t, e, k] => isLabel t && isLabel e && condBrOk k
  | VIdx.MInst.TestBitAndBranch, [k, t, e, rn, b] =>
    enumOk tyTBKind tbKind? k && isLabel t && isLabel e && isReg rn && isNat b
  | VIdx.MInst.TrapIf, [k, c] => condBrOk k && isOp .trapCode c
  | VIdx.MInst.Udf, [c] => isOp .trapCode c
  | VIdx.MInst.JTSequence, [d, ts, ridx, t1, t2] =>
    isLabel d && (match ts with | .labels _ _ => true | _ => false) && isReg ridx && isReg t1 &&
      isReg t2
  | VIdx.MInst.LoadExtNameGot, [rd, nm] => isReg rd && isOp .extName nm
  | VIdx.MInst.LoadExtNameNear, [rd, nm, o] => isReg rd && isOp .extName nm && isInt o
  | VIdx.MInst.LoadAddr, [rd, m] => isReg rd && amodeOk m
  | VIdx.MInst.EmitIsland, [n] => isNat n
  | VIdx.MInst.LoadAcquire, [tA, rt, rn, fl] => isTy tA && isReg rt && isReg rn && isOp .memFlags fl
  | VIdx.MInst.StoreRelease, [tA, rt, rn, fl] => isTy tA && isReg rt && isReg rn && isOp .memFlags fl
  | VIdx.MInst.AtomicRMWLoop, [tA, o, fl, addr, operand, oldval, s1, s2] =>
    isTy tA && enumOk tyAtomicRmwLoopOp (fun k => AtomicRmwLoopOp.all[k]?) o &&
      isOp .memFlags fl && isReg addr && isReg operand && isReg oldval && isReg s1 && isReg s2
  | VIdx.MInst.AtomicCASLoop, [tA, fl, addr, expect, replace, oldval, scratch] =>
    isTy tA && isOp .memFlags fl && isReg addr && isReg expect && isReg replace && isReg oldval &&
      isReg scratch
  | VIdx.MInst.CSetm, [rd, c] => isReg rd && enumOk tyCond Cond.ofIdx? c
  | VIdx.MInst.Fence, [] => true
  | VIdx.MInst.ElfTlsGetAddr, [s, rd, tmp] => isOp .extName s && isReg rd && isReg tmp
  | k, [rd, m, fl] =>
    match loadOpOfIdx? k, storeOpOfIdx? k with
    | some _, _ => isReg rd && amodeOk m && isOp .memFlags fl
    | none, some _ => isReg rd && amodeOk m && isOp .memFlags fl
    | none, none => false
  | _, _ => false

mutual
/-- Every value decodes as an `MInst` (`emit` succeeds). -/
def ofvOk : PA → Bool
  | .bot => true
  | .data t k fs => t == tyMInst && minstOk k fs
  | .alts as => ofvOkL as
  | _ => false
/-- `ofvOk` of alternatives. -/
def ofvOkL : List PA → Bool
  | [] => true
  | a :: as => ofvOk a && ofvOkL as
end

/-! ## Extractors -/

/-- The `RelocDistance` values. -/
def aDist : PA := enumAlts tyRelocDistance [VIdx.RelocDistance.Near, VIdx.RelocDistance.Far]

/-- An extractor result that surely is `fs`. -/
def okOne (fs : List PA) : Option (List (List PA) × Bool) := some ([fs], true)
/-- An extractor result that is `fs` or fails. -/
def mayOne (fs : List PA) : Option (List (List PA) × Bool) := some ([fs], false)
/-- An extractor that surely fails. -/
def noMatch : Option (List (List PA) × Bool) := some ([], false)

/-- A fallible test on an exact integer (`p i`: succeeds with `fs`), any outcome on an unknown one. -/
def intTest (a : PA) (p : Int → Bool) (fs : List PA) : Option (List (List PA) × Bool) :=
  match a with
  | .int _ _ =>
    match a.intOf with
    | some i => if p i then okOne fs else noMatch
    | none => mayOne fs
  | .bot => noMatch
  | _ => none

/-- **Abstract extern extractors** (`externExtract`). -/
def aext (id : TermId) (a : PA) : Option (List (List PA) × Bool) :=
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
  | TId.def_inst, .val _ => mayOne [.inst (.ty eCTys) .idata]
  | TId.value_type, .val ts => okOne [.ty ts]
  | TId.inst_data_value, .inst t d => okOne [t, d]
  | TId.first_result, .inst _ _ => mayOne [.val eCTys]
  | TId.is_second_result, .val ts => mayOne [.val ts]
  | TId.i64_from_iconst, .val _ => mayOne [.int none none]
  | TId.maybe_uextend, .val _ => okOne [.val eCTys]
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
    if 1 ≤ lo then okOne [.val eCTys, .valsMin (lo - 1)] else mayOne [.val eCTys, .valsMin 0]
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
  | _, _ => none

/-! ## Constructors -/

/-- A constructor result that surely is `a`. -/
def cOk (a : PA) : Option (PA × Bool) := some (a, true)
/-- A constructor result that is `a` or fails. -/
def cMay (a : PA) : Option (PA × Bool) := some (a, false)

/-- The signed condition codes (`signed_cond_code`). -/
def signedCCs : List Nat :=
  [VIdx.IntCC.SignedGreaterThanOrEqual, VIdx.IntCC.SignedGreaterThan,
   VIdx.IntCC.SignedLessThanOrEqual, VIdx.IntCC.SignedLessThan]
/-- The unsigned condition codes (`unsigned_cond_code`). -/
def unsignedCCs : List Nat :=
  [VIdx.IntCC.Equal, VIdx.IntCC.UnsignedGreaterThanOrEqual, VIdx.IntCC.UnsignedGreaterThan,
   VIdx.IntCC.UnsignedLessThanOrEqual, VIdx.IntCC.UnsignedLessThan, VIdx.IntCC.NotEqual]

/-- A filter of condition codes: the codes of `cc` in `ok` (it fails on the others). -/
def ccFilter (cc : PA) (ok : List Nat) : Option (PA × Bool) := do
  let ks ← cc.enumsOf tyIntCC
  let good := ks.filter (ok.contains ·)
  if good.isEmpty then some (.bot, false)
  else some (enumAlts tyIntCC good, ks.all (ok.contains ·))

/-- Every type of `a` satisfies `p` (and `a` is a type value). -/
def tysAll (a : PA) (p : CTy → Bool) : Bool :=
  match a.tysOf with
  | some ts => ts.all p
  | none => false

/-- A binary integer operation, exact on exact arguments. -/
def intOp2 (a b : PA) (g : Int → Int → Int) : Option (PA × Bool) :=
  if isInt a && isInt b then
    cOk (match a.intOf, b.intOf with
      | some x, some y => exact (g x y)
      | _, _ => .int none none)
  else none

/-- A unary integer operation, exact on an exact argument. -/
def intOp1 (a : PA) (g : Int → Int) : Option (PA × Bool) :=
  if isInt a then cOk (match a.intOf with | some x => exact (g x) | none => .int none none) else none

/-- A test on an exact integer, any outcome on an unknown one. -/
def boolOp2 (a b : PA) (g : Int → Int → Bool) : Option (PA × Bool) :=
  if isInt a && isInt b then cOk (.bool (do pure (g (← a.intOf) (← b.intOf)))) else none

/-- The type-dependent integer of a single type. -/
def tyInt (a : PA) (g : CTy → Int) : Option (PA × Bool) :=
  match a.tysOf with
  | some (t :: ts) =>
    let vs := (t :: ts).map g
    cOk (.int (some (vs.foldl min (g t))) (some (vs.foldl max (g t))))
  | some [] => some (.bot, true)
  | none => none

/-- An operand of a total helper that fails outside `ok`: every exact type/integer pair must
pass. -/
def tyIntAll (ty i : PA) (ok : CTy → Int → Bool) (r : PA) : Option (PA × Bool) := do
  let ts ← ty.tysOf
  let n ← i.intOf
  if ts.all (ok · n) then cOk r else none

/-- A partial helper on a type and an integer: exact when the integer is (`ok t n`: it
succeeds), else it may fail. -/
def exactTest (tA x : PA) (ok : CTy → Int → Bool) (r : PA) : Option (PA × Bool) :=
  if isTy tA && isInt x then
    match tA.tysOf, x.intOf with
    | some ts, some n =>
      let good := ts.filter (ok · n)
      if good.isEmpty then some (.bot, false) else some (r, good.length == ts.length)
    | _, _ => cMay r
  else none

/-- A partial helper on one integer: exact when the integer is. -/
def exactTest1 (x : PA) (ok : Int → Option Int) : Option (PA × Bool) :=
  if isInt x then
    match x.intOf with
    | some n =>
      match ok n with
      | some m => cOk (exact m)
      | none => some (.bot, false)
    | none => cMay (.int none none)
  else none

/-- **Abstract extern constructors** (`externCtor`). -/
def actor (id : TermId) (as : List PA) : Option (PA × Bool) :=
  match tyPred id with
  | some pr =>
    match as with
    | [.ty ts] =>
      let ok := ts.filter pr
      if ok.isEmpty then some (.bot, false) else some (.ty ok, ts.all pr)
    | _ => none
  | none =>
  match id, as with
  | TId.i64_sextend_imm64, [tA, x] =>
    if isTy tA && isInt x then
      match tA.tysOf, x.intOf with
      | some [t], some v => cOk (exact (sextFrom t.bits v))
      | _, _ => cOk (.int none none)
    else none
  | TId.ty_bits, [tA] => tyInt tA fun t => t.bits
  | TId.ty_bytes, [tA] => tyInt tA fun t => t.bytes
  | TId.ty_mask, [tA] => tyInt tA fun t => 2 ^ t.bits - 1
  | TId.offset32_to_i32, [x] => intOp1 x fun z => z
  | TId.i32_to_offset32, [x] => intOp1 x fun z => z
  | TId.signed_cond_code, [cc] => ccFilter cc signedCCs
  | TId.unsigned_cond_code, [cc] => ccFilter cc unsignedCCs
  | TId.trap_code_division_by_zero, [] => cOk (.op .trapCode none)
  | TId.trap_code_integer_overflow, [] => cOk (.op .trapCode none)
  | TId.safe_divisor_from_imm64, [tA, x] =>
    exactTest tA x (fun t v =>
      !(u64 v % 2 ^ (t.bytes * 8) == 0 || u64 v % 2 ^ (t.bytes * 8) == 2 ^ (t.bytes * 8) - 1))
      (.int none none)
  | TId.value_reg, [r] => if isReg r then cOk (.regs 1) else none
  | TId.value_regs, [r, s] => if isReg r && isReg s then cOk (.regs 2) else none
  | TId.output_none, [] => cOk (.regsVec (some 0))
  | TId.output, [.regs n] => cOk (if n == 1 then .regsVec (some 1) else .any)
  | TId.output_vec, [.regsVec n] => cOk (.regsVec n)
  | TId.temp_writable_reg, [tA] => if tysAll tA (·.regClass?.isSome) then cOk .reg else none
  | TId.opportunistic_def, [_, _] => cOk (.op .unit none)
  | TId.put_in_reg, [.val _] => cOk .reg
  | TId.put_in_regs, [.val _] => cOk (.regs 1)
  | TId.put_in_regs_vec, [.vals xs] => if xs.all isVal then cOk (.regsVec (some xs.length)) else none
  | TId.put_in_regs_vec, [.valsMin _] => cOk (.regsVec none)
  | TId.value_regs_get, [.regs n, i] =>
    match i.intOf with
    | some k => if 0 ≤ k ∧ k < n then cOk .reg else none
    | none => none
  | TId.jump_table_size, [.labels _ _] => cOk (.int (some 0) none)
  | TId.writable_reg_to_reg, [r] => cOk r
  | TId.invalid_reg, [] => cOk .reg
  | TId.is_sinkable_inst, [_] => some (.bot, false)
  | TId.emit, [i] => if ofvOk i then cOk (.op .unit none) else none
  | TId.box_external_name, [n] => cOk n
  | TId.abi_sig, [s] => cOk s
  | TId.abi_stackslot_addr, [rd, .op .stackSlot _, o] =>
    if isInt o then
      cOk (.data tyMInst VIdx.MInst.LoadAddr [rd, .data tyAMode VIdx.AMode.SlotOffset [.int none none]])
    else none
  | TId.abi_stackslot_offset_into_slot_region, [.op .stackSlot _, a, b] =>
    if isInt a && isInt b then cOk (.int none none) else none
  | TId.gen_return, [.regsVec (some n)] => if n ≤ 8 then cOk (.op .unit none) else none
  | TId.gen_call_output, [.op .sig n] => cOk (.regsVec n)
  | TId.gen_call_output, [.op .sigTry _] => cOk (.regsVec none)
  | TId.gen_call_args, [.op .sig _, .regsVec _] => cOk (.op .callArgs none)
  | TId.gen_call_args, [.op .sigTry _, .regsVec _] => cOk (.op .callArgs none)
  | TId.gen_call_rets, [.op .sig _, .regsVec (some n)] =>
    if n ≤ 8 then cOk (.op .callRets none) else none
  | TId.gen_call_rets, [.op .sigTry _, .regsVec (some n)] =>
    if n ≤ 8 then cOk (.op .callRets none) else none
  | TId.try_call_none, [] => cOk (.op .tryCallNone none)
  | TId.try_call_info, [.op .exnTry (some m), .labels _ (some k)] =>
    if k == m + 1 then cOk (.op .tryCallInfo none) else none
  | TId.gen_try_call_rets, [.op .sigTry _] => cOk (.op .callRets none)
  | TId.gen_call_info, [.op .sig _, .op .extName _, .op .callArgs _, .op .callRets _, _, _] =>
    cOk (.op .callInfo none)
  | TId.gen_call_info, [.op .sigTry _, .op .extName _, .op .callArgs _, .op .callRets _, _, _] =>
    cOk (.op .callInfo none)
  | TId.gen_call_ind_info, [.op .sig _, r, .op .callArgs _, .op .callRets _, _] =>
    if isReg r then cOk (.op .callInfo none) else none
  | TId.gen_call_ind_info, [.op .sigTry _, r, .op .callArgs _, .op .callRets _, _] =>
    if isReg r then cOk (.op .callInfo none) else none
  | TId.use_fp16, [] => cOk (.bool (some false))
  | TId.is_pic, [] => cOk (.bool (some true))
  | TId.move_wide_const_from_u64, [tA, x] =>
    exactTest tA x (fun t n =>
      (MoveWideConst.ofNat? (if t.bits < 64 then u64 n % 2 ^ t.bits else u64 n)).isSome) (.op .mwc none)
  | TId.move_wide_const_from_inverted_u64, [tA, x] =>
    exactTest tA x (fun t n =>
      (MoveWideConst.ofNat? (if t.bits < 64 then (2 ^ 64 - 1 - u64 n) % 2 ^ t.bits
        else 2 ^ 64 - 1 - u64 n)).isSome) (.op .mwc none)
  | TId.imm_logic_from_u64, [tA, x] =>
    exactTest tA x (fun t n => (t == .int 32 || t == .int 64) &&
      (ImmLogic.ofNat? (u64 n) (.ofBits t.bits)).isSome) (.op .immLogic none)
  | TId.imm_size_from_type, [tA] =>
    match tA.tysOf with
    | some ts =>
      let ok := ts.filter fun t => t == .int 32 || t == .int 64
      if ok.isEmpty then some (.bot, false) else some (.int none none, ts.all fun t => t == .int 32 || t == .int 64)
    | none => none
  | TId.imm_logic_from_imm64, [tA, x] =>
    exactTest tA x (fun t n =>
      ((if t.bits < 32 then CTy.int 32 else t) == .int 32 ||
        (if t.bits < 32 then CTy.int 32 else t) == .int 64) &&
      (ImmLogic.ofNat? (u64 n) (.ofBits (if t.bits < 32 then CTy.int 32 else t).bits)).isSome)
      (.op .immLogic none)
  | TId.imm_shift_from_imm64, [tA, x] =>
    if isInt x then
      match tA.tysOf with
      | some ts => some (.op .immShift none, ts.all fun t => t.bits ≤ 64)
      | none => none
    else none
  | TId.imm_shift_from_u8, [x] =>
    match x.hiOf with
    | some n => if isInt x && n < 64 then cOk (.op .immShift none) else none
    | none => none
  | TId.u8_into_uimm5, [x] =>
    match x.hiOf with
    | some n => if isInt x && n < 32 then cOk (.op .uimm5 none) else none
    | none => none
  | TId.u8_into_imm12, [x] =>
    match x.loOf, x.hiOf with
    | some l, some h => if 0 ≤ l && h < 4096 then cOk (.op .imm12 none) else none
    | _, _ => none
  | TId.u64_into_imm_logic, [tA, x] =>
    tyIntAll tA x (fun t n => (t == .int 32 || t == .int 64) &&
      (ImmLogic.ofNat? (u64 n) (.ofBits t.bits)).isSome) (.op .immLogic none)
  | TId.branch_target, [.label] => cOk .label
  | TId.targets_jt_space, [.labels _ _] => cOk (.int (some 0) none)
  | TId.lshl_from_imm64, [tA, x] =>
    exactTest tA x (fun t n => (shiftImm? (u64 n)).isSome && decide (t.bits ≤ 255))
      (.op .shiftAmt none)
  | TId.ashr_from_u64, [tA, x] =>
    exactTest tA x (fun t n => (shiftImm? n.toNat).isSome && decide (t.bits ≤ 255))
      (.op .shiftAmt none)
  | TId.put_extended_in_reg, [.op .extended _] => cOk .reg
  | TId.get_extended_op, [.op .extended _] =>
    cOk (enumAlts tyExtendOp (ExtendOp.all.map ExtendOp.idx))
  | TId.nzcv, [a, b, c, d] =>
    if isBool a && isBool b && isBool c && isBool d then cOk (.op .nzcv none) else none
  | TId.cond_br_zero, [r, s] => cOk (.data tyCondBrKind VIdx.CondBrKind.Zero [r, s])
  | TId.cond_br_not_zero, [r, s] => cOk (.data tyCondBrKind VIdx.CondBrKind.NotZero [r, s])
  | TId.cond_br_cond, [c] => cOk (.data tyCondBrKind VIdx.CondBrKind.Cond [c])
  | TId.zero_reg, [] => cOk .reg
  | TId.writable_zero_reg, [] => cOk .reg
  | TId.a64_extr_imm, [tA, .op .immShift _] =>
    if tysAll tA fun t => t == .int 32 || t == .int 64 then cOk (.op .shiftAmt none) else none
  | TId.load_constant_full, [tA, ext, sz, x] =>
    if isTy tA && enumOk tyImmExtend (fun k => if k < 2 then some k else none) ext &&
        enumOk tyOperandSize OperandSize.ofIdx? sz && isInt x then cOk .reg else none
  | TId.uimm12_scaled_from_i64, [x, tA] =>
    exactTest tA x (fun t v => (uimm12Scaled? v t.bytes).isSome) (.op .uimm12Scaled none)
  | TId.uimm12_scaled_nonzero_from_i64, [x, tA] =>
    exactTest tA x (fun t v => v != 0 && (uimm12Scaled? v t.bytes).isSome) (.op .uimm12Scaled none)
  | TId.simm9_from_i64, [x] =>
    if isInt x then
      match x.intOf with
      | some v => if (simm9? v).isSome then cOk (.op .simm9 none) else some (.bot, false)
      | none => cMay (.op .simm9 none)
    else none
  | TId.cond_code, [cc] => do
    let ks ← cc.enumsOf tyIntCC
    let cs ← ks.mapM condOfIntCC
    cOk (enumAlts tyCond (cs.map Cond.idx))
  | TId.invert_cond, [c] => do
    let ks ← c.enumsOf tyCond
    let cs ← ks.mapM Cond.ofIdx?
    cOk (enumAlts tyCond (cs.map fun c => c.invert.idx))
  | TId.shift_masked_imm, [tA, x] => if isTy tA && isInt x then cOk (.int none none) else none
  | TId.shift_mask, [tA] =>
    if tysAll tA fun t => (ImmLogic.ofNat? (t.laneBits - 1) .size32).isSome
    then cOk (.op .immLogic none) else none
  | TId.bfm_immr, [tA, a, b] => if isTy tA && isInt a && isInt b then cOk (.op .uimm6 none) else none
  | TId.bfm_imms, [tA, a, b] => if isTy tA && isInt a && isInt b then cOk (.op .uimm6 none) else none
  | TId.negate_imm_shift, [tA, .op .immShift _] =>
    if tysAll tA fun t => t.bits ≤ 64 then cOk (.op .immShift none) else none
  | TId.rotr_mask, [tA] =>
    if tysAll tA fun t => (ImmLogic.ofNat? (t.bits - 1) .size32).isSome
    then cOk (.op .immLogic none) else none
  | TId.rotr_opposite_amount, [tA, .op .immShift _] =>
    if tysAll tA fun t => t.bits < 64 then cOk (.op .immShift none) else none
  | TId.test_and_compare_bit_const, [tA, x] => if isTy tA && isInt x then cMay (range 0 63) else none
  | TId.i32_checked_add, [a, b] =>
    if isInt a && isInt b then
      match a.intOf, b.intOf with
      | some x, some y =>
        if -(2 ^ 31 : Int) ≤ x + y ∧ x + y < 2 ^ 31 then cOk (exact (x + y)) else some (.bot, false)
      | _, _ => cMay (.int none none)
    else none
  | TId.i64_checked_neg, [a] => exactTest1 a fun x => if x == -(2 ^ 63 : Int) then none else some (-x)
  | TId.u64_eq, [a, b] => boolOp2 a b fun x y => x == y
  | TId.u64_gt, [a, b] => boolOp2 a b fun x y => decide (x > y)
  | TId.u64_wrapping_add, [a, b] => intOp2 a b fun x y => (u64 (x + y) : Int)
  | TId.u64_wrapping_sub, [a, b] => intOp2 a b fun x y => (u64 (x - y) : Int)
  | TId.u64_wrapping_shl, [a, b] => intOp2 a b fun x y => (u64 (x * 2 ^ (y.toNat % 64)) : Int)
  | TId.u64_is_odd, [a] => if isInt a then cOk (.bool (a.intOf.map fun x => x % 2 == 1)) else none
  | TId.u8_into_u32, [a] => intOp1 a fun z => z
  | TId.u8_into_u64, [a] => intOp1 a fun z => z
  | TId.u16_into_u64, [a] => intOp1 a fun z => z
  | TId.i32_into_i64, [a] => intOp1 a fun z => z
  | TId.u32_into_u64, [a] => intOp1 a fun z => z
  | TId.i64_cast_unsigned, [a] => intOp1 a fun x => (u64 x : Int)
  | TId.value_array_2, [x, y] => if isVal x && isVal y then cOk (.vals [x, y]) else none
  | TId.value_array_3, [x, y, z] =>
    if isVal x && isVal y && isVal z then cOk (.vals [x, y, z]) else none
  | TId.block_array_2, [.blockCalls a, .blockCalls b] => cOk (.blockCalls (a + b))
  | _, _ => none

/-! ## The `InstructionData` of an E instruction -/

/-- The opcodes of a format, as an enum value. -/
def aOps (os : List Nat) : PA := enumAlts tyOpcode os

/-- A value of an E type. -/
def aV : PA := .val eCTys

/-- **The fields of the `InstructionData` of an E instruction**, per format (`instData`). -/
def aidata (k : Nat) : Option (List PA) :=
  match k with
  | VIdx.InstructionData.UnaryImm => some [aOps [VIdx.Opcode.Iconst], .int none none]
  | VIdx.InstructionData.Unary => some [aOps [VIdx.Opcode.Ineg, VIdx.Opcode.Bnot, VIdx.Opcode.Clz,
      VIdx.Opcode.Ctz, VIdx.Opcode.Popcnt, VIdx.Opcode.Bswap, VIdx.Opcode.Bitrev,
      VIdx.Opcode.Uextend, VIdx.Opcode.Sextend, VIdx.Opcode.Ireduce, VIdx.Opcode.Bmask], aV]
  | VIdx.InstructionData.Binary => some [aOps [VIdx.Opcode.Iadd, VIdx.Opcode.Isub,
      VIdx.Opcode.Imul, VIdx.Opcode.Umulhi, VIdx.Opcode.Smulhi, VIdx.Opcode.Band, VIdx.Opcode.Bor,
      VIdx.Opcode.Bxor, VIdx.Opcode.Ishl, VIdx.Opcode.Ushr, VIdx.Opcode.Sshr, VIdx.Opcode.Rotl,
      VIdx.Opcode.Rotr, VIdx.Opcode.Smin, VIdx.Opcode.Smax, VIdx.Opcode.Umin, VIdx.Opcode.Umax,
      VIdx.Opcode.Udiv, VIdx.Opcode.Sdiv, VIdx.Opcode.Urem, VIdx.Opcode.Srem], .vals [aV, aV]]
  | VIdx.InstructionData.IntCompare => some [aOps [VIdx.Opcode.Icmp], .vals [aV, aV],
      enumAlts tyIntCC (List.range 10)]
  | VIdx.InstructionData.Load => some [aOps [VIdx.Opcode.Load, VIdx.Opcode.Uload8,
      VIdx.Opcode.Sload8, VIdx.Opcode.Uload16, VIdx.Opcode.Sload16, VIdx.Opcode.Uload32,
      VIdx.Opcode.Sload32], aV, .op .memFlags none, .int none none]
  | VIdx.InstructionData.Store => some [aOps [VIdx.Opcode.Store, VIdx.Opcode.Istore8,
      VIdx.Opcode.Istore16, VIdx.Opcode.Istore32], .vals [aV, aV], .op .memFlags none, .int none none]
  | VIdx.InstructionData.Ternary => some [aOps [VIdx.Opcode.Select], .vals [aV, aV, aV]]
  | VIdx.InstructionData.NullAry => some [aOps [VIdx.Opcode.Nop, VIdx.Opcode.Fence]]
  | VIdx.InstructionData.UnaryGlobalValue => some [aOps [VIdx.Opcode.SymbolValue,
      VIdx.Opcode.TlsValue], .alts [.op .globalValue none, .op .tlsGlobalValue none]]
  | VIdx.InstructionData.StackAddr => some [aOps [VIdx.Opcode.StackAddr], .op .stackSlot none,
      .int none none]
  | VIdx.InstructionData.Call => some [aOps [VIdx.Opcode.Call], .valsMin 0, .op .funcRef none]
  | VIdx.InstructionData.CallIndirect => some [aOps [VIdx.Opcode.CallIndirect], .valsMin 1,
      .op .sig none]
  | VIdx.InstructionData.FuncAddr => some [aOps [VIdx.Opcode.FuncAddr], .op .funcRef none]
  | VIdx.InstructionData.LoadNoOffset => some [aOps [VIdx.Opcode.AtomicLoad], aV,
      .op .memFlags none]
  | VIdx.InstructionData.StoreNoOffset => some [aOps [VIdx.Opcode.AtomicStore], .vals [aV, aV],
      .op .memFlags none]
  | VIdx.InstructionData.AtomicRmw => some [aOps [VIdx.Opcode.AtomicRmw], .vals [aV, aV],
      .op .memFlags none, enumAlts tyAtomicRmwOp (List.range 11)]
  | VIdx.InstructionData.AtomicCas => some [aOps [VIdx.Opcode.AtomicCas], .vals [aV, aV, aV],
      .op .memFlags none]
  | _ => none

end Backend.Proof.Prg
