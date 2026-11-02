import FV.Isle.Lookup
import FV.Backend.Proof.IselCovTFns
import FV.Backend.Proof.IselEmitFns

/-!
# Emission conditions of the typed ISLE lowering (S11): the transfer functions

`IselEmitFns` over the typed domain `AT` (`IselCovTFns`): the typed coverage interpreter with

* precise transfer functions for the extern helpers that build immediates (`actorET`, `aextET`):
  their results are numeric/operand leaves `AT.num k b`, falling back to the typed
  `actor`/`aext`;
* a stronger precondition `apreET`: the typed `apre`, and an `emit`ted instruction passes the
  abstract emission check `emChk true` (immediates in the encoder's ranges, `MInst.emitOk`, not a
  branch);
* the "last" form of the branch rules `aLast`: a rule whose right-hand side ends in an
  `emit_side_effect` of a side effect whose instructions pass `emChk` branches only last
  (`senrLast`).

The typed domain describes the plain `movi` immediate (`AT.movi`), so `VecDupImm` (the zero
float constants) is checked (`eVecDupImm`) where the untyped analysis rejects it.
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Isle Isle.Interp Isle.Aarch64
open Backend.Proof.Cov (NK shB mwB laneB fpSzOk internalOne)

/-! ## Leaves -/

/-- The maximum of `g` over the types an abstract type value names (`none`: not a type value). -/
def tyB (a : AT) (g : CTy → Nat) : Option Nat :=
  match a with
  | .ty ts => some (ts.foldl (fun m t => max m (g t)) 0)
  | _ => none

/-- The conditions other than `al`/`nv`. -/
def condsOk : AT :=
  .alts ((Cond.all.filter fun c => c != .al && c != .nv).map fun c => .data tyCond c.idx [])

/-- An enum value of a condition other than `al`/`nv`. -/
def condA (c : AT) : Bool := c.enumAll fun k => k != Cond.al.idx && k != Cond.nv.idx

/-- **Extern constructors**, with numeric leaves where the emission check needs them. -/
def actorET (id : TermId) (as : List AT) : AT :=
  if id == TId.imm_shift_from_imm64 then
    match as with
    | [t, _] => match tyB t shB with
      | some b => .num .immShift b
      | none => .num .immShift 64
    | _ => actor id as
  else if id == TId.imm_shift_from_u8 then
    match as with
    | [.num .int b] => .num .immShift (min b 64)
    | _ => .num .immShift 64
  else if id == TId.u8_into_uimm5 then .num .uimm5 32
  else if id == TId.u8_into_imm12 then .num .imm12 4096
  else if id == TId.move_wide_const_from_u64 || id == TId.move_wide_const_from_inverted_u64 then
    match as with
    | [t, _] => match tyB t mwB with
      | some b => .num .mwc b
      | none => .num .mwc 4
    | _ => actor id as
  else if id == TId.lshl_from_imm64 || id == TId.ashr_from_u64 then
    match as with
    | [t, _] => match tyB t shB with
      | some b => .num .shiftAmt b
      | none => .num .shiftAmt 64
    | _ => actor id as
  else if id == TId.a64_extr_imm then
    match as with
    | [_, .num .immShift b] => .num .shiftAmt b
    | _ => actor id as
  else if id == TId.bfm_immr || id == TId.bfm_imms then
    match as with
    | t :: _ => match tyB t (fun t => max t.laneBits 1) with
      | some b => .num .uimm6 b
      | none => actor id as
    | _ => actor id as
  else if id == TId.negate_imm_shift then
    match as with
    | [t, _] => match tyB t (fun t => max t.bits 1) with
      | some b => .num .immShift b
      | none => actor id as
    | _ => actor id as
  else if id == TId.rotr_opposite_amount then
    match as with
    | [t, _] => match tyB t (fun t => min (t.bits + 1) 64) with
      | some b => .num .immShift b
      | none => .num .immShift 64
    | _ => actor id as
  else if id == TId.test_and_compare_bit_const then
    match as with
    | [t, _] => match tyB t (fun t => min t.bits 64) with
      | some b => .num .int b
      | none => .num .int 64
    | _ => actor id as
  else if id == TId.ty_bits then
    match as with
    | [t] => match tyB t (fun t => t.bits + 1) with
      | some b => .num .int b
      | none => actor id as
    | _ => actor id as
  else if id == TId.shift_masked_imm then
    match as with
    | [t, _] => match tyB t (fun t => max t.laneBits 1) with
      | some b => .num .int b
      | none => actor id as
    | _ => actor id as
  else if id == TId.imm_size_from_type then .num .int 65
  else if id == TId.cond_code then condsOk
  else if id == TId.invert_cond then
    match as with
    | [c] => if condA c then condsOk else actor id as
    | _ => actor id as
  else if id == TId.gen_call_info then .num .callInfo 0
  else if id == TId.gen_call_ind_info then
    match as with
    | [_, r, _, _, _] => if r.isV then .num .callInfo 0 else actor id as
    | _ => actor id as
  else if id == TId.u8_into_u32 || id == TId.u8_into_u64 || id == TId.u16_into_u64 ||
      id == TId.u32_into_u64 || id == TId.i32_into_i64 then
    match as with
    | [.num .int b] => .num .int b
    | _ => actor id as
  else actor id as

/-- **Extern extractors**: `imm12_from_u64` and `u8_from_u64` give leaves. -/
def aextET (id : TermId) (a : AT) : List AT :=
  if id == TId.imm12_from_u64 then [.num .imm12 4096]
  else if id == TId.u8_from_u64 then [.num .int 256]
  else aext id a

/-! ## The emission check -/

/-- A leaf of kind `k` with bound at most `n`. -/
def leafLe (k : NK) (a : AT) (n : Nat) : Bool :=
  match a with
  | .num k' b => decide (k' = k) && decide (b ≤ n)
  | _ => false

/-- The width bound of an operand-size value: 64 if it is `Size64`, else 32. -/
def sizeBnd (s : AT) : Nat :=
  match s.enumsOf with
  | some ks => if ks.all (· == VIdx.OperandSize.Size64) then 64 else 32
  | none => 32

/-- Every operation an `ALUOp` value may be passes `p`. -/
def aluOk (a : AT) (p : ALUOp → Bool) : Bool :=
  a.enumAll fun k => match ALUOp.ofIdx? k with
    | some o => p o
    | none => false

/-- A `CondBrKind` value whose condition (if any) is not `al`/`nv`. -/
def kindE1 : AT → Bool
  | .data _ k fs => if k == VIdx.CondBrKind.Cond then
      (match fs with
       | [c] => condA c
       | _ => false)
    else true
  | _ => false

/-- `kindE1` of every alternative. -/
def kindE : AT → Bool
  | .alts as => as.all kindE1
  | a => kindE1 a

/-- The types of an atomic loop: 8, 16, 32 or 64 bits. -/
def atomTyE (a : AT) : Bool :=
  match a with
  | .ty ts => ts.all fun t => t.bits == 8 || t.bits == 16 || t.bits == 32 || t.bits == 64
  | _ => false

def eAluRRImm12 : List AT → Bool
  | [op, _, _, _, i] => aluOk op (·.addSub?.isSome) && leafLe .imm12 i 4096
  | _ => false
def eAluRRImmShift : List AT → Bool
  | [_, s, _, _, i] => leafLe .immShift i (sizeBnd s)
  | _ => false
def eAluRRRShift : List AT → Bool
  | [op, s, _, _, _, sh] => leafLe .shiftAmt sh (sizeBnd s) &&
      aluOk op fun o => o == .extr || o.addSub?.isSome || o.logic?.isSome
  | _ => false
def eAluRRRExtend : List AT → Bool
  | [op, _, _, _, _, _] => aluOk op (·.addSub?.isSome)
  | _ => false
def eMovWide : List AT → Bool
  | [_, _, i, s] => leafLe .mwc i (if sizeBnd s == 64 then 4 else 2)
  | _ => false
def eExtend : List AT → Bool
  | [_, _, _, a, _] => leafLe .int a 33
  | _ => false
def eBfm : List AT → Bool
  | [s, _, _, _, a, b] => leafLe .uimm6 a (sizeBnd s) && leafLe .uimm6 b (sizeBnd s)
  | _ => false
def eCSet : List AT → Bool
  | [_, c] => condA c
  | _ => false
def eCCmpImm : List AT → Bool
  | [_, _, i, _, _] => leafLe .uimm5 i 32
  | _ => false
def eMovToFpu : List AT → Bool
  | [_, _, s] => s.enumAll fun k => k == VIdx.ScalarSize.Size16 || k == VIdx.ScalarSize.Size32 ||
      k == VIdx.ScalarSize.Size64
  | _ => false
def eMovFromVec : List AT → Bool
  | [_, _, .num .int b, s] => s.enumAll fun k => decide (b ≤ laneB k)
  | _ => false
def eVecMisc : List AT → Bool
  | [_, _, _, s] => s.enumAll fun k => k == VIdx.VectorSize.Size8x8 || k == VIdx.VectorSize.Size8x16
  | _ => false
def eVecLanes : List AT → Bool
  | [_, _, _, s] => s.enumAll fun k => k != VIdx.VectorSize.Size32x2 && k != VIdx.VectorSize.Size64x2
  | _ => false
def eTbb : List AT → Bool
  | [_, _, _, _, b] => leafLe .int b 64
  | _ => false
def eCondBr : List AT → Bool
  | [_, _, kd] => kindE kd
  | _ => false
def eTrapIf : List AT → Bool
  | [kd, _] => kindE kd
  | _ => false
def eCall : List AT → Bool
  | [.num .callInfo _] => true
  | _ => false
def eAtomic : List AT → Bool
  | ty :: _ => atomTyE ty
  | _ => false
/-- `fmov #imm`: a 32- or 64-bit size. -/
def eFpuMoveFPImm : List AT → Bool
  | [_, _, s] => s.enumAll fun k => k == VIdx.ScalarSize.Size32 || k == VIdx.ScalarSize.Size64
  | _ => false
/-- `movi` (`[rd, imm, invert, size]`): the plain `movi` immediate, not inverted, not on
`64x2`. -/
def eVecDupImm : List AT → Bool
  | [_, .movi, .bool false, s] => s.enumAll (· != VIdx.VectorSize.Size64x2)
  | _ => false
/-- `fpuRRR`/`fpuRRRR` (`[op, size, …]`): single or double precision. -/
def eFpuOpSz : List AT → Bool
  | _ :: s :: _ => s.enumAll fpSzOk
  | _ => false
/-- `fcmp` (`[size, rn, rm]`): single or double precision. -/
def eFpuCmp : List AT → Bool
  | [s, _, _] => s.enumAll fpSzOk
  | _ => false
/-- `fpuRR` (`[op, size, rd, rn]`): single or double precision, and `fcvt` from the size its
operation names. -/
def eFpuRR : List AT → Bool
  | [op, s, _, _] =>
    s.enumAll fpSzOk &&
      (op.enumAll (· != VIdx.FPUOp1.Cvt32To64) || s.enumAll (· == VIdx.ScalarSize.Size32)) &&
      (op.enumAll (· != VIdx.FPUOp1.Cvt64To32) || s.enumAll (· == VIdx.ScalarSize.Size64))
  | _ => false

/-- The emission checks by variant (other variants: no condition). -/
def emTab : List (Nat × (List AT → Bool)) :=
  [(VIdx.MInst.AluRRImm12, eAluRRImm12), (VIdx.MInst.AluRRImmShift, eAluRRImmShift),
   (VIdx.MInst.AluRRRShift, eAluRRRShift), (VIdx.MInst.AluRRRExtend, eAluRRRExtend),
   (VIdx.MInst.MovWide, eMovWide), (VIdx.MInst.MovK, eMovWide), (VIdx.MInst.Extend, eExtend),
   (VIdx.MInst.BitfieldMove, eBfm), (VIdx.MInst.CSet, eCSet), (VIdx.MInst.CSetm, eCSet),
   (VIdx.MInst.CCmpImm, eCCmpImm), (VIdx.MInst.MovToFpu, eMovToFpu),
   (VIdx.MInst.MovFromVec, eMovFromVec), (VIdx.MInst.VecMisc, eVecMisc),
   (VIdx.MInst.VecLanes, eVecLanes), (VIdx.MInst.TestBitAndBranch, eTbb),
   (VIdx.MInst.CondBr, eCondBr), (VIdx.MInst.TrapIf, eTrapIf), (VIdx.MInst.Call, eCall),
   (VIdx.MInst.CallInd, eCall), (VIdx.MInst.AtomicRMWLoop, eAtomic),
   (VIdx.MInst.AtomicCASLoop, eAtomic), (VIdx.MInst.FpuMoveFPImm, eFpuMoveFPImm),
   (VIdx.MInst.VecDupImm, eVecDupImm), (VIdx.MInst.FpuRR, eFpuRR), (VIdx.MInst.FpuRRR, eFpuOpSz),
   (VIdx.MInst.FpuRRRR, eFpuOpSz), (VIdx.MInst.FpuCmp, eFpuCmp)]

/-- The emission check of an `MInst` of variant `k` with fields `fs` (`nb`: not a branch). -/
def em1 (nb : Bool) (k : Nat) (fs : List AT) : Bool :=
  !(nb && Cov.branchKs.contains k) &&
  match emTab.lookup k with
  | some c => c fs
  | none => true

/-- `em1` of an `MInst` value (of every alternative). -/
def emA1 (nb : Bool) : AT → Bool
  | .data t k fs => t == tyMInst && em1 nb k fs
  | _ => false

/-- **The emission check of an `emit`ted instruction.** -/
def emChk (nb : Bool) : AT → Bool
  | .alts as => as.all (emA1 nb)
  | a => emA1 nb a

/-- **Preconditions** of extern constructor calls: the typed ones, and an `emit`ted instruction
passes the emission check and is not a branch. -/
def apreET (id : TermId) (as : List AT) : Bool :=
  apre id as &&
  if id == TId.emit then
    match as with
    | [a] => emChk true a
    | _ => false
  else true

/-! ## The branch rules: branches only last -/

/-- A side effect whose instructions pass the emission check, the last one possibly a branch. -/
def senr1 : AT → Bool
  | .data t k [i] => t == TyId.SideEffectNoResult && k == VIdx.SideEffectNoResult.Inst &&
      emChk false i
  | .data t k [i, j] => t == TyId.SideEffectNoResult && k == VIdx.SideEffectNoResult.Inst2 &&
      emChk true i && emChk false j
  | .data t k [i, j, l] => t == TyId.SideEffectNoResult && k == VIdx.SideEffectNoResult.Inst3 &&
      emChk true i && emChk true j && emChk false l
  | _ => false

/-- `senr1` of every alternative. -/
def senrLast : AT → Bool
  | .alts as => as.all senr1
  | a => senr1 a

/-- The root rules of `lower` checked by hand (`IselEmitTHand`): `Cov.emitHandIds` (`uextend` 808,
`sextend` 819, whose widths are related only by the input condition `ExtendsWiden`; the `extr`
rules 862, 863, whose shift amount is below the width only by the rules' guards) and the
`bitcast` GPR → SIMD&FP rule 1083, whose `mov_to_fpu` size is the operand's scalar size: in the
encoder's range only for a `bitcast` of a 32- or 64-bit integer, by the input condition
`BitcastsSameWidth` (an `i8` operand would give `Size8`). -/
def emitHandIdsT : List Nat := [808, 819, 862, 863, 1083]

section Last
variable (p : Program) (tab : Tab) (aext : TermId → AT → List AT) (actor : TermId → List AT → AT)
  (apre : TermId → List AT → Bool) (aOracle : TermId → List AT → Option AT)

/-- **An expression ending in a branch**: its evaluation emits instructions passing `apre`'s
check, then (last) the instructions of an `emit_side_effect` passing `senrLast`; through `let`s and
calls of internal terms whose matching rules' right-hand sides end so (depth `n`). -/
def aLast : Nat → Isle.Expr → List AT → Bool
  | 0, _, _ => false
  | n + 1, .term _ t args, env =>
    if t == TId.emit_side_effect then
      match args with
      | [e] => match aExpr p tab actor apre aOracle e env with
        | some a => senrLast a
        | none => false
      | _ => false
    else
      internalOne p t && (aOracle t []).isNone &&
      match aArgs p tab actor apre aOracle args env with
      | some as => (rulesOfT p t).all fun r =>
        match aRuleEnvs p tab aext actor apre aOracle as r with
        | some envs => envs.all (aLast n r.rhs)
        | none => false
      | none => false
  | n + 1, .let _ bs body, env =>
    match aBinds p tab actor apre aOracle bs env with
    | some env' => aLast n body env'
    | none => false
  | _ + 1, _, _ => false

/-- A root rule ending in a branch: every environment of its match phase. -/
def aRuleLast (n : Nat) (ins : List AT) (r : Rule) : Bool :=
  match aRuleEnvs p tab aext actor apre aOracle ins r with
  | some envs => envs.all (aLast p tab aext actor apre aOracle n r.rhs)
  | none => false

end Last

end Backend.Proof.CovT
