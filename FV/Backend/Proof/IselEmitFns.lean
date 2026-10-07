import FV.Backend.Proof.IselCovFns
import FV.Backend.EmitOk

/-!
# Emission conditions of the ISLE lowering (V6c): the transfer functions

The emission analysis is V3's abstract interpreter (`IselCovCheck`, domain `AW`) with
* precise transfer functions for the extern helpers that build immediates (`actorE`, `aextE`):
  their results are numeric/operand leaves `AW.num k b` (`NK`), falling back to V3's
  `actor`/`aext`;
* a stronger precondition `apreE`: V3's `apre`, and an `emit`ted instruction passes the abstract
  emission check `emChk true` (its immediates are in the encoder's ranges, `MInst.emitOk`, and it
  is not a branch, so it has no targets);
* the hand-checked "last" form of the branch rules `aLast`: a rule whose right-hand side ends in an
  `emit_side_effect` of a side effect whose instructions pass `emChk`, branches only last
  (`senrLast`).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Isle Isle.Interp Isle.Aarch64

/-! ## Leaves -/

/-- The maximum of `g` over the types an abstract type value names (`none`: not a type value). -/
def tyB (a : AW) (g : CTy → Nat) : Option Nat :=
  match a with
  | .ty ts => some (ts.foldl (fun m t => max m (g t)) 0)
  | _ => none

/-- The conditions other than `al`/`nv`. -/
def condsOk : AW :=
  .alts ((Cond.all.filter fun c => c != .al && c != .nv).map fun c => .data tyCond c.idx [])

/-- An enum value of a condition other than `al`/`nv`. -/
def condA (c : AW) : Bool := c.enumAll fun k => k != Cond.al.idx && k != Cond.nv.idx

/-- A shift amount bound of a type: below its width, below 64, at least 1. -/
def shB (t : CTy) : Nat := min (max t.bits 1) 64

/-- The `MoveWideConst` shift bound of a type. -/
def mwB (t : CTy) : Nat := if t.bits ≤ 32 then 2 else 4

/-- **Extern constructors**, with numeric leaves where the emission check needs them. -/
def actorE (id : TermId) (as : List AW) : AW :=
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
def aextE (id : TermId) (a : AW) : List AW :=
  if id == TId.imm12_from_u64 then [.num .imm12 4096]
  else if id == TId.u8_from_u64 then [.num .int 256]
  else aext id a

/-! ## The emission check -/

/-- A leaf of kind `k` with bound at most `n`. -/
def leafLe (k : NK) (a : AW) (n : Nat) : Bool :=
  match a with
  | .num k' b => decide (k' = k) && decide (b ≤ n)
  | _ => false

/-- The width bound of an operand-size value: 64 if it is `Size64`, else 32. -/
def sizeBnd (s : AW) : Nat :=
  match s.enumsOf with
  | some ks => if ks.all (· == VIdx.OperandSize.Size64) then 64 else 32
  | none => 32

/-- Every operation an `ALUOp` value may be passes `p`. -/
def aluOk (a : AW) (p : ALUOp → Bool) : Bool :=
  a.enumAll fun k => match ALUOp.ofIdx? k with
    | some o => p o
    | none => false

/-- A `CondBrKind` value whose condition (if any) is not `al`/`nv`. -/
def kindE1 : AW → Bool
  | .data _ k fs => if k == VIdx.CondBrKind.Cond then
      (match fs with
       | [c] => condA c
       | _ => false)
    else true
  | _ => false

/-- `kindE1` of every alternative. -/
def kindE : AW → Bool
  | .alts as => as.all kindE1
  | a => kindE1 a

/-- The types of an atomic loop: 8, 16, 32 or 64 bits. -/
def atomTyE (a : AW) : Bool :=
  match a with
  | .ty ts => ts.all fun t => t.bits == 8 || t.bits == 16 || t.bits == 32 || t.bits == 64
  | _ => false

def eAluRRImm12 : List AW → Bool
  | [op, _, _, _, i] => aluOk op (·.addSub?.isSome) && leafLe .imm12 i 4096
  | _ => false
def eAluRRImmShift : List AW → Bool
  | [_, s, _, _, i] => leafLe .immShift i (sizeBnd s)
  | _ => false
def eAluRRRShift : List AW → Bool
  | [op, s, _, _, _, sh] => leafLe .shiftAmt sh (sizeBnd s) &&
      aluOk op fun o => o == .extr || o.addSub?.isSome || o.logic?.isSome
  | _ => false
def eAluRRRExtend : List AW → Bool
  | [op, _, _, _, _, _] => aluOk op (·.addSub?.isSome)
  | _ => false
def eMovWide : List AW → Bool
  | [_, _, i, s] => leafLe .mwc i (if sizeBnd s == 64 then 4 else 2)
  | _ => false
def eExtend : List AW → Bool
  | [_, _, _, a, _] => leafLe .int a 33
  | _ => false
def eBfm : List AW → Bool
  | [s, _, _, _, a, b] => leafLe .uimm6 a (sizeBnd s) && leafLe .uimm6 b (sizeBnd s)
  | _ => false
def eCSet : List AW → Bool
  | [_, c] => condA c
  | _ => false
def eCCmpImm : List AW → Bool
  | [_, _, i, _, _] => leafLe .uimm5 i 32
  | _ => false
def eMovToFpu : List AW → Bool
  | [_, _, s] => s.enumAll fun k => k == VIdx.ScalarSize.Size16 || k == VIdx.ScalarSize.Size32 ||
      k == VIdx.ScalarSize.Size64
  | _ => false
/-- The bound of a lane index per scalar size (`idx * bytes * 2 + bytes < 32`, scaled). -/
def laneB : Nat → Nat
  | VIdx.ScalarSize.Size8 => 16 | VIdx.ScalarSize.Size16 => 8 | VIdx.ScalarSize.Size32 => 4
  | VIdx.ScalarSize.Size64 => 2 | _ => 0
def eMovFromVec : List AW → Bool
  | [_, _, .num .int b, s] => s.enumAll fun k => decide (b ≤ laneB k)
  | _ => false
def eVecMisc : List AW → Bool
  | [_, _, _, s] => s.enumAll fun k => k == VIdx.VectorSize.Size8x8 || k == VIdx.VectorSize.Size8x16
  | _ => false
def eVecLanes : List AW → Bool
  | [_, _, _, s] => s.enumAll fun k => k != VIdx.VectorSize.Size32x2 && k != VIdx.VectorSize.Size64x2
  | _ => false
def eTbb : List AW → Bool
  | [_, _, _, _, b] => leafLe .int b 64
  | _ => false
def eCondBr : List AW → Bool
  | [_, _, kd] => kindE kd
  | _ => false
def eTrapIf : List AW → Bool
  | [kd, _] => kindE kd
  | _ => false
def eCall : List AW → Bool
  | [.num .callInfo _] => true
  | _ => false
def eAtomic : List AW → Bool
  | ty :: _ => atomTyE ty
  | _ => false

/-- The emission checks by variant (other variants: no condition). -/
def emTab : List (Nat × (List AW → Bool)) :=
  [(VIdx.MInst.AluRRImm12, eAluRRImm12), (VIdx.MInst.AluRRImmShift, eAluRRImmShift),
   (VIdx.MInst.AluRRRShift, eAluRRRShift), (VIdx.MInst.AluRRRExtend, eAluRRRExtend),
   (VIdx.MInst.MovWide, eMovWide), (VIdx.MInst.MovK, eMovWide), (VIdx.MInst.Extend, eExtend),
   (VIdx.MInst.BitfieldMove, eBfm), (VIdx.MInst.CSet, eCSet), (VIdx.MInst.CSetm, eCSet),
   (VIdx.MInst.CCmpImm, eCCmpImm), (VIdx.MInst.MovToFpu, eMovToFpu),
   (VIdx.MInst.MovFromVec, eMovFromVec), (VIdx.MInst.VecMisc, eVecMisc),
   (VIdx.MInst.VecLanes, eVecLanes), (VIdx.MInst.TestBitAndBranch, eTbb),
   (VIdx.MInst.CondBr, eCondBr), (VIdx.MInst.TrapIf, eTrapIf), (VIdx.MInst.Call, eCall),
   (VIdx.MInst.CallInd, eCall), (VIdx.MInst.AtomicRMWLoop, eAtomic),
   (VIdx.MInst.AtomicCASLoop, eAtomic)]

/-- The branch variants (instructions with targets). -/
def branchKs : List Nat :=
  [VIdx.MInst.Jump, VIdx.MInst.CondBr, VIdx.MInst.TestBitAndBranch, VIdx.MInst.JTSequence]

/-- The emission check of an `MInst` of variant `k` with fields `fs` (`nb`: not a branch). -/
def em1 (nb : Bool) (k : Nat) (fs : List AW) : Bool :=
  !(nb && branchKs.contains k) &&
  match emTab.lookup k with
  | some c => c fs
  | none => true

/-- `em1` of an `MInst` value (of every alternative). -/
def emA1 (nb : Bool) : AW → Bool
  | .data t k fs => t == tyMInst && em1 nb k fs
  | _ => false

/-- **The emission check of an `emit`ted instruction.** -/
def emChk (nb : Bool) : AW → Bool
  | .alts as => as.all (emA1 nb)
  | a => emA1 nb a

/-- **Preconditions** of extern constructor calls: V3's, and an `emit`ted instruction passes the
emission check and is not a branch. -/
def apreE (id : TermId) (as : List AW) : Bool :=
  apre id as &&
  if id == TId.emit then
    match as with
    | [a] => emChk true a
    | _ => false
  else true

/-! ## The branch rules: branches only last -/

/-- A side effect whose instructions pass the emission check, the last one possibly a branch. -/
def senr1 : AW → Bool
  | .data t k [i] => t == TyId.SideEffectNoResult && k == VIdx.SideEffectNoResult.Inst &&
      emChk false i
  | .data t k [i, j] => t == TyId.SideEffectNoResult && k == VIdx.SideEffectNoResult.Inst2 &&
      emChk true i && emChk false j
  | .data t k [i, j, l] => t == TyId.SideEffectNoResult && k == VIdx.SideEffectNoResult.Inst3 &&
      emChk true i && emChk true j && emChk false l
  | _ => false

/-- `senr1` of every alternative. -/
def senrLast : AW → Bool
  | .alts as => as.all senr1
  | a => senr1 a

/-- Term `t` has an internal constructor and is not a multi-term. -/
def internalOne (p : Program) (t : TermId) : Bool :=
  match termOf p t with
  | .ok term =>
    match term.kind with
    | .decl flags (some .internal) _ => !flags.isMulti
    | _ => false
  | .error _ => false

/-- The root rules of `lower` checked by hand (`IselEmitHand`): `uextend` (808) and `sextend`
(819), whose extension widths are related only by the input condition `ExtendsWiden`, and the
`extr` rules (862, 863), whose shift amount is below the type's width only by the rule's
guards. -/
def emitHandIds : List Nat := [808, 819, 862, 863]

section Last
variable (p : Program) (tab : Tab) (aext : TermId → AW → List AW) (actor : TermId → List AW → AW)
  (apre : TermId → List AW → Bool) (aOracle : TermId → List AW → Option AW)

/-- **An expression ending in a branch**: its evaluation emits instructions passing `apre`'s
check, then (last) the instructions of an `emit_side_effect` passing `senrLast`; through `let`s and
calls of internal terms whose matching rules' right-hand sides end so (depth `n`). -/
def aLast : Nat → Isle.Expr → List AW → Bool
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
      | some as => (p.rulesOf t).all fun r =>
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
def aRuleLast (n : Nat) (ins : List AW) (r : Rule) : Bool :=
  match aRuleEnvs p tab aext actor apre aOracle ins r with
  | some envs => envs.all (aLast p tab aext actor apre aOracle n r.rhs)
  | none => false

end Last

end Backend.Proof.Cov
