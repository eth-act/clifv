import FV.Backend.Proof.RegallocCSem
import FV.Backend.Proof.IselFlowExt
import FV.Backend.Proof.IselExcl

/-!
# Form coverage of the ISLE lowering (V3): the abstract domain

The emitted code of every ISLE run of the driver is covered (`MInst.isCtl` or `FormOk`). This
is decided once over the exported rule data by an abstract interpretation (`IselCovCheck`)
whose abstract values `AW` describe ISLE values (`γ`):

* `flat m c`: every register inside has a kind in the mask `m` (1: int vreg, 2: float vreg,
  4: `xzr`, 8: any other register) and, if `c`, every `MInst` inside is covered (`covV`);
* `reg m`: a register of a kind in `m`; `ty ts`: a type of `ts`; `bool b`;
* `logic sz`, `scale b`, `simm9`: a logical immediate valid at size `sz`, an unsigned offset
  scaled by `b`, a 9-bit signed offset (as the extern constructors build them);
* `xv e`: a value the exclusion checker describes (`AV.Holds`: an instruction of the context,
  the `InstructionData` of an E instruction, a CLIF value), without registers or `MInst`s;
* `data t k fs`: variant `k` of type `t` with fields described by `fs`; `alts as`: one of `as`;
* `num k b`: a numeric or operand leaf of kind `k` with bound `b` (`NK`; V6c's emission check).

`covOk k fs` is the coverage of an `MInst` of variant `k` built from fields `fs`: the
abstract counterpart of `FormOk` (`covOk_sound`, `IselCovForm`). `le` is the order (`le_sound`).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Aarch64

/-! ## Abstract values -/

/-- The kinds of values of the exclusion checker an abstract value can name. -/
inductive XK where
  | inst | data | value
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

/-- The exclusion checker's abstract value. -/
def XK.toAV : XK → AV
  | .inst => .inst
  | .data => .data
  | .value => .value

/-- The kinds of numeric/operand leaves (`AW.num k b`; meaning in `IselCovSem`): an integer in
`[0, b)`, an `Imm12` with `bits < b`, an `ImmShift`/`UImm5`/`UImm6` below `b`, a
`ShiftOpAndAmt` with amount below `b` and no `ror`, a `MoveWideConst` of 16 bits with shift below
`b`, a `CallInfo` whose target is a symbol or an int vreg (any registers inside). -/
inductive NK where
  | int | imm12 | immShift | uimm5 | uimm6 | shiftAmt | mwc | callInfo
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

/-- Abstract ISLE values. -/
inductive AW where
  | bot
  | flat (m : Nat) (c : Bool)
  | reg (m : Nat)
  | ty (ts : List CTy)
  | bool (b : Bool)
  | logic (sz : OperandSize)
  | scale (b : Nat)
  | simm9
  | xv (e : XK)
  | alts (as : List AW)
  | data (t : TypeId) (k : Nat) (fs : List AW)
  | num (k : NK) (b : Nat)
  deriving Repr, Inhabited, BEq

namespace AW

/-- Anything. -/
def top : AW := .flat 15 false
/-- No register, no `MInst`. -/
def c0 : AW := .flat 0 true

/-- The kind of a register (`flat`'s mask bits). -/
def _root_.Backend.Reg.kind : Reg → Nat
  | .vreg _ .int => 1
  | .vreg _ .float => 2
  | .xzr => 4
  | _ => 8

/-- The register kinds of a value an abstract value describes, if it is a register. -/
def mask : AW → Nat
  | .bot => 0
  | .reg m => m
  | .flat m _ => m
  | _ => 15

def isV (a : AW) : Bool := a.mask &&& 14 == 0
def isZ (a : AW) : Bool := a.mask &&& 11 == 0
def isVZ (a : AW) : Bool := a.mask &&& 10 == 0
def isF (a : AW) : Bool := a.mask &&& 13 == 0

/-- The variants of a field-less enum value. -/
def enumsOf : AW → Option (List Nat)
  | .data _ k [] => some [k]
  | .alts as => as.mapM fun a => match a with
    | .data _ k [] => some k
    | _ => none
  | _ => none

/-- Every variant the enum value may have satisfies `p`. -/
def enumAll (a : AW) (p : Nat → Bool) : Bool :=
  match a.enumsOf with
  | some ks => ks.all p
  | none => false

def allBytes : List Nat := [1, 2, 4, 8]

/-- The covered addressing modes, per variant: the access sizes and whether it is a slot offset. -/
def memSlot (_ : List AW) : List Nat × Bool := (allBytes, true)
def memAny (_ : List AW) : List Nat × Bool := (allBytes, false)
def memUnscaled : List AW → List Nat × Bool
  | [a, .simm9] => if a.isV then (allBytes, false) else ([], false)
  | _ => ([], false)
def memUOff : List AW → List Nat × Bool
  | [a, .scale b] => if a.isV then ([b], false) else ([], false)
  | _ => ([], false)
def memRR : List AW → List Nat × Bool
  | [a, b] => if a.isV && b.isV then (allBytes, false) else ([], false)
  | _ => ([], false)
def memRRE : List AW → List Nat × Bool
  | [a, b, e] =>
    if a.isV && b.isV && e.enumAll (fun k => match ExtendOp.ofIdx? k with
      | some e => decide (extOk e) | none => false) then (allBytes, false) else ([], false)
  | _ => ([], false)

/-- The addressing-mode checks by variant. -/
def memTab : List (Nat × (List AW → List Nat × Bool)) :=
  [(VIdx.AMode.SlotOffset, memSlot), (VIdx.AMode.SPOffset, memAny), (VIdx.AMode.FPOffset, memAny),
   (VIdx.AMode.Unscaled, memUnscaled), (VIdx.AMode.UnsignedOffset, memUOff),
   (VIdx.AMode.RegReg, memRR), (VIdx.AMode.RegScaled, memRR),
   (VIdx.AMode.RegScaledExtended, memRRE), (VIdx.AMode.RegExtended, memRRE)]

/-- The covered addressing mode of one variant. -/
def memOk1 (k : Nat) (fs : List AW) : List Nat × Bool :=
  match memTab.lookup k with
  | some c => c fs
  | none => ([], false)

/-- The access sizes at which an `AMode` value is covered (`memOk`), and whether it is a slot
offset. -/
def memOkA : AW → List Nat × Bool
  | .data _ k fs => memOk1 k fs
  | .alts as => as.foldl (fun acc a => match a with
      | .data _ k fs => let q := memOk1 k fs; (acc.1.filter (q.1.contains ·), acc.2 && q.2)
      | _ => ([], false)) (allBytes, true)
  | _ => ([], false)

def sizeIdx : OperandSize → Nat
  | .size32 => VIdx.OperandSize.Size32
  | .size64 => VIdx.OperandSize.Size64

/-- An `aluRRImmLogic`'s operation, size and immediate are covered. -/
def logicOk (op s imm : AW) : Bool :=
  op.enumAll (fun k => match ALUOp.ofIdx? k with | some o => logicOpOk o | none => false) &&
  (match s.enumsOf, imm with
   | some [k], .logic sz => k == sizeIdx sz
   | _, _ => false)

def atomOk : AW → Bool
  | .ty ts => ts.all fun t => decide (AtomTy t)
  | _ => false

def aluOpsIn (a : AW) (ks : List Nat) : Bool := a.enumAll (ks.contains ·)

/-! ### Coverage of an `MInst`, per variant (the abstract `FormOk`) -/

def cAluRRR : List AW → Bool
  | [_, _, rd, rn, rm] => rd.isVZ && rn.isVZ && rm.isVZ && (rn.isV || rm.isV) && (rd.isV || rn.isV)
  | _ => false
def cAluRRRR : List AW → Bool
  | [_, _, rd, rn, rm, ra] => rd.isV && rn.isV && rm.isV && ra.isVZ
  | _ => false
def cAluRRImm12 : List AW → Bool
  | [op, _, rd, rn, _] =>
    rn.isV && (rd.isV || (rd.isVZ && op.aluOpsIn [VIdx.ALUOp.AddS, VIdx.ALUOp.SubS]))
  | _ => false
def cAluRRImmLogic : List AW → Bool
  | [op, s, rd, rn, imm] =>
    logicOk op s imm && rd.isVZ && rn.isVZ &&
      (rd.isV || (rn.isV && op.aluOpsIn [VIdx.ALUOp.AndS])) && (rn.isV || rd.isV)
  | _ => false
def cAluRRImmShift : List AW → Bool
  | [op, _, rd, rn, _] =>
    rd.isV && rn.isV &&
      op.enumAll (fun k => match ALUOp.ofIdx? k with | some o => shiftOpOk o | none => false)
  | _ => false
def cAluRRRShift : List AW → Bool
  | [_, _, rd, rn, rm, _] => rd.isVZ && rn.isVZ && rm.isV && (rd.isV || rn.isV)
  | _ => false
def cAluRRRExtend : List AW → Bool
  | [op, _, rd, rn, rm, _] =>
    rn.isV && rm.isV && (rd.isV || (rd.isVZ && op.aluOpsIn [VIdx.ALUOp.AddS, VIdx.ALUOp.SubS]))
  | _ => false
def cOp2 : List AW → Bool
  | [_, _, rd, rn] => rd.isV && rn.isV
  | _ => false
def cMov : List AW → Bool
  | [_, rd, rm] => rd.isV && rm.isV
  | _ => false
def cMovWide : List AW → Bool
  | [_, rd, _, _] => rd.isV
  | _ => false
def cMovK : List AW → Bool
  | [rd, rn, _, _] => rd.isV && rn.isV
  | _ => false
def cExtend : List AW → Bool
  | [rd, rn, _, _, _] => rd.isV && rn.isV
  | _ => false
def cBfm : List AW → Bool
  | [_, _, rd, rn, _, _] => rd.isV && rn.isV
  | _ => false
def cCSet : List AW → Bool
  | [rd, _] => rd.isV
  | _ => false
def cCSel : List AW → Bool
  | [rd, _, rn, rm] => rd.isV && rn.isV && rm.isV
  | _ => false
def cCCmp : List AW → Bool
  | [_, rn, rm, _, _] => rn.isV && rm.isV
  | _ => false
def cCCmpImm : List AW → Bool
  | [_, rn, _, _, _] => rn.isV
  | _ => false
def cMovToFpu : List AW → Bool
  | [rd, rn, _] => rd.isF && rn.isV
  | _ => false
def cMovFromVec : List AW → Bool
  | [rd, rn, _, _] => rd.isV && rn.isF
  | _ => false
def cVec2 : List AW → Bool
  | [_, rd, rn, _] => rd.isF && rn.isF
  | _ => false
def cVecRRR : List AW → Bool
  | [_, rd, rn, rm, _] => rd.isF && rn.isF && rm.isF
  | _ => false
def cLoadAddr : List AW → Bool
  | [rd, m] => rd.isV && (memOkA m).2
  | _ => false
def cAtomic : List AW → Bool
  | [tyv, rt, rn, _] => atomOk tyv && rt.isV && rn.isV
  | _ => false
def cTrue (_ : List AW) : Bool := true

/-- The coverage checks by variant (loads and stores: `cMem`). -/
def covTab : List (Nat × (List AW → Bool)) :=
  [(VIdx.MInst.AluRRR, cAluRRR), (VIdx.MInst.AluRRRR, cAluRRRR),
   (VIdx.MInst.AluRRImm12, cAluRRImm12), (VIdx.MInst.AluRRImmLogic, cAluRRImmLogic),
   (VIdx.MInst.AluRRImmShift, cAluRRImmShift), (VIdx.MInst.AluRRRShift, cAluRRRShift),
   (VIdx.MInst.AluRRRExtend, cAluRRRExtend), (VIdx.MInst.BitRR, cOp2), (VIdx.MInst.Mov, cMov),
   (VIdx.MInst.MovWide, cMovWide), (VIdx.MInst.MovK, cMovK), (VIdx.MInst.Extend, cExtend),
   (VIdx.MInst.BitfieldMove, cBfm), (VIdx.MInst.CSet, cCSet), (VIdx.MInst.CSel, cCSel),
   (VIdx.MInst.CCmp, cCCmp), (VIdx.MInst.CCmpImm, cCCmpImm), (VIdx.MInst.MovToFpu, cMovToFpu),
   (VIdx.MInst.MovFromVec, cMovFromVec), (VIdx.MInst.VecMisc, cVec2),
   (VIdx.MInst.VecLanes, cVec2), (VIdx.MInst.VecRRR, cVecRRR), (VIdx.MInst.LoadAddr, cLoadAddr),
   (VIdx.MInst.CSetm, cCSet), (VIdx.MInst.Fence, cTrue), (VIdx.MInst.LoadAcquire, cAtomic),
   (VIdx.MInst.StoreRelease, cAtomic),
   (VIdx.MInst.Call, cTrue), (VIdx.MInst.CallInd, cTrue), (VIdx.MInst.Jump, cTrue),
   (VIdx.MInst.CondBr, cTrue), (VIdx.MInst.TestBitAndBranch, cTrue), (VIdx.MInst.TrapIf, cTrue),
   (VIdx.MInst.Udf, cTrue), (VIdx.MInst.JTSequence, cTrue), (VIdx.MInst.LoadExtNameGot, cTrue),
   (VIdx.MInst.LoadExtNameNear, cTrue), (VIdx.MInst.EmitIsland, cTrue),
   (VIdx.MInst.AtomicRMWLoop, cTrue), (VIdx.MInst.AtomicCASLoop, cTrue),
   (VIdx.MInst.ElfTlsGetAddr, cTrue)]

/-- Loads and stores: the register is an int vreg, the addressing mode is covered at the
access size. -/
def cMem (k : Nat) : List AW → Bool
  | [rd, m, _] =>
    match loadOpOfIdx? k, storeOpOfIdx? k with
    | some op, _ => rd.isV && (memOkA m).1.contains op.bytes
    | none, some op => rd.isV && (memOkA m).1.contains op.bytes
    | none, none => false
  | _ => false

/-- **Coverage of an `MInst`** of variant `k` with fields described by `as`. -/
def covOk (k : Nat) (as : List AW) : Bool :=
  match covTab.lookup k with
  | some c => c as
  | none => cMem k as

mutual
/-- Deep facts: the register kinds inside, and whether every `MInst` inside is covered. -/
def deep : AW → Nat × Bool
  | .bot => (0, true)
  | .flat m c => (m, c)
  | .reg m => (m, true)
  | .alts as => deepL as
  | .data t k fs => ((deepL fs).1, (deepL fs).2 && (t != tyMInst || covOk k fs))
  | .num k _ => (if k = .callInfo then 15 else 0, true)
  | _ => (0, true)
/-- `deep` of a list (the union of masks, the conjunction of flags). -/
def deepL : List AW → Nat × Bool
  | [] => (0, true)
  | a :: as => ((deep a).1 ||| (deepL as).1, (deep a).2 && (deepL as).2)
end

/-- The flat value of `deep a`. -/
def flatOf (a : AW) : AW := .flat (deep a).1 (deep a).2

/-- An abstract value no ISLE value has. -/
def isBot : AW → Bool
  | .bot => true
  | .ty [] => true
  | _ => false

/-- Split a set of types into single types (the abstract environments of a rule). -/
def split (a : AW) : List AW :=
  match a with
  | .ty (t :: u :: us) => (t :: u :: us).map fun t => .ty [t]
  | _ => [a]

/-- The masks of `a` are inside those of `m`, and `a`'s flag implies `c`. -/
def deepLe (a : AW) (m : Nat) (c : Bool) : Bool :=
  (deep a).1 &&& m == (deep a).1 && (!c || (deep a).2)

/-- The order on the non-recursive shapes. -/
def leBase : AW → AW → Bool
  | a, .flat m c => deepLe a m c
  | .reg m, .reg n => m &&& n == m
  | .ty ts, .ty us => ts.all fun t => us.any fun u => decide (u = t)
  | .bool b, .bool b' => b == b'
  | .logic s, .logic s' => s == s'
  | .scale b, .scale b' => b == b'
  | .simm9, .simm9 => true
  | .xv e, .xv e' => decide (e = e')
  | .num k b, .num k' b' => decide (k = k') && decide (b ≤ b')
  | _, _ => false

mutual
/-- **The order**: every value `a` describes, `b` describes (`le_sound`). -/
def le : AW → AW → Bool
  | .bot, _ => true
  | .alts as, b => leAlts as b
  | .data t k fs, .flat m c => deepLe (.data t k fs) m c
  | .data t k fs, .data t' k' gs => t == t' && k == k' && leL fs gs
  | .data t k fs, .alts bs => leSome (.data t k fs) bs
  | .data _ _ _, _ => false
  | a, b => leBase a b
  termination_by a b => sizeOf a + sizeOf b
/-- Every element of `as` is below `b`. -/
def leAlts : List AW → AW → Bool
  | [], _ => true
  | a :: as, b => le a b && leAlts as b
  termination_by as b => sizeOf as + sizeOf b
/-- `a` is below some element of `bs`. -/
def leSome : AW → List AW → Bool
  | _, [] => false
  | a, b :: bs => le a b || leSome a bs
  termination_by a bs => sizeOf a + sizeOf bs
/-- Pointwise order (same lengths). -/
def leL : List AW → List AW → Bool
  | [], [] => true
  | a :: as, b :: bs => le a b && leL as bs
  | _, _ => false
  termination_by as bs => sizeOf as + sizeOf bs
end

/-- Pointwise order of argument lists. -/
def leAll (as bs : List AW) : Bool := leL as bs

end AW

end Backend.Proof.Cov
