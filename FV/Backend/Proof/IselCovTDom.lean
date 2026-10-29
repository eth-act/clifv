import FV.Backend.Proof.IselCovDom

/-!
# Form coverage over float-capable contexts (typed V3): the abstract domain

`IselCovDom`'s domain for the typed lowering (S11 slice 8). `AT` is `AW` without the exclusion
checker's values `xv` (whose meaning is subset E's), with atoms that carry the CLIF typing a
float-capable context needs:

* `val ts`: a CLIF value of a type in `ts` (the register class of its vreg is its type's);
* `vals tss`: a `.values` list, position by position; `valsAll ts`: one of any length;
* `inst fs`: an instruction of the context of one of the instruction families `fs` (a family
  pairs the result types with an abstract `InstructionData` whose value fields are typed:
  `IselCovTFam`);
* `movi`: the `ASIMDMovModImm` of the plain `movi` (`FormOk`'s `VecDupImm`); `extv`: an
  extended operand of an integer value (`extended_value_from_value`).

`covOk` is `IselCovDom`'s with the float forms of `FormOk` (`fpuLoad`/`fpuStore` of `s`/`d`,
`fpuRRR`, `fpuRR`, `fpuCmp`, the plain `movi`). `split` also splits a value's types (so a rule's
`value_type` dispatch sees the class of the value it binds).
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Aarch64
open Backend.Proof.Cov (NK)

/-! ## Abstract values -/

/-- Abstract ISLE values. -/
inductive AT where
  | bot
  | flat (m : Nat) (c : Bool)
  | reg (m : Nat)
  | ty (ts : List CTy)
  | bool (b : Bool)
  | logic (sz : OperandSize)
  | scale (b : Nat)
  | simm9
  /-- A CLIF value `.value x` of a type in `ts` (an untyped one: if `ts` has an integer type). -/
  | val (ts : List CTy)
  /-- `.values xs`, value `i` of a type in `tss[i]`. -/
  | vals (tss : List (List CTy))
  /-- `.values xs`, every value of a type in `ts` (a call's arguments). -/
  | valsAll (ts : List CTy)
  /-- `.inst j`: an instruction of the context of one of the families `fs` (`famTab`). -/
  | inst (fs : List Nat)
  /-- An `ASIMDMovModImm` that `FormOk`'s `VecDupImm` accepts (zero, no shift, 32-bit form). -/
  | movi
  /-- An extended operand `.op (.extended x e)` of an integer-typed value `x`. -/
  | extv
  | alts (as : List AT)
  | data (t : TypeId) (k : Nat) (fs : List AT)
  | num (k : NK) (b : Nat)
  deriving Repr, Inhabited, BEq

namespace AT

/-- Anything. -/
def top : AT := .flat 15 false
/-- No register, no `MInst`. -/
def c0 : AT := .flat 0 true

/-- The register kinds of a value an abstract value describes, if it is a register. -/
def mask : AT → Nat
  | .bot => 0
  | .reg m => m
  | .flat m _ => m
  | _ => 15

def isV (a : AT) : Bool := a.mask &&& 14 == 0
def isZ (a : AT) : Bool := a.mask &&& 11 == 0
def isVZ (a : AT) : Bool := a.mask &&& 10 == 0
def isF (a : AT) : Bool := a.mask &&& 13 == 0

/-- The variants of a field-less enum value. -/
def enumsOf : AT → Option (List Nat)
  | .data _ k [] => some [k]
  | .alts as => as.mapM fun a => match a with
    | .data _ k [] => some k
    | _ => none
  | _ => none

/-- Every variant the enum value may have satisfies `p`. -/
def enumAll (a : AT) (p : Nat → Bool) : Bool :=
  match a.enumsOf with
  | some ks => ks.all p
  | none => false

def allBytes : List Nat := [1, 2, 4, 8]

/-- The covered addressing modes, per variant: the access sizes and whether it is a slot offset. -/
def memSlot (_ : List AT) : List Nat × Bool := (allBytes, true)
def memAny (_ : List AT) : List Nat × Bool := (allBytes, false)
def memUnscaled : List AT → List Nat × Bool
  | [a, .simm9] => if a.isV then (allBytes, false) else ([], false)
  | _ => ([], false)
def memUOff : List AT → List Nat × Bool
  | [a, .scale b] => if a.isV then ([b], false) else ([], false)
  | _ => ([], false)
def memRR : List AT → List Nat × Bool
  | [a, b] => if a.isV && b.isV then (allBytes, false) else ([], false)
  | _ => ([], false)
def memRRE : List AT → List Nat × Bool
  | [a, b, e] =>
    if a.isV && b.isV && e.enumAll (fun k => match ExtendOp.ofIdx? k with
      | some e => decide (extOk e) | none => false) then (allBytes, false) else ([], false)
  | _ => ([], false)

/-- The addressing-mode checks by variant. -/
def memTab : List (Nat × (List AT → List Nat × Bool)) :=
  [(VIdx.AMode.SlotOffset, memSlot), (VIdx.AMode.SPOffset, memAny), (VIdx.AMode.FPOffset, memAny),
   (VIdx.AMode.Unscaled, memUnscaled), (VIdx.AMode.UnsignedOffset, memUOff),
   (VIdx.AMode.RegReg, memRR), (VIdx.AMode.RegScaled, memRR),
   (VIdx.AMode.RegScaledExtended, memRRE), (VIdx.AMode.RegExtended, memRRE)]

/-- The covered addressing mode of one variant. -/
def memOk1 (k : Nat) (fs : List AT) : List Nat × Bool :=
  match memTab.lookup k with
  | some c => c fs
  | none => ([], false)

/-- The access sizes at which an `AMode` value is covered (`memOk`), and whether it is a slot
offset. -/
def memOkA : AT → List Nat × Bool
  | .data _ k fs => memOk1 k fs
  | .alts as => as.foldl (fun acc a => match a with
      | .data _ k fs => let q := memOk1 k fs; (acc.1.filter (q.1.contains ·), acc.2 && q.2)
      | _ => ([], false)) (allBytes, true)
  | _ => ([], false)

def sizeIdx : OperandSize → Nat
  | .size32 => VIdx.OperandSize.Size32
  | .size64 => VIdx.OperandSize.Size64

/-- An `aluRRImmLogic`'s operation, size and immediate are covered. -/
def logicOk (op s imm : AT) : Bool :=
  op.enumAll (fun k => match ALUOp.ofIdx? k with | some o => logicOpOk o | none => false) &&
  (match s.enumsOf, imm with
   | some [k], .logic sz => k == sizeIdx sz
   | _, _ => false)

def atomOk : AT → Bool
  | .ty ts => ts.all fun t => decide (AtomTy t)
  | _ => false

def aluOpsIn (a : AT) (ks : List Nat) : Bool := a.enumAll (ks.contains ·)

/-! ### Coverage of an `MInst`, per variant (the abstract `FormOk`) -/

def cAluRRR : List AT → Bool
  | [_, _, rd, rn, rm] => rd.isVZ && rn.isVZ && rm.isVZ && (rn.isV || rm.isV) && (rd.isV || rn.isV)
  | _ => false
def cAluRRRR : List AT → Bool
  | [_, _, rd, rn, rm, ra] => rd.isV && rn.isV && rm.isV && ra.isVZ
  | _ => false
def cAluRRImm12 : List AT → Bool
  | [op, _, rd, rn, _] =>
    rn.isV && (rd.isV || (rd.isVZ && op.aluOpsIn [VIdx.ALUOp.AddS, VIdx.ALUOp.SubS]))
  | _ => false
def cAluRRImmLogic : List AT → Bool
  | [op, s, rd, rn, imm] =>
    logicOk op s imm && rd.isVZ && rn.isVZ &&
      (rd.isV || (rn.isV && op.aluOpsIn [VIdx.ALUOp.AndS])) && (rn.isV || rd.isV)
  | _ => false
def cAluRRImmShift : List AT → Bool
  | [op, _, rd, rn, _] =>
    rd.isV && rn.isV &&
      op.enumAll (fun k => match ALUOp.ofIdx? k with | some o => shiftOpOk o | none => false)
  | _ => false
def cAluRRRShift : List AT → Bool
  | [_, _, rd, rn, rm, _] => rd.isVZ && rn.isVZ && rm.isV && (rd.isV || rn.isV)
  | _ => false
def cAluRRRExtend : List AT → Bool
  | [op, _, rd, rn, rm, _] =>
    rn.isV && rm.isV && (rd.isV || (rd.isVZ && op.aluOpsIn [VIdx.ALUOp.AddS, VIdx.ALUOp.SubS]))
  | _ => false
def cOp2 : List AT → Bool
  | [_, _, rd, rn] => rd.isV && rn.isV
  | _ => false
def cMov : List AT → Bool
  | [_, rd, rm] => rd.isV && rm.isV
  | _ => false
def cMovWide : List AT → Bool
  | [_, rd, _, _] => rd.isV
  | _ => false
def cMovK : List AT → Bool
  | [rd, rn, _, _] => rd.isV && rn.isV
  | _ => false
def cExtend : List AT → Bool
  | [rd, rn, _, _, _] => rd.isV && rn.isV
  | _ => false
def cBfm : List AT → Bool
  | [_, _, rd, rn, _, _] => rd.isV && rn.isV
  | _ => false
def cCSet : List AT → Bool
  | [rd, _] => rd.isV
  | _ => false
def cCSel : List AT → Bool
  | [rd, _, rn, rm] => rd.isV && rn.isV && rm.isV
  | _ => false
def cCCmp : List AT → Bool
  | [_, rn, rm, _, _] => rn.isV && rm.isV
  | _ => false
def cCCmpImm : List AT → Bool
  | [_, rn, _, _, _] => rn.isV
  | _ => false
def cMovToFpu : List AT → Bool
  | [rd, rn, _] => rd.isF && rn.isV
  | _ => false
def cMovFromVec : List AT → Bool
  | [rd, rn, _, _] => rd.isV && rn.isF
  | _ => false
def cVec2 : List AT → Bool
  | [_, rd, rn, _] => rd.isF && rn.isF
  | _ => false
def cVecRRR : List AT → Bool
  | [_, rd, rn, rm, _] => rd.isF && rn.isF && rm.isF
  | _ => false
def cLoadAddr : List AT → Bool
  | [rd, m] => rd.isV && (memOkA m).2
  | _ => false
def cAtomic : List AT → Bool
  | [tyv, rt, rn, _] => atomOk tyv && rt.isV && rn.isV
  | _ => false
/-- `fcsel` (S11e1): float vreg destination and sources. -/
def cFpuCSel : List AT → Bool
  | [rd, rn, rm, _] => rd.isF && rn.isF && rm.isF
  | _ => false
/-- `fmov #imm` (S11e1): a float vreg destination. -/
def cFpuMoveFPImm : List AT → Bool
  | [rd, _, _] => rd.isF
  | _ => false
/-- `ldr`/`str` of an `s`/`d` register (S11e1): a float vreg, the addressing mode covered at the
access size. -/
def cFpuMem (bytes : Nat) : List AT → Bool
  | [rd, m, _] => rd.isF && (memOkA m).1.contains bytes
  | _ => false
/-- The literal-pool entry (`AMode.Const`, #565). -/
def isConstA : AT → Bool
  | .data _ k _ => k == VIdx.AMode.Const
  | _ => false
/-- `ldr s/d` (S11e1): a float vreg, the addressing mode covered at the access size, or the
literal-pool entry (`AMode.Const`: the `ldr (literal)` pool load, `MInst.isPoolLoad`, #565). -/
def cFpuLoad (bytes : Nat) : List AT → Bool
  | [rd, m, _] => rd.isF && ((memOkA m).1.contains bytes || m.isConstA)
  | _ => false
/-- `fadd`… (S11f): float vregs. -/
def cFpuRRR : List AT → Bool
  | [_, _, rd, rn, rm] => rd.isF && rn.isF && rm.isF
  | _ => false
/-- `fabs`/`fneg`/`fsqrt`/`fcvt` (S11f): float vregs. -/
def cFpuRR : List AT → Bool
  | [_, _, rd, rn] => rd.isF && rn.isF
  | _ => false
/-- `fcmp` (S11f): float vregs. -/
def cFpuCmp : List AT → Bool
  | [_, rn, rm] => rn.isF && rm.isF
  | _ => false
/-- `frint*` (S11f, `[op, rd, rn]`): float vregs. -/
def cFpuRound : List AT → Bool
  | [_, rd, rn] => rd.isF && rn.isF
  | _ => false
/-- `fcvtzs`/`fcvtzu` (S11f-cvt, `[op, rd, rn]`): an int vreg destination, a float vreg source. -/
def cFpuToInt : List AT → Bool
  | [_, rd, rn] => rd.isV && rn.isF
  | _ => false
/-- `scvtf`/`ucvtf` (S11f-cvt, `[op, rd, rn]`): a float vreg destination, an int vreg source. -/
def cIntToFpu : List AT → Bool
  | [_, rd, rn] => rd.isF && rn.isV
  | _ => false
/-- The plain `movi` (S11e1): a float vreg, the zero immediate of the 32-bit form, no inversion. -/
def cVecDupImm : List AT → Bool
  | [rd, .movi, .bool false, _] => rd.isF
  | _ => false
def cTrue (_ : List AT) : Bool := true

/-- The coverage checks by variant (loads and stores: `cMem`). -/
def covTab : List (Nat × (List AT → Bool)) :=
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
   (VIdx.MInst.ElfTlsGetAddr, cTrue), (VIdx.MInst.FpuCSel32, cFpuCSel),
   (VIdx.MInst.FpuCSel64, cFpuCSel), (VIdx.MInst.FpuMoveFPImm, cFpuMoveFPImm),
   (VIdx.MInst.FpuLoad32, cFpuLoad 4), (VIdx.MInst.FpuLoad64, cFpuLoad 8),
   (VIdx.MInst.FpuStore32, cFpuMem 4), (VIdx.MInst.FpuStore64, cFpuMem 8),
   (VIdx.MInst.FpuRRR, cFpuRRR), (VIdx.MInst.FpuRR, cFpuRR), (VIdx.MInst.FpuCmp, cFpuCmp),
   (VIdx.MInst.VecDupImm, cVecDupImm), (VIdx.MInst.FpuRound, cFpuRound),
   (VIdx.MInst.FpuToInt, cFpuToInt), (VIdx.MInst.IntToFpu, cIntToFpu)]

/-- Integer loads and stores: the register is an int vreg, the addressing mode is covered at the
access size. -/
def cMem (k : Nat) : List AT → Bool
  | [rd, m, _] =>
    match loadOpOfIdx? k, storeOpOfIdx? k with
    | some op, _ => rd.isV && (memOkA m).1.contains op.bytes
    | none, some op => rd.isV && (memOkA m).1.contains op.bytes
    | none, none => false
  | _ => false

/-- **Coverage of an `MInst`** of variant `k` with fields described by `as`. -/
def covOk (k : Nat) (as : List AT) : Bool :=
  match covTab.lookup k with
  | some c => c as
  | none => cMem k as

mutual
/-- Deep facts: the register kinds inside, and whether every `MInst` inside is covered. -/
def deep : AT → Nat × Bool
  | .bot => (0, true)
  | .flat m c => (m, c)
  | .reg m => (m, true)
  | .alts as => deepL as
  | .data t k fs => ((deepL fs).1, (deepL fs).2 && (t != tyMInst || covOk k fs))
  | .num k _ => (if k = .callInfo then 15 else 0, true)
  | _ => (0, true)
/-- `deep` of a list (the union of masks, the conjunction of flags). -/
def deepL : List AT → Nat × Bool
  | [] => (0, true)
  | a :: as => ((deep a).1 ||| (deepL as).1, (deep a).2 && (deepL as).2)
end

/-- The flat value of `deep a`. -/
def flatOf (a : AT) : AT := .flat (deep a).1 (deep a).2

/-- An abstract value no ISLE value has. -/
def isBot : AT → Bool
  | .bot => true
  | .ty [] => true
  | .val [] => true
  | .inst [] => true
  | _ => false

/-- Split a set of types into single types (the abstract environments of a rule). -/
def split (a : AT) : List AT :=
  match a with
  | .ty (t :: u :: us) => (t :: u :: us).map fun t => .ty [t]
  | .val (t :: u :: us) => (t :: u :: us).map fun t => .val [t]
  | _ => [a]

/-- The masks of `a` are inside those of `m`, and `a`'s flag implies `c`. -/
def deepLe (a : AT) (m : Nat) (c : Bool) : Bool :=
  (deep a).1 &&& m == (deep a).1 && (!c || (deep a).2)

/-- The order on the non-recursive shapes. -/
def leBase : AT → AT → Bool
  | a, .flat m c => deepLe a m c
  | .reg m, .reg n => m &&& n == m
  | .ty ts, .ty us => ts.all fun t => us.any fun u => decide (u = t)
  | .bool b, .bool b' => b == b'
  | .logic s, .logic s' => s == s'
  | .scale b, .scale b' => b == b'
  | .simm9, .simm9 => true
  | .val ts, .val us => ts.all fun t => us.any fun u => decide (u = t)
  | .vals tss, .vals uss => tss.length == uss.length &&
    (tss.zip uss).all fun (ts, us) => ts.all fun t => us.any fun u => decide (u = t)
  | .valsAll ts, .valsAll us => ts.all fun t => us.any fun u => decide (u = t)
  | .inst fs, .inst gs => fs.all fun i => gs.contains i
  | .movi, .movi => true
  | .extv, .extv => true
  | .num k b, .num k' b' => decide (k = k') && decide (b ≤ b')
  | _, _ => false

mutual
/-- **The order**: every value `a` describes, `b` describes (`le_sound`). -/
def le : AT → AT → Bool
  | .bot, _ => true
  | .alts as, b => leAlts as b
  | .data t k fs, .flat m c => deepLe (.data t k fs) m c
  | .data t k fs, .data t' k' gs => t == t' && k == k' && leL fs gs
  | .data t k fs, .alts bs => leSome (.data t k fs) bs
  | .data _ _ _, _ => false
  | a, b => leBase a b
  termination_by a b => sizeOf a + sizeOf b
/-- Every element of `as` is below `b`. -/
def leAlts : List AT → AT → Bool
  | [], _ => true
  | a :: as, b => le a b && leAlts as b
  termination_by as b => sizeOf as + sizeOf b
/-- `a` is below some element of `bs`. -/
def leSome : AT → List AT → Bool
  | _, [] => false
  | a, b :: bs => le a b || leSome a bs
  termination_by a bs => sizeOf a + sizeOf bs
/-- Pointwise order (same lengths). -/
def leL : List AT → List AT → Bool
  | [], [] => true
  | a :: as, b :: bs => le a b && leL as bs
  | _, _ => false
  termination_by as bs => sizeOf as + sizeOf bs
end

/-- Pointwise order of argument lists. -/
def leAll (as bs : List AT) : Bool := leL as bs

end AT

end Backend.Proof.CovT
