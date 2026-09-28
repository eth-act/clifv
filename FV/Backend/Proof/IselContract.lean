import FV.Backend.Proof.IselGeneric
import FV.Backend.Proof.IselData
import FV.Backend.Proof.RegallocOperands

/-!
# The isel contract: what M4 proves about the ISLE rules, and what M7 consumes

**Level.** Rule statements are about VCode: `MInst`s over virtual registers, run
straight-line (`seqRun`, `VStep`'s per-instruction rule) under an *abstract* per-instruction
semantics `isem : Sem` (values `CV`, world = the Arm state), exactly the semantics M6's
`checkAlloc_sound` simulates. M6's `csem F ctx` (the Arm model's execution of an instruction under
a canonical allocation) is the instance; the rules only need `Refines F isem`: `isem` agrees
with `ispec`, the value-level meaning of each emitted instruction form, up to the world
outside the allocatable registers (`SameWorld F`).

**Width convention** (PLAN.md §3.4): a CLIF value of type `ty` is the low `ty.width` bits of
its register (`VHolds`); upper bits are unspecified. Every rule obligation is local.

**Shapes.** `seqRun`, `LowerInstOk`, `LowerTermOk` and their pieces are the definitions agreed
with M7 (`Backend.Proof.Driver` in M7's placeholder, same definitions): the emitted code, run
from any vreg file holding the CLIF frame's values and any related world, computes the
instruction's results into fresh (or value) vregs, writes only fresh vregs, keeps the
memory relation `MR`, and stops at a halting instruction with the CLIF trap code for explicit
traps.

**Per rule.** `LowerRuleOk … r`: whenever root rule `r` of `lower` matches an instruction and
its right-hand side returns a value, the code it emitted satisfies `LowerInstOk`. Selection is
not needed ("the committed rule matched", `IselGeneric`): `lowerInstOk_of_rules` turns
`LowerRulesCorrect p` (every closure root rule is `LowerRuleOk`) plus `ExcludedUnmatchable p`
(the root rules outside the closure never match an E instruction) into `LowerInstOk` for every
successful `lower` call (`runTerm ctx "lower" …`, `lowerInstOk_runTerm`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-! ## Values and the width convention -/

/-- The VCode-level instruction semantics (M6's `csem F ctx` is the instance). -/
abbrev Sem := ISem CV Arm.ArmState

/-- A CLIF value of type `ty` is the low `ty.width` bits of a register value; the upper bits are
unspecified (PLAN.md §3.4). -/
def VHolds (v : Clif.Val) (x : CV) : Prop := x.setWidth v.ty.width = v.bits

/-- `vals` are held by `xs`, index by index. -/
def AllHold (vals : List Clif.Val) (xs : List CV) : Prop :=
  vals.length = xs.length ∧ ∀ (j : Nat) v x, vals[j]? = some v → xs[j]? = some x → VHolds v x

/-- Relation between the CLIF memory (with the activation's slot bases) and the VCode world. -/
abbrev MemRelT := List (Clif.SlotId × Nat) → Clif.Mem → Arm.ArmState → Prop

/-- Every defined CLIF value `x` is held by vreg `x` (`buildCtx`: value `x` has vreg `x`). -/
def ValsHeld (fr : Clif.Frame) (ρ : Nat → CV) : Prop :=
  ∀ x v, fr.regs x = some v → VHolds v (ρ x)

/-! ## Straight-line VCode execution (`VStep`'s per-instruction rule) -/

section
variable {V W : Type}

/-- Use values of an instruction with operands `ops` in the vreg file `ρ`. -/
def vuses (ops : Array Operand) (ρ : Nat → V) : List V :=
  (ops.toList.filter Operand.isUse).map (ρ ·.vreg)

/-- `VStep`'s register-file update: early defs, then late defs. -/
def vdefUpd (ops : Array Operand) (outs : List V) (ρ : Nat → V) : Nat → V :=
  writeV (writeV ρ (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isEarly)))
    (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isLate))

/-- Def vregs of an instruction (empty if it has no operand view). -/
def vdefs (i : MInst) : List Nat :=
  match i.operands with
  | .ok ops => (ops.toList.filter Operand.isDef).map (·.vreg)
  | .error _ => []

/-- Use vregs of an instruction (empty if it has no operand view). -/
def vuseNums (i : MInst) : List Nat :=
  match i.operands with
  | .ok ops => (ops.toList.filter Operand.isUse).map (·.vreg)
  | .error _ => []

/-- How a straight-line run ended. `stop k i ops ρ w outs w' ctl`: instruction `k` (`i`,
operands `ops`) ran in state `ρ, w`, produced `outs, w'` and control `ctl ≠ next`. -/
inductive SeqEnd (V W : Type) where
  | fall (ρ : Nat → V) (w : W)
  | stop (k : Nat) (i : MInst) (ops : Array Operand) (ρ : Nat → V) (w : W) (outs : List V)
      (w' : W) (ctl : Ctl)

def SeqEnd.succ : SeqEnd V W → SeqEnd V W
  | .fall ρ w => .fall ρ w
  | .stop k i ops ρ w outs w' ctl => .stop (k + 1) i ops ρ w outs w' ctl

/-- Straight-line run of `ms`. -/
def seqRun (sem : ISem V W) : List MInst → (Nat → V) → W → Option (SeqEnd V W)
  | [], ρ, w => some (.fall ρ w)
  | i :: ms, ρ, w =>
    match i.operands with
    | .error _ => none
    | .ok ops =>
      match sem i (vuses ops ρ) w with
      | none => none
      | some (outs, w', ctl) =>
        if outs.length = (ops.toList.filter Operand.isDef).length then
          match ctl with
          | .next => (seqRun sem ms (vdefUpd ops outs ρ) w').map SeqEnd.succ
          | ctl => some (.stop 0 i ops ρ w outs w' ctl)
        else none

end

/-! ## The value-level spec of the emitted instruction forms -/

/-- The operand at an operation size: the low `sz.bits` bits of the register. -/
def opnd (sz : OperandSize) (a : CV) : BitVec sz.bits := (lo64 a).setWidth sz.bits

/-- A result at an operation size, zero-extended into the 64-bit register. -/
def resX (sz : OperandSize) (r : BitVec sz.bits) : CV := ofX (r.setWidth 64)

/-- The def outputs of an instruction with destination `rd` (a real register such as `xzr` is
not an operand, so it has no output). -/
def defOut (rd : Reg) (x : CV) : List CV :=
  match rd with
  | .vreg .. => [x]
  | _ => []

/-- The multiply-add operations (`madd`/`msub`: `c ± a * b`), at width `n`. -/
def mulAddVal {n : Nat} (op : ALUOp3) (a b c : BitVec n) : Option (BitVec n) :=
  match op with
  | .mAdd => some (c + a * b)
  | .mSub => some (c - a * b)
  | _ => none

/-- The operations with a shifted-register form (`add`/`sub`/logical). -/
def aluShiftable : ALUOp → Bool
  | .add | .sub | .and | .orr | .eor | .andNot | .orrNot | .eorNot => true
  | _ => false

/-- The extended-register operand (amount 0): the low 8/16/32/64 bits of the register, zero-
or sign-extended to the operation width `n`. -/
def extendVal (e : ExtendOp) (n : Nat) (b : CV) : BitVec n :=
  match e with
  | .uxtb => ((lo64 b).setWidth 8).setWidth n
  | .uxth => ((lo64 b).setWidth 16).setWidth n
  | .uxtw => ((lo64 b).setWidth 32).setWidth n
  | .uxtx => (lo64 b).setWidth n
  | .sxtb => ((lo64 b).setWidth 8).signExtend n
  | .sxth => ((lo64 b).setWidth 16).signExtend n
  | .sxtw => ((lo64 b).setWidth 32).signExtend n
  | .sxtx => (lo64 b).signExtend n

/-- Byte `i` of a 64-bit value. -/
def byteOf (x : BitVec 64) (i : Nat) : BitVec 8 := x.extractLsb' (8 * i) 8

/-- `CNT Vd.8B, Vn.8B`: the population count of each byte. -/
def cntBytes (x : BitVec 64) : BitVec 64 :=
  (byteOf x 7).cpop ++ (byteOf x 6).cpop ++ (byteOf x 5).cpop ++ (byteOf x 4).cpop ++
    (byteOf x 3).cpop ++ (byteOf x 2).cpop ++ (byteOf x 1).cpop ++ (byteOf x 0).cpop

/-- `ADDP Vd.8B, Vn.8B, Vm.8B`: sums of adjacent byte pairs of `n` (low half), then of `m`. -/
def addpBytes (n m : BitVec 64) : BitVec 64 :=
  (byteOf m 6 + byteOf m 7) ++ (byteOf m 4 + byteOf m 5) ++ (byteOf m 2 + byteOf m 3) ++
    (byteOf m 0 + byteOf m 1) ++ (byteOf n 6 + byteOf n 7) ++ (byteOf n 4 + byteOf n 5) ++
    (byteOf n 2 + byteOf n 3) ++ (byteOf n 0 + byteOf n 1)

/-- `ADDV Bd, Vn.8B`: the sum of the eight bytes (modulo 256), zero-extended. -/
def addvBytes (x : BitVec 64) : BitVec 64 :=
  (byteOf x 0 + byteOf x 1 + byteOf x 2 + byteOf x 3 + byteOf x 4 + byteOf x 5 + byteOf x 6 +
    byteOf x 7).setWidth 64

/-- `UBFM`/`SBFM` at width `n` (`immr`, `imms` below `n`): for `immr ≤ imms` the field
`x[imms:immr]` moved to bit 0, else the field `x[imms:0]` moved to bit `n - immr`; zero-extended
(`UBFM`) or sign-extended from the field's top bit (`SBFM`), zeros below. -/
def bfmVal {n : Nat} (op : BfmOp) (x : BitVec n) (immr imms : Nat) : BitVec n :=
  if immr ≤ imms then
    let f := (x >>> immr).setWidth (imms - immr + 1)
    match op with
    | .uBfm => f.setWidth n
    | .sBfm => f.signExtend n
  else
    let f := x.setWidth (imms + 1)
    match op with
    | .uBfm => f.setWidth n <<< (n - immr)
    | .sBfm => f.signExtend n <<< (n - immr)

/-- The non-flag-setting two-operand ALU operations, at width `n`. -/
def aluVal {n : Nat} (op : ALUOp) (a b : BitVec n) : Option (BitVec n) :=
  match op with
  | .add => some (a + b)
  | .sub => some (a - b)
  | .and => some (a &&& b)
  | .orr => some (a ||| b)
  | .eor => some (a ^^^ b)
  | .andNot => some (a &&& ~~~b)
  | .orrNot => some (a ||| ~~~b)
  | .eorNot => some (a ^^^ ~~~b)
  | _ => none

/-- The shift operations (`LSLV`/`LSRV`/`ASRV`/`RORV` as `AluRRR`, `LSL`/`LSR`/`ASR`/`ROR`
immediate as `AluRRImmShift`; `extr` is Cranelift's rotate), by `amt`, at width `n`. -/
def shiftVal {n : Nat} (op : ALUOp) (a : BitVec n) (amt : Nat) : Option (BitVec n) :=
  match op with
  | .lsl => some (a <<< amt)
  | .lsr => some (a >>> amt)
  | .asr => some (a.sshiftRight amt)
  | .extr => some (a.rotateRight amt)
  | _ => none

/-- A register-register ALU operation (`AluRRR`): the two-operand operations, then the shifts
by the second operand modulo the width (`exec_data_processing_shift`). -/
def rrrVal {n : Nat} (op : ALUOp) (a b : BitVec n) : Option (BitVec n) :=
  (aluVal op a b).orElse fun _ => shiftVal op a (b.toNat % n)

/-- `REV16` on a 32-bit register: swap the bytes of each halfword. -/
def rev16w (x : BitVec 32) : BitVec 32 :=
  ((x >>> 8) &&& 0x00FF00FF#32) ||| ((x <<< 8) &&& 0xFF00FF00#32)

/-- The condition of a `CondBrKind` on the use values and the world's flags (`cbz`/`cbnz` test
the low 32 or 64 bits of the register; `b.cond` tests the flags). -/
def condBrHolds (k : CondBrKind) (uses : List CV) (w : Arm.ArmState) : Bool :=
  match k, uses with
  | .cond c, _ => Arm.ConditionHolds c.bits w
  | .zero _ sz, [a] => if sz.is64 then lo64 a == 0 else (lo64 a).setWidth 32 == 0
  | .notZero _ sz, [a] => if sz.is64 then lo64 a != 0 else (lo64 a).setWidth 32 != 0
  | _, _ => false

/-- The flags of `ANDS` (`TST`): `N` = sign bit, `Z` = result is zero, `C = V = 0`. -/
def andsFlags {n : Nat} (r : BitVec n) : Arm.PState :=
  Arm.make_pstate (Arm.BitVec.lsb r (n - 1)) (if r = 0#n then 1#1 else 0#1) 0#1 0#1

/-- `MOVZ`/`MOVN` at width `n`: `imm.bits << 16·imm.shift`, inverted for `MOVN`. -/
def movWideVal (op : MoveWideOp) (n : Nat) (imm : MoveWideConst) : BitVec n :=
  match op with
  | .movZ => BitVec.ofNat n imm.bits <<< (16 * imm.shift)
  | .movN => ~~~(BitVec.ofNat n imm.bits <<< (16 * imm.shift))

/-- `MOVK` at width `n`: the 16-bit slice `imm.shift` of `a` replaced by `imm.bits`. -/
def movKVal {n : Nat} (a : BitVec n) (imm : MoveWideConst) : BitVec n :=
  (a &&& ~~~(BitVec.ofNat n 0xFFFF <<< (16 * imm.shift))) |||
    (BitVec.ofNat n imm.bits <<< (16 * imm.shift))

/-- **Value-level meaning of the instruction forms the proven rules emit**, in terms of the
Arm model's operations (`AddWithCarry`, `write_pstate`, `ConditionHolds`): the def values
(in operand order) and the world after. `none`: form not specified (yet). A 32-bit operation
reads the low 32 bits of its operands and zero-extends its result (Arm `W` registers). -/
def ispec : Sem := fun i uses w =>
  match i, uses with
  -- flags / select / division forms (M4Cmp)
  | .aluRRImm12 .subS sz rd _ imm, [a] =>
    if imm.bits < 4096 then
      let r := Arm.AddWithCarry (opnd sz a) (~~~(BitVec.ofNat sz.bits imm.value)) 1#1
      some (defOut rd (resX sz r.1), Arm.write_pstate r.2 w, .next)
    else none
  | .aluRRImm12 .addS sz rd _ imm, [a] =>
    if imm.bits < 4096 then
      let r := Arm.AddWithCarry (opnd sz a) (BitVec.ofNat sz.bits imm.value) 0#1
      some (defOut rd (resX sz r.1), Arm.write_pstate r.2 w, .next)
    else none
  | .aluRRR .subS sz rd _ .xzr, [a] =>
    let r := Arm.AddWithCarry (opnd sz a) (~~~(0#sz.bits)) 1#1
    some (defOut rd (resX sz r.1), Arm.write_pstate r.2 w, .next)
  | .aluRRRExtend .subS sz rd _ _ e, [a, b] =>
    let r := Arm.AddWithCarry (opnd sz a)
      (~~~(Arm.extend_reg (opnd sz b) (Arm.decode_reg_extend e.bits) 0)) 1#1
    some (defOut rd (resX sz r.1), Arm.write_pstate r.2 w, .next)
  | .aluRRImmLogic .andS sz rd _ imm, [a] =>
    if ImmLogic.ofNat? imm.value sz = some imm then
      let r := opnd sz a &&& BitVec.ofNat sz.bits imm.value
      some (defOut rd (resX sz r), Arm.write_pstate (andsFlags r) w, .next)
    else none
  | .aluRRR .uDiv sz rd _ _, [a, b] => some (defOut rd (resX sz (opnd sz a / opnd sz b)), w, .next)
  | .aluRRR .sDiv sz rd _ _, [a, b] =>
    some (defOut rd (resX sz ((opnd sz a).sdiv (opnd sz b))), w, .next)
  | .csel rd _ _ c, [a, b] =>
    some (defOut rd (ofX (if Arm.ConditionHolds c.bits w then lo64 a else lo64 b)), w, .next)
  | .ccmpImm sz _ imm nzcv c, [a] =>
    if imm < 32 then
      let fl := if Arm.ConditionHolds c.bits w then
          (Arm.AddWithCarry (opnd sz a) (~~~(BitVec.ofNat sz.bits imm)) 1#1).2
        else Arm.make_pstate (BitVec.ofBool nzcv.n) (BitVec.ofBool nzcv.z) (BitVec.ofBool nzcv.c)
          (BitVec.ofBool nzcv.v)
      some ([], Arm.write_pstate fl w, .next)
    else none
  | .trapIf k _, us => some ([], w, if condBrHolds k us w then .halt else .next)
  | .udf _, [] => some ([], w, .halt)
  -- control flow (M4Ctl; as M6's `csem`): returns, branches, jump-table dispatch
  | .rets _, _ => some ([], w, .ret)
  | .jump _, [] => some ([], w, .goto 0)
  | .condBr _ _ k, us => some ([], w, .goto (if condBrHolds k us w then 0 else 1))
  | .testBitAndBranch k _ _ _ bit, [a] =>
    some ([], w, .goto (if ((lo64 a).getLsbD bit == (k == .nz)) then 0 else 1))
  | .emitIsland _, [] => some ([], w, .next)
  | .jtSequence _ ts _ _ _, [a] =>
    if Arm.ConditionHolds Cond.hs.bits w then some ([ofX 0, ofX 0], w, .goto 0)
    else if ((lo64 a).setWidth 32).toNat < ts.length then
      some ([ofX 0, ofX 0], w, .goto (((lo64 a).setWidth 32).toNat + 1))
    else none
  -- multiply-high (64-bit only), multiply-add/sub (`ra = xzr`: no third use), extract, and
  -- the shifted/extended-register forms
  | .aluRRR .sMulH .size64 rd _ _, [a, b] =>
    some (defOut rd (resX .size64 (((opnd .size64 a).signExtend 128 *
      (opnd .size64 b).signExtend 128).extractLsb' 64 64)), w, .next)
  | .aluRRR .uMulH .size64 rd _ _, [a, b] =>
    some (defOut rd (resX .size64 (((opnd .size64 a).zeroExtend 128 *
      (opnd .size64 b).zeroExtend 128).extractLsb' 64 64)), w, .next)
  | .aluRRRR op sz rd _ _ _, [a, b, c] =>
    (mulAddVal op (opnd sz a) (opnd sz b) (opnd sz c)).map fun r =>
      (defOut rd (resX sz r), w, .next)
  | .aluRRRR op sz rd (.vreg ..) (.vreg ..) .xzr, [a, b] =>
    (mulAddVal op (opnd sz a) (opnd sz b) 0).map fun r => (defOut rd (resX sz r), w, .next)
  | .aluRRRShift .extr sz rd _ _ sh, [a, b] =>
    if sh.amt < sz.bits then
      some (defOut rd (resX sz (((opnd sz a ++ opnd sz b) >>> sh.amt).setWidth sz.bits)), w, .next)
    else none
  | .aluRRRShift op sz rd _ _ sh, [a, b] =>
    if aluShiftable op = true ∧ sh.op = .lsl ∧ sh.amt < sz.bits then
      (aluVal op (opnd sz a) (opnd sz b <<< sh.amt)).map fun r =>
        (defOut rd (resX sz r), w, .next)
    else none
  | .aluRRRExtend op sz rd _ _ e, [a, b] =>
    if op = .add ∨ op = .sub then
      (aluVal op (opnd sz a) (extendVal e sz.bits b)).map fun r =>
        (defOut rd (resX sz r), w, .next)
    else none
  | .aluRRR .subS sz rd _ _, [a, b] =>
    let r := Arm.AddWithCarry (opnd sz a) (~~~(opnd sz b)) 1#1
    some (defOut rd (resX sz r.1), Arm.write_pstate r.2 w, .next)
  | .aluRRR .lsr .size32 rd _ _, [a, b] =>
    some (defOut rd (resX .size32 (opnd .size32 a >>> ((opnd .size32 b).toNat % 32))), w, .next)
  | .aluRRR op sz rd _ _, [a, b] =>
    (rrrVal op (opnd sz a) (opnd sz b)).map fun r => (defOut rd (resX sz r), w, .next)
  | .aluRRImm12 .add sz rd _ imm, [a] =>
    if imm.bits < 4096 then
      some (defOut rd (resX sz (opnd sz a + BitVec.ofNat _ imm.value)), w, .next)
    else none
  | .aluRRImm12 .sub sz rd _ imm, [a] =>
    if imm.bits < 4096 then
      some (defOut rd (resX sz (opnd sz a - BitVec.ofNat _ imm.value)), w, .next)
    else none
  | .aluRRImmShift op sz rd _ imm, [a] =>
    if imm < sz.bits then
      (shiftVal op (opnd sz a) imm).map fun r => (defOut rd (resX sz r), w, .next)
    else none
  | .bitRR .rbit sz rd _, [a] => some (defOut rd (resX sz (opnd sz a).reverse), w, .next)
  | .bitRR .clz sz rd _, [a] => some (defOut rd (resX sz (opnd sz a).clz), w, .next)
  | .bitRR .rev16 .size32 rd _, [a] => some (defOut rd (resX .size32 (rev16w (opnd .size32 a))), w, .next)
  | .bitRR .rev32 .size32 rd _, [a] =>
    some (defOut rd (resX .size32 (Clif.Sem.bswap (opnd .size32 a))), w, .next)
  | .bitRR .rev64 .size64 rd _, [a] =>
    some (defOut rd (resX .size64 (Clif.Sem.bswap (opnd .size64 a))), w, .next)
  | .extend rd _ sg 8 16, [a] =>
    let x := (lo64 a).setWidth 8
    some (defOut rd (ofX (if sg then (x.signExtend 32).setWidth 64 else x.setWidth 64)), w, .next)
  | .aluRRImmLogic op sz rd _ imm, [a] =>
    if ImmLogic.ofNat? imm.value sz = some imm ∧ op ≠ .add ∧ op ≠ .sub then
      (aluVal op (opnd sz a) (BitVec.ofNat _ imm.value)).map fun r =>
        (defOut rd (resX sz r), w, .next)
    else none
  | .extend rd _ sg fromB toB, [a] =>
    if (fromB = 8 ∨ fromB = 16 ∨ fromB = 32) ∧ (toB = 32 ∨ toB = 64) ∧ fromB < toB then
      let x := (lo64 a).setWidth fromB
      let r : BitVec 64 :=
        if sg then (x.signExtend toB).setWidth 64 else (x.setWidth toB).setWidth 64
      some (defOut rd (ofX r), w, .next)
    else none
  | .cset rd c, [] =>
    if c = .al ∨ c = .nv then none
    else some (defOut rd (ofX (if Arm.ConditionHolds c.invert.bits w then 0#64 else 1#64)), w, .next)
  | .aluRRR op sz rd .xzr _, [b] =>
    (rrrVal op (0#sz.bits) (opnd sz b)).map fun r => (defOut rd (resX sz r), w, .next)
  -- Family B (M4AluB2): wide moves (`imm`, `load_constant_full`), `orr` of an immediate into
  -- the zero register
  | .movWide op rd imm sz, [] =>
    if imm.bits < 2 ^ 16 ∧ 16 * imm.shift < sz.bits then
      some (defOut rd (resX sz (movWideVal op sz.bits imm)), w, .next)
    else none
  | .movK rd _ imm sz, [a] =>
    if imm.bits < 2 ^ 16 ∧ 16 * imm.shift < sz.bits then
      some (defOut rd (resX sz (movKVal (opnd sz a) imm)), w, .next)
    else none
  | .aluRRImmLogic op sz rd .xzr imm, [] =>
    if ImmLogic.ofNat? imm.value sz = some imm ∧ op ≠ .add ∧ op ≠ .sub then
      (aluVal op (0#sz.bits) (BitVec.ofNat _ imm.value)).map fun r =>
        (defOut rd (resX sz r), w, .next)
    else none
  -- Family B (M4AluB4): a shifted-register ALU operation with the zero register as first
  -- operand (`orn wd, wzr, wm, lsl #amt` of `bnot (ishl x k)`)
  | .aluRRRShift op sz rd .xzr _ sh, [b] =>
    if aluShiftable op = true ∧ sh.op = .lsl ∧ sh.amt < sz.bits then
      (aluVal op (0#sz.bits) (opnd sz b <<< sh.amt)).map fun r => (defOut rd (resX sz r), w, .next)
    else none
  -- Family B (M4AluB4): `ubfm`/`sbfm` (Arm `UBFM`/`SBFM`, `DecodeBitMasks` with `immr`, `imms`
  -- below the width)
  | .bitfieldMove sz op rd _ immr imms, [a] =>
    if immr < sz.bits ∧ imms < sz.bits then
      some (defOut rd (resX sz (bfmVal op (opnd sz a) immr imms)), w, .next)
    else none
  -- Family B (M4AluB4): the `popcnt` vector forms, on the 8-byte arrangement (`8B`); a 64-bit
  -- vector result zeroes the upper half of the 128-bit register
  | .movToFpu rd _ .size32, [a] => some (defOut rd (((lo64 a).setWidth 32).setWidth 128), w, .next)
  | .movToFpu rd _ .size64, [a] => some (defOut rd ((lo64 a).setWidth 128), w, .next)
  | .vecMisc .cnt rd _ .size8x8, [a] => some (defOut rd ((cntBytes (lo64 a)).setWidth 128), w, .next)
  | .vecRRR .addp rd _ _ .size8x8, [a, b] =>
    some (defOut rd ((addpBytes (lo64 a) (lo64 b)).setWidth 128), w, .next)
  | .vecLanes .addv rd _ .size8x8, [a] =>
    some (defOut rd ((addvBytes (lo64 a)).setWidth 128), w, .next)
  | .movFromVec rd _ idx .size8, [a] =>
    if idx < 16 then some (defOut rd (ofX ((a.extractLsb' (8 * idx) 8).setWidth 64)), w, .next)
    else none
  | _, _ => none

/-- **The semantic hypothesis of the rule statements**: on every form `ispec` specifies, the
VCode semantics gives the same def values and the same control (`ispec` only produces `next`,
and `halt` for the trap forms), with a world that agrees with `ispec`'s outside the
allocatable registers and the frame addresses `F` (M6's `SameWorld`). M6's `csem F ctx`
satisfies it form by form (its characterization lemmas). -/
def Refines (F : BitVec 64 → Prop) (isem : Sem) : Prop :=
  ∀ i us w outs w' {ctl : Ctl}, ispec i us w = some (outs, w', ctl) →
    ∃ w'', isem i us w = some (outs, w'', ctl) ∧ SameWorld F w'' w'

/-- `SameWorld` without NZCV: `s` and `t` agree on every unmasked field except the flags, on
memory outside `F`, and on the program. -/
def SameWorldNF (F : BitVec 64 → Prop) (s t : Arm.ArmState) : Prop :=
  (∀ f, ¬ Masked f → (∀ fl, f ≠ .FLAG fl) → Arm.r f s = Arm.r f t) ∧
    (∀ a, ¬ F a → s.mem a = t.mem a) ∧ s.program = t.program

/-- The memory relation does not depend on the allocatable registers, the pc or the flags
(which is all the non-memory instructions change). -/
def MRStable (F : BitVec 64 → Prop) (MR : MemRelT) : Prop :=
  ∀ sl cm w w', SameWorldNF F w' w → MR sl cm w → MR sl cm w'

/-- The types of the E integer types `i8..i64` (`buildCtx` rejects `i128` values). -/
def eCTys : List CTy := [.int 8, .int 16, .int 32, .int 64]

/-- The address operand of a load or store (contract change #7). -/
def memAddr? : Clif.Inst → Option Nat
  | .load _ _ _ p _ | .store _ _ _ _ p _ => some p
  | _ => none

/-! ## The lowering context -/

/-- Facts about the lowering context `buildCtx f` builds (M7 proves `buildCtx f = .ok (ctx, …)
→ CtxInv f ctx`): instruction data is `instData` of the CLIF instruction, result types are the
CLIF result types, value `x` has vreg `x`, value definitions point at instructions, stack slot
offsets are `slotLayout`'s. -/
structure CtxInv (f : Clif.Function) (ctx : Ctx) : Prop where
  func : ctx.func = f
  data : ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
    instData f inst = .ok info.data
  resTys : ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
    ∃ tys, inst.resultTypes (fun r => (f.extern? r).map (·.sig)) = some tys ∧
      info.resTys = tys.map CTy.ofClif ∧ info.results.length = tys.length
  valueReg : ∀ (x : Nat) (r : Reg), ctx.valueReg? x = some r → r = .vreg x .int
  typedReg : ∀ (x : Nat) (t : CTy), ctx.valueType? x = some t → ctx.valueReg? x = some (.vreg x .int)
  defInst : ∀ (x d : Nat), ctx.defInst? x = some d → ∃ info, ctx.insts[d]? = some info ∧ x ∈ info.results
  defClif : ∀ (x d : Nat) (info : IInfo), ctx.defInst? x = some d → ctx.insts[d]? = some info →
    info.clif.isSome = true
  slotOff : ctx.slotOff = (slotLayout f.slots).1
  /-- Result types are `i8..i64` (`buildCtx` rejects `i128` results). -/
  resTysE : ∀ (ii : Nat) (info : IInfo), ctx.insts[ii]? = some info → ∀ t ∈ info.resTys, t ∈ eCTys
  /-- Value types are `i8..i64` (`buildCtx` rejects `i128` values). -/
  valTyE : ∀ (x : Nat) (t : CTy), ctx.valueType? x = some t → t ∈ eCTys
  /-- Load/store addresses are `i64` values (`buildCtx` rejects narrower pointers; contract
  change #7): the lowering uses the whole 64-bit register as the base. -/
  addr64 : ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst) (x : Nat), ctx.insts[ii]? = some info →
    info.clif = some inst → memAddr? inst = some x → ctx.valueType? x = some (.int 64)

/-- Instructions the rules may look through (`def_inst`): their value is a function of their
operands (and the frame's slot bases). -/
def pureInst : Clif.Inst → Bool
  | .iconst .. | .unary .. | .binary .. | .icmp .. | .extend .. | .ireduce .. | .select ..
  | .stackAddr .. => true
  | _ => false

/-- The frame is typed as the context says: a defined value's CLIF type is its `valueType?`
(`buildCtx` sets `valTy` from the declared parameter/result types). Rules dispatching on
`value_type` (`extended_value_from_value`, `put_in_reg_zext32/sext32/zext64/sext64`, …) need
it. -/
def FrameTyped (ctx : Ctx) (fr : Clif.Frame) : Prop :=
  ∀ (x : Nat) (t : CTy) (v : Clif.Val), ctx.valueType? x = some t → fr.regs x = some v →
    CTy.ofClif v.ty = t

/-- DFG consistency: a defined value whose definition is a pure instruction equals that
instruction re-evaluated in the current frame (what `def_inst` look-through relies on), and
the frame is typed as the context says (`FrameTyped`). -/
def DFGCons (ctx : Ctx) (fr : Clif.Frame) : Prop :=
  (∀ (x j : Nat) (info : IInfo) (cl : Clif.Inst) (v : Clif.Val), ctx.defInst? x = some j → ctx.insts[j]? = some info → info.clif = some cl →
    pureInst cl = true → fr.regs x = some v →
    ∃ vals, (∀ cm, Clif.evalInst fr cm cl = .ok (vals, cm)) ∧ (info.results.zip vals).lookup x = some v) ∧
  FrameTyped ctx fr

/-! ## The per-instruction obligation (agreed with M7) -/

/-- The CLIF outcome of a statement's instruction: `evalInst`, and for a `call` the extern's
semantics (as `Clif.stepCall`; a call of a function of `p` is outside the theorem). -/
def instOutcome (env : Clif.Env) (p : Clif.Program) (fr : Clif.Frame) (cm : Clif.Mem) :
    Clif.Inst → Clif.Res (List Clif.Val × Clif.Mem)
  | .call fn args =>
    Clif.Res.bind (do
      let ext ← Clif.Res.ofOption s!"unknown function reference fn{fn}" (fr.func.extern? fn)
      let vals ← fr.getMany args
      Clif.checkTys s!"arguments of call to %{ext.name}" vals (Clif.AbiParam.tys ext.sig.params)
      pure (ext, vals)) fun (ext, vals) =>
    match p.func? ext.name with
    | some _ => .stuck "call of a function of the program"
    | none =>
      match env.extern ext.name with
      | some g =>
        match g vals cm with
        | .returned rvals mem' =>
          if rvals.map (·.ty) == Clif.AbiParam.tys ext.sig.returns then .ok (rvals, mem')
          else .stuck s!"extern %{ext.name} returned values of the wrong types"
        | .trapped c => .trap c
        | .stuck m => .stuck m
        | .outOfFuel => .stuck s!"extern %{ext.name} ran out of fuel"
      | none => .stuck s!"unknown callee %{ext.name}"
  | i => Clif.evalInst fr cm i

/-- Instructions whose trap the lowering makes explicit (check + trap instruction). -/
def explicitTrapInst : Clif.Inst → Bool
  | .div .. => true
  | _ => false

/-- Trap code of a trapping VCode instruction. -/
def trapCode? : MInst → Option Clif.TrapCode
  | .udf c | .trapIf _ c => some c
  | _ => none

/-- The result registers hold the results: one virtual register per result, a fresh vreg
(`≥ lo`) or a defined value's vreg. -/
def ResultsHeld (lo : Nat) (fr : Clif.Frame) (rss : List (List Reg)) (vals : List Clif.Val)
    (ρ : Nat → CV) : Prop :=
  rss.length = vals.length ∧
    ∀ (j : Nat) rs v, rss[j]? = some rs → vals[j]? = some v →
      ∃ out cls, rs = [.vreg out cls] ∧ (lo ≤ out ∨ (fr.regs out).isSome) ∧ VHolds v (ρ out)

/-- The emitted code reads only fresh vregs (`≥ st.nextVreg`) or vregs of values defined in
`fr`. Required on the runs that continue (an undefined operand makes CLIF `stuck`). -/
def UsesOk (st : LState) (fr : Clif.Frame) (ms : List MInst) : Prop :=
  ∀ m ∈ ms, ∀ u ∈ vuseNums m, st.nextVreg ≤ u ∨ (fr.regs u).isSome

/-- **`lower` on a non-terminator** (results `results`; lowering state `st` → `st'`, emitted
code `ms`). -/
structure LowerInstOk (isem : Sem) (MR : MemRelT) (env : Clif.Env) (p : Clif.Program)
    (ctx : Ctx) (inst : Clif.Inst) (results : List Nat) (st : LState) (rss : List (List Reg))
    (st' : LState) (ms : List MInst) : Prop where
  mono : st.nextVreg ≤ st'.nextVreg
  defs : ∀ m ∈ ms, ∀ d ∈ vdefs m, st.nextVreg ≤ d ∧ d < st'.nextVreg
  run : ∀ (fr : Clif.Frame) (cm : Clif.Mem) (ρ : Nat → CV) (w : Arm.ArmState),
    fr.func = ctx.func → ValsHeld fr ρ → DFGCons ctx fr → MR fr.slots cm w →
    match instOutcome env p fr cm inst with
    | .ok (vals, cm') => UsesOk st fr ms ∧ ∃ ρ' w', seqRun isem ms ρ w = some (.fall ρ' w') ∧
        (results = [] ∨ ResultsHeld st.nextVreg fr rss vals ρ') ∧ MR fr.slots cm' w'
    | .trap c => explicitTrapInst inst = true → UsesOk st fr ms ∧
        ∃ k i ops ρ₁ w₁ outs w₂, seqRun isem ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ .halt) ∧
          trapCode? i = some c
    | .stuck _ => True

/-- The successor a branch takes, as an index into the driver's target list (`jump`: its
target; `brif`: then, else; `br_table`: default, then the table). -/
def branchIdx (fr : Clif.Frame) : Clif.Terminator → Clif.Res Nat
  | .jump _ => .ok 0
  | .brif c _ _ => Clif.Res.bind (fr.get c) fun v => .ok (if Clif.Sem.truthy v.bits then 0 else 1)
  | .brTable x _ tbl => Clif.Res.bind (fr.get x) fun v =>
      .ok (if v.toNat < tbl.length then v.toNat + 1 else 0)
  | _ => .stuck "not a branch"

/-- **`lower` on `return`/`trap`, `lower_branch` on a branch** (terminator `t`). -/
structure LowerTermOk (isem : Sem) (MR : MemRelT) (ctx : Ctx) (t : Clif.Terminator)
    (targets : List Label) (st st' : LState) (ms : List MInst) : Prop where
  mono : st.nextVreg ≤ st'.nextVreg
  defs : ∀ m ∈ ms, ∀ d ∈ vdefs m, st.nextVreg ≤ d ∧ d < st'.nextVreg
  run : ∀ (fr : Clif.Frame) (cm : Clif.Mem) (ρ : Nat → CV) (w : Arm.ArmState),
    fr.func = ctx.func → ValsHeld fr ρ → DFGCons ctx fr → MR fr.slots cm w →
    match t with
    | .ret xs => ∀ vals, fr.getMany xs = .ok vals → UsesOk st fr ms ∧
        ∃ k us ops ρ₁ w₁ outs w₂,
          seqRun isem ms ρ w = some (.stop k (.rets us) ops ρ₁ w₁ outs w₂ .ret) ∧
          us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = vals.length ∧
          AllHold vals (vuses ops ρ₁) ∧ MR fr.slots cm w₂
    | .trap c => UsesOk st fr ms ∧ ∃ k i ops ρ₁ w₁ outs w₂,
        seqRun isem ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ .halt) ∧ trapCode? i = some c
    | t => (∀ i, ms.getLast? = some i → i.targets = targets) ∧ ∀ j, branchIdx fr t = .ok j →
        UsesOk st fr ms ∧ ∃ k i ops ρ₁ w₁ outs w₂,
          seqRun isem ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ (.goto j)) ∧ k + 1 = ms.length ∧
          MR fr.slots cm w₂

/-! ## Per-rule statements and the M4 target predicate -/

/-- Rule `r` is a root rule of the emitter-subset closure (`Isle.Aarch64.Closure`). -/
def closureRoot (r : Rule) : Bool := Closure.rules.any fun c => c.isRoot && c.rule == r.id

/-- The vreg of every value with a register is below the lowering state's next fresh vreg
(`buildCtx` starts `nextVreg` above every value's vreg and lowering only increases it), so
fresh temporaries never alias an operand. -/
def ValsBelow (ctx : Ctx) (st : LState) : Prop :=
  ∀ (x : Nat) (r : Reg), ctx.valueReg? x = some r → x < st.nextVreg

/-- **Root rule correctness (`lower`).** Whenever rule `r` matches instruction `ii` (from any
lowering state) and its right-hand side returns `out`, the instructions it appended are a
correct lowering of the CLIF instruction: `out` lists the result registers and
`LowerInstOk` holds. Stated for all fuels `≥ 1000` (the driver runs with fuel 10⁶; a rule
needs a bounded amount, so the lemmas never need fuel monotonicity). -/
def LowerRuleOk (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx → ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ii]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx inst info.results st rss st' ms

/-- The root rules of `lower` on `call`: `rule_lower_2508` (colocated callee, `bl`, rule id
1031) and `rule_lower_2518` (callee through the GOT, `loadExtNameGot` + `blr`, rule id 1032).
They are proven under the callee contract `CallsRefine` (`CallRulesCorrect`), not in
`LowerRulesCorrect`. (`call_indirect`, `rule_lower_2529`, is not in E.) -/
def callRootRule (r : Rule) : Bool := r.id == 1031 || r.id == 1032

/-! ### Memory (contract change #7, M4Mem)

The memory rules (`load`/`uload*`/`sload*`, `store`/`istore*`, `stack_addr`, `symbol_value`)
need more than `Refines`/`MRStable`: what the VCode semantics does on loads, stores, stack-slot
addresses and GOT loads (`MemRefines`, relative to the slot-region offset `sb` and the link-time
symbol addresses `syms`), and what the memory relation says about bytes, allocations, slots and
stores (`MemRelOk`; M7's `Rel.holds` satisfies it, `E2E.memRelOk_holds`). They are proven under
these (`MemRulesCorrect`), not in `LowerRulesCorrect`. -/

/-- The effective address of an addressing mode for an access of `bytes` bytes, from the use
values of its register operands (operand order) and the world (`sp`); `sb` is the offset of the
stack-slot region from `sp` (M6: `FnCtx.slotBase`, M7: `Rel.slotOff`). Only the forms the
lowering emits (int vreg operands, `simm9` / scaled `uimm12` immediates as the ISLE rules check
them, 32-bit index extensions); `none` otherwise. As M6's `AMode.addr`. -/
def amodeAddr (sb : Nat) (am : AMode) (bytes : Nat) (uses : List CV) (w : Arm.ArmState) :
    Option (BitVec 64) :=
  match am, uses with
  | .regReg (.vreg _ .int) (.vreg _ .int), [a, b] => some (lo64 a + lo64 b)
  | .regScaled (.vreg _ .int) (.vreg _ .int), [a, b] => some (lo64 a + (lo64 b <<< log2 bytes))
  | .regScaledExtended (.vreg _ .int) (.vreg _ .int) e, [a, b] =>
    if e = .uxtw ∨ e = .sxtw then some (lo64 a + (extendVal e 64 b <<< log2 bytes)) else none
  | .regExtended (.vreg _ .int) (.vreg _ .int) e, [a, b] =>
    if e = .uxtw ∨ e = .sxtw then some (lo64 a + extendVal e 64 b) else none
  | .unscaled (.vreg _ .int) off, [a] =>
    if -256 ≤ off ∧ off ≤ 255 then some (lo64 a + BitVec.ofInt 64 off) else none
  | .unsignedOffset (.vreg _ .int) off, [a] =>
    if off % bytes = 0 ∧ off ≤ 4095 * bytes then some (lo64 a + BitVec.ofNat 64 off) else none
  | .slotOffset off, [] => some (spOf w + BitVec.ofInt 64 (off + sb))
  | _, _ => none

/-- Sign-extending loads (`ldrsb`/`ldrsh`/`ldrsw` into an X register). -/
def loadSigned : LoadOp → Bool
  | .sload8 | .sload16 | .sload32 => true
  | _ => false

/-- The 64-bit register value a load `op` from `a` leaves: the `op.bytes` bytes at `a`
(little-endian), sign- or zero-extended. -/
def loadVal (op : LoadOp) (a : BitVec 64) (w : Arm.ArmState) : BitVec 64 :=
  if loadSigned op then (Arm.read_mem_bytes op.bytes a w).signExtend 64
  else (Arm.read_mem_bytes op.bytes a w).setWidth 64

/-- **What the memory rules need of the VCode semantics** (M6 discharges it for `csem F ctx X`
with `ctx.slotBase = sb` and `X.sym n 0` the address `b` of `n` when `syms n = some b`): a
load or store through an addressing mode whose access avoids the frame addresses `F`
reads/writes the Arm memory at `amodeAddr`, a `loadAddr` of a slot offset is `sp + off + sb`, a
GOT load of a linked symbol is its address (with `CallsRefine`: its `sym` at the linked
symbols); the world otherwise as for the other forms (`SameWorld F`). -/
def MemRefines (F : BitVec 64 → Prop) (sb : Nat) (syms : String → Option Nat) (isem : Sem) :
    Prop :=
  (∀ (op : LoadOp) (d : Nat) (am : AMode) (fl : Clif.MemFlags) (uses : List CV)
      (w : Arm.ArmState) (a : BitVec 64),
    op ≠ .fpuLoad128 → amodeAddr sb am op.bytes uses w = some a → Avoids F op.bytes a →
    ∃ w', isem (.load op (.vreg d .int) am fl) uses w = some ([ofX (loadVal op a w)], w', .next) ∧
      SameWorld F w' w) ∧
  (∀ (op : StoreOp) (d : Nat) (am : AMode) (fl : Clif.MemFlags) (v : CV) (uses : List CV)
      (w : Arm.ArmState) (a : BitVec 64),
    op ≠ .fpuStore128 → amodeAddr sb am op.bytes uses w = some a → Avoids F op.bytes a →
    ∃ w', isem (.store op (.vreg d .int) am fl) (v :: uses) w = some ([], w', .next) ∧
      SameWorld F w' (Arm.write_mem_bytes op.bytes a ((lo64 v).setWidth (op.bytes * 8)) w)) ∧
  (∀ (d : Nat) (off : Int) (w : Arm.ArmState), ∃ w',
    isem (.loadAddr (.vreg d .int) (.slotOffset off)) [] w =
      some ([ofX (spOf w + BitVec.ofInt 64 (off + sb))], w', .next) ∧ SameWorld F w' w) ∧
  (∀ (d : Nat) (n : String) (b : Nat) (w : Arm.ArmState), syms n = some b → ∃ w',
    isem (.loadExtNameGot (.vreg d .int) n) [] w = some ([ofX (BitVec.ofNat 64 b)], w', .next) ∧
      SameWorld F w' w)

/-- **What the memory rules need of the memory relation** of function `f` (M7's `Rel.holds`
satisfies it): initialised bytes of live allocations are the Arm bytes, live allocations are
64-bit addresses outside `F`, `symbol_value` addresses are `syms`, slot `id` is at
`sp + sb + off(id)`, and a store to a live allocation on both sides keeps the relation. -/
structure MemRelOk (F : BitVec 64 → Prop) (sb : Nat) (syms : String → Option Nat)
    (f : Clif.Function) (MR : MemRelT) : Prop where
  bytes : ∀ sl cm w (a : Nat) b, MR sl cm w → cm.valid a 1 = true → cm.bytes a = some b →
    Arm.read_mem (BitVec.ofNat 64 a) w = b
  valid : ∀ sl cm w (a n : Nat), MR sl cm w → cm.valid a n = true →
    a + n ≤ 2 ^ 64 ∧ ∀ k < n, ¬ F (BitVec.ofNat 64 (a + k))
  symbols : ∀ sl cm w, MR sl cm w → cm.symbols = syms
  slots : ∀ sl cm w id b, MR sl cm w → sl.lookup id = some b →
    ∃ off, (slotLayout f.slots).1.lookup id = some off ∧ b = (spOf w).toNat + sb + off
  store : ∀ sl cm w (a n : Nat) (y : BitVec (n * 8)), MR sl cm w → cm.valid a n = true →
    MR sl (cm.writeBits false a n y) (Arm.write_mem_bytes n (BitVec.ofNat 64 a) y w)

/-- The memory root rules of `lower`: `symbol_value` (rule id 1027), the loads (1041–1044
`load`, 1052–1057 `uload*`/`sload*`), the stores (1064–1067 `store`, 1068–1070 `istore*`),
`stack_addr` (1093), and `uextend`/`sextend` of a load (815, 824: never match, the backend does
not sink loads). -/
def memRootRule (r : Rule) : Bool :=
  r.id == 1027 || r.id == 1093 || r.id == 815 || r.id == 824 || (1041 ≤ r.id && r.id ≤ 1044) ||
    (1052 ≤ r.id && r.id ≤ 1057) || (1064 ≤ r.id && r.id ≤ 1070)

/-- `LowerRuleOk` for a memory rule: additionally assumes `MemRelOk F sb syms f MR`. -/
def MemRuleOk (F : BitVec 64 → Prop) (sb : Nat) (syms : String → Option Nat) (isem : Sem)
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx → MemRelOk F sb syms f MR →
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ii]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx inst info.results st rss st' ms

/-- **M4's target for the memory rules**: under `MemRefines`, every memory root rule is correct
for every function whose memory relation is `MemRelOk`. -/
def MemRulesCorrect (p : Program) : Prop :=
  ∀ (F : BitVec 64 → Prop) (sb : Nat) (syms : String → Option Nat) (isem : Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program),
    Refines F isem → MRStable F MR → MemRefines F sb syms isem →
    ∀ r ∈ p.rulesOf TId.lower, memRootRule r = true → MemRuleOk F sb syms isem MR env cp p r

/-- **M4's target (`lower`).** For every VCode semantics refining `ispec` and every stable
memory relation, every root rule of `lower` in the E-closure other than the call rules
(`callRootRule`, see `CallRulesCorrect`) and the memory rules (`memRootRule`, see
`MemRulesCorrect`) is correct. This is the M4 hypothesis of M7's theorem (with `data_program`:
`lowerInstOk_runTerm`). -/
def LowerRulesCorrect (p : Program) : Prop :=
  ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program),
    Refines F isem → MRStable F MR →
    ∀ r ∈ p.rulesOf TId.lower, closureRoot r = true → callRootRule r = false →
      memRootRule r = false → LowerRuleOk isem MR env cp p r

/-! ### Calls (contract change #5) -/

/-- **The callee contract at the VCode level** (M6 discharges it for `csem` from `CalleeSound`
and `ExtSem.sym`): there is a link-time address `sym n` for every symbol such that
`loadExtNameGot rd n` loads it (changing nothing else the memory relation sees), and a call of
the extern `name` (`bl name`, or `blr` of a register holding `sym name`, whose value is then the
first use) with at most 8 argument values in x0.. (`AllHold`: low bits) returns the extern's
results in x0.. (the defs, in order) and a world related to the extern's memory. -/
def CallsRefine (F : BitVec 64 → Prop) (env : Clif.Env) (MR : MemRelT) (isem : Sem) : Prop :=
  ∃ sym : String → BitVec 64,
    (∀ (rd : Reg) (n : String) (w : Arm.ArmState), ∃ w',
      isem (.loadExtNameGot rd n) [] w = some ([ofX (sym n)], w', .next) ∧ SameWorldNF F w' w) ∧
    ∀ (name : String) g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem) (w : Arm.ArmState)
      (dest : CallDest) (us ds : List (Reg × Reg)) (uses args : List CV)
      (vals rvals : List Clif.Val) (cm' : Clif.Mem),
      env.extern name = some g →
      (dest = .sym name ∧ uses = args ∨ ∃ r, dest = .reg r ∧ uses = ofX (sym name) :: args) →
      us.map (·.2) = (List.range us.length).map Reg.x →
      ds.map (·.1) = (List.range ds.length).map Reg.x →
      vals.length ≤ 8 → AllHold vals args → MR sl cm w →
      g vals cm = .returned rvals cm' → ds.length = rvals.length →
      ∃ outs w', isem (.call ⟨dest, us, ds⟩) uses w = some (outs, w', .next) ∧
        AllHold rvals outs ∧ MR sl cm' w'

/-- Every extern of `f` takes at most 8 parameters (all in registers; `E2E.InSubset.callRegArgs`):
calls with stack-passed arguments are outside the theorem. -/
def CallRegArgs (f : Clif.Function) : Prop :=
  ∀ (fn : Clif.FnRef) (e : Clif.ExtFunc), f.extern? fn = some e → e.sig.params.length ≤ 8

/-- `LowerRuleOk` for a call rule: additionally assumes `CallRegArgs f`. -/
def CallRuleOk (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx → CallRegArgs f →
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ii]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx inst info.results st rss st' ms

/-- **M4's target for the call rules**: under the callee contract, the call root rules are
correct. -/
def CallRulesCorrect (p : Program) : Prop :=
  ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program),
    Refines F isem → MRStable F MR → CallsRefine F env MR isem →
    ∀ r ∈ p.rulesOf TId.lower, callRootRule r = true → CallRuleOk isem MR env cp p r

/-- The root rules of `lower` outside the closure (their patterns name a non-E opcode, a
non-`i8..i64` type or a vector/float type test) never match an instruction of a context
`buildCtx` builds. -/
def ExcludedUnmatchable (p : Program) : Prop :=
  ∀ r ∈ p.rulesOf TId.lower, closureRoot r = false →
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx → ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
  ∀ (cfg : Config) (m : Nat) (s : LState × Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId),
    (matchRule p (sem ctx) cfg m r [.inst ii]).run s ≠ .ok (some env', s1)

/-- The index of a `br_table` has at most 32 bits (contract change #6): the lowering compares and
dispatches on the low 32 bits, and Cranelift's verifier requires an `i32` index. M7's `lowerCheck`
decides it for every terminator (`brIdxOk`). -/
def BrIdxTyped (ctx : Ctx) (t : Clif.Terminator) : Prop :=
  ∀ x d tbl, t = .brTable x d tbl → ∃ w, w ≤ 32 ∧ ctx.valueType? x = some (.int w)

/-- The driver's successor labels of a `br_table` are one per jump-table entry plus the default
(contract change #8): the lowering dispatches on the length of the label list
(`jump_table_size`), CLIF on the table's. M7 discharges it from `targetsOf` (`dests`). -/
def TargetsLen (t : Clif.Terminator) (targets : List Label) : Prop :=
  ∀ x d tbl, t = .brTable x d tbl → targets.length = tbl.length + 1

/-- **Root rule correctness (`lower_branch`)**, on the terminator `t` lowered in the driver's
context `ctx` (instruction `ti` holds the terminator's data; `CtxInv`, `ValsBelow` and "the
rules before `r` failed" as for `LowerRuleOk`), with branch targets `targets`. -/
def BranchRuleOk (isem : Sem) (MR : MemRelT) (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx →
  ∀ (ti : Nat) (t : Clif.Terminator) (data : V) (targets : List Label), termData t = .ok data →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ → BrIdxTyped ctx t → TargetsLen t targets →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (∀ pre post, p.rulesOf TId.lower_branch = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti, .labels targets]).run (st, tr) =
        .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ti, .labels targets]).run (st, tr) =
      .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧ LowerTermOk isem MR ctx t targets st st' ms

/-- M4's target for `lower_branch` (not proven yet; stated for M7). -/
def BranchRulesCorrect (p : Program) : Prop :=
  ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT),
    Refines F isem → MRStable F MR →
    ∀ r ∈ p.rulesOf TId.lower_branch, closureRoot r = true → BranchRuleOk isem MR p r

/-! ## From the rules to every `lower` call -/

set_option maxRecDepth 100000 in
/-- The rules of `lower` are pairwise distinct (so "the rules before `r`" is well defined). -/
theorem lower_rules_nodup {p : Program} (hp : Data p) : (p.rulesOf TId.lower).Nodup := by
  rw [show TId.lower = 686 from rfl, hp.r686]
  refine List.Pairwise.of_map (S := fun a b : Nat => a ≠ b) Rule.id
    (fun _ _ h e => h (congrArg Rule.id e)) ?_
  decide +kernel

theorem lowerInstOk_of_rules {p : Program} (hp : Data p) (hrules : LowerRulesCorrect p)
    (hex : ExcludedUnmatchable p) (hcalls : CallRulesCorrect p) (hmem : MemRulesCorrect p)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) (hcr : CallsRefine F env MR isem) (hMem : MemRefines F sb syms isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) (hra : CallRegArgs f)
    (hMRo : MemRelOk F sb syms f MR) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (p.rulesOf TId.lower).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId} (hvb : ValsBelow ctx st)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty TId.lower [.inst ii]).run (st, tr) =
      .ok (some out, (st', tr'))) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx inst info.results st rss st' ms := by
  change 1002 + (p.rulesOf 686).length ≤ n at hn
  obtain ⟨r, pre0, post0, hsplit, hpre0, m, env', s1, st2, tr2, hmn, hmatch, heval, hs⟩ :=
    applyTerm_internal_some_first hco hp.t686 term_686_kind rfl h
  have hr : r ∈ p.rulesOf TId.lower := by
    change r ∈ p.rulesOf 686; rw [hsplit]; simp
  have hfirst : ∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s') := by
    intro pre post hsp r' hr'
    have hnd : (pre0 ++ r :: post0).Nodup := hsplit ▸ lower_rules_nodup hp
    have hpre := prefix_unique_of_nodup hnd (hsplit.symm.trans hsp)
    subst hpre
    obtain ⟨m', hm', s', h'⟩ := hpre0 r' hr'
    exact ⟨m', by omega, s', h'⟩
  simp only [Prod.mk.injEq] at hs
  rw [← hs.1] at heval
  cases hroot : closureRoot r
  · exact absurd hmatch (hex r hr hroot f ctx hctx ii info inst hi hc cfg m (st, tr) env' s1)
  · cases hcall : callRootRule r
    · cases hm : memRootRule r
      · exact hrules F isem MR env cp hR hMR r hr hroot hcall hm f ctx hctx ii info inst hi hc cfg
          hco m n st tr env' s1 out st' tr2 (by omega) (by omega) hvb hfirst hmatch heval
      · exact hmem F sb syms isem MR env cp hR hMR hMem r hr hm f ctx hctx hMRo ii info inst hi hc
          cfg hco m n st tr env' s1 out st' tr2 (by omega) (by omega) hvb hfirst hmatch heval
    · exact hcalls F isem MR env cp hR hMR hcr r hr hcall f ctx hctx hra ii info inst hi hc cfg hco
        m n st tr env' s1 out st' tr2 (by omega) (by omega) hvb hfirst hmatch heval

set_option maxRecDepth 20000 in
/-- `lowerInstOk_of_rules` for the exported program and the backend's own call
(`runTerm ctx "lower" [.inst ii]`, as `lowerFunction` makes it). -/
theorem lowerInstOk_runTerm (hrules : LowerRulesCorrect program)
    (hex : ExcludedUnmatchable program) (hcalls : CallRulesCorrect program)
    (hmem : MemRulesCorrect program)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR)
    (hcr : CallsRefine F env MR isem) (hMem : MemRefines F sb syms isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) (hra : CallRegArgs f)
    (hMRo : MemRelOk F sb syms f MR) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {st : LState} {out : V} {st' : LState} {tr : List RuleId} (hvb : ValsBelow ctx st)
    (h : runTerm ctx "lower" [.inst ii] st = .ok (some out, st', tr)) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx inst info.results st rss st' ms := by
  unfold runTerm Interp.run at h
  rw [program_termByName_lower] at h
  dsimp only at h
  cases ha : (applyTerm program (sem ctx) {} 1000000 T.lower.ret T.lower.id [.inst ii]).run
      (st, #[]) with
  | error e => rw [ha] at h; cases h
  | ok q =>
    obtain ⟨v, st2, tr2⟩ := q
    rw [ha] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    injection h with h
    injection h with h1 h2
    subst h1
    injection h2 with h2 _
    subst h2
    have hlen : (program.rulesOf TId.lower).length ≤ 1000 := by
      rw [show TId.lower = 686 from rfl, data_program.r686]; decide
    obtain ⟨ms, rss, h1, h2, h3⟩ := lowerInstOk_of_rules data_program hrules hex hcalls hmem hR
      hMR hcr hMem hctx hra hMRo hi hc rfl (by omega) hvb ha
    exact ⟨ms, rss, by simpa using h1, h2, h3⟩

/-! ## Terminators (stated by M7; M4's obligations `LowerTermRulesCorrect`, `TermUnmatchable`,
`BranchRulesCorrect`, `BranchExcludedUnmatchable`)

`lowerFunction` lowers `return`/`trap` with `lower` and the branches with `lower_branch`, in
its terminator context: instruction `ti` holds the terminator's data (`termData`), no results,
no CLIF instruction. `lowerTermOk_runTerm` / `branchOk_runTerm` turn the per-rule statements
into `LowerTermOk` for every successful call, as `lowerInstOk_runTerm` does for statements. -/

/-- The root rules of `lower` on terminators: `rule_lower_2237` (`trap`, rule id 964) and
`rule_lower_2574` (`return`, rule id 1037). -/
def termRootRule (r : Rule) : Bool := r.id == 964 || r.id == 1037

/-- Terminators lowered by `lower` (the others by `lower_branch`). -/
def retOrTrap : Clif.Terminator → Bool
  | .ret _ | .trap _ => true
  | _ => false

/-- **Root rule correctness (`lower`, terminators)**: whenever rule `r` matches the
`return`/`trap` terminator at `ti` (the rules before it having failed) and its right-hand side
returns, the instructions it appended are a correct lowering of the terminator. -/
def LowerTermRuleOk (isem : Sem) (MR : MemRelT) (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx →
  ∀ (ti : Nat) (t : Clif.Terminator) (data : V), retOrTrap t = true → termData t = .ok data →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti]).run (st, tr) = .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ti]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧ LowerTermOk isem MR ctx t [] st st' ms

/-- **M4's target (`lower` on terminators)**: the two terminator root rules are correct. -/
def LowerTermRulesCorrect (p : Program) : Prop :=
  ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT), Refines F isem → MRStable F MR →
    ∀ r ∈ p.rulesOf TId.lower, termRootRule r = true → LowerTermRuleOk isem MR p r

/-- The other rules of `lower` never match a `return`/`trap` terminator. -/
def TermUnmatchable (p : Program) : Prop :=
  ∀ r ∈ p.rulesOf TId.lower, termRootRule r = false →
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx →
  ∀ (ti : Nat) (t : Clif.Terminator) (data : V), retOrTrap t = true → termData t = .ok data →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ →
  ∀ (cfg : Config) (m : Nat) (s : LState × Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId),
    (matchRule p (sem ctx) cfg m r [.inst ti]).run s ≠ .ok (some env', s1)

/-- The root rules of `lower_branch` outside the closure never match a branch terminator. -/
def BranchExcludedUnmatchable (p : Program) : Prop :=
  ∀ r ∈ p.rulesOf TId.lower_branch, closureRoot r = false →
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx →
  ∀ (ti : Nat) (t : Clif.Terminator) (data : V) (targets : List Label), retOrTrap t = false →
  termData t = .ok data → ctx.insts[ti]? = some ⟨data, [], [], none⟩ →
  ∀ (cfg : Config) (m : Nat) (s : LState × Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId),
    (matchRule p (sem ctx) cfg m r [.inst ti, .labels targets]).run s ≠ .ok (some env', s1)

set_option maxRecDepth 100000 in
theorem lower_branch_rules_nodup {p : Program} (hp : Data p) :
    (p.rulesOf TId.lower_branch).Nodup := by
  rw [show TId.lower_branch = 687 from rfl, hp.r687]
  refine List.Pairwise.of_map (S := fun a b : Nat => a ≠ b) Rule.id
    (fun _ _ h e => h (congrArg Rule.id e)) ?_
  decide +kernel

theorem lowerTermOk_of_rules {p : Program} (hp : Data p) (hrules : LowerTermRulesCorrect p)
    (hun : TermUnmatchable p) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    (hR : Refines F isem) (hMR : MRStable F MR) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) {ti : Nat} {t : Clif.Terminator} {data : V} (hrt : retOrTrap t = true)
    (hd : termData t = .ok data) (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩)
    {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (p.rulesOf TId.lower).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId} (hvb : ValsBelow ctx st)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty TId.lower [.inst ti]).run (st, tr) =
      .ok (some out, (st', tr'))) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧ LowerTermOk isem MR ctx t [] st st' ms := by
  change 1002 + (p.rulesOf 686).length ≤ n at hn
  obtain ⟨r, pre0, post0, hsplit, hpre0, m, env', s1, st2, tr2, hmn, hmatch, heval, hs⟩ :=
    applyTerm_internal_some_first hco hp.t686 term_686_kind rfl h
  have hr : r ∈ p.rulesOf TId.lower := by
    change r ∈ p.rulesOf 686; rw [hsplit]; simp
  have hfirst : ∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti]).run (st, tr) = .ok (none, s') := by
    intro pre post hsp r' hr'
    have hnd : (pre0 ++ r :: post0).Nodup := hsplit ▸ lower_rules_nodup hp
    have hpre := prefix_unique_of_nodup hnd (hsplit.symm.trans hsp)
    subst hpre
    obtain ⟨m', hm', s', h'⟩ := hpre0 r' hr'
    exact ⟨m', by omega, s', h'⟩
  simp only [Prod.mk.injEq] at hs
  rw [← hs.1] at heval
  cases hroot : termRootRule r
  · exact absurd hmatch (hun r hr hroot f ctx hctx ti t data hrt hd hi cfg m (st, tr) env' s1)
  · exact hrules F isem MR hR hMR r hr hroot f ctx hctx ti t data hrt hd hi cfg hco m n st tr
      env' s1 out st' tr2 (by omega) (by omega) hvb hfirst hmatch heval

theorem branchOk_of_rules {p : Program} (hp : Data p) (hrules : BranchRulesCorrect p)
    (hex : BranchExcludedUnmatchable p) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    (hR : Refines F isem) (hMR : MRStable F MR) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) {ti : Nat} {t : Clif.Terminator} {data : V} {targets : List Label}
    (hrt : retOrTrap t = false) (hd : termData t = .ok data)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (hbt : BrIdxTyped ctx t)
    (htl : TargetsLen t targets) {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (p.rulesOf TId.lower_branch).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId} (hvb : ValsBelow ctx st)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty TId.lower_branch [.inst ti, .labels targets]).run
      (st, tr) = .ok (some out, (st', tr'))) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧ LowerTermOk isem MR ctx t targets st st' ms := by
  change 1002 + (p.rulesOf 687).length ≤ n at hn
  obtain ⟨r, pre0, post0, hsplit, hpre0, m, env', s1, st2, tr2, hmn, hmatch, heval, hs⟩ :=
    applyTerm_internal_some_first hco hp.t687 term_687_kind rfl h
  have hr : r ∈ p.rulesOf TId.lower_branch := by
    change r ∈ p.rulesOf 687; rw [hsplit]; simp
  have hfirst : ∀ pre post, p.rulesOf TId.lower_branch = pre ++ r :: post → ∀ r' ∈ pre,
      ∃ m', 1000 ≤ m' ∧ ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti, .labels targets]).run
        (st, tr) = .ok (none, s') := by
    intro pre post hsp r' hr'
    have hnd : (pre0 ++ r :: post0).Nodup := hsplit ▸ lower_branch_rules_nodup hp
    have hpre := prefix_unique_of_nodup hnd (hsplit.symm.trans hsp)
    subst hpre
    obtain ⟨m', hm', s', h'⟩ := hpre0 r' hr'
    exact ⟨m', by omega, s', h'⟩
  simp only [Prod.mk.injEq] at hs
  rw [← hs.1] at heval
  cases hroot : closureRoot r
  · exact absurd hmatch (hex r hr hroot f ctx hctx ti t data targets hrt hd hi cfg m (st, tr) env' s1)
  · exact hrules F isem MR hR hMR r hr hroot f ctx hctx ti t data targets hd hi hbt htl cfg hco m n st
      tr env' s1 out st' tr2 (by omega) (by omega) hvb hfirst hmatch heval

theorem program_termByName_lower_branch :
    program.termByName? "lower_branch" = some T.lower_branch := by
  decide +kernel

set_option maxRecDepth 20000 in
/-- `lowerTermOk_of_rules` for the exported program and the backend's call
(`runTerm ctx "lower" [.inst ti]` on a `return`/`trap`). -/
theorem lowerTermOk_runTerm (hrules : LowerTermRulesCorrect program)
    (hun : TermUnmatchable program) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    (hR : Refines F isem) (hMR : MRStable F MR) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) {ti : Nat} {t : Clif.Terminator} {data : V} (hrt : retOrTrap t = true)
    (hd : termData t = .ok data) (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩)
    {st : LState} {out : V} {st' : LState} {tr : List RuleId} (hvb : ValsBelow ctx st)
    (h : runTerm ctx "lower" [.inst ti] st = .ok (some out, st', tr)) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧ LowerTermOk isem MR ctx t [] st st' ms := by
  unfold runTerm Interp.run at h
  rw [program_termByName_lower] at h
  dsimp only at h
  cases ha : (applyTerm program (sem ctx) {} 1000000 T.lower.ret T.lower.id [.inst ti]).run
      (st, #[]) with
  | error e => rw [ha] at h; cases h
  | ok q =>
    obtain ⟨v, st2, tr2⟩ := q
    rw [ha] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    injection h with h
    injection h with h1 h2
    subst h1
    injection h2 with h2 _
    subst h2
    have hlen : (program.rulesOf TId.lower).length ≤ 1000 := by
      rw [show TId.lower = 686 from rfl, data_program.r686]; decide
    obtain ⟨ms, h1, h2⟩ := lowerTermOk_of_rules data_program hrules hun hR hMR hctx hrt hd hi
      rfl (by omega) hvb ha
    exact ⟨ms, by simpa using h1, h2⟩

set_option maxRecDepth 20000 in
/-- `branchOk_of_rules` for the exported program and the backend's call
(`runTerm ctx "lower_branch" [.inst ti, .labels targets]`). -/
theorem branchOk_runTerm (hrules : BranchRulesCorrect program)
    (hex : BranchExcludedUnmatchable program) {F : BitVec 64 → Prop} {isem : Sem}
    {MR : MemRelT} (hR : Refines F isem) (hMR : MRStable F MR) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) {ti : Nat} {t : Clif.Terminator} {data : V} {targets : List Label}
    (hrt : retOrTrap t = false) (hd : termData t = .ok data)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (hbt : BrIdxTyped ctx t)
    (htl : TargetsLen t targets) {st : LState} {out : V} {st' : LState} {tr : List RuleId} (hvb : ValsBelow ctx st)
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] st = .ok (some out, st', tr)) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧ LowerTermOk isem MR ctx t targets st st' ms := by
  unfold runTerm Interp.run at h
  rw [program_termByName_lower_branch] at h
  dsimp only at h
  cases ha : (applyTerm program (sem ctx) {} 1000000 T.lower_branch.ret T.lower_branch.id
      [.inst ti, .labels targets]).run (st, #[]) with
  | error e => rw [ha] at h; cases h
  | ok q =>
    obtain ⟨v, st2, tr2⟩ := q
    rw [ha] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    injection h with h
    injection h with h1 h2
    subst h1
    injection h2 with h2 _
    subst h2
    have hlen : (program.rulesOf TId.lower_branch).length ≤ 1000 := by
      rw [show TId.lower_branch = 687 from rfl, data_program.r687]; decide
    obtain ⟨ms, h1, h2⟩ := branchOk_of_rules data_program hrules hex hR hMR hctx hrt hd hi hbt htl
      rfl (by omega) hvb ha
    exact ⟨ms, by simpa using h1, h2⟩

end Backend.Proof
