import FV.E2E.EmitSize

/-! # The decidable emission conditions on the prepared VCode (V6b, `emitCondsB`)

The executable definitions of the conditions under which the spill allocation's code is ready
(`E2E.emitReady_spill`, `FV/E2E/EmitTotal.lean`), kept apart from their proofs
(`FV/E2E/EmitEnc.lean`, `EmitNear.lean`, `EmitLabels.lean`) so that a crate's proof file can decide
them by `native_decide` (the input conditions `E2E.LinkCheck.InScopeP`, `FV/E2E/LinkScopeDefs.lean`):
the size bound `spillSizeOkB` (`FV/E2E/EmitSize.lean`), the immediates `immsOkB`, no `al`/`nv`
branch `VCode.noAlwaysB`, the branch targets `branchTargetsOkB`. -/

namespace Backend

def MInst.noAlways : MInst → Bool
  | .condBr _ _ (.cond c) => !(c == .al || c == .nv)
  | .trapIf (.cond c) _ => !(c == .al || c == .nv)
  | _ => true

/-- No `condBr`/`trapIf` of the VCode has an `al`/`nv` condition. -/
def VCode.noAlwaysB (vc : VCode) : Bool :=
  vc.blocks.toList.all fun vb => vb.insts.toList.all MInst.noAlways

end Backend

namespace E2E

open Backend

/-- **The immediates of a VCode instruction are in the encodable range** (the operand values the
instruction selection chooses; registers are not checked, except that an indirect call's target is
an int vreg). Exactly the conditions `Insn.armFields` imposes on the non-register operands of the
lines `MInst.lines` expands the instruction to (the forms `FormOk` already restricts — logical
immediates, addressing modes, atomic access sizes — are not repeated). -/
def immOkB : MInst → Bool
  | .aluRRImm12 op _ _ _ i => op.addSub?.isSome && decide (i.bits < 4096)
  | .aluRRImmShift _ s _ _ amt => decide (amt < (if s.is64 then 64 else 32))
  | .aluRRRShift op s _ _ _ sh =>
    decide (sh.amt < (if s.is64 then 64 else 32)) &&
      (op == .extr || (op.addSub?.isSome && sh.op != .ror) || op.logic?.isSome)
  | .aluRRRExtend op .. => op.addSub?.isSome
  | .movWide _ _ i s | .movK _ _ i s =>
    decide (i.bits < 2 ^ 16) && decide (i.shift < (if s.is64 then 4 else 2))
  | .extend _ _ sg a b =>
    (!sg && a == 1) || (!sg && a == 32 && b == 64) || decide (a - 1 < (if sg && b > 32 then 64 else 32))
  | .bitfieldMove s _ _ _ immr imms =>
    decide (immr < (if s.is64 then 64 else 32)) && decide (imms < (if s.is64 then 64 else 32))
  | .cset _ c | .csetm _ c => c != .al && c != .nv
  | .ccmpImm _ _ i _ _ => decide (i < 32)
  | .movToFpu _ _ s => s == .size16 || s == .size32 || s == .size64
  | .movFromVec _ _ idx s => match s with
    | .size8 => decide (idx * 2 + 1 < 32) | .size16 => decide (idx * 4 + 2 < 32)
    | .size32 => decide (idx * 8 + 4 < 32) | .size64 => decide (idx * 16 + 8 < 32)
    | _ => false
  | .vecMisc _ _ _ s => s == .size8x8 || s == .size8x16
  | .vecLanes _ _ _ s => s != .size32x2 && s != .size64x2
  | .testBitAndBranch _ _ _ _ bit => decide (bit < 64)
  | .atomicRmwLoop ty .. | .atomicCasLoop ty .. =>
    ty.bits == 8 || ty.bits == 16 || ty.bits == 32 || ty.bits == 64
  | .call info | .tryCall info _ => match info.dest with
    | .sym _ => true
    | .reg r => r.isVregInt
  | _ => true

/-- `immOkB` on every instruction of every block. -/
def immsOkB (vc : VCode) : Bool := vc.blocks.all fun vb => vb.insts.all immOkB

/-- Every branch target of every instruction of `vc` is the label of one of its blocks
(`VCode.cfg` checks this for the blocks' last instructions only). -/
def branchTargetsOkB (vc : VCode) : Bool :=
  vc.blocks.all fun vb => vb.insts.all fun i => i.targets.all fun l => vc.blocks.any (·.label == l)

/-- The decidable conditions on the prepared VCode under which the spill allocation's code is
ready (`emitReady_spill`). -/
def emitCondsB (vcp : VCode) : Bool :=
  spillSizeOkB vcp && immsOkB vcp && vcp.noAlwaysB && branchTargetsOkB vcp

end E2E
