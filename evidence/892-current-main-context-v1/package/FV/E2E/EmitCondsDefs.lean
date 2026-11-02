import FV.E2E.EmitSize
import FV.Backend.EmitOk

/-! # The decidable emission conditions on the prepared VCode (V6b, `emitCondsB`)

The executable definitions of the conditions under which the spill allocation's code is ready
(`E2E.emitReady_spill`, `FV/E2E/EmitTotal.lean`), kept apart from their proofs
(`FV/E2E/EmitEnc.lean`, `EmitNear.lean`, `EmitLabels.lean`) so that a crate's proof file can decide
them by `native_decide` (the input conditions `E2E.LinkCheck.InScopeP`, `FV/E2E/LinkScopeDefs.lean`):
the size bound `spillSizeOkB` (`FV/E2E/EmitSize.lean`), the immediates `immsOkB`, no `al`/`nv`
branch `VCode.noAlwaysB`, the branch targets `branchTargetsOkB`. -/

namespace Backend

/-- No `condBr`/`trapIf` of the VCode has an `al`/`nv` condition. -/
def VCode.noAlwaysB (vc : VCode) : Bool :=
  vc.blocks.toList.all fun vb => vb.insts.toList.all MInst.noAlways

end Backend

namespace E2E

open Backend

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
