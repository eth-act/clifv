import FV.Link.RelocShapeProof
import FV.Link.DeadCleanupImage
namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend Backend.Proof LinkSpec

theorem relocShapes_of_pipeCleanupT {g : Clif.Function} {k : Nat} {base : BitVec 64} {o : Lean.Json}
    {a : Art} (ha : pipeCleanupT g k base o = .ok a) : relocShapesB a = true := by
  obtain ⟨-, -, -, -, he, hl, -, -⟩ := pipeCleanupT_spec ha
  exact relocShapesB_of_seqOk hl (seqOk_codeLines (emitFunc_seqOk he))


end Link.DeadCleanup
