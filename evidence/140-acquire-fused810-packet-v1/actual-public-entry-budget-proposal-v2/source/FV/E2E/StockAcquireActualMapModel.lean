import FV.E2E.StockAcquireMapRelRWWithResults
import FV.E2E.BinaryBoundaryDefs

namespace E2E.StockAcquirePending
open Backend Backend.Proof Backend.Proof.Driver E2E.SemanticBinary
set_option autoImplicit false
set_option Elab.async false

/-- The model image update leaves every original nonwritable-byte condition unchanged. -/
theorem actual_mapRelRW_modelOf {I : SemanticStackBound.CompilerInput} {f : Clif.Function}
    {mp : ArmFault.MemMap} {N : Nat} {r : Arm.ArmState} {args : List Clif.Val} {cm : Clif.Mem}
    (mapped : MapRelRWWithResults mp I.results f N r args cm) :
    MapRelRWWithResults mp I.results f N (modelOf I f r) args cm := by
  refine ⟨⟨?_,?_,mapped.nw.valid⟩,mapped.code⟩
  · simpa only [spv_modelOf] using mapped.nw.stack
  · simpa only [spv_modelOf] using mapped.nw.args

end E2E.StockAcquirePending
