import FV.E2E.CallStorePhysicalImage
import FV.Arm.Tactics.Sym
import FV.Arm.Tactics.StepThms
import FV.E2E.Statement

namespace E2E.CallStorePhysicalExec
open Arm _root_.BitVec Arm.BitVec
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def literalWords : List (BitVec 64 × BitVec 32) :=
  [(0x200160#64,0xa9bf7bfd#32),
   (0x200164#64,0x910003fd#32),
   (0x200168#64,0xf81f0ff3#32),
   (0x20016c#64,0xaa0003f3#32),
   (0x200170#64,0xaa0103e0#32),
   (0x200174#64,0x94000006#32),
   (0x200178#64,0xf9000660#32),
   (0x20017c#64,0xf84107f3#32),
   (0x200180#64,0xa8c17bfd#32),
   (0x200184#64,0xd65f03c0#32),
   (0x20018c#64,0xa9bf7bfd#32),
   (0x200190#64,0x910003fd#32),
   (0x200194#64,0x91003400#32),
   (0x200198#64,0xa8c17bfd#32),
   (0x20019c#64,0xd65f03c0#32)]
def literalProgram : Arm.Program := def_program literalWords
#genStepEqTheorems literalProgram

/-- The actual linked bytes in both modes give this exact instruction stream. -/
-- witness: native_decide (fixed compiler, original allocation answers, linker, and byte decoding only)
theorem linked_words_exact (cleanup : Bool) : linkedWords cleanup = literalWords := by
  cases cleanup <;> native_decide


end E2E.CallStorePhysicalExec
