import FV.Backend.ABIReadFlags

namespace Backend.ABIReadScalar
set_option autoImplicit false

/-- Actual virtual-register MOVK used by multi-word constant materialization.
The dead-code cleanup whitelist and existing ABI checkers retain their behavior. -/
def constant : MInst → Bool
  | .movK (.vreg _ .int) (.vreg _ .int) _ _ => true
  | _ => false

/-- Shift and bitfield producers frame ABI reads without changing cleanup rules. -/
def shiftOp : ALUOp → Bool
  | .lsl | .lsr | .asr => true
  | _ => false

def shift : MInst → Bool
  | .aluRRR op .. | .aluRRImmShift op .. => shiftOp op
  | .bitfieldMove .. => true
  | _ => false

/-- The six integer extension forms supported by the machine specification. -/
def extension : MInst → Bool
  | .extend _ _ _ fromB toB =>
      [(8,16),(8,32),(8,64),(16,32),(16,64),(32,64)].contains (fromB,toB)
  | _ => false

/-- Additional bit/rotate producers; earlier scalar selectors remain fixed. -/
def bitProducer : MInst → Bool
  | .bitRR .. | .aluRRR .extr .. | .aluRRImmShift .extr .. => true
  | _ => false

def instruction (sig : Clif.Signature) (b k : Nat) (i : MInst) : Bool :=
  ABIReadFlags.instruction sig b k i || constant i || shift i || extension i || bitProducer i

def check (sig : Clif.Signature) (vc : VCode) : Bool :=
  vc.blocks.toList.zipIdx.all fun (block,b) =>
    block.insts.toList.zipIdx.all fun (i,k) => instruction sig b k i

end Backend.ABIReadScalar
