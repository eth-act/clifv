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
  | .bitRR .. | .aluRRR .extr .. | .aluRRImmShift .extr .. | .aluRRRShift .extr .. => true
  | _ => false

/-- The exact vector producers used by scalar popcount. -/
def popcountProducer : MInst → Bool
  | .movToFpu _ _ .size32 | .movToFpu _ _ .size64
  | .movFromVec _ _ 0 .size8 | .vecMisc .cnt _ _ .size8x8
  | .vecLanes .addv _ _ .size8x8 | .vecRRR .addp _ _ _ .size8x8 => true
  | _ => false

/-- Actual two-register and immediate comparisons used by min/max and later scalar classes. -/
def comparisonProducer : MInst → Bool
  | .aluRRR .subS _ .xzr (.vreg _ .int) (.vreg _ .int) => true
  | .aluRRImm12 .subS _ .xzr (.vreg _ .int) _ => true
  | _ => false

/-- The exact virtual result consumer of scalar comparison booleans. -/
def booleanProducer : MInst → Bool
  | .cset (.vreg _ .int) _ => true
  | _ => false

/-- Exact virtual-register high products; earlier ABI selectors remain fixed. -/
def highmulProducer : MInst → Bool
  | .aluRRR .sMulH .size64 (.vreg _ .int) (.vreg _ .int) (.vreg _ .int)
  | .aluRRR .uMulH .size64 (.vreg _ .int) (.vreg _ .int) (.vreg _ .int) => true
  | _ => false

/-- Flag-only extended comparisons and masked tests used by narrow operands.
The zero destination preserves every physical argument register. -/
def extendedComparisonProducer : MInst → Bool
  | .aluRRRExtend .subS _ .xzr (.vreg _ .int) (.vreg _ .int) _
  | .aluRRImmLogic .andS _ .xzr (.vreg _ .int) _ => true
  | _ => false

/-- The actual virtual-register CSETM consumer of scalar bmask. -/
def maskProducer : MInst → Bool
  | .csetm (.vreg _ .int) _ => true
  | _ => false

def instruction (sig : Clif.Signature) (b k : Nat) (i : MInst) : Bool :=
  ABIReadFlags.instruction sig b k i || constant i || shift i || extension i || bitProducer i || popcountProducer i || comparisonProducer i || booleanProducer i || highmulProducer i || extendedComparisonProducer i || maskProducer i

def check (sig : Clif.Signature) (vc : VCode) : Bool :=
  vc.blocks.toList.zipIdx.all fun (block,b) =>
    block.insts.toList.zipIdx.all fun (i,k) => instruction sig b k i

end Backend.ABIReadScalar
