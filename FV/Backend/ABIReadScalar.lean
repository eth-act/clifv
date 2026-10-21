import FV.Backend.ABIReadFlags

namespace Backend.ABIReadScalar
set_option autoImplicit false

/-- Actual virtual-register MOVK used by multi-word constant materialization.
The dead-code cleanup whitelist and existing ABI checkers retain their behavior. -/
def constant : MInst → Bool
  | .movK (.vreg _ .int) (.vreg _ .int) _ _ => true
  | _ => false

def instruction (sig : Clif.Signature) (b k : Nat) (i : MInst) : Bool :=
  ABIReadFlags.instruction sig b k i || constant i

def check (sig : Clif.Signature) (vc : VCode) : Bool :=
  vc.blocks.toList.zipIdx.all fun (block,b) =>
    block.insts.toList.zipIdx.all fun (i,k) => instruction sig b k i

end Backend.ABIReadScalar
