module

public import FV.Backend.ABIReadOnly

@[expose] public section

namespace Backend.ABIReadFlags
set_option autoImplicit false

def extra : MInst → Bool
  | .aluRRR .subS _ .xzr (.vreg _ .int) .xzr => true
  | .csel (.vreg _ .int) (.vreg _ .int) (.vreg _ .int) _ => true
  | _ => false

def instruction (sig : Clif.Signature) (b k : Nat) (i : MInst) : Bool :=
  Backend.ABIReadOnly.instruction sig b k i || extra i

def check (sig : Clif.Signature) (vc : VCode) : Bool :=
  vc.blocks.toList.zipIdx.all fun (block,b) =>
    block.insts.toList.zipIdx.all fun (i,k) => instruction sig b k i


end Backend.ABIReadFlags
