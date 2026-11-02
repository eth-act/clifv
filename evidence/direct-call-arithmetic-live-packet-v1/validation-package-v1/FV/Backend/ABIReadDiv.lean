import FV.Backend.ABIReadScalar

namespace Backend.ABIReadDiv
set_option autoImplicit false

/-- Actual quotient, zero and signed-overflow guard forms, and the unconditional `udf` of a
`trap` terminator. Existing scalar selectors retain their original meaning. No divisor values
are inspected. -/
def additional : MInst → Bool
  | .aluRRR .sDiv _ (.vreg _ .int) (.vreg _ .int) (.vreg _ .int)
  | .aluRRR .uDiv _ (.vreg _ .int) (.vreg _ .int) (.vreg _ .int)
  | .aluRRImm12 .addS _ .xzr (.vreg _ .int) ⟨1,false⟩
  | .ccmpImm _ (.vreg _ .int) 1 ⟨false,false,false,false⟩ .eq
  | .trapIf (.zero (.vreg _ .int) _) .intDivz
  | .trapIf (.cond .vs) .intOvf
  | .udf _ => true
  | _ => false

def instruction (sig : Clif.Signature) (b k : Nat) (i : MInst) : Bool :=
  ABIReadScalar.instruction sig b k i || additional i

def check (sig : Clif.Signature) (vc : VCode) : Bool :=
  vc.blocks.toList.zipIdx.all fun (block,b) =>
    block.insts.toList.zipIdx.all fun (i,k) => instruction sig b k i

end Backend.ABIReadDiv
