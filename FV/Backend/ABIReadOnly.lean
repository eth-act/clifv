module

public import FV.Backend.DeadCleanup

@[expose] public section

namespace Backend.ABIReadOnly
set_option autoImplicit false

/-- A declared register read, tied to an actual signature parameter. -/
def registerRead (sig : Clif.Signature) (pin : Reg) : Bool :=
  ((locsOf sig).zip sig.params).any fun row =>
    match row.1 with | .reg r => r == pin | .stack _ => false

/-- A load reads only bytes of one declared stack parameter, at the ordinary
body-entry FP offset. This check does not depend on argument values. -/
def stackRead (sig : Clif.Signature) (off : Int) (bytes : Nat) : Bool :=
  ((locsOf sig).zip sig.params).any fun row =>
    match row.1 with
    | .stack slot => off == 16 + (slot : Int) && decide (bytes ≤ row.2.ty.bytes)
    | .reg _ => false

/-- Pure producers that do not read the flags (`pureNoFlags`: a `cset`'s value depends on the
entry flags), entry argument copies, declared stack-argument loads and return. Entry copies
may occur only at block zero/PC zero. -/
def instruction (sig : Clif.Signature) (block pc : Nat) (i : MInst) : Bool :=
  if DeadCleanup.pureNoFlags i then true
  else match i with
  | .args pairs => block == 0 && pc == 0 && pairs.all (fun p => registerRead sig p.2)
  | .load op (.vreg _ .int) (.fpOffset off) _ =>
      op != .fpuLoad128 && stackRead sig off op.bytes
  | .rets _ => true
  | _ => false

def check (sig : Clif.Signature) (vc : VCode) : Bool :=
  vc.blocks.toList.zipIdx.all fun (block,b) =>
    block.insts.toList.zipIdx.all fun (i,k) => instruction sig b k i

end Backend.ABIReadOnly
