module

public import FV.Backend.ABIReadDiv

public section

namespace Backend.ABIReadCfg
set_option autoImplicit false

/-- Branches read their virtual condition, with no additional ABI/world read. -/
def additional : MInst → Bool
  | .jump _
  | .condBr _ _ (.zero (.vreg _ .int) _)
  | .condBr _ _ (.notZero (.vreg _ .int) _) => true
  | _ => false

/-- Existing scalar/division/ABI reads and proved CFG branch forms. -/
def instruction (sig : Clif.Signature) (b k : Nat) (i : MInst) : Bool :=
  ABIReadDiv.instruction sig b k i || additional i

/-- A successful computed CFG excludes re-entry into the argument-read site. -/
def noEntryEdges (vc : VCode) : Bool :=
  match vc.cfg with
  | .ok (successors,_) => successors.all fun row => !row.contains 0
  | .error _ => false

def check (sig : Clif.Signature) (vc : VCode) : Bool :=
  (vc.blocks.toList.zipIdx.all fun (block,b) =>
    block.insts.toList.zipIdx.all fun (i,k) => instruction sig b k i) && noEntryEdges vc

end Backend.ABIReadCfg
