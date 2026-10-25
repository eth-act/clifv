import FV.Backend.ABIReadDiv

namespace Backend.ABIReadCfg
set_option autoImplicit false

/-- Existing scalar/division/ABI reads plus unconditional CFG jumps. -/
def instruction (sig : Clif.Signature) (b k : Nat) (i : MInst) : Bool :=
  ABIReadDiv.instruction sig b k i || match i with | .jump _ => true | _ => false

/-- A successful computed CFG excludes re-entry into the argument-read site. -/
def noEntryEdges (vc : VCode) : Bool :=
  match vc.cfg with
  | .ok (successors,_) => successors.all fun row => !row.contains 0
  | .error _ => false

def check (sig : Clif.Signature) (vc : VCode) : Bool :=
  (vc.blocks.toList.zipIdx.all fun (block,b) =>
    block.insts.toList.zipIdx.all fun (i,k) => instruction sig b k i) && noEntryEdges vc

end Backend.ABIReadCfg
