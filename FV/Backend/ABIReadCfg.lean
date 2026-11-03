import FV.Backend.ABIReadDiv

namespace Backend.ABIReadCfg
set_option autoImplicit false

/-- Branches read their virtual condition or the NZCV flags, with no additional
ABI/world read. Bit-test branches and jump tables read only their virtual index
(and, for the table's bounds check, the flags); islands read nothing. -/
def additional : MInst → Bool
  | .jump _
  | .condBr _ _ (.zero (.vreg _ .int) _)
  | .condBr _ _ (.notZero (.vreg _ .int) _)
  | .condBr _ _ (.cond _) => true
  | .testBitAndBranch _ _ _ (.vreg _ .int) _ => true
  | .emitIsland _ => true
  | .jtSequence _ _ (.vreg _ .int) (.vreg _ .int) (.vreg _ .int) => true
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
