import FV.Backend.Lowering.Stock
import FV.Backend.Proof.IselExtern
import FV.Backend.Proof.PrepareCheck
import FV.Backend.Proof.RegallocInstsFP

namespace Backend.Stock.Proof.LinearCfg
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The actual RPO and successor rows of a three-block source chain. Source
bodies, jump arguments and value identities remain unrestricted. -/
theorem block_order_three {f : Clif.Function} {entry middle target : Clif.Block}
    {first second : Clif.BlockCall} {xs : List Nat}
    (blocks : f.blocks = [entry,middle,target])
    (firstJump : entry.term = .jump first) (secondJump : middle.term = .jump second)
    (ret : target.term = .ret xs)
    (firstDestination : first.block = middle.id) (secondDestination : second.block = target.id)
    (entryMiddle : entry.id ≠ middle.id) (entryTarget : entry.id ≠ target.id)
    (middleTarget : middle.id ≠ target.id) :
    blockOrder f = .ok ⟨#[.original 0,.original 1,.original 2],#[#[1],#[2],#[]]⟩ := by
  have traversal : rpo #[#[1],#[2],#[]] = #[0,1,2] := by decide +kernel
  simp [blockOrder,blocks,firstJump,secondJump,ret,firstDestination,secondDestination,
    entryMiddle,Ne.symm entryMiddle,entryTarget,Ne.symm entryTarget,
    middleTarget,Ne.symm middleTarget,destinations,List.findIdx?_cons,traversal]
  rfl

end Backend.Stock.Proof.LinearCfg
