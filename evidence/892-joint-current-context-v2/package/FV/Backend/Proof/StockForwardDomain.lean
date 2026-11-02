import FV.Backend.Proof.StockForwardEntry
import FV.Backend.Proof.StockForwardCompatibility
import FV.Backend.Proof.StockScalarContract

namespace Backend.Stock.Scalar
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Arbitrary ranked scalar jump/return/trap graphs satisfy the unchanged production
consumer domain, including ABI entry, inherited values and first traps. -/
theorem domain_of_forward_leaf_cfg {f : Clif.Function} {rank : Nat → Nat}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false)
    (ranked : ForwardSource.Ranked f rank) (terms : ForwardSource.JumpLeafBlocks f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {entry : Clif.Block} {bc : Clif.BlockCall} (source : f.blocks[0]? = some entry)
    (jump : entry.term = .jump bc) : Domain f := by
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable w memory arguments
    obtain ⟨ρ,simulation⟩ := ForwardSource.scalar_return_frame_of_leaf run scope dominated abi ranked terms family source jump
      entered returned refines driver memorySem stable memory arguments
    exact ⟨ρ,simulation.legacyCompatible (ForwardSource.legacy_compatible_of_leaf run scope terms)⟩
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable w memory arguments
    obtain ⟨ρ,simulation⟩ := ForwardSource.scalar_trap_frame_of_leaf run scope dominated abi ranked terms family source jump
      entered trapped refines driver memorySem stable memory arguments
    exact ⟨ρ,simulation.legacyCompatible (ForwardSource.legacy_compatible_of_leaf run scope terms)⟩

/-- Arbitrary ranked scalar jump/return graphs satisfy the unchanged production
consumer domain, including ABI entry, inherited values and first traps. -/
theorem domain_of_forward_cfg {f : Clif.Function} {rank : Nat → Nat}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false)
    (ranked : ForwardSource.Ranked f rank) (terms : ForwardSource.JumpReturnBlocks f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {entry : Clif.Block} {bc : Clif.BlockCall} (source : f.blocks[0]? = some entry)
    (jump : entry.term = .jump bc) : Domain f :=
  domain_of_forward_leaf_cfg scope dominated abi ordinary ranked terms.toLeaf family source jump

end Backend.Stock.Scalar
