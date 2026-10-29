module

public import FV.Backend.Proof.StockLinearCfgReturn
public import FV.Backend.Proof.StockLinearCfgTrap
public import FV.Backend.Proof.StockLinearCfgCompatibility
public import FV.Backend.Proof.StockScalarContract

@[expose] public section

namespace Backend.Stock.Scalar
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Three-block scalar CFGs satisfy the existing universal consumer domain,
including first traps and values inherited across empty-argument jumps. -/
theorem domain_of_linear_cfg {f : Clif.Function}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false)
    {entry middle target : Clif.Block} {first second : Clif.BlockCall} {xs : List Nat}
    (blocks : f.blocks = [entry,middle,target])
    (firstJump : entry.term = .jump first) (secondJump : middle.term = .jump second)
    (ret : target.term = .ret xs)
    (firstDestination : first.block = middle.id) (secondDestination : second.block = target.id)
    (entryMiddle : entry.id ≠ middle.id) (entryTarget : entry.id ≠ target.id)
    (middleTarget : middle.id ≠ target.id)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst) : Domain f := by
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable w memory arguments
    obtain ⟨ρ,source⟩ := LinearCfg.scalar_return_frame run scope dominated abi blocks firstJump secondJump ret firstDestination
      secondDestination entryMiddle entryTarget middleTarget family entered returned refines driver memorySem stable memory arguments
    exact ⟨ρ,source.legacyCompatible (LinearCfg.legacy_compatible run scope blocks firstJump secondJump ret firstDestination
      secondDestination entryMiddle entryTarget middleTarget)⟩
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable w memory arguments
    obtain ⟨ρ,source⟩ := LinearCfg.scalar_trap_frame run scope dominated abi blocks firstJump secondJump ret firstDestination
      secondDestination entryMiddle entryTarget middleTarget family entered trapped refines driver memorySem stable memory arguments
    exact ⟨ρ,source.legacyCompatible (LinearCfg.legacy_compatible run scope blocks firstJump secondJump ret firstDestination
      secondDestination entryMiddle entryTarget middleTarget)⟩

end Backend.Stock.Scalar
