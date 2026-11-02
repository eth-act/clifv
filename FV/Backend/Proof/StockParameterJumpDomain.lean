import FV.Backend.Proof.StockParameterEntry
import FV.Backend.Proof.StockParameterCompatibility
import FV.Backend.Proof.StockScalarContract

namespace Backend.Stock.Proof.ParameterCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues Backend.Stock.Proof.ForwardSource
set_option autoImplicit false
set_option Elab.async false

theorem domain_of_parameter_jump_cfg {f : Clif.Function} {rank : Nat → Nat}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false)
    (ranked : Ranked f rank) (terms : ParameterTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {entry : Clif.Block} {bc : Clif.BlockCall} (source : f.blocks[0]? = some entry)
    (jump : entry.term = .jump bc) : Scalar.Domain f := by
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable w memory arguments
    obtain ⟨ρ,simulation⟩ := parameter_jump_return_frame run scope dominated abi ranked
      (parameter_terms_nonentry terms) family source jump entered returned refines driver memorySem stable memory arguments
    exact ⟨ρ,simulation.legacyCompatible
      (parameter_legacy_compatible terms run scope dominated family refines driver stable env cp)⟩
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable w memory arguments
    obtain ⟨ρ,simulation⟩ := parameter_jump_trap_frame run scope dominated abi ranked
      (parameter_terms_nonentry terms) family source jump entered trapped refines driver memorySem stable memory arguments
    exact ⟨ρ,simulation.legacyCompatible
      (parameter_legacy_compatible terms run scope dominated family refines driver stable env cp)⟩



theorem domain_of_parameter_jump_leaf_cfg {f : Clif.Function} {rank : Nat → Nat}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false)
    (ranked : Ranked f rank) (terms : ParameterLeafTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {entry : Clif.Block} {bc : Clif.BlockCall} (source : f.blocks[0]? = some entry)
    (jump : entry.term = .jump bc) : Scalar.Domain f := by
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable w memory arguments
    obtain ⟨ρ,simulation⟩ := parameter_jump_return_frame_of_leaf run scope dominated abi ranked
      (parameter_leaf_terms_nonentry terms) family source jump entered returned refines driver memorySem stable memory arguments
    exact ⟨ρ,simulation.legacyCompatible
      (parameter_legacy_compatible_of_leaf terms run scope dominated family refines driver stable env cp)⟩
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable w memory arguments
    obtain ⟨ρ,simulation⟩ := parameter_jump_trap_frame_of_leaf run scope dominated abi ranked
      (parameter_leaf_terms_nonentry terms) family source jump entered trapped refines driver memorySem stable memory arguments
    exact ⟨ρ,simulation.legacyCompatible
      (parameter_legacy_compatible_of_leaf terms run scope dominated family refines driver stable env cp)⟩

end Backend.Stock.Proof.ParameterCfg
