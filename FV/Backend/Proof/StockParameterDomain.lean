module

public import FV.Backend.Proof.StockParameterJumpDomain
public import FV.Backend.Proof.StockParameterConditionalDomain
public import FV.Backend.Proof.StockParameterReturnEntry

@[expose] public section

namespace Backend.Stock.Proof.ParameterCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues Backend.Stock.Proof.ForwardSource
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

theorem domain_of_parameter_return_cfg {f : Clif.Function}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false)
    (terms : ParameterTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {entry : Clif.Block} {xs : List Nat} (source : f.blocks[0]? = some entry)
    (ret : entry.term = .ret xs) : Scalar.Domain f := by
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable w memory arguments
    obtain ⟨ρ,simulation⟩ := parameter_return_entry_frame run scope dominated abi family source ret entered returned refines driver memorySem stable memory arguments
    exact ⟨ρ,simulation.legacyCompatible
      (parameter_legacy_compatible terms run scope dominated family refines driver stable env cp)⟩
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable w memory arguments
    obtain ⟨ρ,simulation⟩ := parameter_return_entry_trap_frame run scope dominated abi family source ret entered trapped refines driver memorySem stable memory arguments
    exact ⟨ρ,simulation.legacyCompatible
      (parameter_legacy_compatible terms run scope dominated family refines driver stable env cp)⟩

/-- The source-ranked quiet parameter-conditional class satisfies the unchanged domain. -/
theorem domain_of_parameter_cfg {f : Clif.Function} {rank : Nat → Nat}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false)
    (ranked : Ranked f rank) (terms : ParameterTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst) : Scalar.Domain f := by
  have entry : ∃ (b : Clif.Block),f.blocks[0]? = some b := by
    cases blocks : f.blocks with
    | nil => exact False.elim (scope.nonempty blocks)
    | cons b rest => exact ⟨b,by simp only [blocks,List.getElem?_cons_zero]⟩
  obtain ⟨b,source⟩ := entry
  rcases terms 0 b source with ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,yesEmpty,noEmpty,parameter⟩
  · exact domain_of_parameter_jump_cfg scope dominated abi ordinary ranked terms family source jump
  · exact domain_of_parameter_return_cfg scope dominated abi ordinary terms family source ret
  · exact domain_of_parameter_conditional_cfg scope dominated abi ordinary ranked terms family source term yesEmpty noEmpty parameter

end Backend.Stock.Proof.ParameterCfg
