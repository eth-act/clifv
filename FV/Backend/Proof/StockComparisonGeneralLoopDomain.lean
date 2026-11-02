import FV.Backend.Proof.StockComparisonGeneralLoopCompatibility
import FV.Backend.Proof.StockComparisonComputedArgsLoopDomain

/-! The legacy loop class with all six comparison forms satisfies the unchanged production domain
(#140, CB-10).

The class is the class of `domainAt_of_computed_args_loop_cfg` (CB-9) with empty `brif`
arguments (`GeneralTerms.args`), so its returns and first traps hold over the actual
per-successor vectors (`Scalar.DomainAt`). Its actual code keeps exact per-edge/single-vector
agreement (`general_loop_legacy_compatible`), so `RunOkABIAt.legacyCompatible` and
`EdgeLegacyCompatible.star` transport them to the legacy observations of the unsplit code
(`Scalar.Domain`). -/

namespace Backend.Stock.Proof.ComparisonGeneralLoopCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- **The legacy six-form loop class satisfies the unchanged production domain.** Every block
jumps (with any arguments), returns, branches with empty arguments on a wide parameter or on a
comparison (`ComputedArgsCondition`: two parameters, or two computed values, of one wide type; a
wide parameter or a computed wide value with an encodable 12-bit constant, nonzero for `eq`/`ne`;
or `eq`/`ne` of a wide parameter or a computed wide value with zero, where the computed value is
not a `band` result for `eq`), or, outside the entry, ends in `trap`. No rank: jump and branch
targets may be loop headers. -/
theorem domain_of_general_loop_cfg {f : Clif.Function}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false)
    (terms : GeneralTerms f)
    (entryKind : ∀ b,f.blocks[0]? = some b → ∀ c,b.term ≠ .trap c)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst) : Scalar.Domain f := by
  have domainAt := ComparisonComputedArgsLoopCfg.domainAt_of_computed_args_loop_cfg scope dominated abi ordinary
    terms.args entryKind family
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable world memory arguments
    have compatible := general_loop_legacy_compatible terms run scope dominated family refines driver stable env cp
    obtain ⟨ρ,simulation⟩ := domainAt.returns run entered returned refines driver memorySem stable memory arguments
    exact ⟨ρ,simulation.legacyCompatible compatible⟩
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable world memory arguments
    have compatible := general_loop_legacy_compatible terms run scope dominated family refines driver stable env cp
    obtain ⟨ρ,b,k,ρ',w,vb,i,ops,outs,w',path,tail⟩ :=
      domainAt.traps run entered trapped refines driver memorySem stable memory arguments
    exact ⟨ρ,b,k,ρ',w,vb,i,ops,outs,w',compatible.star path,tail⟩

end Backend.Stock.Proof.ComparisonGeneralLoopCfg
