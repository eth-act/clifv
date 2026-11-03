import FV.Backend.Proof.StockAcquireOriginalValueType

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program

/-- The actual eligibility if-let preserves the original source type and memory flags. -/
theorem acquire_root_match_argument_fields {ctx : Ctx} {st matched : State}
    {tr tr' : Array RuleId} {bound : Isle.Interp.Env V} {n root value producer pointer : Nat}
    {rootInfo info : IInfo} {targetTy sourceTy : CTy} {flags : Clif.MemFlags}
    (little : flags.endianness ≠ some .big)
    (rootInstalled : ctx.insts[root]? = some rootInfo)
    (rootData : rootInfo.data = .data 152 29 [.data 151 141 [],.value value])
    (rootType : rootInfo.resTys.head?.getD .invalid = targetTy) (fits : targetTy.bits ≤ 64)
    (valueType : ctx.valueType? value = some sourceTy) (defined : ctx.defInst? value = some producer)
    (installed : ctx.insts[producer]? = some info)
    (atomic : info.data = .data 152 17 [.data 151 158 [],.value pointer,.op (.memFlags flags)])
    (run : (matchRule program (Stock.sem ctx) {} (n+5) rule_lower_1272 [.inst root]).run
      (st,tr) = .ok (some bound,matched,tr')) :
    bound[1]? = some (some (V.ty sourceTy)) ∧ bound[2]? = some (some (.op (.memFlags flags))) := by
  obtain ⟨env,args,iflets⟩ := matchRule_some_inv (m := n+4) run
  have fields := acquire_root_argument_fields little rootInstalled rootData rootType fits valueType defined installed atomic args
  have held := acquire_root_args_value rootInstalled rootData args
  have actual : (matchIfLets program (Stock.sem ctx) {} (n+4)
      [⟨.bind 18 4 (.wildcard 18),.term 18 221 [.var 15 3]⟩] env).run (st,tr) =
        .ok (some bound,matched,tr') := by
    simpa only [rule_lower_1272] using iflets
  obtain ⟨i,called,same,trace,environment⟩ := stock_sink_iflet_environment held actual
  rw [environment]
  simpa only [Array.getElem?_setIfInBounds_ne (by decide : 1 ≠ 4),
    Array.getElem?_setIfInBounds_ne (by decide : 2 ≠ 4)] using fields

end Backend.Stock.Proof.Acquire810
