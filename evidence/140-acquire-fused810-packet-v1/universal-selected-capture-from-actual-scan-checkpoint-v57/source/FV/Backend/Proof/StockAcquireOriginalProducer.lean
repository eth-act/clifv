import FV.Backend.Proof.StockAcquireRootSourceValue
import FV.Backend.Proof.StockAcquireRulePendingSource

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Actual matching connects the original extension operand to its actual atomic producer. -/
theorem acquire_rule_original_extension_source {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {st matched next : State} {before matchedTrace after : Array RuleId}
    {bound : Isle.Interp.Env V} {m n ii value : Nat} {rootInfo : IInfo} {target : Clif.Ty} {out : V}
    (rootInstalled : ctx.insts[ii]? = some rootInfo)
    (rootSource : rootInfo.clif = some (.extend .uextend target value))
    (matchedRun : (matchRule program (Stock.sem ctx) {} (m+5) rule_lower_1272 [.inst ii]).run
      (st,before) = .ok (some bound,matched,matchedTrace))
    (evaluatedRun : (evalExpr program (Stock.sem ctx) {} (n+20) rule_lower_1272.rhs bound).run
      (matched,matchedTrace) = .ok (some out,next,after)) :
    ∃ (producer : Nat) (info : IInfo) (ty : Clif.Ty) (flags : Clif.MemFlags) (pointer : Nat),
      ctx.defInst? value = some producer ∧ ctx.insts[producer]? = some info ∧
      info.clif = some (.atomicLoad ty flags pointer) ∧ eTy ty = true ∧
      flags.endianness ≠ some .big := by
  obtain ⟨actualValue,producer,sunk,info,ty,flags,pointer,defined,once,arity,positive,color,
    sink,state,installed,original,integer,little,binding,sameState,sameTrace⟩ :=
    acquire_rule_pending_source mapped matchedRun evaluatedRun
  obtain ⟨actualProducer,originalSource,_,_,originalBinding⟩ :=
    acquire_root_match_original_value mapped rootInstalled rootSource matchedRun
  have same : actualProducer = producer :=
    V.inst.inj (Option.some.inj (Option.some.inj (originalBinding.symm.trans binding)))
  subst actualProducer
  have originalDefined := (source_effect_eligible originalSource positive).1
  exact ⟨producer,info,ty,flags,pointer,originalDefined,installed,original,integer,little⟩

end Backend.Stock.Proof.Acquire810
