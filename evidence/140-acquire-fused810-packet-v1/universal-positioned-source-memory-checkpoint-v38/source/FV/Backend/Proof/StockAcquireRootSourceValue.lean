import FV.Backend.Proof.StockAcquireMatchSource
import FV.Backend.Proof.StockPatternBindings
import FV.Backend.Proof.StockDFG

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program

/-- Actual unary source data fixes the matched source value before helper evaluation. -/
theorem acquire_root_args_value {ctx : Ctx} {st : State} {env : Isle.Interp.Env V}
    {ii value : Nat} {info : IInfo}
    (installed : ctx.insts[ii]? = some info)
    (shape : info.data = .data 152 29 [.data 151 141 [],.value value])
    (args : matchArgs program (Stock.sem ctx) st rule_lower_1272.args [.inst ii]
      (Array.replicate rule_lower_1272.vars.length none) = .ok (some env)) :
    env[3]? = some (some (.value value)) := by
  obtain ⟨env1,head,empty⟩ := matchArgs_cons_inv args
  simp only [matchArgs,pure,Except.pure] at empty
  cases empty
  obtain ⟨values,extracted,fields⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl head
  change Backend.externExtract ctx T.inst_data_value (.inst ii) st.base = .ok values at extracted
  change (match ctx.insts[ii]? with
    | some info => ExtResult.ok [V.ty (info.resTys.head?.getD .invalid),info.data]
    | none => ExtResult.unmodeled s!"inst {ii}") = ExtResult.ok values at extracted
  rw [installed] at extracted
  cases extracted
  obtain ⟨envFit,fit,remaining⟩ := matchArgs_cons_inv fields
  obtain ⟨envData,dataPat,empty⟩ := matchArgs_cons_inv remaining
  simp only [matchArgs,pure,Except.pure] at empty
  cases empty
  obtain ⟨items,decoded,arguments⟩ := matchPat_enum_inv data_program.t2476 term_2476_kind dataPat
  change (Backend.sem ctx).unData 152 info.data = some (29,items) at decoded
  rw [shape] at decoded
  change some (29,[V.data 151 141 [],V.value value]) = some (29,items) at decoded
  cases decoded
  obtain ⟨envOpcode,opcode,tail⟩ := matchArgs_cons_inv arguments
  obtain ⟨envOperand,operand,empty⟩ := matchArgs_cons_inv tail
  simp only [matchArgs,pure,Except.pure] at empty
  cases empty
  obtain ⟨inside,inner⟩ := matchPat_bind_inv operand
  have kept := stock_pattern_keeps (k := 3) (by decide) inner
  exact kept.trans (Array.getElem?_setIfInBounds_self_of_lt inside)

private theorem data_fields_unData (ctx : Ctx) (name : String) (fields : List V)
    {tag : Nat} {actual : List V}
    (decoded : (Backend.sem ctx).unData 152 (instDataV name fields) = some (tag,actual)) :
    actual = fields := by
  unfold instDataV mkVariant at decoded
  cases found : variantIdx tyInstData name with
  | none => rw [found] at decoded; cases decoded
  | some k =>
    rw [found] at decoded
    change some (k,fields) = some (tag,actual) at decoded
    exact (Prod.mk.inj (Option.some.inj decoded)).2.symm

/-- Generic field inversion avoids reducing the complete generated program. -/
theorem acquire_root_args_value_data {ctx : Ctx} {st : State} {env : Isle.Interp.Env V}
    {ii value : Nat} {info : IInfo}
    (installed : ctx.insts[ii]? = some info)
    (shape : info.data = instDataV "Unary" [opcodeV "Uextend",.value value])
    (args : matchArgs program (Stock.sem ctx) st rule_lower_1272.args [.inst ii]
      (Array.replicate rule_lower_1272.vars.length none) = .ok (some env)) :
    env[3]? = some (some (.value value)) := by
  obtain ⟨env1,head,empty⟩ := matchArgs_cons_inv args
  simp only [matchArgs,pure,Except.pure] at empty
  cases empty
  obtain ⟨values,extracted,fields⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl head
  change Backend.externExtract ctx T.inst_data_value (.inst ii) st.base = .ok values at extracted
  change (match ctx.insts[ii]? with
    | some info => ExtResult.ok [V.ty (info.resTys.head?.getD .invalid),info.data]
    | none => ExtResult.unmodeled s!"inst {ii}") = ExtResult.ok values at extracted
  rw [installed] at extracted
  cases extracted
  obtain ⟨envFit,fit,remaining⟩ := matchArgs_cons_inv fields
  obtain ⟨envData,dataPat,empty⟩ := matchArgs_cons_inv remaining
  simp only [matchArgs,pure,Except.pure] at empty
  cases empty
  obtain ⟨items,decoded,arguments⟩ := matchPat_enum_inv data_program.t2476 term_2476_kind dataPat
  change (Backend.sem ctx).unData 152 info.data = some (29,items) at decoded
  have itemsEq := data_fields_unData ctx "Unary" [opcodeV "Uextend",.value value]
    (by rw [← shape]; exact decoded)
  subst items
  obtain ⟨envOpcode,opcode,tail⟩ := matchArgs_cons_inv arguments
  obtain ⟨envOperand,operand,empty⟩ := matchArgs_cons_inv tail
  simp only [matchArgs,pure,Except.pure] at empty
  cases empty
  obtain ⟨inside,inner⟩ := matchPat_bind_inv operand
  have kept := stock_pattern_keeps (k := 3) (by decide) inner
  exact kept.trans (Array.getElem?_setIfInBounds_self_of_lt inside)

/-- Successful mapped source data derives the exact original extension operand. -/
theorem acquire_original_extension_data {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {ii value : Nat} {info : IInfo} {target : Clif.Ty}
    (installed : ctx.insts[ii]? = some info)
    (source : info.clif = some (.extend .uextend target value)) :
    info.data = instDataV "Unary" [opcodeV "Uextend",.value value] := by
  have encoded := mapped.data ii info _ installed source
  cases integer : eTy target with
  | false => simp only [instData,integer,Bool.false_eq_true,ite_false] at encoded; cases encoded
  | true =>
    have computation : instData f (.extend .uextend target value) =
        .ok (instDataV "Unary" [opcodeV "Uextend",.value value]) := by
      simp only [instData,integer,ite_true,beq_self_eq_true,pure,Except.pure]
    rw [computation] at encoded
    exact (Except.ok.inj encoded).symm

/-- Actual root matching uses the original extension operand as the deferred source value. -/
theorem acquire_root_match_original_value {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {st matched : State} {before after : Array RuleId}
    {bound : Isle.Interp.Env V} {n ii value : Nat} {info : IInfo} {target : Clif.Ty}
    (installed : ctx.insts[ii]? = some info)
    (source : info.clif = some (.extend .uextend target value))
    (run : (matchRule program (Stock.sem ctx) {} (n+5) rule_lower_1272 [.inst ii]).run
      (st,before) = .ok (some bound,matched,after)) :
    ∃ producer, Stock.source ctx st value = some (producer,true) ∧ matched = st ∧ after = before ∧
      bound[4]? = some (some (.inst producer)) := by
  obtain ⟨env,actual,producer,args,held,actualSource,sameState,sameTrace,binding⟩ :=
    acquire_root_match_source run
  have data := acquire_original_extension_data mapped installed source
  have originalValue := acquire_root_args_value_data installed data args
  have equal : actual = value := V.value.inj (Option.some.inj (Option.some.inj (held.symm.trans originalValue)))
  subst actual
  exact ⟨producer,actualSource,sameState,sameTrace,binding⟩

end Backend.Stock.Proof.Acquire810
