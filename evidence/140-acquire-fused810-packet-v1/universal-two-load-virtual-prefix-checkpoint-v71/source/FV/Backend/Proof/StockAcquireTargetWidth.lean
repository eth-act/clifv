import FV.Backend.Proof.StockAcquireMatchSource
import FV.Backend.Proof.StockDFG

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program

/-- The actual root matcher derives its target-width bound internally. -/
theorem acquire_root_match_target_width {ctx : Ctx} {st matched : State}
    {before after : Array RuleId} {bound : Isle.Interp.Env V} {n ii : Nat}
    (run : (matchRule program (Stock.sem ctx) {} (n+5) rule_lower_1272 [.inst ii]).run
      (st,before) = .ok (some bound,matched,after)) :
    ∃ info, ctx.insts[ii]? = some info ∧ (info.resTys.head?.getD .invalid).bits ≤ 64 := by
  obtain ⟨env,args,iflets⟩ := matchRule_some_inv run
  obtain ⟨env1,head,tail⟩ := matchArgs_cons_inv args
  obtain ⟨values,extracted,fields⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl head
  change Backend.externExtract ctx T.inst_data_value (.inst ii) st.base = .ok values at extracted
  change (match ctx.insts[ii]? with
    | some info => ExtResult.ok [V.ty (info.resTys.head?.getD .invalid),info.data]
    | none => ExtResult.unmodeled s!"inst {ii}") = ExtResult.ok values at extracted
  cases installed : ctx.insts[ii]? with
  | none => rw [installed] at extracted; cases extracted
  | some info =>
    rw [installed] at extracted
    cases extracted
    obtain ⟨env2,fit,rest⟩ := matchArgs_cons_inv fields
    obtain ⟨fits,accepted,_⟩ := matchPat_extract_inv data_program.t113 term_113_kind rfl fit
    change Backend.externExtract ctx T.fits_in_64 (.ty (info.resTys.head?.getD .invalid)) st.base =
      .ok fits at accepted
    have test : Backend.externExtract ctx T.fits_in_64 (.ty (info.resTys.head?.getD .invalid)) st.base =
        if decide ((info.resTys.head?.getD .invalid).bits ≤ 64) then
          .ok [.ty (info.resTys.head?.getD .invalid)] else .fail := rfl
    rw [test] at accepted
    split at accepted
    · rename_i width
      exact ⟨info,rfl,of_decide_eq_true width⟩
    · cases accepted

/-- The original CLIF extension inherits the actual matched target-width bound. -/
theorem acquire_root_source_target_width {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {st matched : State} {before after : Array RuleId}
    {bound : Isle.Interp.Env V} {n ii : Nat} {info : IInfo} {target : Clif.Ty} {value : Nat}
    (installed : ctx.insts[ii]? = some info) (source : info.clif = some (.extend .uextend target value))
    (run : (matchRule program (Stock.sem ctx) {} (n+5) rule_lower_1272 [.inst ii]).run
      (st,before) = .ok (some bound,matched,after)) : target.width ≤ 64 := by
  obtain ⟨actual,found,width⟩ := acquire_root_match_target_width run
  have same : actual = info := Option.some.inj (found.symm.trans installed)
  subst actual
  obtain ⟨tys,types,resultTypes,length⟩ := mapped.resTys ii info _ installed source
  have tysEq : tys = [target] := by simpa only [Clif.Inst.resultTypes,Option.some.injEq] using types.symm
  rw [tysEq] at resultTypes
  rw [resultTypes] at width
  change (CTy.ofClif target).bits ≤ 64 at width
  have bits : (CTy.ofClif target).bits = target.width := by cases target <;> rfl
  rwa [bits] at width

end Backend.Stock.Proof.Acquire810
