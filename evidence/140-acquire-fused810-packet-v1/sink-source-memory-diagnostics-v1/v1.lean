import FV.Backend.Proof.StockAcquireSinkFormatSources

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle
set_option autoImplicit false
set_option Elab.async false

/-- Successful source evaluation of either sink format preserves memory, including bitcasts. -/
theorem sink_format_eval_memory {f : Clif.Function} {inst : Clif.Inst} {fmt : Nat} {fields : List V}
    (encoded : instData f inst = .ok (.data 152 fmt fields)) (format : fmt = 16 ∨ fmt = 17)
    {fr : Clif.Frame} {cm next : Clif.Mem} {values : List Clif.Val}
    (evaluated : Clif.evalInst fr cm inst = .ok (values,next)) : next = cm := by
  rcases instData_read_format encoded format with ⟨op,ty,flags,pointer,offset,rfl⟩ |
    ⟨ty,flags,pointer,rfl⟩ | ⟨ty,flags,value,rfl⟩
  · simp only [Clif.evalInst] at evaluated
    obtain ⟨pv,found,evaluated⟩ := res_bind_eq_ok evaluated
    obtain ⟨unit,checked,evaluated⟩ := res_bind_eq_ok evaluated
    obtain ⟨raw,read,evaluated⟩ := res_bind_eq_ok evaluated
    simp only [Clif.Res.pure_eq,Clif.Res.ok.injEq,Prod.mk.injEq] at evaluated
    exact evaluated.2.symm
  · simp only [Clif.evalInst] at evaluated
    obtain ⟨pv,found,evaluated⟩ := res_bind_eq_ok evaluated
    obtain ⟨unit,checked,evaluated⟩ := res_bind_eq_ok evaluated
    obtain ⟨raw,read,evaluated⟩ := res_bind_eq_ok evaluated
    simp only [Clif.Res.pure_eq,Clif.Res.ok.injEq,Prod.mk.injEq] at evaluated
    exact evaluated.2.symm
  · simp only [Clif.evalInst] at evaluated
    obtain ⟨pv,found,evaluated⟩ := res_bind_eq_ok evaluated
    split at evaluated
    · cases evaluated; rfl
    · cases evaluated

/-- Actual successful source steps at original sink-format slots preserve the complete source memory. -/
theorem sink_format_source_step_memory {f : Clif.Function} {ctx : Ctx}
    (sources : SinkFormatSources f ctx) {producer : Nat} {info : IInfo}
    {fmt : Nat} {fields : List V} (installed : ctx.insts[producer]? = some info)
    (format : fmt = 16 ∨ fmt = 17)
    (decoded : (Backend.sem ctx).unData 152 info.data = some (fmt,fields))
    {env : Clif.Env} {p : Clif.Program} {before after : Clif.Frame × Clif.Mem}
    (step : SourceInstResult env p ctx producer before after) : after.2 = before.2 := by
  obtain ⟨inst,original,encoded,kinds⟩ := sources producer info installed fmt fields format decoded
  obtain ⟨actualInfo,actual,values,regs,rest,found,source,body,evaluated,updated,frame⟩ := step
  have same : actualInfo = info := Option.some.inj (found.symm.trans installed)
  subst actualInfo
  have instruction : actual = inst := Option.some.inj (source.symm.trans original)
  subst actual
  have shape : info.data = .data 152 fmt fields := by
    cases data : info.data <;> try (rw [data] at decoded; cases decoded)
    rename_i actualTy actualTag actualFields
    change (if actualTy == 152 then some (actualTag,actualFields) else none) = some (fmt,fields) at decoded
    split at decoded
    · rename_i equal
      have sameTy : actualTy = 152 := by simpa only [beq_iff_eq] using equal
      subst actualTy
      cases Option.some.inj decoded
      exact data
    · cases decoded
  have rawEncoded := encoded.trans (congrArg Except.ok shape)
  rcases kinds with ⟨op,ty,flags,pointer,offset,rfl⟩ | ⟨ty,flags,pointer,rfl⟩ | ⟨ty,flags,value,rfl⟩
  all_goals
    change Clif.evalInst _ _ _ = .ok _ at evaluated
    exact sink_format_eval_memory rawEncoded format evaluated

end Backend.Stock.Proof.Acquire810
