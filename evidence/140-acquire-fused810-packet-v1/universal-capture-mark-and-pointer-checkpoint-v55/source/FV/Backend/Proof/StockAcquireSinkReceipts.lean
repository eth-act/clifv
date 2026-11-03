import FV.Backend.Proof.StockAcquireSinkForward

namespace Backend.Stock.Proof.AcquireHelpers
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program

/-- An actual successful atomic sink evaluation derives its real sink update.
This is an evaluator call. It adds no CLIF call or source input condition. -/
theorem sink_atomic_call_receipt {ctx : Ctx} {st next : State} {before after : Array RuleId}
    {fuel ii : Nat} {out : V} (enough : 10 ≤ fuel)
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 27 564 [.inst ii]
      (st,before) out (next,after)) :
    ∃ sunk info fields,
      Stock.externCtor ctx T.sink_inst [.inst ii] st = .ok (.op .unit,sunk) ∧
      sunk = {st with color := some st.entryColor[ii]!,sunk := st.sunk.set! ii true} ∧
      ctx.insts[ii]? = some info ∧
      (Backend.sem ctx).unData 152 info.data = some (17,fields) := by
  unfold ApplyInternal at run
  obtain ⟨rule,member,matchFuel,env,matched,final,trace,bounded,matchedRun,evaluatedRun,finished⟩ :=
    applyTerm_internal_some (by rfl) data_program.t564 term_564_kind rfl run
  have same : rule = rule_inst_3905 := by simpa only [data_program.r564,List.mem_singleton] using member
  subst rule
  have enoughMatch : 0 < matchFuel := by
    rw [data_program.r564] at bounded
    simp only [List.length_cons,List.length_nil] at bounded
    omega
  obtain ⟨m,matchEq⟩ : ∃ m,matchFuel = m+1 := ⟨matchFuel-1,by omega⟩
  obtain ⟨n,evalEq⟩ : ∃ n,fuel = n+5 := ⟨fuel-5,by omega⟩
  rw [matchEq] at matchedRun
  rw [evalEq] at evaluatedRun
  simpa only [ite_true] using
    (stock_loadSink_call (ty := .int 8) true matchedRun evaluatedRun)

end Backend.Stock.Proof.AcquireHelpers
