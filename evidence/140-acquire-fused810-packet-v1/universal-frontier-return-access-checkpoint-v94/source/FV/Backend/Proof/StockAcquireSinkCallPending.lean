import FV.Backend.Proof.StockAcquireSinkPending

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program

/-- Actual complete atomic sink evaluation contributes its original producer exactly once. -/
theorem sink_atomic_call_pending {ctx : Ctx} {st next : State} {before after : Array RuleId}
    {fuel producer : Nat} {out : V} (enough : 25 ≤ fuel)
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 27 564 [.inst producer]
      (st,before) out (next,after)) :
    ∃ middle,Stock.externCtor ctx T.sink_inst [.inst producer] st = .ok (.op .unit,middle) ∧
      PendingSinks ctx st [producer] next ∧ next.sunk = middle.sunk := by
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
  obtain ⟨n,evalEq⟩ : ∃ n,fuel = n+20 := ⟨fuel-20,by omega⟩
  rw [matchEq] at matchedRun
  rw [evalEq] at evaluatedRun
  obtain ⟨sameState,sameTrace,producerValue⟩ := stock_loadSink_binding (ty := .int 8) true matchedRun
  have samePair : matched = (st,before) := Prod.ext sameState sameTrace
  rw [samePair] at evaluatedRun
  have result := sink_atomic_rhs_pending producerValue evaluatedRun
  have nextEq : next = final := congrArg Prod.fst finished
  rw [nextEq]
  exact result

end Backend.Stock.Proof.Acquire810
