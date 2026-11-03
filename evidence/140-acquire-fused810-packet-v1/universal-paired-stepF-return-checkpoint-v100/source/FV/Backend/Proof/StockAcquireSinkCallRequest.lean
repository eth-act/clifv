import FV.Backend.Proof.StockAcquireSinkRequest

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program

/-- Actual complete sink evaluation derives the original pointer request and exact marked state. -/
theorem sink_atomic_call_request {ctx : Ctx} {st next : State} {before after : Array RuleId}
    {fuel producer pointer : Nat} {out : V} {info : IInfo} {flags : Clif.MemFlags}
    (installed : ctx.insts[producer]? = some info)
    (atomic : info.data = .data 152 17 [.data 151 158 [],.value pointer,.op (.memFlags flags)])
    (enough : 25 ≤ fuel)
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 27 564 [.inst producer]
      (st,before) out (next,after)) :
    ∃ middle address,
      Stock.externCtor ctx T.sink_inst [.inst producer] st = .ok (.op .unit,middle) ∧
      Stock.externCtor ctx T.put_in_reg [.value pointer] middle = .ok (.reg address,next) ∧
      DemandAllowed ctx middle pointer ∧ ctx.valueReg? pointer = some address ∧
      out = .reg address ∧ next = middle.mark pointer := by
  unfold ApplyInternal at run
  obtain ⟨rule,member,matchFuel,env,matched,final,trace,bounded,matchedRun,evaluatedRun,finished⟩ :=
    applyTerm_internal_some (by rfl) data_program.t564 term_564_kind rfl run
  have same : rule = rule_inst_3905 := by simpa only [data_program.r564,List.mem_singleton] using member
  subst rule
  have enoughMatch : 2 ≤ matchFuel := by
    rw [data_program.r564] at bounded
    simp only [List.length_cons,List.length_nil] at bounded
    omega
  obtain ⟨m,matchEq⟩ : ∃ m,matchFuel = m+2 := ⟨matchFuel-2,by omega⟩
  obtain ⟨n,evalEq⟩ : ∃ n,fuel = n+20 := ⟨fuel-20,by omega⟩
  rw [matchEq] at matchedRun
  rw [evalEq] at evaluatedRun
  have pointerValue := sink_atomic_match_address installed atomic matchedRun
  obtain ⟨sameState,sameTrace,producerValue⟩ := stock_loadSink_binding (ty := .int 8) true
    (n := m+1) (by simpa only [Nat.add_assoc,ite_true] using matchedRun)
  have samePair : matched = (st,before) := Prod.ext sameState sameTrace
  rw [samePair] at evaluatedRun
  have request := sink_atomic_rhs_request producerValue pointerValue evaluatedRun
  have nextEq : next = final := congrArg Prod.fst finished
  rw [nextEq]
  exact request

end Backend.Stock.Proof.Acquire810
