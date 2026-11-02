import FV.Backend.Proof.StockComparisonBranchFacts
import FV.Backend.Proof.StockComparisonBranchSelectionWitness

namespace Backend.Stock.Proof.ComparisonBranch.FactsWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private def built : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx Witness.function).toOption.getD (sinkCtx,#[],sinkState)
private def ctx : Ctx := Driver.termCtx built.1 1 Witness.brifData
private theorem build : Stock.buildCtx Witness.function = .ok built := by rfl
private theorem operandB : ctx.defInst? 1 = none := by rfl
private theorem typeA : ctx.valueType? 0 = some (.int (if true then 64 else 32)) := by rfl
private theorem typeB : ctx.valueType? 1 = some (.int (if true then 64 else 32)) := by rfl

/-- The real calls packet of the entry `brif` on `icmp slt v0, v1` (two i64
parameters) instantiates the three comparison facts: the branch allocates no
virtual register, keeps the demand extent, appends exactly two instructions,
and its fragment defines no virtual register. -/
theorem comparison_facts_witness : ∃ (result : Result) (out : V) (next : State) (trace : List RuleId)
    (calls : ConditionalCalls.Calls (Driver.termCtx result.ctx 1 Witness.brifData) 1 [2,1]
      result.initial out next),
    Stock.lower Witness.function = .ok result ∧
    Stock.runTerm (Driver.termCtx result.ctx 1 Witness.brifData) "lower_branch"
      [.inst 1,.labels [2,1]] result.initial = .ok (some out,next,trace) ∧
    calls.source = .value 2 ∧
    next.base.nextVreg = result.initial.base.nextVreg ∧ next.demand.size = result.initial.demand.size ∧
    next.base.emitted.size = result.initial.base.emitted.size+2 ∧
    ∃ code,Frag result.initial.base next.base code ∧ ∀ inst ∈ code,vdefs inst = [] := by
  obtain ⟨result,out,next,trace,run,_,⟨ranges,created,_⟩,_,inv,origin,operand,branch,calls,source⟩ :=
    Witness.comparison_calls_witness
  have same := Except.ok.inj (created.symm.trans build)
  have context : result.ctx = built.1 := congrArg Prod.fst same
  have operandB' : (Driver.termCtx result.ctx 1 Witness.brifData).defInst? 1 = none := by
    rw [context]
    exact operandB
  have typeA' : (Driver.termCtx result.ctx 1 Witness.brifData).valueType? 0 =
      some (.int (if true then 64 else 32)) := by
    rw [context]
    exact typeA
  have typeB' : (Driver.termCtx result.ctx 1 Witness.brifData).valueType? 1 =
      some (.int (if true then 64 else 32)) := by
    rw [context]
    exact typeB
  obtain ⟨frontier,extent⟩ := calls.comparison_wide_bounds inv source origin true typeA' typeB' operand operandB'
  have size := calls.comparison_wide_emitted_size inv source origin true typeA' typeB' operand operandB'
  obtain ⟨code,fragment,noDefs⟩ :=
    calls.comparison_wide_no_defs inv source origin true typeA' typeB' operand operandB'
  exact ⟨result,out,next,trace,calls,run,branch,source,frontier,extent,size,code,fragment,noDefs⟩

end Backend.Stock.Proof.ComparisonBranch.FactsWitness
