module

public import FV.Backend.Proof.StockConditionalCalls
public import FV.Backend.Proof.StockConditionalTargetsWitness

@[expose] public section

namespace Backend.Stock.Proof.ConditionalCalls
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- The existing complete original conditional driver supplies a real selected
rule and therefore inhabits every field of the derived call packet. -/
theorem calls_witness : ∃ (f : Clif.Function) (ctx : Ctx) (result : Result)
    (out : V) (next : State) (trace : List RuleId),
    Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
    Stock.runTerm ctx "lower_branch" [.inst 0,.labels [2,1]] result.initial =
      .ok (some out,next,trace) ∧ Nonempty (Calls ctx 0 [2,1] result.initial out next) := by
  obtain ⟨result,out,next,trace,run,scope,dominated,actual,selected,root,_⟩ :=
    ConditionalTargetsWitness.stock_selected_brif_targets_witness
  exact ⟨_,_,result,out,next,trace,run,scope,dominated,actual,selected_calls selected root⟩



private def originalBrifData : V :=
  .data 152 5 [.data 151 1 [],.value 7,.blockCalls [0,1]]

/-- The fixed complete source of the retained conditional selection witness. -/
def sourceFunction : Clif.Function := {
  name := "stock_per_successor_migration"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],term := .brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩},
    {id := 1,params := [(31,.i64)],term := .ret [31]}, {id := 2,params := [(47,.i64)],term := .ret [47]}] }

/-- The same complete actual driver derives condition value7 from its real
prepared terminator, inhabiting source_of_slot rather than assuming provenance. -/
theorem source_calls_fixture_witness : ∃ (result : Result)
    (out : V) (next : State) (trace : List RuleId),
    Stock.lower sourceFunction = .ok result ∧ LowerScope sourceFunction ∧ Dominated sourceFunction ∧
    Stock.runTerm (Driver.termCtx result.ctx 0 originalBrifData) "lower_branch"
      [.inst 0,.labels [2,1]] result.initial = .ok (some out,next,trace) ∧
    ∃ calls : Calls (Driver.termCtx result.ctx 0 originalBrifData) 0 [2,1] result.initial out next,
      calls.source = .value 7 := by
  obtain ⟨result,out,next,trace,run,scope,dominated,actual,selected,root,_⟩ :=
    ConditionalTargetsWitness.stock_selected_brif_targets_witness
  let ctx := Driver.termCtx result.ctx 0 originalBrifData
  let selectedHere : BranchSelection ctx 0 [2,1] result.initial out next trace := selected
  obtain ⟨calls⟩ := selected_calls selectedHere root
  obtain ⟨info,targets,found,_⟩ := calls.sourceData
  obtain ⟨bound,_⟩ := Array.getElem?_eq_some_iff.mp found
  have originalBound : 0 < result.ctx.insts.size := by simpa [ctx,Driver.termCtx] using bound
  have slot : ctx.insts[0]? = some ⟨originalBrifData,[],[],none⟩ := by
    simp [ctx,Driver.termCtx,Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_self_of_lt originalBound]
  have source := calls.source_of_slot (c := 7) (yes := ⟨1,[7]⟩) (no := ⟨2,[7]⟩) slot rfl
  exact ⟨result,out,next,trace,run,scope,dominated,actual,calls,source⟩


/-- The same complete actual driver derives condition value7 from its real
prepared terminator, inhabiting source_of_slot rather than assuming provenance. -/
theorem source_calls_witness : ∃ (f : Clif.Function) (result : Result)
    (out : V) (next : State) (trace : List RuleId),
    Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
    Stock.runTerm (Driver.termCtx result.ctx 0 originalBrifData) "lower_branch"
      [.inst 0,.labels [2,1]] result.initial = .ok (some out,next,trace) ∧
    ∃ calls : Calls (Driver.termCtx result.ctx 0 originalBrifData) 0 [2,1] result.initial out next,
      calls.source = .value 7 := by
  obtain ⟨result,out,next,trace,run,scope,dominated,actual,calls,source⟩ := source_calls_fixture_witness
  exact ⟨sourceFunction,result,out,next,trace,run,scope,dominated,actual,calls,source⟩

end Backend.Stock.Proof.ConditionalCalls
