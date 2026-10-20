import FV.Backend.Proof.StockCallResultValues
import FV.Backend.Proof.StockCallEmissionWitness
import FV.Backend.Proof.StockIndirectCallEmissionWitness
import FV.Backend.Proof.StockGotCallWitness
namespace Backend.Stock.Proof.CallResultBindingWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open TupleBindingDraft CallResultBindingDraft CallResultValuesDraft CallStaticFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower
private def values (implicit : Bool) : List Clif.Val := if implicit then [] else [⟨.i64,7⟩,⟨.i64,9⟩]
private def outputs (implicit : Bool) : List CV := if implicit then [123] else [7,9]
private theorem prefix_held (implicit : Bool) : PrefixHold (values implicit) (outputs implicit) := by
  cases implicit with
  | false =>
    constructor
    · decide
    · intro j v x atValue atResult
      rcases j with _ | (_ | j)
      all_goals simp [values,outputs] at atValue atResult
      all_goals cases atValue; cases atResult; rfl
  | true => exact ⟨by decide,by intro j v x atValue; simp [values] at atValue⟩
private theorem set_exists (xs : List Nat) (vs : List Clif.Val) (length : xs.length = vs.length)
    (regs : Clif.Regs) : ∃ next,regs.setMany xs vs = some next := by
  induction xs generalizing vs regs with
  | nil => cases vs <;> simp_all [Clif.Regs.setMany]
  | cons x xs ih =>
    cases vs with
    | nil => simp at length
    | cons v vs => exact ih vs (by simpa using length) (regs.set x v)

def ResultBindingFacts (implicit : Bool) (result : Result) (event : BlockScanEvent)
    (record : ScanRecord) (info : IInfo) (step : Step) : Prop :=
  info.results.length = (if implicit then 0 else 2) ∧
  step.results = freshVectors record.input.base.nextVreg info.results.length ∧
  (∀ j x,info.results[j]? = some x → ∃ key,event.ctx.valueReg? x = some (.vreg key .int) ∧
    (result.final.alias[key]?).join = some (record.input.base.nextVreg+j) ∧
    aliasNum result.final.alias key = record.input.base.nextVreg+j) ∧
  ∃ (fr fr' : Clif.Frame) (regs : Clif.Regs),
    fr.regs.setMany info.results (values implicit) = some regs ∧ fr'.regs = regs ∧
    PrefixHold (values implicit) (outputs implicit) ∧
    ValuesHeld (fun x => x ∈ info.results) result.ctx fr'
      (fun key => writeV (fun _ => 0)
        ((callDefOps (outDefs record.input.base.nextVreg info.results.length)).zip (outputs implicit))
          (aliasNum result.final.alias key))

private theorem make_facts (implicit : Bool) (f : Clif.Function) (result : Result) (event : BlockScanEvent)
    (record : ScanRecord) (info : IInfo) (step : Step)
    (length : info.results.length = (if implicit then 0 else 2))
    (output : step.results = freshVectors record.input.base.nextVreg info.results.length)
    (bindings : ∀ j x,info.results[j]? = some x → ∃ key,event.ctx.valueReg? x = some (.vreg key .int) ∧
      (result.final.alias[key]?).join = some (record.input.base.nextVreg+j) ∧
      aliasNum result.final.alias key = record.input.base.nextVreg+j)
    (transfer : ∀ (fr fr' : Clif.Frame) (regs : Clif.Regs),
      fr.regs.setMany info.results (values implicit) = some regs → fr'.regs = regs →
      ValuesHeld (fun x => x ∈ info.results) result.ctx fr'
        (fun key => writeV (fun _ => 0)
          ((callDefOps (outDefs record.input.base.nextVreg info.results.length)).zip (outputs implicit))
            (aliasNum result.final.alias key))) : ResultBindingFacts implicit result event record info step := by
  let fr : Clif.Frame := ⟨f,fun _ => none,[],[],.ret []⟩
  have count : info.results.length = (values implicit).length := by rw [length]; cases implicit <;> rfl
  obtain ⟨regs,set⟩ := set_exists info.results (values implicit) count fr.regs
  exact ⟨length,output,bindings,fr,{fr with regs},regs,set,rfl,prefix_held implicit,transfer fr {fr with regs} regs set rfl⟩

/-- Complete original-condition direct ordinary/two-result and sret/zero-result
pipelines inhabit actual tuple aliases and successful source value binding.
The sret case also exercises an extra unused ABI value; cached pipelines are reused. -/
theorem stock_complete_direct_call_result_binding_witness (implicit : Bool) :
    ∃ (out : Output) (event : BlockScanEvent) (record : ScanRecord) (info : IInfo) (step : Step),
      LowerScope (function false implicit) ∧ Dominated (function false implicit) ∧ ArityOk (function false implicit) ∧ AbiSigsOk (function false implicit) ∧
      Stock.lower (function false implicit) = .ok out.result ∧
      prepareAt out.result.code out.result.edgeArgs = .ok out.prepared ∧
      out.rf = spillAllocAt out.prepared.code out.prepared.edges ∧
      checkAllocAt out.prepared.code out.prepared.edges out.rf = .ok () ∧
      lowerRFunc out.prepared.code out.rf = .ok out.af ∧ Facts false implicit out ∧
      event ∈ out.result.blockScans.toList ∧ record ∈ event.output.records ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.call 0 (arguments false implicit)) ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      ResultBindingFacts implicit out.result event record info step := by
  obtain ⟨out,event,record,info,step,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,
    facts,events,records,slot,clif,recorded,emitted,actual,placed⟩ :=
    CallEmissionWitnessDraft.stock_complete_direct_call_emission_witness implicit
  let ext : Clif.ExtFunc := {name := calleeName,sig := signature false implicit,colocated := true}
  have external : (function false implicit).extern? 0 = some ext := rfl
  obtain ⟨length,output,bindings⟩ := stock_lower_call_result_binding lowered scope dominated.ssa abi events records slot clif external recorded emitted
  have count : info.results.length = (if implicit then 0 else 2) := by
    rw [length]
    cases implicit <;> rfl
  have bound := make_facts implicit (function false implicit) out.result event record info step count output bindings (by
    intro fr fr' regs set updated
    exact stock_lower_call_result_values lowered scope dominated.ssa abi events records slot clif external recorded emitted set updated (prefix_held implicit))
  exact ⟨out,event,record,info,step,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,
    facts,events,records,slot,clif,recorded,emitted,bound⟩

/-- Complete original-condition indirect ordinary/two-result and sret/zero-result
pipelines inhabit actual tuple aliases and successful source value binding.
The sret case also exercises an extra unused ABI value; cached pipelines are reused. -/
theorem stock_complete_indirect_call_result_binding_witness (implicit : Bool) :
    ∃ (out : Output) (event : BlockScanEvent) (record : ScanRecord) (info : IInfo) (step : Step),
      LowerScope (function true implicit) ∧ Dominated (function true implicit) ∧ ArityOk (function true implicit) ∧ AbiSigsOk (function true implicit) ∧
      Stock.lower (function true implicit) = .ok out.result ∧
      prepareAt out.result.code out.result.edgeArgs = .ok out.prepared ∧
      out.rf = spillAllocAt out.prepared.code out.prepared.edges ∧
      checkAllocAt out.prepared.code out.prepared.edges out.rf = .ok () ∧
      lowerRFunc out.prepared.code out.rf = .ok out.af ∧ Facts true implicit out ∧
      event ∈ out.result.blockScans.toList ∧ record ∈ event.output.records ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.callIndirect 0 80 (arguments true implicit)) ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      ResultBindingFacts implicit out.result event record info step := by
  obtain ⟨out,event,record,info,step,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,
    facts,events,records,slot,clif,recorded,emitted,origin,actual,placed⟩ :=
    IndirectCallEmissionWitnessDraft.stock_complete_indirect_call_emission_witness implicit
  obtain ⟨sig,declared,length,output,bindings⟩ := stock_lower_indirect_call_result_binding lowered scope dominated.ssa abi events records slot clif recorded emitted
  have expected : (function true implicit).sigDecls.lookup 0 = some (signature true implicit) := rfl
  have same := Option.some.inj (declared.symm.trans expected)
  subst sig
  have count : info.results.length = (if implicit then 0 else 2) := by
    rw [length]
    cases implicit <;> rfl
  have bound := make_facts implicit (function true implicit) out.result event record info step count output bindings (by
    intro fr fr' regs set updated
    exact stock_lower_indirect_call_result_values lowered scope dominated.ssa abi events records slot clif recorded emitted set updated (prefix_held implicit))
  exact ⟨out,event,record,info,step,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,
    facts,events,records,slot,clif,recorded,emitted,bound⟩

/-- Complete original-condition got ordinary/two-result and sret/zero-result
pipelines inhabit actual tuple aliases and successful source value binding.
The sret case also exercises an extra unused ABI value; cached pipelines are reused. -/
theorem stock_complete_got_call_result_binding_witness (implicit : Bool) :
    ∃ (out : GotCallFixture.Output) (event : BlockScanEvent) (record : ScanRecord) (info : IInfo) (step : Step),
      LowerScope (GotCallFixture.function implicit) ∧ Dominated (GotCallFixture.function implicit) ∧ ArityOk (GotCallFixture.function implicit) ∧ AbiSigsOk (GotCallFixture.function implicit) ∧
      Stock.lower (GotCallFixture.function implicit) = .ok out.result ∧
      prepareAt out.result.code out.result.edgeArgs = .ok out.prepared ∧
      out.rf = spillAllocAt out.prepared.code out.prepared.edges ∧
      checkAllocAt out.prepared.code out.prepared.edges out.rf = .ok () ∧
      lowerRFunc out.prepared.code out.rf = .ok out.af ∧ GotCallFixture.Facts implicit out ∧
      event ∈ out.result.blockScans.toList ∧ record ∈ event.output.records ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.call 0 (arguments false implicit)) ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      ResultBindingFacts implicit out.result event record info step := by
  obtain ⟨out,event,record,info,step,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,
    facts,events,records,slot,clif,recorded,emitted,protocol,actual,placed⟩ :=
    GotCallWitnessDraft.stock_complete_got_call_emission_witness implicit
  let ext : Clif.ExtFunc := {name := calleeName,sig := signature false implicit,colocated := false}
  have external : (GotCallFixture.function implicit).extern? 0 = some ext := rfl
  obtain ⟨length,output,bindings⟩ := stock_lower_call_result_binding lowered scope dominated.ssa abi events records slot clif external recorded emitted
  have count : info.results.length = (if implicit then 0 else 2) := by
    rw [length]
    cases implicit <;> rfl
  have bound := make_facts implicit (GotCallFixture.function implicit) out.result event record info step count output bindings (by
    intro fr fr' regs set updated
    exact stock_lower_call_result_values lowered scope dominated.ssa abi events records slot clif external recorded emitted set updated (prefix_held implicit))
  exact ⟨out,event,record,info,step,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,
    facts,events,records,slot,clif,recorded,emitted,bound⟩
end Backend.Stock.Proof.CallResultBindingWitnessDraft
