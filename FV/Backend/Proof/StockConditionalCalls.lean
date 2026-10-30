import FV.Backend.Proof.IselCtlBrif
import FV.Backend.Proof.IselCtlTry
import FV.Backend.Proof.StockBranchSelection

namespace Backend.Stock.Proof.ConditionalCalls
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl


/-- Internal actual calls selected by ordinary brif; no semantic condition
or branch-choice certificate is supplied by the caller. -/
structure Calls (ctx : Ctx) (i : Nat) (labels : List Label) (before : State) (out : V) (next : State) where
  source : V
  sourceData : ∃ info targetData, ctx.insts[i]? = some info ∧ info.data = .data 152 5 [.data 151 1 [],source,targetData]
  yes : Label
  no : Label
  labels_eq : labels = [yes,no]
  middle : State
  constructed : State
  condition : V
  descriptor : V
  conditionFuel : Nat
  constructFuel : Nat
  emitFuel : Nat
  conditionTrace : Array RuleId
  constructTrace : Array RuleId
  selectTrace : Array RuleId
  conditionEnough : 400 ≤ conditionFuel
  constructEnough : 100 ≤ constructFuel
  emitEnough : 30 ≤ emitFuel
  conditionRun : ApplyInternal program (Stock.sem ctx) {} conditionFuel 123 650
    [source] (before,#[]) condition (middle,conditionTrace)
  constructRun : ApplyInternal program (Stock.sem ctx) {} constructFuel 46 722
    [condition,.label yes,.label no] (middle,conditionTrace) descriptor (constructed,constructTrace)
  emitRun : ApplyInternal program (Stock.sem ctx) {} emitFuel 13 242
    [descriptor] (constructed,constructTrace) out (next,selectTrace)

theorem selected_calls {ctx : Ctx} {i : Nat} {labels : List Label}
    {before next : State} {out : V} {trace : List RuleId}
    (selected : BranchSelection ctx i labels before out next trace)
    (root : selected.rule = rule_lower_3231) :
    Nonempty (Calls ctx i labels before out next) := by
  have count : (program.rulesOf T.lower_branch.id).length = 8 := by
    rw [show T.lower_branch.id = 687 from rfl,data_program.r687]; rfl
  have bound := selected.fuelBound
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+20 := ⟨selected.matchFuel-20,by omega⟩
  have matched := selected.matchedRun
  have rhs := selected.rhsRun
  rw [root,fuelEq] at matched
  rw [root] at rhs
  have hp := data_program
  cases hp
  isel_inv [*,rule_lower_3231,sem_ctor,sem_extract,sem_unData,ext_two_targets_iff] at matched rhs
  isel_destruct
  subst_vars
  repeat (isel_inv_simp [ext_two_targets_iff] at * <;> isel_destruct <;> subst_vars)
  have envEq := ‹selected.env = _›
  have firstOperand := ‹selected.env[0]? = some (some _)›
  rw [envEq] at firstOperand
  simp at firstOperand
  cases firstOperand
  have firstLabel := ‹selected.env[1]? = some (some _)›
  have secondLabel := ‹selected.env[2]? = some (some _)›
  rw [envEq] at firstLabel secondLabel
  simp at firstLabel secondLabel
  cases firstLabel
  cases secondLabel
  have construct := ‹ApplyInternal _ _ _ _ 46 722 _ _ _ _›
  have emit := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  have conditionCall := ‹ApplyInternal _ _ _ _ 123 650 _ _ _ _›
  rw [‹selected.matched = before›, ‹selected.matchTrace = #[]›] at conditionCall
  exact ⟨{
    source := _
    sourceData := ⟨_,_,by assumption,(by assumption : _ = _).symm⟩
    yes := _
    no := _
    labels_eq := rfl
    middle := _
    constructed := _
    condition := _
    descriptor := _
    conditionFuel := _
    constructFuel := _
    emitFuel := _
    conditionTrace := _
    constructTrace := _
    selectTrace := _
    conditionEnough := by omega
    constructEnough := by omega
    emitEnough := by omega
    conditionRun := conditionCall
    constructRun := construct
    emitRun := emit }⟩

/-- Source condition provenance is derived from the actual prepared terminator
slot. It adds no accepted-input predicate or condition-value certificate. -/
theorem Calls.source_of_slot {ctx : Ctx} {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {info : IInfo} {c : Nat} {yes no : Clif.BlockCall}
    (slot : ctx.insts[i]? = some info)
    (data : termData (.brif c yes no) = .ok info.data) : calls.source = .value c := by
  obtain ⟨other,targets,found,shape⟩ := calls.sourceData
  rw [slot] at found
  cases found
  rw [termData_brif] at data
  have sourceShape := (Except.ok.inj data).trans shape
  simp only [V.data.injEq,List.cons.injEq,and_true,true_and] at sourceShape
  exact sourceShape.1.symm

end Backend.Stock.Proof.ConditionalCalls


