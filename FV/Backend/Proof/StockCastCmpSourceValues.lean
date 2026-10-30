import FV.Backend.Proof.IselFamAluBExtend
import FV.Backend.Proof.StockCastCmpRhsValues
import FV.Backend.Proof.StockCastCmpSelection
import FV.Backend.Proof.StockCastCmpOperands
import FV.Backend.Proof.StockAvailableTypes
import FV.Backend.Proof.StockGuardedRecordValues
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem scan_frontier (st : State) (i : Nat) :
    (scanState st i).base.nextVreg = st.base.nextVreg := by
  unfold scanState; dsimp only; split <;> rfl
private theorem scan_empty (st : State) (i : Nat) :
    (scanState st i).base.emitted = #[] := by
  unfold scanState; dsimp only; split <;> rfl
private theorem setAlias_base {st next : State} {dst src : Reg}
    (h : st.setAlias dst src = .ok next) : next.base = st.base := by
  cases dst <;> cases src <;>
    simp only [State.setAlias,bind,Except.bind,pure,Except.pure,throw,throwThe,MonadExceptOf.throw] at h
  all_goals repeat' first | (solve | cases h; rfl) | (solve | cases h) | split at h
private theorem fold_base {α β : Type} (field : α → LState)
    (step : α → β → Except String α)
    (preserves : ∀ a b next,step a b = .ok next → field next = field a)
    (xs : List β) {a next : α} (run : xs.foldlM step a = .ok next) : field next = field a := by
  induction xs generalizing a with
  | nil => cases run; rfl
  | cons x xs ih =>
    rw [List.foldlM_cons] at run
    cases call : step a x with
    | error e => simp only [call,bind,Except.bind] at run; cases run
    | ok middle => simp only [call,bind,Except.bind] at run; exact (ih run).trans (preserves _ _ _ call)
private theorem binding_base {ctx : Ctx} {pairs : List (Nat × List Reg)} {st next : State} {copies : Array MInst}
    (run : bindResults ctx pairs st = .ok (next,copies)) : next.base = st.base := by
  unfold bindResults at run
  apply fold_base (fun a : State × Array MInst => a.1.base) _ ?_ pairs run
  intro acc pair next call
  rcases acc with ⟨s,code⟩
  rcases pair with ⟨v,rs⟩
  dsimp only at call
  cases mapped : ctx.valueReg? v with
  | none => simp only [mapped] at call; cases call
  | some r =>
    simp only [mapped] at call
    split at call
    · rename_i _ n cls
      cases alias : s.setAlias r (.vreg n cls) with
      | error e => simp only [alias,bind,Except.bind] at call; cases call
      | ok q => simp only [alias,bind,Except.bind,pure,Except.pure] at call; cases call; exact setAlias_base alias
    · cases call; rfl
    · cases call


/-- A real fused cast record computes the original zero-extended comparison,
binds its actual result through final aliases, and transfers the complete
availability-guarded original source frame. Operand types, availability, RHS
calls and scratch separation are derived internally. The caller's dispatcher
supplies the actual trace root, as for the older base-cast variant. -/
theorem stock_lower_cast_cmp_source_values_framed {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {input z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.extend .uextend ty input))
    (results : info.results = [z]) (statementResults : stmt.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 811)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun value => Demanded record.output.state value ∧ value ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun key => ρ (aliasNum result.final.alias key)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    cm' = cm ∧ ∀ world,∃ d,Runs F isem (record.output.emitted.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world (fun ρ' _ =>
        step.results = [[.vreg d .int]] ∧
        (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → ρ' key = ρ key) ∧
        ValuesHeld (fun value => Demanded record.input value ∧ value ∈ availOf f (availIn f result.ctx) bi (j+1))
          event.ctx fr' (fun key => ρ' (aliasNum result.final.alias key))) := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have inv := (stock_lower_record_context run scope events).1
  have maps := (stock_lower_record_context run scope events).2.1
  have base := binding_base receipt.binding
  have recordBase : record.output.state.base = receipt.next.base := by rw [receipt.state,base]
  have demand : record.output.state.demand = receipt.next.demand := by rw [receipt.state,stock_bindResults_demand receipt.binding]
  have id : receipt.selected.rule.id = 811 := by
    rw [receipt.rules,receipt.selected.last_rule] at selectedId
    exact Option.some.inj selectedId
  have chosen : receipt.selected.rule = rule_lower_1281 :=
    eq_of_mem_of_id lower_ids_nodup receipt.selected.rule_mem
      (by rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) id
  obtain ⟨defining,comparison,cc,cmpTy,x,y,defined,found,original,envEq,stateEq,traceEq⟩ :=
    stock_cast_cmp_selected_definition inv source clif receipt.selected chosen
  have rhs := receipt.selected.rhsRun
  rw [chosen,envEq,stateEq,traceEq] at rhs
  obtain ⟨outputAccepted,_,_⟩ := stock_cast_cmp_source_data inv source clif
  have sourceProof := sourceStep
  obtain ⟨info',inst,vals,regs,rest,located,originalInst,body,evaluated,written,updated⟩ := sourceProof
  have sameInfo := Option.some.inj (located.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (originalInst.symm.trans clif)
  subst inst
  have plain : Clif.evalInst fr cm (.extend .uextend ty input) = .ok (vals,cm') := evaluated
  obtain ⟨inputValue,getInput,grows,memory,values⟩ := evalInst_extend_ok plain
  have availableInput := stock_lower_record_args_available run scope dominated events foundBlock foundStmt current
    source clif input (by simp [Driver.instArgs])
  have restrictedInput : (restrict fr (availOf f (availIn f result.ctx) bi j)).regs input = some inputValue := by
    rw [restrict_regs_of_mem availableInput]; exact getInput
  obtain ⟨u,v,getX,getY,inputEq⟩ := stock_cast_cmp_source_operands dfg defined found original restrictedInput
  have availableX := restrict_regs_isSome (by rw [getAs_ok getX]; rfl)
  have availableY := restrict_regs_isSome (by rw [getAs_ok getY]; rfl)
  have typeX := stock_lower_available_getAs_type run events availableX dfg getX
  have typeY := stock_lower_available_getAs_type run events availableY dfg getY
  have accepted : eTy cmpTy = true := by
    simpa [Compile.instE,Compile.tyE,eTy] using inv.instE defining comparison _ found original
  have restrictedHeld : ValuesHeld (Demanded receipt.next) event.ctx
      (restrict fr (availOf f (availIn f result.ctx) bi j)) (fun key => ρ (aliasNum result.final.alias key)) := by
    intro value needed val lookup
    have available := restrict_regs_isSome (by rw [lookup]; rfl)
    rw [restrict_regs_of_mem available] at lookup
    exact held value ⟨by simpa only [Demanded,demand] using needed,available⟩ val lookup
  have bounded := stock_lower_blockScanAliasBounds run event events record records
  have extent : ∀ x r,event.ctx.valueReg? x = some r → x < (scanState record.input record.inst).demand.size := by
    intro x r map
    simpa only [scanState_demands] using (Extent.lower_mapped_demand_bounds run scope events records map).1
  have allocation := stock_cast_cmp_rhs_growth inv accepted typeX typeY rhs dfg getX getY
    refines bounded extent restrictedHeld
  have allocated : record.input.base.nextVreg < record.output.state.base.nextVreg := by
    rw [recordBase]
    simpa only [scan_frontier] using allocation
  have separatedY : ∀ r,event.ctx.valueReg? y = some (.vreg r .int) →
      aliasNum result.final.alias r ≠ (scanState record.input record.inst).base.nextVreg := by
    intro r map equal
    have outside := stock_lower_available_alias_outside_record run scope dominated events records
      foundBlock foundStmt current availableY (by rw [← maps]; exact map)
    rw [scan_frontier] at equal
    omega
  obtain ⟨d,instructions,output,lower,upper,fragment,execution⟩ := stock_cast_cmp_rhs_source_values
    inv accepted outputAccepted typeX typeY (scan_empty record.input record.inst) rhs dfg getX getY refines
    bounded extent restrictedHeld separatedY
  have rss : receipt.results = [[.vreg d .int]] := V.regsVec.inj (receipt.output.symm.trans output)
  have installed := bindResults_virtual event.ctx receipt.next [(z,a,d)] (by
    intro p member; have same := List.mem_singleton.mp member; subst p; exact mapped)
  simp only [List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil] at installed
  have binding := receipt.binding
  have infoBang : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def,source]
  rw [infoBang,results,rss] at binding
  simp only [List.zip_cons_cons,List.zip_nil_left] at binding
  rw [installed] at binding
  have boundEq := (Prod.mk.inj (Except.ok.inj binding)).1.symm
  have copiesEq := (Prod.mk.inj (Except.ok.inj binding)).2.symm
  have code : record.output.emitted.toList = instructions := by
    rw [receipt.code,boundEq,copiesEq]
    simp only [Array.append_empty]
    have empty := scan_empty record.input record.inst
    have actual := fragment.emitted
    rw [empty] at actual
    simp only [Array.empty_append] at actual
    rw [actual,List.toList_toArray]
  have outputRegs := receipt.resultRegs.trans rss
  have recordLower : record.input.base.nextVreg ≤ d := by simpa only [scan_frontier] using lower
  have installedFinal := (stock_lower_record_fresh_result run scope dominated.ssa events records source clif results
    mapped recorded emitted outputRegs recordLower).2
  have evaluatedValue : instOutcome env cp fr cm (.extend .uextend ty input) =
      .ok ([⟨ty,Clif.Sem.uextend ty.width (Clif.Sem.bool8 (Clif.Sem.intcc cc u v))⟩],cm') := by
    rw [inputEq] at values
    rw [values] at evaluated
    exact evaluated
  refine ⟨memory,?_⟩
  intro world
  refine ⟨d,?_⟩
  rw [code]
  apply (execution world).imp
  intro final world' executed resultValue
  obtain ⟨value,kept⟩ := resultValue
  refine ⟨outputRegs,?_,?_⟩
  · intro key outside
    exact kept key (by simpa only [scan_frontier,recordBase] using outside)
  · apply source_single_result_values source clif results sourceStep evaluatedValue
    intro old required oldVal lookup
    by_cases equal : old = z
    · subst old
      simp only [withValue,eq_self,ite_true] at lookup
      cases lookup
      exact ⟨a,mapped,by change VHolds _ (final (aliasNum result.final.alias a)); rw [installedFinal]; exact value⟩
    · simp only [withValue,ite_eq_right equal] at lookup
      have before := available_before_of_after_not_result foundBlock foundStmt required.2
        (by simpa only [statementResults,List.mem_singleton] using equal)
      have needed : Demanded record.output.state old := by
        intro zero
        have count := stock_lower_record_demand_mono run events records recorded emitted old
        change record.output.state.demand[old]! = 0 at zero
        rw [zero] at count
        exact required.1 (Nat.eq_zero_of_le_zero count)
      obtain ⟨key,map,previous⟩ := held old ⟨needed,before⟩ oldVal lookup
      have outside := stock_lower_available_alias_outside_record run scope dominated events records
        foundBlock foundStmt current before (by rw [← maps]; exact map)
      refine ⟨key,map,?_⟩
      change VHolds oldVal (final (aliasNum result.final.alias key))
      rw [kept _ (by simpa only [scan_frontier,recordBase] using outside)]
      exact previous

/-- Retained original interface. -/
theorem stock_lower_cast_cmp_source_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {input z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.extend .uextend ty input))
    (results : info.results = [z]) (statementResults : stmt.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 811)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun value => Demanded record.output.state value ∧ value ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun key => ρ (aliasNum result.final.alias key)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    cm' = cm ∧ ∀ world,∃ d,Runs F isem (record.output.emitted.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world (fun ρ' _ =>
        step.results = [[.vreg d .int]] ∧
        ValuesHeld (fun value => Demanded record.input value ∧ value ∈ availOf f (availIn f result.ctx) bi (j+1))
          event.ctx fr' (fun key => ρ' (aliasNum result.final.alias key))) := by
  obtain ⟨memory,execution⟩ := stock_lower_cast_cmp_source_values_framed run scope dominated
    events records foundBlock foundStmt current source clif results statementResults mapped recorded emitted
    selectedId refines dfg held sourceStep
  refine ⟨memory,?_⟩
  intro world
  obtain ⟨d,ρ',w',executed,same,output,_,post⟩ := execution world
  exact ⟨d,ρ',w',executed,same,output,post⟩

end Backend.Stock.Proof.ScalarCmp
