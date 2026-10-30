import FV.Backend.Proof.StockDemandExtent
import FV.Backend.Proof.StockCmpZero32OriginalRightRootValues
import FV.Backend.Proof.StockGuardedRecordValues
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
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

/-- An actual retained comparison record derives its selected root, original
parameter values, fresh boolean result binding and emitted execution internally.
No caller-selected rule, helper, output or binding certificate is needed. -/
theorem stock_lower_cmp_zero32_original_right_record_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} (nonzero : Bool) {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.icmp (if nonzero then .ne else .eq) .i32 x y))
    (typeX : event.ctx.valueType? x = some (.int 32))
    (notConstant : NonConstantSource event.ctx x)
    {constantJ : Nat} {constantInfo : IInfo} {literal : Int}
    (defined : event.ctx.defInst? y = some constantJ) (found : event.ctx.insts[constantJ]? = some constantInfo)
    (data : constantInfo.data = .data 152 35 [.data 151 57 [],.int literal])
    (normalized : u64 literal = 0)
    (results : info.results = [z]) (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} (dfg : DFGCons event.ctx fr) {ρ : Nat → CV} {u v : BitVec 32}
    (getX : fr.getAs x .i32 = .ok u) (getY : fr.getAs y .i32 = .ok v)
    (held : ValuesHeld (Demanded record.output.state) event.ctx fr (fun key => ρ (aliasNum result.final.alias key))) :
    ∃ d,step.results = [[.vreg d .int]] ∧
      record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg ∧
      ∀ world,Runs F isem (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc (if nonzero then .ne else .eq) u v)⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = ρ k) := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have base := binding_base receipt.binding
  have recordBase : record.output.state.base = receipt.next.base := by rw [receipt.state,base]
  have demand : record.output.state.demand = receipt.next.demand := by rw [receipt.state,stock_bindResults_demand receipt.binding]
  have inv := (stock_lower_record_context run scope events).1
  have rootHeld : ValuesHeld (Demanded receipt.next) event.ctx fr (fun key => ρ (aliasNum result.final.alias key)) := by
    simpa only [ValuesHeld,Demanded,demand] using held
  have bounded := stock_lower_blockScanAliasBounds run event events record records
  have extent : ∀ x r,event.ctx.valueReg? x = some r → x < (scanState record.input record.inst).demand.size := by
    intro x r map
    simpa only [scanState_demands] using (Extent.lower_mapped_demand_bounds run scope events records map).1
  obtain ⟨nx,d,mapX,output,lower,upper,fragment,execution⟩ := stock_cmp_zero32_original_right_selected_source_values
    inv nonzero source clif typeX notConstant defined found data normalized receipt.selected dfg getX getY refines bounded extent rootHeld
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
  have code : record.output.emitted.toList =
      [cmpImm0 .size32 nx,.cset (.vreg d .int) (if nonzero then .ne else .eq)] := by
    rw [receipt.code,boundEq,copiesEq]
    simp only [Array.append_empty]
    have empty := scan_empty record.input record.inst
    have actual := fragment.emitted
    rw [empty] at actual
    simp only [Array.empty_append] at actual
    rw [actual,List.toList_toArray]
  refine ⟨d,receipt.resultRegs.trans rss,?_,?_,?_⟩
  · simpa only [scan_frontier] using lower
  · rw [recordBase]; exact upper
  · intro world
    rw [code]
    exact execution world
/-- Original demanded-and-available source transfer for actual immediate constant
comparison records. The DFG premise retains the original restricted-frame scope;
original values outside availability need not be materialized. -/
theorem stock_lower_cmp_zero32_original_right_available_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} (nonzero : Bool) {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.icmp (if nonzero then .ne else .eq) .i32 x y))
    (typeX : event.ctx.valueType? x = some (.int 32))
    (notConstant : NonConstantSource event.ctx x)
    {constantJ : Nat} {constantInfo : IInfo} {literal : Int}
    (defined : event.ctx.defInst? y = some constantJ) (found : event.ctx.insts[constantJ]? = some constantInfo)
    (data : constantInfo.data = .data 152 35 [.data 151 57 [],.int literal])
    (normalized : u64 literal = 0)
    (results : info.results = [z]) (statementResults : stmt.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV} {u v : BitVec 32}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x .i32 = .ok u)
    (getY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y .i32 = .ok v)
    (held : ValuesHeld (fun value => Demanded record.output.state value ∧ value ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun key => ρ (aliasNum result.final.alias key))) :
    ∃ d,step.results = [[.vreg d .int]] ∧
      record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg ∧
      ∀ world,Runs F isem (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc (if nonzero then .ne else .eq) u v)⟩ (ρ' d) ∧ (∀ k,k ≠ d → ρ' k = ρ k) ∧
          ValuesHeld (fun value => Demanded record.input value ∧ value ∈ availOf f (availIn f result.ctx) bi (j+1))
            event.ctx (withValue fr z ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc (if nonzero then .ne else .eq) u v)⟩)
              (fun key => ρ' (aliasNum result.final.alias key))) := by
  have restrictedHeld : ValuesHeld (Demanded record.output.state) event.ctx
      (restrict fr (availOf f (availIn f result.ctx) bi j)) (fun key => ρ (aliasNum result.final.alias key)) := by
    intro value needed val lookup
    have available := restrict_regs_isSome (by rw [lookup]; rfl)
    rw [restrict_regs_of_mem available] at lookup
    exact held value ⟨needed,available⟩ val lookup
  obtain ⟨d,output,lower,upper,execution⟩ := stock_lower_cmp_zero32_original_right_record_values run scope events records
    nonzero source clif typeX notConstant defined found data normalized results mapped recorded emitted refines dfg getX getY restrictedHeld
  have maps := (stock_lower_record_context run scope events).2.1
  have installed := (stock_lower_record_fresh_result run scope dominated.ssa events records source clif results
    mapped recorded emitted output lower).2
  refine ⟨d,output,lower,upper,?_⟩
  intro world
  exact (execution world).imp (fun ρ' _ _ ⟨value,kept⟩ => by
    refine ⟨value,kept,?_⟩
    intro old required oldVal lookup
    by_cases equal : old = z
    · subst old
      simp only [withValue,eq_self,ite_true] at lookup
      cases lookup
      exact ⟨a,mapped,by change VHolds _ (ρ' (aliasNum result.final.alias a)); rw [installed]; exact value⟩
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
      have different : aliasNum result.final.alias key ≠ d := by omega
      refine ⟨key,map,?_⟩
      change VHolds oldVal (ρ' (aliasNum result.final.alias key))
      rw [kept _ different]
      exact previous)
end Backend.Stock.Proof.ScalarCmp
