import FV.Backend.Proof.StockDemandExtent
import FV.Backend.Proof.StockCastBaseValues
import FV.Backend.Proof.StockGuardedRecordValues
namespace Backend.Stock.Proof.ScalarCast
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
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

private theorem renamed_defs (aliases : Array (Option Nat)) (m : MInst) :
    vdefs (m.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))) = (vdefs m).map (aliasNum aliases) := by
  have aliasRenaming : VRenaming (Backend.lowerFunction.resolve aliases (aliases.size+1)) (aliasNum aliases) := by
    refine ⟨fun n c => resolve_vreg aliases _ n c,?_⟩
    intro r notVirtual
    cases r with
    | vreg n c => exact False.elim (notVirtual n c rfl)
    | _ => simp [Backend.lowerFunction.resolve]
  unfold vdefs
  rw [operands_mapRegs aliasRenaming]
  cases m.operands with
  | error e => rfl
  | ok ops =>
    simp only [Except.map,Array.toList_map]
    rw [filter_map_rn _ Operand.isDef (fun _ => rfl)]
    simp only [List.map_map]
    rfl

/-- Actual base zero/sign-extension records establish the original source value
and demanded/available post-frame. The widening guard is the original successful
source-evaluation condition, not an additional accepted-program certificate. -/
theorem stock_lower_extend_available_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt} (block : f.blocks[bi]? = some b)
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi + j)
    (sg : Bool) {info : IInfo} {x z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.extend (extendOp sg) ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (extendRule sg).id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j))) {ρ : Nat → CV}
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧ v ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {val : Clif.Val} (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).regs x = some val)
    (grows : val.ty.width < ty.width) :
    ∃ (d : Nat) (ρ' : Nat → CV),step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,extendBits sg ty.width val.bits⟩ (ρ' d) ∧
      (∀ n,n < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ n → ρ' n = ρ n) ∧
      ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx
        (withValue fr z ⟨ty,extendBits sg ty.width val.bits⟩) (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have last : receipt.fired.getLast? = some (extendRule sg).id := by rw [← receipt.rules]; exact selectedId
  have idEq := Option.some.inj (receipt.selected.last_rule.symm.trans last)
  have candidate : extendRule sg ∈ program.rulesOf T.lower.id := by
    cases sg <;> rw [extendRule,show T.lower.id = 686 from rfl,data_program.r686] <;> decide +kernel
  have chosen := eq_of_mem_of_id lower_ids_nodup receipt.selected.rule_mem candidate idEq
  have boundBase := binding_base receipt.binding
  have recordBase : record.output.state.base = receipt.next.base := by rw [receipt.state,boundBase]
  have demand : record.output.state.demand = receipt.next.demand := by rw [receipt.state,stock_bindResults_demand receipt.binding]
  have maps := (stock_lower_record_context run scope events).2.1
  have restrictedHeld : ValuesHeld (Demanded receipt.next) event.ctx
      (restrict fr (availOf f (availIn f result.ctx) bi j)) (fun k => ρ (aliasNum result.final.alias k)) := by
    intro v needed value lookup
    have available := restrict_regs_isSome (by rw [lookup]; rfl)
    rw [restrict_regs_of_mem available] at lookup
    exact held v ⟨by simpa only [Demanded,demand] using needed,available⟩ value lookup
  have bounded := stock_lower_blockScanAliasBounds run event events record records
  have extent : ∀ v r,event.ctx.valueReg? v = some r → v < (scanState record.input record.inst).demand.size := by
    intro v r map
    simpa only [scanState_demands] using (Extent.lower_mapped_demand_bounds run scope events records map).1
  obtain ⟨ρ',output,nextEq,execution,value,kept⟩ := stock_extend_selected_values
    (stock_lower_record_context run scope events).1 sg source clif refines dfg getX grows
    receipt.selected chosen bounded extent restrictedHeld
  let d := (scanState record.input record.inst).base.nextVreg
  have fresh : record.input.base.nextVreg ≤ d := by simpa only [d,scan_frontier] using Nat.le_refl record.input.base.nextVreg
  have high : record.output.state.base.nextVreg = d+1 := by rw [recordBase,nextEq]; rfl
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
  let m : MInst := .extend (.vreg d .int) ((event.ctx.valueReg? x).getD .xzr) sg val.ty.width ty.width
  have recordCode : record.output.emitted.toList = [m] := by
    rw [receipt.code,boundEq,copiesEq,nextEq]
    simp [m,d,State.mark,LState.fresh,LState.emit,scan_empty]
  have recordExec : PRun F isem (record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' := by
    rw [recordCode]; exact execution
  refine ⟨d,ρ',receipt.resultRegs.trans rss,⟨fresh,by rw [high]; omega⟩,recordExec,value,?_,?_⟩
  · intro n outside
    apply kept
    rw [high] at outside
    have start : record.input.base.nextVreg = d := by simp only [d,scan_frontier]
    rw [start] at outside
    omega
  · intro v required oldVal lookup
    by_cases equal : v = z
    · subst v
      simp only [withValue,eq_self,ite_true] at lookup
      cases lookup
      have installedFinal := (stock_lower_record_fresh_result run scope dominated.ssa events records source clif results mapped recorded emitted
        (receipt.resultRegs.trans rss) fresh).2
      exact ⟨a,mapped,by change VHolds _ (ρ' (aliasNum result.final.alias a)); rw [installedFinal]; exact value⟩
    · simp only [withValue,ite_eq_right equal] at lookup
      have before := available_before_of_after_not_result block statement required.2
        (by simpa only [statementResults,List.mem_singleton] using equal)
      have needed : Demanded record.output.state v := by
        intro zero
        have count := stock_lower_record_demand_mono run events records recorded emitted v
        change record.output.state.demand[v]! = 0 at zero
        rw [zero] at count
        exact required.1 (Nat.eq_zero_of_le_zero count)
      obtain ⟨key,map,old⟩ := held v ⟨needed,before⟩ oldVal lookup
      have outside := stock_lower_available_alias_outside_record run scope dominated events records block statement current before
        (by rw [← maps]; exact map)
      refine ⟨key,map,?_⟩
      change VHolds oldVal (ρ' (aliasNum result.final.alias key))
      rw [kept _ (by
        have start : record.input.base.nextVreg = d := by simp only [d,scan_frontier]
        rw [high,start] at outside
        omega)]
      exact old
end Backend.Stock.Proof.ScalarCast
