import FV.Backend.Proof.IselCtlRuleIds
import FV.Backend.Proof.StockMemoryIntegerLoadSelection
import FV.Backend.Proof.StockSelectionReceipts

namespace Backend.Stock.Memory.IntegerRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def Width.sourceTy : Width → Clif.Ty
  | .w8 => .i8 | .w16 => .i16 | .w32 => .i32 | .w64 => .i64

private theorem sem_i8 (ctx : Ctx) :
    (Stock.sem ctx).prim 14 "I8" = some (.ty (.int 8)) := rfl
private theorem sem_i16 (ctx : Ctx) :
    (Stock.sem ctx).prim 14 "I16" = some (.ty (.int 16)) := rfl
private theorem sem_i64 (ctx : Ctx) :
    (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl

private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty t k : Nat) (fs : List V) :
    (Stock.sem ctx).unData ty (.data t k fs) = if t = ty then some (k,fs) else none :=
  Backend.Proof.sem_unData ctx ty t k fs
private theorem sem_i32 (ctx : Ctx) :
    (Stock.sem ctx).prim 14 "I32" = some (.ty (.int 32)) := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl

/-- The actual memory root matches the original load data, retaining the entire
Stock state and binding the source pointer and flags in its typed environment. -/
theorem stock_match_integer_load {p : Program} (hp : Data p) (width : Width) (ctx : Ctx) {cfg : Config}
    {i x : Nat} {info : IInfo} {flags : Clif.MemFlags}
    (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int width.bits))
    (data : info.data = .data 152 16 [.data 151 29 [],.value x,.op (.memFlags flags),.int 0])
    (little : flags.endianness ≠ some .big) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) cfg (n+2) width.root [.inst i]).run (st,tr) =
      .ok (some (env3 (.value x) (.op (.memFlags flags)) (.int 0)),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have endian := (ext_little_or_native_endian_iff ctx st.base flags [.op (.memFlags flags)]).mpr ⟨little,rfl⟩
  cases width <;> simp only [Width.bits,Width.root] at * <;> cases hp <;>
    isel_eval [*,rule_lower_2604,rule_lower_2607,rule_lower_2610,rule_lower_2613,
      sem_extract,sem_unData,sem_i8,sem_i16,sem_i32,sem_i64,sem_eq]

section SourceData
attribute [local semireducible] Isle.Aarch64.program
theorem integer_load_source_data (width : Width) {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {flags : Clif.MemFlags}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.load .load width.sourceTy flags x 0)) :
    flags.endianness ≠ some .big ∧
      info.data = .data 152 16 [.data 151 29 [],.value x,.op (.memFlags flags),.int 0] ∧
      info.resTys.head? = some (.int width.bits) := by
  have data := inv.data i info _ source clif
  have little : flags.endianness ≠ some .big := by
    intro big
    cases width <;> simp [Width.sourceTy,instData,eTy,big] at data
  have shape : instData f (.load .load width.sourceTy flags x 0) =
      .ok (.data 152 16 [.data 151 29 [],.value x,.op (.memFlags flags),.int 0]) := by
    cases width <;>
      change (if flags.endianness == some .big then Except.error "big-endian load" else
      Except.ok (V.data 152 16 [.data 151 29 [],.value x,.op (.memFlags flags),.int 0])) = _
    all_goals
      rw [show (flags.endianness == some .big) = false from by simpa using little]
      rfl
  obtain ⟨types,typed,resTys,length⟩ := inv.resTys i info _ source clif
  change some [width.sourceTy] = some types at typed
  cases typed
  exact ⟨little,Except.ok.inj (data.symm.trans shape),by rw [resTys]; cases width <;> rfl⟩
end SourceData

/-- A retained actual root ID and original source metadata derive all typed
match/RHS/named-root receipts. The caller supplies no separate execution certificate. -/
theorem stock_lower_integer_load_selected_receipts (width : Width) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {x : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.load .load width.sourceTy flags x 0))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some width.root.id) :
    flags.endianness ≠ some .big ∧
      ∃ (out : V) (next : State) (trace : List RuleId) (rhsTrace : Array RuleId),
        Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
          .ok (some out,next,trace) ∧
        (evalExpr program (Stock.sem event.ctx) {} 999999 width.root.rhs
          (env3 (.value x) (.op (.memFlags flags)) (.int 0))).run
          (scanState record.input record.inst,#[]) = .ok (some out,next,rhsTrace) := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have member : width.root ∈ program.rulesOf T.lower.id := by
    cases width <;> rw [show T.lower.id = 686 from rfl,data_program.r686]
    all_goals decide +kernel
  have last : receipt.fired.getLast? = some width.root.id := by
    rw [← receipt.rules]
    exact selectedId
  have idEq := Option.some.inj (receipt.selected.last_rule.symm.trans last)
  have ruleEq := eq_of_mem_of_id lower_ids_nodup receipt.selected.rule_mem member idEq
  obtain ⟨little,data,type⟩ := integer_load_source_data width (stock_lower_record_context run scope events).1 source clif
  have bound : (program.rulesOf T.lower.id).length ≤ 999995 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]
    decide +kernel
  have fuelBound := receipt.selected.fuelBound
  have enough : 2 ≤ receipt.selected.matchFuel := by omega
  obtain ⟨n,fuelEq⟩ : ∃ n,receipt.selected.matchFuel = n+2 := ⟨receipt.selected.matchFuel-2,by omega⟩
  have actualMatch := receipt.selected.matchedRun
  rw [ruleEq,fuelEq] at actualMatch
  have expected := stock_match_integer_load data_program width event.ctx (cfg := {}) source type data little
    (scanState record.input record.inst) #[] n
  have same := Except.ok.inj (actualMatch.symm.trans expected)
  have envEq := Option.some.inj (congrArg Prod.fst same)
  have stateEq := congrArg (fun q => q.2.1) same
  have traceEq := congrArg (fun q => q.2.2) same
  change receipt.selected.matched = scanState record.input record.inst at stateEq
  change receipt.selected.matchTrace = #[] at traceEq
  have evaluated := receipt.selected.rhsRun
  rw [ruleEq,envEq,stateEq,traceEq] at evaluated
  exact ⟨little,receipt.out,receipt.next,receipt.fired,receipt.selected.rhsTrace,receipt.rootRun,evaluated⟩

end Backend.Stock.Memory.IntegerRoots
