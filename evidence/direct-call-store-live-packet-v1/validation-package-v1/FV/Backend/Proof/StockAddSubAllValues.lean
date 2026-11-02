import FV.Backend.Proof.StockAluSelectedValues
import FV.Backend.Proof.StockMulFusedRecordValues
import FV.Backend.Proof.StockAddSubDispatch
import FV.Backend.Proof.StockAddSubRecordValues
namespace Backend.Stock.Proof.ScalarAddSub
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
/-- Actual first-match source opcode dispatch covers every add/subtract rule:
base, multiply fusion and all twelve immediate/shift/extend variants. No rule
ID, chosen-root or match certificate is an extra premise. -/
theorem stock_lower_addsub_available_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (subtract : Bool) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u v : BitVec ty.width}
    (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    (getY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩ (ρ' record.input.base.nextVreg) ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          (withValue fr z ⟨ty,Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩)
          (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have inv := (stock_lower_record_context run scope events).1
  have member := stock_addsub_selected_rule_ids inv subtract source clif receipt.selected
  have availableX := restrict_regs_isSome (by rw [getAs_ok getX]; rfl)
  have availableY := restrict_regs_isSome (by rw [getAs_ok getY]; rfl)
  have originalX : fr.getAs x ty = .ok u :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := x) (ty := ty) (restrict_regs_of_mem availableX)).symm.trans getX
  have originalY : fr.getAs y ty = .ok v :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := y) (ty := ty) (restrict_regs_of_mem availableY)).symm.trans getY
  cases subtract
  · simp only [Bool.false_eq_true,ite_false,ite_true,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with id595 | id597 | id596 | id598 | id590 | id589 | id592 | id591 | id594 | id593 | id588
    · have last : step.rules.getLast? = some 595 := by
        rw [receipt.rules,receipt.selected.last_rule,id595]
      exact stock_lower_addsub_fused_available_values run scope dominated events records block statement current
        .shifted false false (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 597 := by
        rw [receipt.rules,receipt.selected.last_rule,id597]
      exact ScalarMul.Fused.stock_lower_mul_fused_available_values run scope dominated events records
        block statement current .addRight source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 596 := by
        rw [receipt.rules,receipt.selected.last_rule,id596]
      exact stock_lower_addsub_fused_available_values run scope dominated events records block statement current
        .shifted false true (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 598 := by
        rw [receipt.rules,receipt.selected.last_rule,id598]
      exact ScalarMul.Fused.stock_lower_mul_fused_available_values run scope dominated events records
        block statement current .addLeft (x := y) (y := x) source clif results statementResults mapped recorded emitted last refines dfg held getY getX
    · have last : step.rules.getLast? = some 590 := by
        rw [receipt.rules,receipt.selected.last_rule,id590]
      exact stock_lower_addsub_fused_available_values run scope dominated events records block statement current
        .immediate false true (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 589 := by
        rw [receipt.rules,receipt.selected.last_rule,id589]
      exact stock_lower_addsub_fused_available_values run scope dominated events records block statement current
        .immediate false false (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 592 := by
        rw [receipt.rules,receipt.selected.last_rule,id592]
      exact stock_lower_addsub_fused_available_values run scope dominated events records block statement current
        .negative false true (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 591 := by
        rw [receipt.rules,receipt.selected.last_rule,id591]
      exact stock_lower_addsub_fused_available_values run scope dominated events records block statement current
        .negative false false (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 594 := by
        rw [receipt.rules,receipt.selected.last_rule,id594]
      exact stock_lower_addsub_fused_available_values run scope dominated events records block statement current
        .extended false true (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 593 := by
        rw [receipt.rules,receipt.selected.last_rule,id593]
      exact stock_lower_addsub_fused_available_values run scope dominated events records block statement current
        .extended false false (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 588 := by
        rw [receipt.rules,receipt.selected.last_rule,id588]
      exact stock_lower_alu_selected_values run scope dominated events records block statement current false
        source clif results statementResults mapped recorded emitted last refines held originalX originalY
  · simp only [Bool.false_eq_true,ite_false,ite_true,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with id747 | id748 | id599 | id746 | id749 | id745
    · have last : step.rules.getLast? = some 747 := by
        rw [receipt.rules,receipt.selected.last_rule,id747]
      exact stock_lower_addsub_fused_available_values run scope dominated events records block statement current
        .negative true false (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 748 := by
        rw [receipt.rules,receipt.selected.last_rule,id748]
      exact stock_lower_addsub_fused_available_values run scope dominated events records block statement current
        .extended true false (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 599 := by
        rw [receipt.rules,receipt.selected.last_rule,id599]
      exact ScalarMul.Fused.stock_lower_mul_fused_available_values run scope dominated events records
        block statement current .subRight source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 746 := by
        rw [receipt.rules,receipt.selected.last_rule,id746]
      exact stock_lower_addsub_fused_available_values run scope dominated events records block statement current
        .immediate true false (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 749 := by
        rw [receipt.rules,receipt.selected.last_rule,id749]
      exact stock_lower_addsub_fused_available_values run scope dominated events records block statement current
        .shifted true false (by simp) source clif results statementResults mapped recorded emitted last refines dfg held getX getY
    · have last : step.rules.getLast? = some 745 := by
        rw [receipt.rules,receipt.selected.last_rule,id745]
      exact stock_lower_alu_selected_values run scope dominated events records block statement current true
        source clif results statementResults mapped recorded emitted last refines held originalX originalY
end Backend.Stock.Proof.ScalarAddSub
