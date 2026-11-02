import FV.Backend.Proof.StockAcquire810Witness

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Stock.lower

def acquireInstruction : MInst := .loadAcquire (.int 8) (.vreg 195 .int) (.vreg 192 .int) {}
def completeCode : Array MInst := #[.args [(.vreg 192 .int,.x 0)],acquireInstruction,.rets [(.vreg 195 .int,.x 0)]]

private def facts (result : Stock.Result) : Bool :=
  decide (result.ctx.valueReg? 1 = some (.vreg 192 .int) ∧
    result.ctx.valueReg? 0 = some (.vreg 193 .int) ∧
    result.ctx.valueReg? 2 = some (.vreg 194 .int) ∧
    (result.final.alias[194]?).join = some 195) &&
  (result.code.blocks[0]?).any (fun block => decide (block.insts = completeCode)) &&
  result.blockScans.toList.any fun event => decide (event.block = 0) &&
    event.output.records.any fun consumer => decide (consumer.inst = 1) &&
      decide (consumer.output.emitted = #[acquireInstruction]) &&
      consumer.output.state.sunk[0]! &&
      consumer.output.step.any (fun step => decide (step.decision = .emitted ∧
        step.results = [[.vreg 195 .int]] ∧ step.rules.getLast? = some 810)) &&
      event.output.records.any (fun producer => decide (producer.inst = 0) &&
        decide (producer.output.emitted = #[]) && producer.input.sunk[0]! &&
        decide (producer.input.demand[0]! = 0) &&
        producer.output.step.any (fun step => decide (step.decision = .sunk)))

private def observed : Option Bool := (Stock.lower function).toOption.map facts
private theorem observed_true : observed = some true := by native_decide -- witness: native_decide

/-- Actual source records derive the deferred producer, exact fresh result and final alias.
The complete code is the original Stock result, including its real ABI entry and return. -/
theorem actual_record_binding {result : Stock.Result} (lowered : Stock.lower function = .ok result) :
    (result.ctx.valueReg? 1 = some (.vreg 192 .int) ∧
      result.ctx.valueReg? 0 = some (.vreg 193 .int) ∧
      result.ctx.valueReg? 2 = some (.vreg 194 .int) ∧
      (result.final.alias[194]?).join = some 195) ∧
    (∃ block,result.code.blocks[0]? = some block ∧ block.insts = completeCode) ∧
    ∃ event ∈ result.blockScans.toList,event.block = 0 ∧
      ∃ consumer ∈ event.output.records,consumer.inst = 1 ∧
        consumer.output.emitted = #[acquireInstruction] ∧ consumer.output.state.sunk[0]! = true ∧
        (∃ step,consumer.output.step = some step ∧ step.decision = .emitted ∧
          step.results = [[.vreg 195 .int]] ∧ step.rules.getLast? = some 810) ∧
        ∃ producer ∈ event.output.records,producer.inst = 0 ∧
          producer.output.emitted = #[] ∧ producer.input.sunk[0]! = true ∧
          producer.input.demand[0]! = 0 ∧
          ∃ step,producer.output.step = some step ∧ step.decision = .sunk := by
  have checked := observed_true
  unfold observed at checked
  rw [lowered] at checked
  have yes := Option.some.inj checked
  simpa only [facts,Bool.and_eq_true,decide_eq_true_eq,List.any_eq_true,Option.any_eq_true,and_assoc] using yes

end Backend.Stock.Proof.Acquire810
