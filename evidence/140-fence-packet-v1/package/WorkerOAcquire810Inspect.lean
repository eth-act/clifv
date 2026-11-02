import FV.Backend.Proof.StockAcquire810Witness
open Backend Backend.Stock Backend.Stock.Proof
#eval match Stock.lower Acquire810.function with
  | .error error => IO.println error
  | .ok result => do
    IO.println s!"mapped pointer: {reprStr (result.ctx.valueReg? 1)}; producer: {reprStr (result.ctx.valueReg? 0)}; consumer: {reprStr (result.ctx.valueReg? 2)}"
    for event in result.blockScans do
      for record in event.output.records do
        IO.println s!"record {record.inst}: emitted={reprStr record.output.emitted}; sunk0={record.input.sunk[0]!}; demand0={record.input.demand[0]!}; color={reprStr record.input.color}; aliases={reprStr record.output.state.alias}"
        if let some step := record.output.step then
          IO.println s!"decision={reprStr step.decision}; outputs={reprStr step.results}; rules={reprStr step.rules}; fresh={step.before.base.nextVreg}->{step.after.base.nextVreg}"
    for block in result.code.blocks do
      IO.println s!"actual code: {reprStr block.insts}"
