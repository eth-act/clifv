import FV.Backend.Lowering.Stock
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.Proof.AcquireTwoDeferredDiagnostic
open Backend.Proof Backend.Proof.Driver

def function : Clif.Function := {
  name := "two_deferred_acquires"
  sig := {
    params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩]
    returns := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩]
    callConv := some .systemV }
  blocks := [{id := 0,params := [(7,.i64),(31,.i64)],body := [
    ⟨[63],.atomicLoad .i8 {} 7⟩,
    ⟨[64],.atomicLoad .i8 {} 31⟩,
    ⟨[100],.extend .uextend .i64 63⟩,
    ⟨[101],.extend .uextend .i64 64⟩],term := .ret [100,101]}]}

#eval (lowerScopeB function,dominatedB function,sigAbiOk function.sig)

#eval (Stock.lower function).toOption.map fun result =>
  result.blockScans.toList.map fun event => event.output.records.map fun record =>
    (record.inst,record.output.step.map (fun step => step.rules.getLast?),
      record.input.color,record.input.entryColor[0]!,record.input.entryColor[1]!)

private def regNumber : Reg → Nat
  | .vreg n _ => n
  | _ => 0

#eval (Stock.lower function).toOption.map fun result =>
  ((result.ctx.valueReg? 7).map regNumber,(result.ctx.valueReg? 31).map regNumber,
    result.code.blocks.toList.map fun block => block.insts.toList.filterMap fun
      | .loadAcquire _ dst address _ => some (regNumber dst,regNumber address)
      | _ => none)

end Backend.Stock.Proof.AcquireTwoDeferredDiagnostic
