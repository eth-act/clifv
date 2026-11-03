import FV.Backend.Lowering.Stock
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.Proof.AcquireInterveningEffectDiagnostic
open Backend.Proof Backend.Proof.Driver

def function (middle : Clif.Inst) : Clif.Function := {
  name := "acquire_intervening_effect"
  sig := {
    params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩]
    returns := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩]
    callConv := some .systemV }
  blocks := [{id := 0,params := [(7,.i64),(31,.i64)],body := [
    ⟨[63],.atomicLoad .i8 {} 7⟩,
    ⟨[64],middle⟩,
    ⟨[100],.extend .uextend .i64 63⟩],term := .ret [100,64]}]}

def division := function (.div .udiv .i64 7 31)
def trappingLoad := function (.load .load .i64 {} 31 0)
def unmarkedLoad := function (.load .load .i64 {trapCode := none} 31 0)

def report (f : Clif.Function) :=
  let lowered := (Stock.lower f).map fun result =>
    let records := result.blockScans.toList.map fun event =>
      event.output.records.reverse.map fun record =>
        (record.inst,record.output.step.map (fun step => (step.decision,step.rules.getLast?)),
         record.output.emitted.toList)
    let code := result.code.blocks.toList.map fun block => block.insts.toList
    (records,code)
  ((lowerScopeB f,dominatedB f,sigAbiOk f.sig),lowered)

#eval report division
#eval report trappingLoad
#eval report unmarkedLoad

end Backend.Stock.Proof.AcquireInterveningEffectDiagnostic
