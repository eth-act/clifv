import FV.Backend.Proof.StockAcquireFirstFaultOrderDiagnostic
import FV.Backend.Proof.RegallocCover

namespace Backend.Stock.Proof.AcquirePostFaultExtendDiagnostic
open Backend.Proof Backend.Proof.Driver

def function : Clif.Function := {
  name := "acquire_before_unreached_equal_extend"
  sig := {
    params := [⟨.i64,.none,.normal⟩,⟨.i8,.none,.normal⟩]
    returns := [⟨.i64,.none,.normal⟩,⟨.i8,.none,.normal⟩]
    callConv := some .systemV }
  blocks := [{id := 0,params := [(7,.i64),(31,.i8)],body := [
    ⟨[63],.atomicLoad .i8 {} 7⟩,
    ⟨[64],.extend .uextend .i8 31⟩,
    ⟨[100],.extend .uextend .i64 63⟩],term := .ret [100,64]}]}

#eval (lowerScopeB function,dominatedB function,sigAbiOk function.sig)
#eval AcquireInterveningEffectDiagnostic.report function
#eval (Stock.lower function).toOption.map fun result => formsCoveredB ⟨0,0⟩ result.code
#eval AcquireFirstFaultOrderDiagnostic.code function
#eval match Clif.runWith .empty {funcs := [function]} function.name [⟨.i64,0⟩,⟨.i8,0⟩] .empty 20 with
  | .trapped code => some code
  | _ => none
#eval match Clif.initState {funcs := [function]} function.name [⟨.i64,0⟩,⟨.i8,0⟩] .empty with
  | .ok state => match Clif.evalInst state.frame state.mem (.extend .uextend .i8 31) with
    | .stuck message => message
    | _ => "unexpected successful instruction"
  | _ => "entry failure"
#eval ((MInst.extend (.x 2) (.x 1) false 8 8).lines ⟨0,0⟩ {}).map (fun pair => pair.1)

example : FormOk ⟨0,0⟩ (.extend (.vreg 2 .int) (.vreg 1 .int) false 8 8) = true := rfl
example (world : Arm.ArmState) :
    ispec (.extend (.vreg 2 .int) (.vreg 1 .int) false 8 8) [0] world = none := rfl

end Backend.Stock.Proof.AcquirePostFaultExtendDiagnostic
