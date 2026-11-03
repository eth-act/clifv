import FV.Backend.Proof.StockAcquireInterveningEffectDiagnostic
import FV.Backend.Proof.StockAcquireTwoDeferredDiagnostic

namespace Backend.Stock.Proof.AcquireFirstFaultOrderDiagnostic
open Backend.Proof Backend.Proof.Driver

def codeTag : MInst → String
  | .loadAcquire .. => "acquire"
  | .load .. => "load"
  | .trapIf .. => "trapIf"
  | .aluRRR .. => "alu"
  | .extend .. => "extend"
  | .args .. => "args"
  | .rets .. => "rets"
  | _ => "other"

def guards (f : Clif.Function) (producer consumer value : Nat) :=
  (Stock.lower f).toOption.map fun result =>
    result.blockScans.toList.flatMap fun event =>
      event.output.records.filterMap fun record =>
        if record.inst == consumer then
          let state := scanState record.input record.inst
          some (record.input.entryColor[producer]!,state.color,Stock.source event.ctx state value,
            record.output.step.map (fun step => step.rules.getLast?))
        else none

def code (f : Clif.Function) :=
  (Stock.lower f).toOption.map fun result =>
    result.code.blocks.toList.map fun block => block.insts.toList.map codeTag

def sourceFault (f : Clif.Function) : Option Clif.TrapCode :=
  match Clif.runWith .empty {funcs := [f]} f.name [⟨.i64,0⟩,⟨.i64,0⟩] .empty 20 with
  | .trapped code => some code
  | _ => none

#eval guards AcquireInterveningEffectDiagnostic.division 0 2 63
#eval guards AcquireInterveningEffectDiagnostic.trappingLoad 0 2 63
#eval guards AcquireInterveningEffectDiagnostic.unmarkedLoad 0 2 63
#eval code AcquireInterveningEffectDiagnostic.division
#eval code AcquireInterveningEffectDiagnostic.trappingLoad
#eval code AcquireInterveningEffectDiagnostic.unmarkedLoad
#eval sourceFault AcquireInterveningEffectDiagnostic.division
#eval sourceFault AcquireInterveningEffectDiagnostic.trappingLoad
#eval sourceFault AcquireInterveningEffectDiagnostic.unmarkedLoad
#eval guards AcquireTwoDeferredDiagnostic.function 0 2 63
#eval guards AcquireTwoDeferredDiagnostic.function 1 3 64
#eval code AcquireTwoDeferredDiagnostic.function
#eval sourceFault AcquireTwoDeferredDiagnostic.function

end Backend.Stock.Proof.AcquireFirstFaultOrderDiagnostic
