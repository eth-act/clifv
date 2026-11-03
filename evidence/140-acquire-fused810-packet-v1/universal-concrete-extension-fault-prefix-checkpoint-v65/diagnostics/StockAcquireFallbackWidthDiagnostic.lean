import FV.Backend.Proof.StockAcquirePostFaultExtendDiagnostic

namespace Backend.Stock.Proof.AcquireFallbackWidthDiagnostic
open Backend.Proof Backend.Proof.Driver

def function (signed : Bool) (source target : Clif.Ty) : Clif.Function := {
  name := "acquire_before_unreached_extension"
  sig := {
    params := [⟨.i64,.none,.normal⟩,⟨source,.none,.normal⟩]
    returns := [⟨.i64,.none,.normal⟩,⟨target,.none,.normal⟩]
    callConv := some .systemV }
  blocks := [{id := 0,params := [(7,.i64),(31,source)],body := [
    ⟨[63],.atomicLoad .i8 {} 7⟩,
    ⟨[64],.extend (if signed then .sextend else .uextend) target 31⟩,
    ⟨[100],.extend .uextend .i64 63⟩],term := .ret [100,64]}]}

def assemblyAccepted (signed : Bool) (source target : Clif.Ty) : Bool :=
  match (MInst.extend (.x 2) (.x 1) signed source.width target.width).lines ⟨0,0⟩ {} with
  | .error _ => false
  | .ok (lines,_) => lines.all fun
    | .ins instruction _ => (instruction.armFields env0).toOption.isSome
    | _ => false

def report (signed : Bool) (source target : Clif.Ty) :=
  let f := function signed source target
  (signed,source,target,lowerScopeB f,dominatedB f,sigAbiOk f.sig,
    (Stock.lower f).toOption.map (fun result =>
      (formsCoveredB ⟨0,0⟩ result.code,result.blockScans.toList.flatMap fun event =>
        event.output.records.reverse.map fun record => record.output.step.map (fun step => step.rules.getLast?))),
    assemblyAccepted signed source target)

#eval [false,true].flatMap fun signed => ([Clif.Ty.i8,.i16,.i32,.i64].flatMap fun source =>
  [Clif.Ty.i8,.i16,.i32,.i64].map fun target => report signed source target)

end Backend.Stock.Proof.AcquireFallbackWidthDiagnostic
