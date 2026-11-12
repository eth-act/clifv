import FV.E2E.PreparedReturnPinSretWitness

/-! # A `try_call` that uses its exception payload, of a Stock-route `sret` function (#1003)

The shape that kept two of the survey's executables (`b_slices` and `e_option_result`, test
`values`) out of the return-pin route: the caller's `try_call` passes `exn0` to its landing pad,
so its definitions are the payload register x0 (the callee declares no result); the callee is
an `sret` function compiled by the Stock route, whose only return pin is x8 (the struct
pointer). Comparing all the call's definitions with the callee's return pins (the check before
#1003) rejects the call; a linked call supplies the declared results only, here none
(`LinkSys.progXWithPins`), which is what `LinkSys.returnPinSiteB` checks since #1003. -/

namespace E2E.ReturnPinPayloadWitness
open Backend E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def callerText : String := "function %payload_caller(i64, i64) -> i64 system_v {\n    sig0 = (i64 sret, i64) system_v\n    fn0 = colocated %_RNxC7fv_demo11HawPMC3YC2b(i64 sret, i64) system_v\nblock0(v0: i64, v1: i64):\n    try_call fn0(v0, v1), sig0, block1, [ tag0: block2(exn0) ]\nblock1:\n    v2 = iconst.i64 0\n    return v2\nblock2(v3: i64):\n    return v3\n}\n"

/-- The captured `sret` function of `PreparedReturnPinSretWitness` and a caller that reaches it
through a `try_call` whose landing pad takes the exception payload. -/
def input : LinkInput := {PreparedReturnPinSretWitness.input with
  funcs := PreparedReturnPinSretWitness.input.funcs ++ [{clif := callerText,ra := "null"}],
  addrs := PreparedReturnPinSretWitness.input.addrs ++ [("payload_caller",12288)]}

def outputs (cleanup : Bool) : Res :=
  input.resultsProductionWith Stock.MemorySretCopy.lowerValidated cleanup

/-- The `sret` function (Stock route). -/
def callee : Clif.Function := input.funcs[0]!.func

/-- Its caller (`lowerFunction`). -/
def caller : Clif.Function := input.funcs[1]!.func

/-- The registers each call and try-call of `vc` defines, in instruction order. -/
def callDefRegs (vc : VCode) : List (List Reg) :=
  vc.blocks.toList.flatMap fun block => block.insts.toList.filterMap fun
    | .call info => some (info.defs.map (·.1))
    | .tryCall info _ => some (info.defs.map (·.1))
    | _ => none

/-- The site check before #1003 on the caller's calls of `callee`: all the call's definitions
against the callee's return pins. -/
def allDefsCheck (cleanup : Bool) : Bool :=
  allInsts (artOf (outputs cleanup) caller).vcp (siteB fun info =>
    ReturnPinCheck.check info.defs callee (artOf (outputs cleanup) callee).vc)

private def shape (cleanup : Bool) : Bool :=
  okRReturnPins (productionStage cleanup) input (outputs cleanup) &&
  returnPinChecks input (outputs cleanup) caller &&
  decide (callDefRegs (artOf (outputs cleanup) caller).vcp = [[.x 0]]) &&
  decide (ReturnPinCheck.pins callee (artOf (outputs cleanup) callee).vc = [.x 8]) &&
  decide (callee.sig.returns.length = 0) &&
  !allDefsCheck cleanup

attribute [local irreducible] shape
-- witness: native_decide (the two fixed complete mixed programs only)
private theorem shape_true : (shape false && shape true) = true := by native_decide

/-- **The shape of #1003 passes the return-pin checks.** The caller's only call defines x0, the
exception payload; the callee declares no result and returns its struct pointer in x8; the
check of all the call's definitions against the callee's pins fails (`allDefsCheck`, the verdict
before #1003), and the program passes `okRReturnPins`, whose scan reads the call's results. -/
theorem payload_try_call_accepted (cleanup : Bool) :
    okRReturnPins (productionStage cleanup) input (outputs cleanup) = true ∧
      returnPinChecks input (outputs cleanup) caller = true ∧
      callDefRegs (artOf (outputs cleanup) caller).vcp = [[.x 0]] ∧
      ReturnPinCheck.pins callee (artOf (outputs cleanup) callee).vc = [.x 8] ∧
      callee.sig.returns.length = 0 ∧
      allDefsCheck cleanup = false := by
  have both := Bool.and_eq_true_iff.mp shape_true
  have checked : shape cleanup = true := by
    cases cleanup with
    | false => exact both.1
    | true => exact both.2
  simpa only [shape,Bool.and_eq_true,and_assoc,decide_eq_true_eq,Bool.not_eq_true'] using checked

/-- The program statement of the return-pin route holds for the caller: the mixed program is
inside the route's theorem. -/
theorem program_correct (cleanup : Bool) :
    CrateStmtReturnPins input (outputs cleanup) "payload_caller" :=
  preparedReturnPins_correct (productionStage cleanup) (productionStage_cases cleanup)
    (input.resultsProductionWith_prepared Stock.MemorySretCopy.lowerValidated cleanup)
    (payload_try_call_accepted cleanup).1 _

end E2E.ReturnPinPayloadWitness
