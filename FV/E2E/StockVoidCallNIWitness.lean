import FV.E2E.StockVoidCallNI
import FV.E2E.StockVoidCallWitness
import FV.Backend.LinearScan

namespace E2E.VoidCallMachineWitness
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private structure Data (cleanup : Bool) where
  result : Stock.Result
  prepared : VCode
  allocated : RFunc
  frame : AFunc
  assembly : FnAsm
  binary : FnBin
  lowered : Stock.lower VoidCallViewWitness.caller = .ok result
  source : Stock.VoidCall.NI.check VoidCallViewWitness.caller result.code = true
  preparedRun : Backend.prepare (Stock.Arithmetic.stage cleanup result.code) = .ok prepared
  prepOk : prepCheck (Stock.Arithmetic.stage cleanup result.code) prepared = true
  checkRun : checkAlloc prepared allocated = .ok ()
  allocRun : lowerRFunc prepared allocated = .ok frame
  emitRun : emitFunc 0 frame = .ok assembly
  layoutRun : assembly.layout = .ok binary
  covered : FormsCovered ⟨assembly.k,frame.slotBase⟩ prepared
  noTry : result.code.hasTryCall = false

private def candidate (cleanup : Bool) : Except String (Data cleanup) :=
  match lowered : Stock.lower VoidCallViewWitness.caller with
  | .error message => .error message
  | .ok result =>
    if source : Stock.VoidCall.NI.check VoidCallViewWitness.caller result.code = true then
      match preparedRun : Backend.prepare (Stock.Arithmetic.stage cleanup result.code) with
      | .error message => .error message
      | .ok prepared =>
        if prepOk : prepCheck (Stock.Arithmetic.stage cleanup result.code) prepared = true then
          match allocatedRun : leanAlloc prepared with
          | .error message => .error message
          | .ok allocated =>
            match checkRun : checkAlloc prepared allocated with
            | .error message => .error message
            | .ok () =>
              match allocRun : lowerRFunc prepared allocated with
              | .error message => .error message
              | .ok frame =>
                match emitRun : emitFunc 0 frame with
                | .error message => .error message
                | .ok assembly =>
                  match layoutRun : assembly.layout with
                  | .error message => .error message
                  | .ok binary =>
                    if covered : formsCoveredB ⟨assembly.k,frame.slotBase⟩ prepared = true then
                      .ok ⟨result,prepared,allocated,frame,assembly,binary,lowered,source,
                        preparedRun,prepOk,checkRun,allocRun,emitRun,layoutRun,
                        (formsCoveredB_iff _ _).mp covered,
                        Stock.VoidCall.NI.noTryCall_of_codeCheck (Bool.and_eq_true_iff.mp source).2⟩
                    else .error "forms are not covered"
        else .error "prepare check rejected"
    else .error "source admission rejected"

private theorem candidates_ok : ((candidate false).isOk && (candidate true).isOk) = true := by
  native_decide

/-- Both real cleanup modes inhabit every static premise of the complete machine theorem. -/
theorem compiled_caller (cleanup : Bool) :
    ∃ (result : Stock.Result) (prepared : VCode) (allocated : RFunc) (frame : AFunc)
      (assembly : FnAsm) (binary : FnBin),
      Stock.VoidCall.NI.check VoidCallViewWitness.caller result.code = true ∧
      CompiledStockArithmeticStage VoidCallViewWitness.caller cleanup 0 result prepared allocated frame assembly binary ∧
      result.code.hasTryCall = false ∧ FormsCovered ⟨assembly.k,frame.slotBase⟩ prepared := by
  have available : (candidate cleanup).isOk = true := by
    have both := Bool.and_eq_true_iff.mp candidates_ok
    cases cleanup with
    | false => exact both.1
    | true => exact both.2
  cases found : candidate cleanup with
  | error message => rw [found] at available; cases available
  | ok d =>
    exact ⟨d.result,d.prepared,d.allocated,d.frame,d.assembly,d.binary,d.source,
      ⟨d.lowered,d.preparedRun,d.prepOk,d.checkRun,d.allocRun,d.emitRun,d.layoutRun⟩,d.noTry,d.covered⟩

end E2E.VoidCallMachineWitness


namespace E2E.VoidCallPairedWitness
open Backend Backend.Proof Backend.Proof.Driver LinkCheck
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- Additional fixture. The original captured caller remains unchanged. -/
def stackCaller : Clif.Function :=
  let original := VoidCallViewWitness.caller
  {original with
    name := "stock_void_stack_caller"
    sig := {original.sig with params := List.replicate 9 ⟨.i64,.none,.normal⟩}
    blocks := [{original.blocks[0]! with
      params := (List.range 9).map (fun i => (i,Clif.Ty.i64))
      body := [⟨[],.call 0 [0,8]⟩]
      term := .ret []}]}

private def checked (f : Clif.Function) : Bool := match Stock.lower f with
  | .error _ => false
  | .ok result => Stock.VoidCall.check f result.code && Stock.VoidCall.NI.codeCheck f.sig result.code
attribute [local irreducible] checked
-- witness: native_decide (the original caller and one additional consumed-stack-argument fixture)
private theorem checked_true : (checked VoidCallViewWitness.caller && checked stackCaller) = true := by
  native_decide

/-- The unchanged caller and an actually consumed stack argument satisfy the finite read boundary. -/
theorem caller_boundaries (f : Clif.Function)
    (member : f = VoidCallViewWitness.caller ∨ f = stackCaller) :
    ∃ result,Stock.lower f = .ok result ∧ Stock.VoidCall.check f result.code = true ∧
      Stock.VoidCall.NI.codeCheck f.sig result.code = true ∧ result.code.hasTryCall = false := by
  have both := Bool.and_eq_true_iff.mp checked_true
  have accepted : checked f = true := by
    rcases member with rfl | rfl
    · exact both.1
    · exact both.2
  unfold checked at accepted
  cases lowered : Stock.lower f with
  | error message => simp only [lowered,Bool.false_eq_true] at accepted
  | ok result =>
    simp only [lowered,Bool.and_eq_true] at accepted
    exact ⟨result,rfl,accepted.1,accepted.2,Stock.VoidCall.NI.noTryCall_of_codeCheck accepted.2⟩

end E2E.VoidCallPairedWitness
