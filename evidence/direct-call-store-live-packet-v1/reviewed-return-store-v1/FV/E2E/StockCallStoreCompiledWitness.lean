import FV.E2E.StockCallStoreSourceWitness
import FV.E2E.StockCallStoreDomain
import FV.E2E.StockArithmeticStageContract
import FV.Backend.Lowering.StockArithmetic

namespace E2E.CallStoreCompiledWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof CallStoreFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private structure Data (cleanup : Bool) where
  result : Stock.Result
  prepared : VCode
  allocated : RFunc
  physical : AFunc
  assembly : FnAsm
  binary : FnBin
  lowered : Stock.lower caller = .ok result
  admitted : Stock.CallStore.check caller result.code = true
  prepareRun : prepare (Stock.Arithmetic.stage cleanup result.code) = .ok prepared
  prepareOk : prepCheck (Stock.Arithmetic.stage cleanup result.code) prepared = true
  checkRun : checkAlloc prepared allocated = .ok ()
  physicalRun : lowerRFunc prepared allocated = .ok physical
  assemblyRun : emitFunc 0 physical = .ok assembly
  layoutRun : assembly.layout = .ok binary
  saved : allocated.saved = [.x 19]
  covered : FormsCovered ⟨assembly.k,physical.slotBase⟩ prepared

private def compiled (cleanup : Bool) : Except String (Data cleanup) :=
  match lowered : Stock.lower caller with
  | .error message => .error message
  | .ok result =>
    if admitted : Stock.CallStore.check caller result.code = true then
      match prepareRun : prepare (Stock.Arithmetic.stage cleanup result.code) with
      | .error message => .error message
      | .ok prepared =>
        if prepareOk : prepCheck (Stock.Arithmetic.stage cleanup result.code) prepared = true then
          match allocatedRun : leanAlloc prepared with
          | .error message => .error message
          | .ok allocated =>
            match checkRun : checkAlloc prepared allocated with
            | .error message => .error message
            | .ok () =>
              match physicalRun : lowerRFunc prepared allocated with
              | .error message => .error message
              | .ok physical =>
                match assemblyRun : emitFunc 0 physical with
                | .error message => .error message
                | .ok assembly =>
                  match layoutRun : assembly.layout with
                  | .error message => .error message
                  | .ok binary =>
                    if saved : allocated.saved = [.x 19] then
                      if coverage : formsCoveredB ⟨assembly.k,physical.slotBase⟩ prepared = true then
                        .ok ⟨result,prepared,allocated,physical,assembly,binary,lowered,admitted,prepareRun,
                          prepareOk,checkRun,physicalRun,assemblyRun,layoutRun,saved,
                          (formsCoveredB_iff _ _).mp coverage⟩
                      else .error "forms are not covered"
                    else .error "the original live parameter is not saved in x19"
        else .error "prepare check failed"
    else .error "live-call class rejected"

attribute [local irreducible] compiled
-- witness: native_decide (the fixed source and complete actual pipelines only)
private theorem compiled_ok : ((compiled false).isOk && (compiled true).isOk) = true := by native_decide

private theorem available {α : Type} {action : Except String α} (positive : action.isOk = true) :
    ∃ result,action = .ok result := by
  cases action with
  | error message => cases positive
  | ok result => exact ⟨result,rfl⟩

/-- Both checked pipelines keep the original store flags, call result, and saved pointer. -/
-- witness: native_decide (fixed pipeline metadata only)
theorem complete_caller (cleanup : Bool) :
    ∃ (result : Stock.Result) (prepared : VCode) (allocated : RFunc) (physical : AFunc)
      (assembly : FnAsm) (binary : FnBin),
      Stock.CallStore.ReturnStoreDomain caller result.code ∧
      CompiledStockArithmeticStage caller cleanup 0 result prepared allocated physical assembly binary ∧
      allocated.saved = [.x 19] ∧ FormsCovered ⟨assembly.k,physical.slotBase⟩ prepared ∧
      result.ctx.valueReg? 7 = some (.vreg 192 .int) ∧
      result.ctx.valueReg? 11 = some (.vreg 193 .int) ∧
      result.ctx.valueReg? 31 = some (.vreg 194 .int) ∧
      aliasNum result.final.alias 192 = 192 ∧ aliasNum result.final.alias 194 = 195 := by
  have positive : (compiled cleanup).isOk = true := by
    have both := Bool.and_eq_true_iff.mp compiled_ok
    cases cleanup with
    | false => exact both.1
    | true => exact both.2
  obtain ⟨data,found⟩ := available positive
  obtain ⟨actual,oldAllocated,lowered,pointer,argument,called,pointerAlias,calledAlias,oldCompiled,saved,item⟩ :=
    CallStoreFixture.actual_retained_and_saved cleanup
  have same : actual = data.result := Except.ok.inj (lowered.symm.trans data.lowered)
  subst actual
  exact ⟨data.result,data.prepared,data.allocated,data.physical,data.assembly,data.binary,
    Stock.CallStore.check_return_store_domain data.admitted,
    ⟨data.lowered,data.prepareRun,data.prepareOk,data.checkRun,data.physicalRun,data.assemblyRun,data.layoutRun⟩,
    data.saved,data.covered,pointer,argument,called,pointerAlias,calledAlias⟩

end E2E.CallStoreCompiledWitness
