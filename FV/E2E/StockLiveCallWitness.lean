import FV.E2E.StockLiveCallFixture
import FV.E2E.StockLiveCallNI
import FV.Backend.Lowering.StockLiveCallWith
import FV.Backend.Lowering.StockResultCallRoutes

namespace E2E.LiveCallWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof LiveCallFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def value (word : BitVec 64) : Clif.Val := ⟨.i64,word⟩
def frame (word : BitVec 64) : Clif.Frame := {
  func := caller
  regs := Clif.Regs.empty.set 7 (value word)
  slots := []
  body := [⟨[31],.call 0 [7]⟩,⟨[79],.binary .iadd .i64 31 7⟩]
  term := .ret [79] }

def program : Clif.Program := {funcs := [caller,callee]}

/-- The unchanged caller and clobbering callee execute their complete original source for every word. -/
theorem source_execution (word : BitVec 64) :
    Clif.enterFunc caller [value word] Clif.Mem.empty = .ok (frame word,Clif.Mem.empty) ∧
    Clif.runLoop Clif.Env.empty program 6 ⟨frame word,[],Clif.Mem.empty⟩ =
      .returned [value ((word+13)+word)] Clif.Mem.empty := by
  exact ⟨rfl,rfl⟩

private structure Data (cleanup : Bool) where
  result : Stock.Result
  prepared : VCode
  allocated : RFunc
  physical : AFunc
  assembly : FnAsm
  binary : FnBin
  lowered : Stock.lower caller = .ok result
  admitted : Stock.LiveCall.check caller result.code = true
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
    if admitted : Stock.LiveCall.check caller result.code = true then
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

/-- Both real pipelines preserve the original live parameter, source result mapping, and complete call Domain. -/
-- witness: native_decide (fixed pipeline metadata; the source argument remains arbitrary)
theorem complete_caller (cleanup : Bool) (word : BitVec 64) :
    ∃ (result : Stock.Result) (prepared : VCode) (allocated : RFunc) (physical : AFunc)
      (assembly : FnAsm) (binary : FnBin),
      Clif.enterFunc caller [value word] Clif.Mem.empty = .ok (frame word,Clif.Mem.empty) ∧
      Clif.runLoop Clif.Env.empty program 6 ⟨frame word,[],Clif.Mem.empty⟩ =
        .returned [value ((word+13)+word)] Clif.Mem.empty ∧
      Stock.LiveCall.Domain caller result.code ∧
      CompiledStockArithmeticStage caller cleanup 0 result prepared allocated physical assembly binary ∧
      allocated.saved = [.x 19] ∧ FormsCovered ⟨assembly.k,physical.slotBase⟩ prepared ∧
      result.ctx.valueReg? 7 = some (.vreg 192 .int) ∧
      result.ctx.valueReg? 31 = some (.vreg 193 .int) ∧
      result.ctx.valueReg? 79 = some (.vreg 194 .int) ∧
      aliasNum result.final.alias 192 = 192 ∧ aliasNum result.final.alias 193 = 196 ∧
      aliasNum result.final.alias 194 = 195 := by
  have positive : (compiled cleanup).isOk = true := by
    have both := Bool.and_eq_true_iff.mp compiled_ok
    cases cleanup with
    | false => exact both.1
    | true => exact both.2
  obtain ⟨data,found⟩ := available positive
  obtain ⟨actual,oldAllocated,lowered,admitted,live,called,sum,liveAlias,calledAlias,sumAlias,oldCompiled,saved⟩ :=
    LiveCallFixture.actual_retained_and_saved cleanup
  have same : actual = data.result := Except.ok.inj (lowered.symm.trans data.lowered)
  subst actual
  obtain ⟨entered,returned⟩ := source_execution word
  exact ⟨data.result,data.prepared,data.allocated,data.physical,data.assembly,data.binary,entered,returned,
    Stock.LiveCall.check_domain data.admitted,
    ⟨data.lowered,data.prepareRun,data.prepareOk,data.checkRun,data.physicalRun,data.assemblyRun,data.layoutRun⟩,
    data.saved,data.covered,live,called,sum,liveAlias,calledAlias,sumAlias⟩

private def previousObserved : Bool :=
  (Stock.ResultCall.lowerValidated caller).toOption.any (fun code => !Stock.LiveCall.check caller code)
attribute [local irreducible] previousObserved
-- witness: native_decide (the real unchanged predecessor accepts this exact caller)
private theorem previousObserved_true : previousObserved = true := by native_decide

private theorem option_available {α : Type} {action : Except String α} {predicate : α → Bool}
    (positive : action.toOption.any predicate = true) : ∃ result,action = .ok result ∧ predicate result = true := by
  cases action with
  | error message => cases positive
  | ok result => exact ⟨result,rfl,positive⟩

/-- The new provider selects Stock even though its real predecessor accepts the original caller. -/
-- witness: native_decide (fixed source and actual provider/pipeline data only)
theorem actual_provider (cleanup : Bool) :
    ∃ (result : Stock.Result) (previous : VCode),Stock.lower caller = .ok result ∧
      Stock.ResultCall.lowerValidated caller = .ok previous ∧
      Stock.LiveCall.lowerWithPrevious Stock.ResultCall.lowerValidated caller = .ok result.code ∧
      result.code ≠ previous ∧ Stock.LiveCall.Domain caller result.code := by
  have positive : (compiled cleanup).isOk = true := by
    have both := Bool.and_eq_true_iff.mp compiled_ok
    cases cleanup with
    | false => exact both.1
    | true => exact both.2
  obtain ⟨data,found⟩ := available positive
  have candidate : Stock.LiveCall.candidate caller = .ok data.result.code := by
    unfold Stock.LiveCall.candidate Stock.CheckedWith.candidate
    rw [data.lowered]
    simp only [bind,Except.bind,data.admitted,↓reduceIte,pure,Except.pure]
  have old := previousObserved_true
  unfold previousObserved at old
  obtain ⟨previous,oldRun,oldCheck⟩ := option_available old
  have rejected : Stock.LiveCall.check caller previous = false := by simpa using oldCheck
  refine ⟨data.result,previous,data.lowered,oldRun,Stock.LiveCall.lowerWithPrevious_selects candidate,?_,
    Stock.LiveCall.check_domain data.admitted⟩
  intro same
  have checked := data.admitted
  rw [same,rejected] at checked
  cases checked

end E2E.LiveCallWitness
