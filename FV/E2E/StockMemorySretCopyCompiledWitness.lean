import FV.E2E.CompiledSemanticABI
import FV.Backend.Lowering.StockMemorySretCopyNI
import FV.Backend.Proof.StockMemorySretCopyBodyWitness
import FV.Backend.LinearScan

namespace E2E.StockMemorySretCopyCompiledWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Memory.StoreRoots.ComputedFixture (function)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private structure Data (cleanup : Bool) where
  result : Stock.Result
  prepared : VCode
  allocated : RFunc
  frame : AFunc
  assembly : FnAsm
  binary : FnBin
  lowered : Stock.lower function = .ok result
  source : Stock.MemorySretCopy.check function result.code = true
  preparedRun : Backend.prepare (Stock.Arithmetic.stage cleanup result.code) = .ok prepared
  prepOk : prepCheck (Stock.Arithmetic.stage cleanup result.code) prepared = true
  checkRun : checkAlloc prepared allocated = .ok ()
  allocRun : lowerRFunc prepared allocated = .ok frame
  emitRun : emitFunc 0 frame = .ok assembly
  layoutRun : assembly.layout = .ok binary
  covered : FormsCovered ⟨assembly.k,frame.slotBase⟩ prepared
  provider : Stock.MemorySretCopy.lowerValidated function = .ok result.code

private def candidate (cleanup : Bool) : Except String (Data cleanup) :=
  match lowered : Stock.lower function with
  | .error message => .error message
  | .ok result =>
    if source : Stock.MemorySretCopy.check function result.code = true then
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
                      match provider : Stock.MemorySretCopy.lowerValidated function with
                      | .error message => .error message
                      | .ok code =>
                        if same : code = result.code then
                          .ok ⟨result,prepared,allocated,frame,assembly,binary,lowered,source,
                            preparedRun,prepOk,checkRun,allocRun,emitRun,layoutRun,
                            (formsCoveredB_iff _ _).mp covered,by simpa only [same] using provider⟩
                        else .error "provider artifact changed"
                    else .error "forms are not covered"
        else .error "prepare check rejected"
    else .error "source admission rejected"

private theorem candidates_ok : ((candidate false).isOk && (candidate true).isOk) = true := by
  native_decide

/-- The unchanged captured source compiles through the actual Stock provider and every backend stage.
Both cleanup modes inhabit the ABI-aware artifact and the machine theorem's form premise. -/
theorem compiled_sret_pipeline_witness (cleanup : Bool) :
    ∃ (result : Stock.Result) (prepared : VCode) (allocated : RFunc) (frame : AFunc)
      (assembly : FnAsm) (binary : FnBin),
      Stock.lower function = .ok result ∧
      Stock.MemorySretCopy.lowerValidated function = .ok result.code ∧
      Stock.MemorySretCopy.check function result.code = true ∧
      CompiledSemanticABI function 0 result.code prepared allocated frame assembly binary ∧
      FormsCovered ⟨assembly.k,frame.slotBase⟩ prepared := by
  have available : (candidate cleanup).isOk = true := by
    have both := Bool.and_eq_true_iff.mp candidates_ok
    cases cleanup with
    | false => exact both.1
    | true => exact both.2
  cases found : candidate cleanup with
  | error message => rw [found] at available; cases available
  | ok d =>
    obtain ⟨actual,family,lowered,equal,effects⟩ := Stock.MemorySretCopy.check_sound d.source
    have same : actual = d.result := Except.ok.inj (lowered.symm.trans d.lowered)
    cases same
    refine ⟨d.result,d.prepared,d.allocated,d.frame,d.assembly,d.binary,d.lowered,d.provider,d.source,?_,d.covered⟩
    exact .memorySretCopy family equal effects
      ⟨lowered,d.preparedRun,d.prepOk,d.checkRun,d.allocRun,d.emitRun,d.layoutRun⟩

/-- Expose the actual stage for additive consumers without changing the previous artifact witness. -/
theorem compiled_sret_stage_witness (cleanup : Bool) :
    ∃ (result : Stock.Result) (prepared : VCode) (allocated : RFunc) (frame : AFunc)
      (assembly : FnAsm) (binary : FnBin),
      Stock.lower function = .ok result ∧
      Stock.MemorySretCopy.lowerValidated function = .ok result.code ∧
      Stock.MemorySretCopy.check function result.code = true ∧
      CompiledStockArithmeticStage function cleanup 0 result prepared allocated frame assembly binary ∧
      FormsCovered ⟨assembly.k,frame.slotBase⟩ prepared := by
  have available : (candidate cleanup).isOk = true := by
    have both := Bool.and_eq_true_iff.mp candidates_ok
    cases cleanup with
    | false => exact both.1
    | true => exact both.2
  cases found : candidate cleanup with
  | error message => rw [found] at available; cases available
  | ok d =>
    exact ⟨d.result,d.prepared,d.allocated,d.frame,d.assembly,d.binary,d.lowered,d.provider,d.source,
      ⟨d.lowered,d.preparedRun,d.prepOk,d.checkRun,d.allocRun,d.emitRun,d.layoutRun⟩,d.covered⟩

end E2E.StockMemorySretCopyCompiledWitness
