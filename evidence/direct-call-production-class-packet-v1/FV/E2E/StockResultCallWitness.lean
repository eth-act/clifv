import FV.E2E.StockResultCallProvider
import FV.Backend.Proof.StockDirectCallResultWitness
import FV.Backend.LinearScan
import FV.Backend.Lowering.StockVoidCallNI

namespace E2E.ResultCallWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Proof.DirectCallResultFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Stock.lower Isle.Aarch64.program Stock.runTerm

private structure Data (cleanup : Bool) where
  result : Stock.Result
  prepared : VCode
  allocated : RFunc
  frame : AFunc
  assembly : FnAsm
  binary : FnBin
  lowered : Stock.lower caller = .ok result
  source : Stock.ResultCall.check caller result.code = true
  preparedRun : Backend.prepare (Stock.Arithmetic.stage cleanup result.code) = .ok prepared
  prepOk : prepCheck (Stock.Arithmetic.stage cleanup result.code) prepared = true
  checkRun : checkAlloc prepared allocated = .ok ()
  allocRun : lowerRFunc prepared allocated = .ok frame
  emitRun : emitFunc 0 frame = .ok assembly
  layoutRun : assembly.layout = .ok binary
  covered : FormsCovered ⟨assembly.k,frame.slotBase⟩ prepared

private def candidate (cleanup : Bool) : Except String (Data cleanup) :=
  match lowered : Stock.lower caller with
  | .error message => .error message
  | .ok result =>
    if source : Stock.ResultCall.check caller result.code = true then
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
                        (formsCoveredB_iff _ _).mp covered⟩
                    else .error "forms are not covered"
        else .error "prepare check rejected"
    else .error "source admission rejected"

attribute [local irreducible] candidate
-- witness: native_decide (only fixed source, artifact and allocator metadata)
private theorem candidates_ok : ((candidate false).isOk && (candidate true).isOk) = true := by
  native_decide

/-- Generic extraction avoids eliminating a concrete compiler result during elaboration. -/
private theorem available_result {α : Type} {action : Except String α}
    (available : action.isOk = true) : ∃ result,action = .ok result := by
  cases action with
  | error message => cases available
  | ok result => exact ⟨result,rfl⟩

/-- The unchanged sparse-result caller inhabits both actual compiler stages and their function Domain. -/
theorem compiled_caller (cleanup : Bool) :
    ∃ (result : Stock.Result) (prepared : VCode) (allocated : RFunc) (frame : AFunc)
      (assembly : FnAsm) (binary : FnBin),
      Stock.ResultCall.check caller result.code = true ∧
      CompiledStockArithmeticStage caller cleanup 0 result prepared allocated frame assembly binary ∧
      Stock.ResultCall.Domain caller result.code ∧
      Nonempty (DirectCallResult.Binding result.ctx result.final 31) ∧
      FormsCovered ⟨assembly.k,frame.slotBase⟩ prepared := by
  have available : (candidate cleanup).isOk = true := by
    have both := Bool.and_eq_true_iff.mp candidates_ok
    cases cleanup with
    | false => exact both.1
    | true => exact both.2
  obtain ⟨d,found⟩ := available_result available
  exact ⟨d.result,d.prepared,d.allocated,d.frame,d.assembly,d.binary,d.source,
    ⟨d.lowered,d.preparedRun,d.prepOk,d.checkRun,d.allocRun,d.emitRun,d.layoutRun⟩,
    Stock.ResultCall.check_domain d.source,(binding_of_run d.lowered).1,d.covered⟩

/-- The original external callback and source return execute for every argument word. -/
theorem original_source_execution (word : BitVec 64) :
    Clif.enterFunc caller [value word] Clif.Mem.empty = .ok (before word,Clif.Mem.empty) ∧
    Clif.runLoop environment {funcs := []} 2 ⟨before word,[],Clif.Mem.empty⟩ =
      .returned [value word] Clif.Mem.empty := by
  exact ⟨rfl,rfl⟩

/-- Both compiled modes retain the original inhabited source and exact sparse result binding. -/
theorem complete_source_and_compiler (word : BitVec 64) (cleanup : Bool) :
    ∃ (result : Stock.Result) (prepared : VCode) (allocated : RFunc) (frame : AFunc)
      (assembly : FnAsm) (binary : FnBin),
      Clif.enterFunc caller [value word] Clif.Mem.empty = .ok (before word,Clif.Mem.empty) ∧
      Clif.runLoop environment {funcs := []} 2 ⟨before word,[],Clif.Mem.empty⟩ =
        .returned [value word] Clif.Mem.empty ∧
      Stock.ResultCall.Domain caller result.code ∧
      CompiledStockArithmeticStage caller cleanup 0 result prepared allocated frame assembly binary ∧
      Nonempty (DirectCallResult.Binding result.ctx result.final 31) := by
  obtain ⟨result,prepared,allocated,frame,assembly,binary,checked,compiled,domain,binding,covered⟩ :=
    compiled_caller cleanup
  obtain ⟨entered,returned⟩ := original_source_execution word
  exact ⟨result,prepared,allocated,frame,assembly,binary,entered,returned,domain,compiled,binding⟩

private def legacyInfo : CallInfo :=
  ⟨.sym callee.name,[(.vreg 7 .int,.x 0)],[(.x 0,.vreg 32 .int)]⟩

private def previousChecked (action : Except String VCode) : Bool := match action with
  | .error _ => false
  | .ok vc => (vc.blocks[0]?).any fun block =>
      decide (callData block.insts[1]? = some (legacyInfo.dest,legacyInfo.uses,legacyInfo.defs))

private theorem previousChecked_sound {action : Except String VCode}
    (good : previousChecked action = true) :
    ∃ vc,action = .ok vc ∧ ∃ block,vc.blocks[0]? = some block ∧
      callData block.insts[1]? = some (legacyInfo.dest,legacyInfo.uses,legacyInfo.defs) := by
  cases action with
  | error message => cases good
  | ok vc =>
    refine ⟨vc,rfl,?_⟩
    simpa only [previousChecked,Option.any_eq_true,decide_eq_true_eq] using good

private def previousSuccess : Bool := previousChecked (Stock.VoidCall.NI.lowerValidated caller)
attribute [local irreducible] previousSuccess
-- witness: native_decide (the actual predecessor and unchanged original caller)
private theorem previousSuccess_true : previousSuccess = true := by native_decide

/-- The real previous provider succeeds through legacy code, while the new class selects Stock code. -/
theorem actual_predecessor_selection (cleanup : Bool) :
    ∃ (result : Stock.Result) (previous : VCode) (prepared : VCode) (allocated : RFunc)
      (frame : AFunc) (assembly : FnAsm) (binary : FnBin),
      Stock.VoidCall.NI.lowerValidated caller = .ok previous ∧
      Stock.ResultCall.lowerWithPrevious Stock.VoidCall.NI.lowerValidated caller = .ok result.code ∧
      result.code ≠ previous ∧
      CompiledStockArithmeticStage caller cleanup 0 result prepared allocated frame assembly binary ∧
      Nonempty (DirectCallResult.Binding result.ctx result.final 31) := by
  obtain ⟨result,prepared,allocated,frame,assembly,binary,checked,compiled,domain,binding,covered⟩ :=
    compiled_caller cleanup
  have prior := previousSuccess_true
  unfold previousSuccess at prior
  obtain ⟨previous,previousRun,oldBlock,oldPlaced,oldCall⟩ := previousChecked_sound prior
  have candidateRun : Stock.ResultCall.candidate caller = .ok result.code := by
    unfold Stock.ResultCall.candidate
    rw [compiled.lower]
    simp only [bind,Except.bind,checked,↓reduceIte,pure,Except.pure]
  refine ⟨result,previous,prepared,allocated,frame,assembly,binary,previousRun,
    Stock.ResultCall.lowerWithPrevious_selects candidateRun,?_,compiled,binding⟩
  intro equal
  obtain ⟨_,newBlock,newPlaced,newCall,newReturn⟩ := binding_of_run compiled.lower
  rw [← equal] at oldPlaced
  have blockEqual : oldBlock = newBlock := Option.some.inj (oldPlaced.symm.trans newPlaced)
  subst oldBlock
  have pairEqual := Option.some.inj (oldCall.symm.trans newCall)
  have defsEqual := congrArg (fun data : CallDest × List (Reg × Reg) × List (Reg × Reg) => data.2.2) pairEqual
  simp only [legacyInfo,actualInfo] at defsEqual
  cases defsEqual

end E2E.ResultCallWitness
