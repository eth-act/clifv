import FV.E2E.PreparedReturnPinCalls

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A proof kernel selects its source classes and derives the same complete artifact contract. -/
structure ReturnPinAdmission where
  extra : Clif.Function → VCode → Bool
  checked : ∀ {f : Clif.Function} {vc : VCode},
    (SemanticNI.check f vc || extra f vc) = true → SemanticABI.checkResultCalls f vc = true

def returnPinResultCallsExtra (f : Clif.Function) (vc : VCode) : Bool :=
  returnPinCallsExtra f vc || Stock.ResultCall.check f vc

def ReturnPinAdmission.previous : ReturnPinAdmission :=
  ⟨returnPinCallsExtra,by
    intro f vc accepted
    have prior : SemanticABI.checkCalls f vc = true := by
      simpa only [SemanticABI.checkCalls,SemanticABI.check,returnPinCallsExtra,Bool.or_assoc] using accepted
    exact SemanticABI.previous_check_result_calls prior⟩

def ReturnPinAdmission.resultCalls : ReturnPinAdmission :=
  ⟨returnPinResultCallsExtra,by
    intro f vc accepted
    simpa only [SemanticABI.checkResultCalls,SemanticABI.checkCalls,SemanticABI.check,
      returnPinResultCallsExtra,returnPinCallsExtra,Bool.or_assoc] using accepted⟩

def okRReturnPinFor (admission : ReturnPinAdmission) (stage : Clif.Function → VCode → VCode)
    (I : LinkInput) (R : Res) : Bool :=
  okRSemanticFor admission.extra stage I R && (progOf R).funcs.all (returnPinChecks I R)

/-- Every old checker input keeps the exact old verdict. -/
theorem okRReturnPinFor_previous (stage : Clif.Function → VCode → VCode) (I : LinkInput) (R : Res) :
    okRReturnPinFor .previous stage I R = okRReturnPinCalls stage I R := rfl

def okRReturnPinResultCalls (stage : Clif.Function → VCode → VCode) (I : LinkInput) (R : Res) : Bool :=
  okRReturnPinFor .resultCalls stage I R

/-- The generic kernel reuses metadata, allocation, physical call checks, and program proof composition. -/
theorem semanticPreparedReturnPinFor_sound (admission : ReturnPinAdmission)
    (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res}
    (hstage : stage = (fun _ => id) ∨ stage = (fun _ => DeadCleanup.prune))
    (prepared : PreparedResults stage I R) (checked : okRReturnPinFor admission stage I R = true)
    {B : BaseEnv} {F : BitVec 64 → Prop} (base : BaseOk (ofRes I R B F))
    (world : ∀ a,(ofRes I R B F).Img a → F a) : (ofRes I R B F).OkSemanticReturnPins := by
  simp only [okRReturnPinFor,Bool.and_eq_true,List.all_eq_true] at checked
  have metadata := semanticPreparedMetadata_sound admission.extra stage prepared checked.1 base world
  refine metadata.toReturnPins fun g member => ?_
  have facts := semanticPreparedFactsFor admission.extra stage prepared checked.1 member
  have lower : SemanticABI.checkResultCalls g (artOf R g).vc = true := admission.checked facts.lowerOk
  have pins : (ofRes I R B F).returnPinsB g = true := by
    rw [← returnPinChecks_eq]
    exact checked.2 g member
  obtain ⟨prepare,alloc,emit,layout,_⟩ := facts.pipe
  rcases hstage with rfl | rfl
  · exact CompiledProgramReturnPins.of_checks_result_calls (cleanup := false) lower prepare facts.prepOk
      facts.check alloc emit layout pins
  · exact CompiledProgramReturnPins.of_checks_result_calls (cleanup := true) lower prepare facts.prepOk
      facts.check alloc emit layout pins

/-- New admission preserves every old complete program acceptance. -/
theorem okRReturnPinResultCalls_previous {stage : Clif.Function → VCode → VCode}
    {I : LinkInput} {R : Res} (previous : okRReturnPinCalls stage I R = true) :
    okRReturnPinResultCalls stage I R = true := by
  simp only [okRReturnPinCalls,Bool.and_eq_true] at previous
  simp only [okRReturnPinResultCalls,okRReturnPinFor,Bool.and_eq_true]
  refine ⟨?_,previous.2⟩
  simp only [okRSemanticFor,chksSemanticFor,List.all_append,Bool.and_eq_true,List.all_eq_true] at previous ⊢
  refine ⟨previous.1.1,?_⟩
  intro e member
  have old := previous.1.2 e member
  refine ⟨?_,old.2⟩
  simp only [staticChksSemanticFor,List.all_map,List.all_eq_true,Function.comp_def] at old ⊢
  intro check present
  obtain ⟨raw,rawMember,rfl⟩ := List.mem_map.mp present
  have accepted := old.1 _ (List.mem_map.mpr ⟨raw,rawMember,rfl⟩)
  by_cases named : raw.1 = "compiled: lowerCheck"
  · simp only [named,↓reduceIte] at accepted ⊢
    simpa only [ReturnPinAdmission.resultCalls,returnPinResultCallsExtra,← Bool.or_assoc,accepted,Bool.true_or]
  · simpa only [named,↓reduceIte] using accepted

end E2E.LinkCheck
