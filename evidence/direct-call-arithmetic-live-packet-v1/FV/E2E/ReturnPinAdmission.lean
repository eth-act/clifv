import FV.E2E.PreparedReturnPinCalls

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A proof kernel selects its source classes and derives the same complete artifact contract. -/
structure ReturnPinAdmission where
  extra : Clif.Function → VCode → Bool
  compiled : ∀ {f : Clif.Function} {vc vcp : VCode} {rf : RFunc} {af : AFunc}
      {fa : FnAsm} {fb : FnBin} {cleanup : Bool} {k : Nat},
    (SemanticNI.check f vc || extra f vc) = true →
    Backend.prepare (Stock.Arithmetic.stage cleanup vc) = .ok vcp →
    prepCheck (Stock.Arithmetic.stage cleanup vc) vcp = true →
    checkAlloc vcp rf = .ok () → lowerRFunc vcp rf = .ok af →
    emitFunc k af = .ok fa → fa.layout = .ok fb →
      CompiledSemanticReturnPins f k vc vcp rf af fa fb (ReturnPinMode.checked f vc)

def returnPinResultCallsExtra (f : Clif.Function) (vc : VCode) : Bool :=
  returnPinCallsExtra f vc || Stock.ResultCall.check f vc

def ReturnPinAdmission.previous : ReturnPinAdmission :=
  ⟨returnPinCallsExtra,by
    intro f vc vcp rf af fa fb cleanup k accepted prepared prepOk check alloc emit layout
    have prior : SemanticABI.checkCalls f vc = true := by
      simpa only [SemanticABI.checkCalls,SemanticABI.check,returnPinCallsExtra,Bool.or_assoc] using accepted
    exact CompiledSemanticReturnPins.of_checks_calls prior prepared prepOk check alloc emit layout⟩

def ReturnPinAdmission.resultCalls : ReturnPinAdmission :=
  ⟨returnPinResultCallsExtra,by
    intro f vc vcp rf af fa fb cleanup k accepted prepared prepOk check alloc emit layout
    have lower : SemanticABI.checkResultCalls f vc = true := by
      simpa only [SemanticABI.checkResultCalls,SemanticABI.checkCalls,SemanticABI.check,
        returnPinResultCallsExtra,returnPinCallsExtra,Bool.or_assoc] using accepted
    exact CompiledSemanticReturnPins.of_checks_result_calls lower prepared prepOk check alloc emit layout⟩

def okRReturnPinFor (admission : ReturnPinAdmission) (stage : Clif.Function → VCode → VCode)
    (I : LinkInput) (R : Res) : Bool :=
  okRSemanticFor admission.extra stage I R && (progOf R).funcs.all (returnPinChecks I R)

/-- Cache the complete program's return convention once for all call sites. -/
def okRReturnPinForFast (admission : ReturnPinAdmission) (stage : Clif.Function → VCode → VCode)
    (I : LinkInput) (R : Res) : Bool :=
  okRSemanticFor admission.extra stage I R &&
    let C := ReturnPinCtx.of I R
    (progOf R).funcs.all (returnPinsWith C)

@[csimp] theorem okRReturnPinFor_eq_fast : @okRReturnPinFor = @okRReturnPinForFast := by
  funext admission stage I R
  unfold okRReturnPinFor okRReturnPinForFast
  dsimp only
  rw [show returnPinsWith (ReturnPinCtx.of I R) = returnPinChecks I R from
    funext (returnPinsWith_of I R)]

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
  have pins : (ofRes I R B F).returnPinsB g = true := by
    rw [← returnPinChecks_eq]
    exact checked.2 g member
  obtain ⟨prepare,alloc,emit,layout,_⟩ := facts.pipe
  rcases hstage with rfl | rfl
  · exact ⟨admission.compiled (cleanup := false) facts.lowerOk prepare facts.prepOk facts.check alloc emit layout,
      (ofRes I R B F).returnPinsB_sound pins⟩
  · exact ⟨admission.compiled (cleanup := true) facts.lowerOk prepare facts.prepOk facts.check alloc emit layout,
      (ofRes I R B F).returnPinsB_sound pins⟩

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

/-- Every profile derives the unchanged whole-program statement from actual checks. -/
theorem preparedReturnPinFor_correct (admission : ReturnPinAdmission)
    (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res}
    (hstage : stage = (fun _ => id) ∨ stage = (fun _ => DeadCleanup.prune))
    (prepared : PreparedResults stage I R) (checked : okRReturnPinFor admission stage I R = true)
    (name : String) : CrateStmtReturnPins I R name := by
  intro B F base world f found M ra s w₀ args cs entry room frame free image body arguments source
    avoids relation placement traps
  exact backend_correct_program_return_pins _
    (semanticPreparedReturnPinFor_sound admission stage hstage prepared checked base world)
    (Clif.Program.func?_some found).1 M entry room frame free image body arguments source
    avoids relation placement traps


/-- The new profile leaves every prior checker and profile unchanged. -/
def returnPinLiveCallsExtra (f : Clif.Function) (vc : VCode) : Bool :=
  returnPinResultCallsExtra f vc || Stock.LiveCall.check f vc

def ReturnPinAdmission.liveCalls : ReturnPinAdmission where
  extra := returnPinLiveCallsExtra
  compiled := by
    intro f k vc vcp rf af fa fb cleanup checked prepared prepOk check alloc emit layout
    apply CompiledSemanticReturnPins.of_checks_live_calls ?_ prepared prepOk check alloc emit layout
    simpa only [returnPinLiveCallsExtra,returnPinResultCallsExtra,returnPinCallsExtra,
      SemanticABI.checkLiveCalls,SemanticABI.checkResultCalls,SemanticABI.checkCalls,SemanticABI.check,
      Bool.or_assoc] using checked

abbrev okRReturnPinLiveCalls := okRReturnPinFor ReturnPinAdmission.liveCalls

/-- The live-result profile preserves every complete result-call program acceptance. -/
theorem okRReturnPinLiveCalls_previous {stage : Clif.Function → VCode → VCode}
    {I : LinkInput} {R : Res} (previous : okRReturnPinResultCalls stage I R = true) :
    okRReturnPinLiveCalls stage I R = true := by
  simp only [okRReturnPinResultCalls,okRReturnPinFor,Bool.and_eq_true] at previous
  simp only [okRReturnPinLiveCalls,okRReturnPinFor,Bool.and_eq_true]
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
    simp only [ReturnPinAdmission.resultCalls] at accepted
    simpa only [ReturnPinAdmission.liveCalls,returnPinLiveCallsExtra,
      ← Bool.or_assoc,accepted,Bool.true_or]
  · simpa only [named,↓reduceIte] using accepted

end E2E.LinkCheck
