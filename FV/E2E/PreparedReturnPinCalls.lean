import FV.E2E.PreparedReturnPinProgram
import FV.E2E.ReturnPinPipelineRetry
import FV.E2E.ProductionPipelineWith
import FV.Backend.Lowering.StockVoidCallNI

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Extend only source-class admission. The existing global and per-function checks remain. -/
def returnPinCallsExtra (f : Clif.Function) (vc : VCode) : Bool :=
  Stock.MemorySretCopy.check f vc || Stock.VoidCall.NI.check f vc

def okRReturnPinCalls (stage : Clif.Function → VCode → VCode) (I : LinkInput) (R : Res) : Bool :=
  okRSemanticFor returnPinCallsExtra stage I R && (progOf R).funcs.all (returnPinChecks I R)

/-- Reuse the proved physical return cache once for the complete program. -/
def okRReturnPinCallsFast (stage : Clif.Function → VCode → VCode) (I : LinkInput) (R : Res) : Bool :=
  okRSemanticFor returnPinCallsExtra stage I R &&
    let C := ReturnPinCtx.of I R
    (progOf R).funcs.all (returnPinsWith C)

@[csimp] theorem okRReturnPinCalls_eq_fast : @okRReturnPinCalls = @okRReturnPinCallsFast := by
  funext stage I R
  unfold okRReturnPinCalls okRReturnPinCallsFast
  dsimp only
  rw [show returnPinsWith (ReturnPinCtx.of I R) = returnPinChecks I R from
    funext (returnPinsWith_of I R)]

/-- Every complete program accepted by the previous ABI checker remains accepted. -/
theorem okRReturnPinCalls_previous {stage : Clif.Function → VCode → VCode} {I : LinkInput} {R : Res}
    (previous : okRReturnPins stage I R = true) : okRReturnPinCalls stage I R = true := by
  simp only [okRReturnPins,Bool.and_eq_true] at previous
  simp only [okRReturnPinCalls,Bool.and_eq_true]
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
    simpa only [returnPinCallsExtra,← Bool.or_assoc,accepted,Bool.true_or]
  · simpa only [named,↓reduceIte] using accepted

/-- Actual checks derive the complete existing program contract, including the new caller. -/
theorem semanticPreparedReturnPinCallsResults_sound (stage : Clif.Function → VCode → VCode)
    {I : LinkInput} {R : Res}
    (hstage : stage = (fun _ => id) ∨ stage = (fun _ => DeadCleanup.prune))
    (prepared : PreparedResults stage I R) (checked : okRReturnPinCalls stage I R = true)
    {B : BaseEnv} {F : BitVec 64 → Prop} (base : BaseOk (ofRes I R B F))
    (world : ∀ a,(ofRes I R B F).Img a → F a) : (ofRes I R B F).OkSemanticReturnPins := by
  simp only [okRReturnPinCalls,Bool.and_eq_true,List.all_eq_true] at checked
  have metadata := semanticPreparedMetadata_sound returnPinCallsExtra stage prepared checked.1 base world
  refine metadata.toReturnPins fun g member => ?_
  have facts := semanticPreparedFactsFor returnPinCallsExtra stage prepared checked.1 member
  have lower : SemanticABI.checkCalls g (artOf R g).vc = true := by
    simpa only [SemanticABI.checkCalls,SemanticABI.check,returnPinCallsExtra,Bool.or_assoc] using facts.lowerOk
  have pins : (ofRes I R B F).returnPinsB g = true := by
    rw [← returnPinChecks_eq]
    exact checked.2 g member
  obtain ⟨prepare,alloc,emit,layout,_⟩ := facts.pipe
  rcases hstage with rfl | rfl
  · exact CompiledProgramReturnPins.of_checks_calls (cleanup := false) lower prepare facts.prepOk
      facts.check alloc emit layout pins
  · exact CompiledProgramReturnPins.of_checks_calls (cleanup := true) lower prepare facts.prepOk
      facts.check alloc emit layout pins

/-- The original program statement uses the original base and world conditions. -/
theorem preparedReturnPinCalls_correct (stage : Clif.Function → VCode → VCode)
    {I : LinkInput} {R : Res}
    (hstage : stage = (fun _ => id) ∨ stage = (fun _ => DeadCleanup.prune))
    (prepared : PreparedResults stage I R) (checked : okRReturnPinCalls stage I R = true)
    (name : String) : CrateStmtReturnPins I R name := by
  intro B F base world f found M ra s w₀ args cs entry room frame free image body arguments source
    avoids relation placement traps
  exact backend_correct_program_return_pins _
    (semanticPreparedReturnPinCallsResults_sound stage hstage prepared checked base world)
    (Clif.Program.func?_some found).1 M entry room frame free image body arguments source
    avoids relation placement traps

/-- Publish a complete checked attempt or retain the complete previous program. -/
def LinkInput.resultsReturnPinCalls (I : LinkInput) (cleanup : Bool) : Res :=
  let attempt := I.resultsProductionWith Stock.VoidCall.NI.lowerValidated cleanup
  if okRReturnPinCalls (productionStage cleanup) I attempt then attempt
  else I.resultsReturnPins cleanup

theorem LinkInput.resultsReturnPinCalls_accept (I : LinkInput) (cleanup : Bool)
    (accepted : okRReturnPinCalls (productionStage cleanup) I
      (I.resultsProductionWith Stock.VoidCall.NI.lowerValidated cleanup) = true) :
    I.resultsReturnPinCalls cleanup = I.resultsProductionWith Stock.VoidCall.NI.lowerValidated cleanup := by
  simp only [LinkInput.resultsReturnPinCalls,accepted,↓reduceIte]

theorem LinkInput.resultsReturnPinCalls_retry (I : LinkInput) (cleanup : Bool)
    (rejected : okRReturnPinCalls (productionStage cleanup) I
      (I.resultsProductionWith Stock.VoidCall.NI.lowerValidated cleanup) = false) :
    I.resultsReturnPinCalls cleanup = I.resultsReturnPins cleanup := by
  simp only [LinkInput.resultsReturnPinCalls,rejected,Bool.false_eq_true,↓reduceIte]

theorem LinkInput.resultsReturnPinCalls_prepared (I : LinkInput) (cleanup : Bool) :
    PreparedResults (productionStage cleanup) I (I.resultsReturnPinCalls cleanup) := by
  unfold LinkInput.resultsReturnPinCalls
  dsimp only
  split
  · exact I.resultsProductionWith_prepared Stock.VoidCall.NI.lowerValidated cleanup
  · exact I.resultsReturnPins_prepared cleanup

/-- Whole-program retry retains the exact original source sequence, names, and signatures. -/
theorem LinkInput.resultsReturnPinCalls_source (I : LinkInput) (cleanup : Bool) :
    progOf (I.resultsReturnPinCalls cleanup) = progOf (I.resultsProduction cleanup) := by
  unfold LinkInput.resultsReturnPinCalls
  dsimp only
  split
  · simp only [progOf,LinkInput.resultsProductionWith,LinkInput.resultsProduction,List.map_map,
      Function.comp_def]
  · exact I.resultsReturnPins_source cleanup

/-- Every original accepted program retains success without a new input condition. -/
theorem LinkInput.resultsReturnPinCalls_checked (I : LinkInput) (cleanup : Bool)
    (previous : okRSemanticNI (productionStage cleanup) I (I.resultsProduction cleanup) = true) :
    okRReturnPinCalls (productionStage cleanup) I (I.resultsReturnPinCalls cleanup) = true := by
  unfold LinkInput.resultsReturnPinCalls
  dsimp only
  split
  · assumption
  · exact okRReturnPinCalls_previous (I.resultsReturnPins_checked cleanup previous)

theorem LinkInput.resultsReturnPinCalls_sound (I : LinkInput) (cleanup : Bool)
    (previous : okRSemanticNI (productionStage cleanup) I (I.resultsProduction cleanup) = true)
    {B : BaseEnv} {F : BitVec 64 → Prop}
    (base : BaseOk (ofRes I (I.resultsReturnPinCalls cleanup) B F))
    (world : ∀ a,(ofRes I (I.resultsReturnPinCalls cleanup) B F).Img a → F a) :
    (ofRes I (I.resultsReturnPinCalls cleanup) B F).OkSemanticReturnPins :=
  semanticPreparedReturnPinCallsResults_sound (productionStage cleanup) (productionStage_cases cleanup)
    (I.resultsReturnPinCalls_prepared cleanup) (I.resultsReturnPinCalls_checked cleanup previous) base world

theorem LinkInput.resultsReturnPinCalls_correct (I : LinkInput) (cleanup : Bool)
    (previous : okRSemanticNI (productionStage cleanup) I (I.resultsProduction cleanup) = true)
    (name : String) : CrateStmtReturnPins I (I.resultsReturnPinCalls cleanup) name :=
  preparedReturnPinCalls_correct (productionStage cleanup) (productionStage_cases cleanup)
    (I.resultsReturnPinCalls_prepared cleanup) (I.resultsReturnPinCalls_checked cleanup previous) name

end E2E.LinkCheck
