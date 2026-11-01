import FV.E2E.PreparedReturnPinPipeline
import FV.E2E.SemanticPreparedPipeline
import FV.E2E.ProductionPipelineWith
import FV.E2E.PreparedReturnPinProgram
import FV.Backend.Lowering.StockMemorySretCopyNI

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Adding a proved lowering class retains every previous checker success. -/
theorem okRSemanticFor_of_previous (extra : Clif.Function → VCode → Bool)
    (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res}
    (previous : okRSemanticNI stage I R = true) : okRSemanticFor extra stage I R = true := by
  simp only [okRSemanticNI,Bool.and_eq_true] at previous
  simp only [okRSemanticFor,Bool.and_eq_true]
  refine ⟨previous.1,List.all_eq_true.mpr ?_⟩
  intro e member
  have checks := List.all_eq_true.mp previous.2 e member
  simp only [chksSemanticNI,List.all_append,Bool.and_eq_true] at checks
  simp only [chksSemanticFor,List.all_append,Bool.and_eq_true]
  refine ⟨?_,checks.2⟩
  simp only [staticChksSemanticFor,List.all_map,List.all_eq_true,Function.comp_def]
  intro check member
  have accepted := List.all_eq_true.mp checks.1 check member
  split <;> simp_all

/-- A call accepted by the old register check keeps its verdict when every callee uses that branch. -/
theorem returnPinSiteB_of_previous {L : LinkSys} {g : Clif.Function} {info : CallInfo}
    (lower : ∀ h ∈ L.P.funcs,SemanticNI.check h (L.A h).vc = true)
    (previous : siteOk L.P g (indToB L.syms g) (L.A g).vcp info = true) :
    L.returnPinSiteB g info = true := by
  cases dest : info.dest with
  | sym name =>
    cases found : L.P.func? name with
    | none => simp [LinkSys.returnPinSiteB,dest,found]
    | some h =>
      obtain ⟨_,uses,definitions,same,_,pins⟩ := siteOk_sound previous dest found
      have defs : info.defs = callDefs definitions := congrArg CallInfo.defs same
      simp only [LinkSys.returnPinSiteB,dest,found]
      rw [defs,returnPinCheck_previous (lower h (Clif.Program.func?_some found).1)]
      simpa only [decide_eq_true_eq] using pins
  | reg r =>
    have indirect := siteOk_reg previous (fun n impossible => by rw [dest] at impossible; cases impossible)
    obtain ⟨t,uses,definitions,same,targets⟩ := blrOk_sound indirect
    subst info
    simp only [LinkSys.returnPinSiteB,List.all_eq_true]
    intro h member
    by_cases reachable : indToB L.syms g h = true
    · by_cases gotMatches : ∀ n,gotOf (L.A g).vcp t = some n → h.name = n
      · by_cases arity : (regLocs h.sig).length = uses.length
        · have pins := (targets h member reachable gotMatches arity).2
          have accepted : ReturnPinCheck.check (callDefs definitions) h (L.A h).vc = true := by
            rw [returnPinCheck_previous (lower h member)]
            simpa only [decide_eq_true_eq] using pins
          simp only [accepted,Bool.or_true]
        · simp [retPairs,arity]
      · cases found : gotOf (L.A g).vcp t with
        | none =>
          exact False.elim (gotMatches (by
            intro n impossible
            rw [found] at impossible
            cases impossible))
        | some name =>
          by_cases equal : h.name = name
          · exact False.elim (gotMatches (by
              intro n hn
              rw [found] at hn
              cases hn
              exact equal))
          · simp [equal]
    · have rejected : indToB L.syms g h = false := by
        cases value : indToB L.syms g h <;> simp_all
      simp only [rejected,Bool.not_false,Bool.true_or]

/-- The new physical scan accepts every instruction accepted by the previous call checks. -/
theorem returnPinsB_of_previous {L : LinkSys} {g : Clif.Function}
    (lower : ∀ h ∈ L.P.funcs,SemanticNI.check h (L.A h).vc = true)
    (previous : allInsts (L.A g).vcp
      (siteB (siteOk L.P g (indToB L.syms g) (L.A g).vcp)) = true) : L.returnPinsB g = true := by
  apply (array_all_iff _ _).2
  intro b vb block
  apply (array_all_iff _ _).2
  intro k i inst
  have accepted := allInsts_sound previous block inst
  cases i <;> try rfl
  all_goals exact returnPinSiteB_of_previous lower (by simpa only [siteB] using accepted)

/-- Original accepted artifacts need no new condition for physical return checking. -/
theorem okRReturnPins_of_previous (stage : Clif.Function → VCode → VCode)
    {I : LinkInput} {R : Res} (prepared : PreparedResults stage I R)
    (previous : okRSemanticNI stage I R = true) : okRReturnPins stage I R = true := by
  have lower : ∀ g ∈ (progOf R).funcs,SemanticNI.check g (artOf R g).vc = true :=
    fun g member => (semanticPreparedFacts stage prepared previous member).lowerOk
  simp only [okRReturnPins,Bool.and_eq_true,List.all_eq_true]
  refine ⟨okRSemanticFor_of_previous _ stage previous,fun g member => ?_⟩
  apply returnPinsB_of_previous (L := ofRes I R closedBase (fun _ => False)) lower
  exact (semanticPreparedFacts stage prepared previous member).sites


/-- Commit the complete attempted program only after its actual ABI-aware checks pass. -/
def LinkInput.resultsReturnPins (I : LinkInput) (cleanup : Bool) : Res :=
  let attempt := I.resultsProductionWith Stock.MemorySretCopy.lowerValidated cleanup
  if okRReturnPins (productionStage cleanup) I attempt then attempt
  else I.resultsProduction cleanup

/-- A successful attempt retains every actual artifact, not a reconstructed replacement. -/
theorem LinkInput.resultsReturnPins_accept (I : LinkInput) (cleanup : Bool)
    (accepted : okRReturnPins (productionStage cleanup) I
      (I.resultsProductionWith Stock.MemorySretCopy.lowerValidated cleanup) = true) :
    I.resultsReturnPins cleanup = I.resultsProductionWith Stock.MemorySretCopy.lowerValidated cleanup := by
  simp only [LinkInput.resultsReturnPins,accepted,↓reduceIte]

/-- Rejection retries the complete previous program with the exact original inputs. -/
theorem LinkInput.resultsReturnPins_retry (I : LinkInput) (cleanup : Bool)
    (rejected : okRReturnPins (productionStage cleanup) I
      (I.resultsProductionWith Stock.MemorySretCopy.lowerValidated cleanup) = false) :
    I.resultsReturnPins cleanup = I.resultsProduction cleanup := by
  simp only [LinkInput.resultsReturnPins,rejected,Bool.false_eq_true,↓reduceIte]

/-- Either complete branch retains its real preparation, allocation, emission, and layout facts. -/
theorem LinkInput.resultsReturnPins_prepared (I : LinkInput) (cleanup : Bool) :
    PreparedResults (productionStage cleanup) I (I.resultsReturnPins cleanup) := by
  unfold LinkInput.resultsReturnPins
  dsimp only
  split
  · exact I.resultsProductionWith_prepared Stock.MemorySretCopy.lowerValidated cleanup
  · exact I.resultsProduction_prepared cleanup

/-- Retry preserves the complete original source sequence, including names and signatures. -/
theorem LinkInput.resultsReturnPins_source (I : LinkInput) (cleanup : Bool) :
    progOf (I.resultsReturnPins cleanup) = progOf (I.resultsProduction cleanup) := by
  unfold LinkInput.resultsReturnPins
  dsimp only
  split
  · simp only [progOf,LinkInput.resultsProductionWith,LinkInput.resultsProduction,List.map_map,
      Function.comp_def]
  · rfl

/-- A previous successful program remains accepted without a new input condition. -/
theorem LinkInput.resultsReturnPins_checked (I : LinkInput) (cleanup : Bool)
    (previous : okRSemanticNI (productionStage cleanup) I (I.resultsProduction cleanup) = true) :
    okRReturnPins (productionStage cleanup) I (I.resultsReturnPins cleanup) = true := by
  unfold LinkInput.resultsReturnPins
  dsimp only
  split
  · assumption
  · exact okRReturnPins_of_previous _ (I.resultsProduction_prepared cleanup) previous

/-- The producer derives its complete return-pin contract from the original checker conditions. -/
theorem LinkInput.resultsReturnPins_sound (I : LinkInput) (cleanup : Bool)
    (previous : okRSemanticNI (productionStage cleanup) I (I.resultsProduction cleanup) = true)
    {B : BaseEnv} {F : BitVec 64 → Prop}
    (base : BaseOk (ofRes I (I.resultsReturnPins cleanup) B F))
    (world : ∀ a,(ofRes I (I.resultsReturnPins cleanup) B F).Img a → F a) :
    (ofRes I (I.resultsReturnPins cleanup) B F).OkSemanticReturnPins :=
  semanticPreparedReturnPinsResults_sound (productionStage cleanup) (productionStage_cases cleanup)
    (I.resultsReturnPins_prepared cleanup) (I.resultsReturnPins_checked cleanup previous) base world

/-- The complete checked producer supplies the original program statement in every valid world. -/
theorem LinkInput.resultsReturnPins_correct (I : LinkInput) (cleanup : Bool)
    (previous : okRSemanticNI (productionStage cleanup) I (I.resultsProduction cleanup) = true)
    (name : String) : CrateStmtReturnPins I (I.resultsReturnPins cleanup) name :=
  preparedReturnPins_correct (productionStage cleanup) (productionStage_cases cleanup)
    (I.resultsReturnPins_prepared cleanup) (I.resultsReturnPins_checked cleanup previous) name

end E2E.LinkCheck
