import FV.Backend.VoidCallABIProduction
import FV.E2E.PreparedReturnPinCalls
import FV.E2E.ActualCompilerModes

namespace E2E.LinkCheck.VoidCallFile
open Backend Backend.Proof Backend.Proof.Driver E2E E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false

def fromResult (R : Res) (f : Clif.Function) : ReturnPinFile.Entry :=
  ⟨f,(artOf R f).vc,(artOf R f).vcp,Thunk.mk (fun _ => ReturnPinCheck.pins f (artOf R f).vc),rfl⟩

def ofResults (R : Res) : List ReturnPinFile.Entry := (progOf R).funcs.map (fromResult R)

theorem direct_ofResults (R : Res) (name : String) :
    (ReturnPinFile.context (ofResults R)).direct name = ((progOf R).func? name).map (fromResult R) := by
  rw [ReturnPinFile.context_direct]
  simp only [ofResults,List.find?_map,Function.comp_def,fromResult,Clif.Program.func?]

theorem site_sound (I : LinkInput) (R : Res) (g : Clif.Function) (info : CallInfo)
    (checked : ReturnPinFile.site (ReturnPinFile.context (ofResults R)) info = true) :
    (ofRes I R closedBase (fun _ => False)).returnPinSiteB g info = true := by
  cases destination : info.dest with
  | sym name =>
    simp only [ReturnPinFile.site,destination,direct_ofResults] at checked
    simp only [LinkSys.returnPinSiteB,destination,ofRes]
    cases found : (progOf R).func? name with
    | none => rfl
    | some target =>
      simp only [found,Option.map_some] at checked
      simpa only [ReturnPinFile.Entry.matches_eq,fromResult] using checked
  | reg register =>
    cases register with
    | vreg index cls =>
      cases cls with
      | int =>
        simp only [ReturnPinFile.site,destination,ReturnPinFile.context,ofResults,
          List.all_map,List.all_eq_true,Function.comp_def] at checked
        simp only [LinkSys.returnPinSiteB,destination,ofRes,List.all_eq_true]
        intro target member
        have selected := checked target member
        simp only [fromResult,ReturnPinFile.Entry.matches_eq] at selected
        simp only [Bool.or_eq_true] at selected
        rcases selected with arity | matched
        · simp only [Bool.or_eq_true]
          exact Or.inl (Or.inr (show decide ((regLocs target.sig).length ≠ info.uses.length) = true from arity))
        · simp [matched]
      | float => simp only [LinkSys.returnPinSiteB,destination]
    | x index => simp only [LinkSys.returnPinSiteB,destination]
    | xzr => simp only [LinkSys.returnPinSiteB,destination]
    | sp => simp only [LinkSys.returnPinSiteB,destination]
    | v index => simp only [LinkSys.returnPinSiteB,destination]

theorem check_sound (I : LinkInput) (R : Res)
    (checked : ReturnPinFile.check (ofResults R) = true) :
    (progOf R).funcs.all (returnPinChecks I R) = true := by
  simp only [ReturnPinFile.check,ofResults,List.all_map,List.all_eq_true,Function.comp_def] at checked
  simp only [List.all_eq_true]
  intro g member
  have blocks := checked g member
  simp only [fromResult] at blocks
  change allInsts (artOf R g).vcp (siteB ((ofRes I R closedBase (fun _ => False)).returnPinSiteB g)) = true
  refine (array_all_iff _ _).2 ?_
  intro b vb block
  have instructions := (array_all_iff _ _).1 blocks b vb block
  refine (array_all_iff _ _).2 ?_
  intro k i inst
  have checkedInst := (array_all_iff _ _).1 instructions k i inst
  cases i <;> simp only [ReturnPinFile.instruction,siteB] at checkedInst ⊢ <;>
    first | rfl | exact site_sound I R g _ checkedInst

end E2E.LinkCheck.VoidCallFile

namespace E2E.LinkCheck.VoidCallFile
open Backend Backend.Proof Backend.Proof.Driver E2E E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false

theorem entry_of_artifact {I : LinkInput} {R : Res} {cleanup : Bool}
    (verify : Clif.Function → Bool)
    (provenance : ResOkWithLowering (fun f => lowerCheckedVoidCallABI f (verify f))
      (productionStage cleanup) I R)
    (checked : okRSemanticFor returnPinCallsExtra (productionStage cleanup) I R = true)
    {g : Clif.Function} (member : g ∈ (progOf R).funcs) :
    ReturnPinFile.entry g (verify g) cleanup = .ok (fromResult R g) := by
  have names := okRSemanticFor_names returnPinCallsExtra (productionStage cleanup) checked
  obtain ⟨e,present,rfl,artifact⟩ := artOf_spec names member
  have success : e.2.toBool = true := by
    simp only [okRSemanticFor,Bool.and_eq_true,List.all_eq_true] at checked
    exact checked.2 e present ("compiled: pipeline",e.2.toBool)
      (by simp [chksSemanticFor,staticChksSemanticFor_expanded])
  obtain ⟨lower,prepared,_,_,_,_⟩ := provenance e present _ (getOk_eq success)
  have prepared' : prepare (Stock.Arithmetic.stage cleanup (getOk e.2).vc) = .ok (getOk e.2).vcp := by
    cases cleanup <;> simpa [productionStage,Stock.Arithmetic.stage] using prepared
  simp only [ReturnPinFile.entry,fromResult,artifact,lower,bind,Except.bind,prepared',pure,Except.pure]

theorem entries_of_artifacts {I : LinkInput} {R : Res} {cleanup : Bool}
    (verify : Clif.Function → Bool)
    (provenance : ResOkWithLowering (fun f => lowerCheckedVoidCallABI f (verify f))
      (productionStage cleanup) I R)
    (checked : okRSemanticFor returnPinCallsExtra (productionStage cleanup) I R = true) :
    (progOf R).funcs.mapM (fun g => ReturnPinFile.entry g (verify g) cleanup) = .ok (ofResults R) := by
  have map_eq : ∀ sources : List Clif.Function,
      (∀ g ∈ sources,ReturnPinFile.entry g (verify g) cleanup = .ok (fromResult R g)) →
      sources.mapM (fun g => ReturnPinFile.entry g (verify g) cleanup) = .ok (sources.map (fromResult R)) := by
    intro sources
    induction sources with
    | nil => intro each; rfl
    | cons g sources ih =>
      intro each
      have head := each g (by simp)
      have tail := ih (fun f member => each f (by simp [member]))
      simp only [List.mapM_cons,head,bind,Except.bind,tail,pure,Except.pure,List.map_cons]
  exact map_eq _ (fun g member => entry_of_artifact verify provenance checked member)

theorem checked_artifacts_sound {I : LinkInput} {R : Res} {cleanup : Bool}
    (verify : Clif.Function → Bool)
    (provenance : ResOkWithLowering (fun f => lowerCheckedVoidCallABI f (verify f))
      (productionStage cleanup) I R)
    (checked : okRSemanticFor returnPinCallsExtra (productionStage cleanup) I R = true)
    (pins : ((progOf R).funcs.mapM (fun g => ReturnPinFile.entry g (verify g) cleanup)).toOption.any
      ReturnPinFile.check = true)
    {B : BaseEnv} {F : BitVec 64 → Prop} (base : BaseOk (ofRes I R B F))
    (world : ∀ a,(ofRes I R B F).Img a → F a) : (ofRes I R B F).OkSemanticReturnPins := by
  have entries := entries_of_artifacts verify provenance checked
  rw [entries] at pins
  have physical : ReturnPinFile.check (ofResults R) = true := pins
  have prepared : PreparedResults (productionStage cleanup) I R := by
    intro e member a success
    exact (provenance e member a success).2
  exact semanticPreparedReturnPinCallsResults_sound (productionStage cleanup) (productionStage_cases cleanup)
    prepared (Bool.and_eq_true_iff.mpr ⟨checked,check_sound I R physical⟩) base world

theorem results_sound (I : LinkInput) (cleanup : Bool) (verify : Clif.Function → Bool)
    (checked : okRSemanticFor returnPinCallsExtra (productionStage cleanup) I
      (I.resultsWithLowering (fun f => lowerCheckedVoidCallABI f (verify f)) (productionStage cleanup)) = true)
    (pins : ((progOf (I.resultsWithLowering (fun f => lowerCheckedVoidCallABI f (verify f))
      (productionStage cleanup))).funcs.mapM (fun g => ReturnPinFile.entry g (verify g) cleanup)).toOption.any
        ReturnPinFile.check = true)
    {B : BaseEnv} {F : BitVec 64 → Prop}
    (base : BaseOk (ofRes I (I.resultsWithLowering (fun f => lowerCheckedVoidCallABI f (verify f))
      (productionStage cleanup)) B F))
    (world : ∀ a,(ofRes I (I.resultsWithLowering (fun f => lowerCheckedVoidCallABI f (verify f))
      (productionStage cleanup)) B F).Img a → F a) :
    (ofRes I (I.resultsWithLowering (fun f => lowerCheckedVoidCallABI f (verify f))
      (productionStage cleanup)) B F).OkSemanticReturnPins :=
  checked_artifacts_sound verify (I.resultsWithLowering_provenance _ _) checked pins base world

theorem results_correct (I : LinkInput) (cleanup : Bool) (verify : Clif.Function → Bool)
    (checked : okRSemanticFor returnPinCallsExtra (productionStage cleanup) I
      (I.resultsWithLowering (fun f => lowerCheckedVoidCallABI f (verify f)) (productionStage cleanup)) = true)
    (pins : ((progOf (I.resultsWithLowering (fun f => lowerCheckedVoidCallABI f (verify f))
      (productionStage cleanup))).funcs.mapM (fun g => ReturnPinFile.entry g (verify g) cleanup)).toOption.any
        ReturnPinFile.check = true) (name : String) :
    CrateStmtReturnPins I (I.resultsWithLowering (fun f => lowerCheckedVoidCallABI f (verify f))
      (productionStage cleanup)) name := by
  intro B F base world f found M ra s w₀ args cs entry room frame free image body arguments source
    avoids relation placement traps
  exact backend_correct_program_return_pins _ (results_sound I cleanup verify checked pins base world)
    (Clif.Program.func?_some found).1 M entry room frame free image body arguments source
    avoids relation placement traps

end E2E.LinkCheck.VoidCallFile
