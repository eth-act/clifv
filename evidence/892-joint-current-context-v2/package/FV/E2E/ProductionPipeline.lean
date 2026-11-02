import FV.Backend.Lowering.StockProduction
import FV.E2E.PreparedPipeline
import FV.E2E.ActualCompilerModes

/-! A complete production pipeline attempt, retried with the retained D0/legacy
lowering on any lowering/preparation/allocation/emission/layout error. -/
set_option autoImplicit false
namespace E2E.LinkCheck
open Backend

def productionStage (cleanup : Bool) : Clif.Function → VCode → VCode :=
  fun _ => cond cleanup DeadCleanup.prune id

def LinkInput.pipeProduction (I : LinkInput) (cleanup : Bool) (fi : FnInput) : Except String Art :=
  match I.pipeOfWithLowering Stock.Production.lower (productionStage cleanup) fi with
  | .ok a => .ok a
  | .error _ => I.pipeOfWithLowering Stock.D0.defaultLower (productionStage cleanup) fi

def LinkInput.resultsProduction (I : LinkInput) (cleanup : Bool) : Res :=
  I.funcs.map fun fi => (fi.func, I.pipeProduction cleanup fi)

theorem productionStage_cases (cleanup : Bool) :
    productionStage cleanup = (fun _ => id) ∨ productionStage cleanup = (fun _ => DeadCleanup.prune) := by
  cases cleanup with
  | false => exact .inl rfl
  | true => exact .inr rfl

theorem LinkInput.pipeProduction_spec {I : LinkInput} {cleanup : Bool} {fi : FnInput} {a : Art}
    (h : I.pipeProduction cleanup fi = .ok a) :
    (Stock.Production.lower fi.func = .ok a.vc ∨ Stock.D0.defaultLower fi.func = .ok a.vc) ∧
    prepare (productionStage cleanup fi.func a.vc) = .ok a.vcp ∧
    lowerRFunc a.vcp a.rf = .ok a.af ∧ emitFunc a.k a.af = .ok a.fa ∧
    a.fa.layout = .ok a.fb ∧ a.k = fi.k ∧
    a.base = BitVec.ofNat 64 (I.baseOf fi.func.name) := by
  unfold LinkInput.pipeProduction at h
  split at h
  · rename_i a' htry
    cases h
    obtain ⟨hl, hp, ha, he, hb, hk, hbase⟩ := LinkInput.pipeOfWithLowering_provenance htry
    exact ⟨.inl hl, hp, ha, he, hb, hk, hbase⟩
  · obtain ⟨hl, hp, ha, he, hb, hk, hbase⟩ := LinkInput.pipeOfWithLowering_provenance h
    exact ⟨.inr hl, hp, ha, he, hb, hk, hbase⟩

theorem LinkInput.pipeProduction_success {I : LinkInput} {cleanup : Bool} {fi : FnInput} {a : Art}
    (h : I.pipeOfWithLowering Stock.Production.lower (productionStage cleanup) fi = .ok a) :
    I.pipeProduction cleanup fi = .ok a := by
  simp only [LinkInput.pipeProduction, h]

theorem LinkInput.pipeProduction_retry {I : LinkInput} {cleanup : Bool} {fi : FnInput} {message : String}
    (h : I.pipeOfWithLowering Stock.Production.lower (productionStage cleanup) fi = .error message) :
    I.pipeProduction cleanup fi =
      I.pipeOfWithLowering Stock.D0.defaultLower (productionStage cleanup) fi := by
  simp only [LinkInput.pipeProduction, h]

theorem LinkInput.resultsProduction_prepared (I : LinkInput) (cleanup : Bool) :
    PreparedResults (productionStage cleanup) I (I.resultsProduction cleanup) := by
  intro e he a ha
  obtain ⟨fi, hfi, rfl⟩ := List.mem_map.mp he
  obtain ⟨_, hp, hal, hem, hla, _, hb⟩ := LinkInput.pipeProduction_spec ha
  exact ⟨hp, hal, hem, hla, hb⟩

theorem LinkInput.resultsProduction_sound (I : LinkInput) (cleanup : Bool)
    (hI : okRWith (productionStage cleanup) I (I.resultsProduction cleanup) = true)
    {B : BaseEnv} {F : BitVec 64 → Prop}
    (hB : BaseOk (ofRes I (I.resultsProduction cleanup) B F))
    (hF : ∀ a, (ofRes I (I.resultsProduction cleanup) B F).Img a → F a) :
    (ofRes I (I.resultsProduction cleanup) B F).OkProduction :=
  preparedResults_sound (productionStage cleanup) (productionStage_cases cleanup)
    (I.resultsProduction_prepared cleanup) hI hB hF

end E2E.LinkCheck
