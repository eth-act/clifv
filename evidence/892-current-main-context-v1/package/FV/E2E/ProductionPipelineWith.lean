import FV.E2E.ProductionPipeline
import FV.Backend.Lowering.StockPrologueAll

/-! Lowerer-parametric transactional orchestration. Existing production APIs
retain their definitions; successive proved classes can share the preparation,
allocation, emission and layout provenance without changing those APIs. -/
set_option autoImplicit false
namespace E2E.LinkCheck
open Backend

abbrev ProductionLowering := Clif.Function → Except String VCode

def LinkInput.pipeProductionWith (I : LinkInput) (lower : ProductionLowering)
    (cleanup : Bool) (fi : FnInput) : Except String Art :=
  match I.pipeOfWithLowering lower (productionStage cleanup) fi with
  | .ok a => .ok a
  | .error _ => I.pipeOfWithLowering Stock.D0.defaultLower (productionStage cleanup) fi

def LinkInput.resultsProductionWith (I : LinkInput) (lower : ProductionLowering)
    (cleanup : Bool) : Res :=
  I.funcs.map fun fi => (fi.func, I.pipeProductionWith lower cleanup fi)

theorem LinkInput.pipeProductionWith_original (I : LinkInput) (cleanup : Bool) (fi : FnInput) :
    I.pipeProductionWith Stock.Production.lower cleanup fi = I.pipeProduction cleanup fi := rfl

theorem LinkInput.resultsProductionWith_original (I : LinkInput) (cleanup : Bool) :
    I.resultsProductionWith Stock.Production.lower cleanup = I.resultsProduction cleanup := rfl

theorem LinkInput.pipeProductionWith_spec {I : LinkInput} {lower : ProductionLowering}
    {cleanup : Bool} {fi : FnInput} {a : Art}
    (h : I.pipeProductionWith lower cleanup fi = .ok a) :
    (lower fi.func = .ok a.vc ∨ Stock.D0.defaultLower fi.func = .ok a.vc) ∧
    prepare (productionStage cleanup fi.func a.vc) = .ok a.vcp ∧
    lowerRFunc a.vcp a.rf = .ok a.af ∧ emitFunc a.k a.af = .ok a.fa ∧
    a.fa.layout = .ok a.fb ∧ a.k = fi.k ∧
    a.base = BitVec.ofNat 64 (I.baseOf fi.func.name) := by
  unfold LinkInput.pipeProductionWith at h
  split at h
  · rename_i a' htry
    cases h
    obtain ⟨hl, hp, ha, he, hb, hk, hbase⟩ := LinkInput.pipeOfWithLowering_provenance htry
    exact ⟨.inl hl, hp, ha, he, hb, hk, hbase⟩
  · obtain ⟨hl, hp, ha, he, hb, hk, hbase⟩ := LinkInput.pipeOfWithLowering_provenance h
    exact ⟨.inr hl, hp, ha, he, hb, hk, hbase⟩

theorem LinkInput.pipeProductionWith_retry {I : LinkInput} {lower : ProductionLowering}
    {cleanup : Bool} {fi : FnInput} {message : String}
    (h : I.pipeOfWithLowering lower (productionStage cleanup) fi = .error message) :
    I.pipeProductionWith lower cleanup fi =
      I.pipeOfWithLowering Stock.D0.defaultLower (productionStage cleanup) fi := by
  simp only [LinkInput.pipeProductionWith, h]

theorem LinkInput.resultsProductionWith_prepared (I : LinkInput) (lower : ProductionLowering)
    (cleanup : Bool) :
    PreparedResults (productionStage cleanup) I (I.resultsProductionWith lower cleanup) := by
  intro e he a ha
  obtain ⟨fi, hfi, rfl⟩ := List.mem_map.mp he
  obtain ⟨_, hp, hal, hem, hla, _, hb⟩ := LinkInput.pipeProductionWith_spec ha
  exact ⟨hp, hal, hem, hla, hb⟩

theorem LinkInput.resultsProductionWith_sound (I : LinkInput) (lower : ProductionLowering)
    (cleanup : Bool)
    (hI : okRWith (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true)
    {B : BaseEnv} {F : BitVec 64 → Prop}
    (hB : BaseOk (ofRes I (I.resultsProductionWith lower cleanup) B F))
    (hF : ∀ a, (ofRes I (I.resultsProductionWith lower cleanup) B F).Img a → F a) :
    (ofRes I (I.resultsProductionWith lower cleanup) B F).OkProduction :=
  preparedResults_sound (productionStage cleanup) (productionStage_cases cleanup)
    (I.resultsProductionWith_prepared lower cleanup) hI hB hF

abbrev LinkInput.pipePrologueAll (I : LinkInput) :=
  I.pipeProductionWith Stock.Prologue.AllConfigurations.lower

abbrev LinkInput.resultsPrologueAll (I : LinkInput) :=
  I.resultsProductionWith Stock.Prologue.AllConfigurations.lower

end E2E.LinkCheck
