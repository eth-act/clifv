import FV.E2E.ProductionPipelineWith
import FV.E2E.SemanticPreparedPipeline

set_option autoImplicit false
namespace E2E.SemanticChecksWith
open E2E.BinCheck E2E.LinkCheck Elf
variable {lower : ProductionLowering}
open Backend E2E.SemanticChecksWith Elf

def artInProduction (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool) (fi : FnInput) : Art :=
  getOk (I.pipeProductionWith lower cleanup fi)

def codeBProduction (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool) (ex : Excerpt) (fs : List FnInput) : Bool :=
  match phdrs (exRd ex) with
  | some phs => fs.all fun fi => artB I (exRd ex) phs (artInProduction lower I cleanup fi)
  | none => false

def ArtsOkProduction (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool) (file : ByteArray) (fs : List FnInput) : Prop :=
  ∀ fi ∈ fs, ArtOk I file (artInProduction lower I cleanup fi)

theorem codeBProduction_sound {I : LinkInput}
    {cleanup : Bool}
    {ex : Excerpt} {fs : List FnInput} (h : codeBProduction lower I cleanup ex fs = true)
    {file : ByteArray} (hA : Agrees file ex) : ArtsOkProduction lower I cleanup file fs := by
  unfold codeBProduction at h
  split at h
  · rename_i phs hp
    exact fun fi hfi => artB_sound hA hp (List.all_eq_true.1 h fi hfi)
  · cases h

theorem binOkProduction_of_checks {I : LinkInput}
    {cleanup : Bool}
    {D : List Clif.DataObject} {file : ByteArray} (hs : Static file)
    (hc : ArtsOkProduction lower I cleanup file I.funcs)
    (hd : ∀ o ∈ D, DataOk I file o) (hy : SymsOk I file) :
    BinOkWithResults I (I.resultsProductionWith lower cleanup) D file := by
  refine ⟨hs, fun e he => ?_, hd, hy⟩
  simp only [tabOf, LinkInput.resultsProductionWith, List.map_map, List.mem_map,
    Function.comp] at he
  obtain ⟨fi, hfi, rfl⟩ := he
  exact hc fi hfi

theorem img_bytesProduction {I : LinkInput}
    {cleanup : Bool}
    {D : List Clif.DataObject} {file : ByteArray}
    (hB : BinOkWithResults I (I.resultsProductionWith lower cleanup) D file)
    (hI : okRSemanticNI (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true)
    {a : BitVec 64} (ha : ImgT (tabOf (I.resultsProductionWith lower cleanup)) a) :
    Elf.ro file a ∧
      (loadMem file a = some (memT (tabOf (I.resultsProductionWith lower cleanup)) a) ∨
        RelocAtWithResults I (I.resultsProductionWith lower cleanup) a) := by
  have himg : imgB (tabOf (I.resultsProductionWith lower cleanup)) = true :=
    okRSemanticNI_global (productionStage cleanup) hI
      ("imgCode: the image reads back", imgB (tabOf (I.resultsProductionWith lower cleanup)))
      (by simp [globalChks])
  exact img_bytesWithResults hB himg ha

end E2E.SemanticChecksWith

namespace E2E.SemanticChecksWith
open E2E.BinCheck E2E.LinkCheck Elf
variable {lower : ProductionLowering}
open Backend

def globalBProduction (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool) : Bool :=
  let R := I.resultsProductionWith lower cleanup
  (globalChks I (progOf R) (tabOf R)).all (·.2)

def fnsBProduction (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool) (fs : List FnInput) : Bool :=
  let R := I.resultsProductionWith lower cleanup
  fs.all fun fi => (chksSemanticNI (productionStage cleanup) I (progOf R) (tabOf R) fi.func
    (I.pipeProductionWith lower cleanup fi)).all (·.2)

theorem fnsBProduction_append (I : LinkInput) (cleanup : Bool) (a b : List FnInput) :
    fnsBProduction lower I cleanup (a ++ b) =
      (fnsBProduction lower I cleanup a && fnsBProduction lower I cleanup b) := by
  simp only [fnsBProduction, List.all_append]

theorem okRProduction_of_checks {I : LinkInput} {cleanup : Bool}
    (hg : globalBProduction lower I cleanup = true)
    (hf : fnsBProduction lower I cleanup I.funcs = true) :
    okRSemanticNI (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true := by
  unfold okRSemanticNI
  rw [Bool.and_eq_true]
  constructor
  · exact hg
  · simpa only [fnsBProduction, LinkInput.resultsProductionWith, List.all_map,
      Function.comp_def] using hf

end E2E.SemanticChecksWith

namespace E2E.SemanticChecksWith
open E2E.BinCheck E2E.LinkCheck Elf
variable {lower : ProductionLowering}
open Backend E2E.SemanticChecksWith

theorem artsOkProduction_append {I : LinkInput} {cleanup : Bool}
    {file : ByteArray} {a b : List FnInput}
    (ha : ArtsOkProduction lower I cleanup file a)
    (hb : ArtsOkProduction lower I cleanup file b) :
    ArtsOkProduction lower I cleanup file (a ++ b) := by
  intro fi hfi
  rcases List.mem_append.mp hfi with h | h
  · exact ha fi h
  · exact hb fi h
end E2E.SemanticChecksWith

namespace E2E.SemanticChecksWith
open E2E.BinCheck E2E.LinkCheck Elf
variable {lower : ProductionLowering}
open Backend

def CrateStmtProduction (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool) (n : String) : Prop :=
  ∀ (B : BaseEnv) (F : BitVec 64 → Prop),
    BaseOk (ofRes I (I.resultsProductionWith lower cleanup) B F) →
    (∀ a, (ofRes I (I.resultsProductionWith lower cleanup) B F).Img a → F a) →
    ProgStmt (ofRes I (I.resultsProductionWith lower cleanup) B F) n

theorem crate_correct_production (I : LinkInput) (cleanup : Bool)
    (hI : okRSemanticNI (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true) (n : String) :
    CrateStmtProduction lower I cleanup n :=
  fun _ _ hB hF f hf M _ _ _ _ _ hent hres hFeq hgfree himg hbe hargs hcs hsav hrel hpl htr =>
    backend_correct_program_semantic _
      (semanticPreparedResults_sound (productionStage cleanup) (productionStage_cases cleanup)
        (I.resultsProductionWith_prepared lower cleanup) hI hB hF)
      (Clif.Program.func?_some hf).1 M hent hres hFeq hgfree himg hbe hargs hcs hsav hrel hpl htr
end E2E.SemanticChecksWith
