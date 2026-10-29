module

public import FV.E2E.ProductionPipeline

@[expose] public section

set_option autoImplicit false
namespace E2E.BinCheck
open Backend E2E.LinkCheck Elf

def artInProduction (I : LinkInput) (cleanup : Bool) (fi : FnInput) : Art :=
  getOk (I.pipeProduction cleanup fi)

def codeBProduction (I : LinkInput) (cleanup : Bool) (ex : Excerpt) (fs : List FnInput) : Bool :=
  match phdrs (exRd ex) with
  | some phs => fs.all fun fi => artB I (exRd ex) phs (artInProduction I cleanup fi)
  | none => false

def ArtsOkProduction (I : LinkInput) (cleanup : Bool) (file : ByteArray) (fs : List FnInput) : Prop :=
  ∀ fi ∈ fs, ArtOk I file (artInProduction I cleanup fi)

theorem codeBProduction_sound {I : LinkInput}
    {cleanup : Bool}
    {ex : Excerpt} {fs : List FnInput} (h : codeBProduction I cleanup ex fs = true)
    {file : ByteArray} (hA : Agrees file ex) : ArtsOkProduction I cleanup file fs := by
  unfold codeBProduction at h
  split at h
  · rename_i phs hp
    exact fun fi hfi => artB_sound hA hp (List.all_eq_true.1 h fi hfi)
  · cases h

theorem binOkProduction_of_checks {I : LinkInput}
    {cleanup : Bool}
    {D : List Clif.DataObject} {file : ByteArray} (hs : Static file)
    (hc : ArtsOkProduction I cleanup file I.funcs)
    (hd : ∀ o ∈ D, DataOk I file o) (hy : SymsOk I file) :
    BinOkWithResults I (I.resultsProduction cleanup) D file := by
  refine ⟨hs, fun e he => ?_, hd, hy⟩
  simp only [tabOf, LinkInput.resultsProduction, List.map_map, List.mem_map,
    Function.comp] at he
  obtain ⟨fi, hfi, rfl⟩ := he
  exact hc fi hfi

theorem img_bytesProduction {I : LinkInput}
    {cleanup : Bool}
    {D : List Clif.DataObject} {file : ByteArray}
    (hB : BinOkWithResults I (I.resultsProduction cleanup) D file)
    (hI : okRWith (productionStage cleanup) I (I.resultsProduction cleanup) = true)
    {a : BitVec 64} (ha : ImgT (tabOf (I.resultsProduction cleanup)) a) :
    Elf.ro file a ∧
      (loadMem file a = some (memT (tabOf (I.resultsProduction cleanup)) a) ∨
        RelocAtWithResults I (I.resultsProduction cleanup) a) := by
  have himg : imgB (tabOf (I.resultsProduction cleanup)) = true :=
    okRWith_global (productionStage cleanup) hI
      ("imgCode: the image reads back", imgB (tabOf (I.resultsProduction cleanup)))
      (by simp [globalChks])
  exact img_bytesWithResults hB himg ha

end E2E.BinCheck

namespace E2E.LinkCheck
open Backend

def globalBProduction (I : LinkInput) (cleanup : Bool) : Bool :=
  let R := I.resultsProduction cleanup
  (globalChks I (progOf R) (tabOf R)).all (·.2)

def fnsBProduction (I : LinkInput) (cleanup : Bool) (fs : List FnInput) : Bool :=
  let R := I.resultsProduction cleanup
  fs.all fun fi => (chksWith (productionStage cleanup) I (progOf R) (tabOf R) fi.func
    (I.pipeProduction cleanup fi)).all (·.2)

theorem fnsBProduction_append (I : LinkInput) (cleanup : Bool) (a b : List FnInput) :
    fnsBProduction I cleanup (a ++ b) =
      (fnsBProduction I cleanup a && fnsBProduction I cleanup b) := by
  simp only [fnsBProduction, List.all_append]

theorem okRProduction_of_checks {I : LinkInput} {cleanup : Bool}
    (hg : globalBProduction I cleanup = true)
    (hf : fnsBProduction I cleanup I.funcs = true) :
    okRWith (productionStage cleanup) I (I.resultsProduction cleanup) = true := by
  unfold okRWith
  rw [Bool.and_eq_true]
  constructor
  · exact hg
  · simpa only [fnsBProduction, LinkInput.resultsProduction, List.all_map,
      Function.comp_def] using hf

end E2E.LinkCheck

namespace E2E.BinCheck
open Backend E2E.LinkCheck

theorem artsOkProduction_append {I : LinkInput} {cleanup : Bool}
    {file : ByteArray} {a b : List FnInput}
    (ha : ArtsOkProduction I cleanup file a)
    (hb : ArtsOkProduction I cleanup file b) :
    ArtsOkProduction I cleanup file (a ++ b) := by
  intro fi hfi
  rcases List.mem_append.mp hfi with h | h
  · exact ha fi h
  · exact hb fi h
end E2E.BinCheck

namespace E2E.LinkCheck
open Backend

def CrateStmtProduction (I : LinkInput) (cleanup : Bool) (n : String) : Prop :=
  ∀ (B : BaseEnv) (F : BitVec 64 → Prop),
    BaseOk (ofRes I (I.resultsProduction cleanup) B F) →
    (∀ a, (ofRes I (I.resultsProduction cleanup) B F).Img a → F a) →
    ProgStmt (ofRes I (I.resultsProduction cleanup) B F) n

theorem crate_correct_production (I : LinkInput) (cleanup : Bool)
    (hI : okRWith (productionStage cleanup) I (I.resultsProduction cleanup) = true) (n : String) :
    CrateStmtProduction I cleanup n :=
  fun _ _ hB hF f hf M _ _ _ _ _ hent hres hFeq hgfree himg hbe hargs hcs hsav hrel hpl htr =>
    backend_correct_program_production _
      (I.resultsProduction_sound cleanup hI hB hF)
      (Clif.Program.func?_some hf).1 M hent hres hFeq hgfree himg hbe hargs hcs hsav hrel hpl htr
end E2E.LinkCheck
