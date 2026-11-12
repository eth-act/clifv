import FV.E2E.ActualBinCheck

/-! Preserve strict and fallback allocation modes, original k/j/oracle/base
metadata and actual lowering output. No new checks or input conditions. -/
set_option autoImplicit false

namespace E2E.LinkCheck
open Backend

theorem pipeWithLowering_actual_spec {lower : Clif.Function → Except String VCode}
    {stage : Clif.Function → VCode → VCode} {f : Clif.Function} {k : Nat} {base : BitVec 64} {o : Lean.Json} {a : Art}
    (h : pipeWithLowering lower stage f k base o = .ok a) :
    lower f = .ok a.vc ∧ prepare (stage f a.vc) = .ok a.vcp ∧ lowerRFunc a.vcp a.rf = .ok a.af ∧
      emitFunc a.k a.af = .ok a.fa ∧ a.fa.layout = .ok a.fb ∧ a.k = k ∧ a.base = base := by
  unfold pipeWithLowering at h
  rcases h1 : lower f with _ | vc <;> simp only [h1, bind, Except.bind] at h
  · cases h
  rcases h2 : prepare (stage f vc) with _ | vcp <;> simp only [h2] at h
  · cases h
  rcases h3 : parseRAOut o with _ | o' <;> simp only [h3] at h
  · cases h
  rcases h4 : buildRFunc vcp o' with _ | rf <;> simp only [h4] at h
  · cases h
  rcases h5 : lowerRFunc vcp rf with _ | af <;> simp only [h5] at h
  · cases h
  rcases h6 : emitFunc k af with _ | fa <;> simp only [h6] at h
  · cases h
  rcases h7 : fa.layout with _ | fb <;> simp only [h7] at h
  · cases h
  cases h
  exact ⟨rfl, h2, h5, h6, h7, rfl, rfl⟩


/-- Same original allocator-fallback flag, with explicit actual lowering/stage. -/
def LinkInput.pipeOfWithLowering (I : LinkInput)
    (lower : Clif.Function → Except String VCode) (stage : Clif.Function → VCode → VCode)
    (fi : FnInput) : Except String Art :=
  cond I.fallback (pipeTWithLowering lower stage) (pipeWithLowering lower stage)
    fi.func fi.k (BitVec.ofNat 64 (I.baseOf fi.func.name)) (raJ fi.ra fi.j)

def LinkInput.resultsWithLowering (I : LinkInput)
    (lower : Clif.Function → Except String VCode) (stage : Clif.Function → VCode → VCode) : Res :=
  I.funcs.map fun fi => (fi.func, I.pipeOfWithLowering lower stage fi)

theorem LinkInput.pipeOfWithLowering_provenance {I : LinkInput}
    {lower : Clif.Function → Except String VCode} {stage : Clif.Function → VCode → VCode}
    {fi : FnInput} {a : Art} (h : I.pipeOfWithLowering lower stage fi = .ok a) :
    lower fi.func = .ok a.vc ∧ prepare (stage fi.func a.vc) = .ok a.vcp ∧
      lowerRFunc a.vcp a.rf = .ok a.af ∧ emitFunc a.k a.af = .ok a.fa ∧
      a.fa.layout = .ok a.fb ∧ a.k = fi.k ∧
      a.base = BitVec.ofNat 64 (I.baseOf fi.func.name) := by
  unfold LinkInput.pipeOfWithLowering at h
  cases flag : I.fallback with
  | false =>
    simp only [flag, cond] at h
    exact pipeWithLowering_actual_spec h
  | true =>
    simp only [flag, cond] at h
    obtain ⟨lowered, prep, rf, alloc, emit, layout, index, addr⟩ :=
      E2E.LinkCheck.pipeTWithLowering_spec h
    exact ⟨lowered, prep, alloc, emit, layout, index, addr⟩

theorem LinkInput.resultsWithLowering_provenance (I : LinkInput)
    (lower : Clif.Function → Except String VCode) (stage : Clif.Function → VCode → VCode) :
    ResOkWithLowering lower stage I (I.resultsWithLowering lower stage) := by
  intro e he a ha
  unfold LinkInput.resultsWithLowering at he
  obtain ⟨fi, hfi, rfl⟩ := List.mem_map.mp he
  obtain ⟨lowered, prep, alloc, emit, layout, index, addr⟩ :=
    LinkInput.pipeOfWithLowering_provenance ha
  exact ⟨lowered, prep, alloc, emit, layout, addr⟩

theorem LinkInput.resultsWithLowering_legacy (I : LinkInput) :
    I.resultsWithLowering lowerFunction (fun _ => id) = I.results := by
  cases flag : I.fallback <;> simp only [LinkInput.resultsWithLowering, LinkInput.results, LinkInput.pipeOf,
    LinkInput.pipeOfWithLowering, pipe, pipeT, pipeWithLowering, pipeTWithLowering,
    flag, cond, Stock.D0.defaultLower_eq_legacy]

theorem LinkInput.resultsWithLowering_sound (I : LinkInput)
    (lower : Clif.Function → Except String VCode) (stage : Clif.Function → VCode → VCode)
    (hstage : stage = (fun _ => id) ∨ stage = cleanupStage)
    (hI : okRWith stage I (I.resultsWithLowering lower stage) = true)
    {B : BaseEnv} {F : BitVec 64 → Prop}
    (hB : BaseOk (ofRes I (I.resultsWithLowering lower stage) B F))
    (hF : ∀ a, (ofRes I (I.resultsWithLowering lower stage) B F).Img a → F a) :
    (ofRes I (I.resultsWithLowering lower stage) B F).OkProduction :=
  okRWithLowering_sound lower stage hstage
    (I.resultsWithLowering_provenance lower stage) hI hB hF

def CrateStmtWithCompilerModes (I : LinkInput)
    (lower : Clif.Function → Except String VCode) (stage : Clif.Function → VCode → VCode) (n : String) : Prop :=
  ∀ (B : BaseEnv) (F : BitVec 64 → Prop),
    BaseOk (ofRes I (I.resultsWithLowering lower stage) B F) →
    (∀ a, (ofRes I (I.resultsWithLowering lower stage) B F).Img a → F a) →
    ProgStmt (ofRes I (I.resultsWithLowering lower stage) B F) n

theorem crate_correct_withCompilerModes (I : LinkInput)
    (lower : Clif.Function → Except String VCode) (stage : Clif.Function → VCode → VCode)
    (hstage : stage = (fun _ => id) ∨ stage = cleanupStage)
    (hI : okRWith stage I (I.resultsWithLowering lower stage) = true) (n : String) :
    CrateStmtWithCompilerModes I lower stage n :=
  fun _ _ hB hF f hf M _ _ _ _ _ hent hres hFeq hgfree himg hbe hargs hcs hsav hrel hpl htr =>
    backend_correct_program_production _
      (I.resultsWithLowering_sound lower stage hstage hI hB hF)
      (Clif.Program.func?_some hf).1 M hent hres hFeq hgfree himg hbe hargs hcs hsav hrel hpl htr

end E2E.LinkCheck

namespace E2E.BinCheck
open Backend E2E.LinkCheck Elf

def artInWithCompilerModes (I : LinkInput) (lower : Clif.Function → Except String VCode)
    (stage : Clif.Function → VCode → VCode) (fi : FnInput) : Art :=
  getOk (I.pipeOfWithLowering lower stage fi)

def codeBWithCompilerModes (I : LinkInput) (lower : Clif.Function → Except String VCode)
    (stage : Clif.Function → VCode → VCode) (ex : Excerpt) (fs : List FnInput) : Bool :=
  match phdrs (exRd ex) with
  | some phs => fs.all fun fi => artB I (exRd ex) phs (artInWithCompilerModes I lower stage fi)
  | none => false

def ArtsOkWithCompilerModes (I : LinkInput) (lower : Clif.Function → Except String VCode)
    (stage : Clif.Function → VCode → VCode) (file : ByteArray) (fs : List FnInput) : Prop :=
  ∀ fi ∈ fs, ArtOk I file (artInWithCompilerModes I lower stage fi)

theorem codeBWithCompilerModes_sound {I : LinkInput}
    {lower : Clif.Function → Except String VCode} {stage : Clif.Function → VCode → VCode}
    {ex : Excerpt} {fs : List FnInput} (h : codeBWithCompilerModes I lower stage ex fs = true)
    {file : ByteArray} (hA : Agrees file ex) : ArtsOkWithCompilerModes I lower stage file fs := by
  unfold codeBWithCompilerModes at h
  split at h
  · rename_i phs hp
    exact fun fi hfi => artB_sound hA hp (List.all_eq_true.1 h fi hfi)
  · cases h

theorem binOkWithResults_ofCompilerModes {I : LinkInput}
    {lower : Clif.Function → Except String VCode} {stage : Clif.Function → VCode → VCode}
    {D : List Clif.DataObject} {file : ByteArray} (hs : Static file)
    (hc : ArtsOkWithCompilerModes I lower stage file I.funcs)
    (hd : ∀ o ∈ D, DataOk I file o) (hy : SymsOk I file) :
    BinOkWithResults I (I.resultsWithLowering lower stage) D file := by
  refine ⟨hs, fun e he => ?_, hd, hy⟩
  simp only [tabOf, LinkInput.resultsWithLowering, List.map_map, List.mem_map,
    Function.comp] at he
  obtain ⟨fi, hfi, rfl⟩ := he
  exact hc fi hfi

theorem img_bytesWithCompilerModes {I : LinkInput}
    {lower : Clif.Function → Except String VCode} {stage : Clif.Function → VCode → VCode}
    {D : List Clif.DataObject} {file : ByteArray}
    (hB : BinOkWithResults I (I.resultsWithLowering lower stage) D file)
    (hI : okRWith stage I (I.resultsWithLowering lower stage) = true)
    {a : BitVec 64} (ha : ImgT (tabOf (I.resultsWithLowering lower stage)) a) :
    Elf.ro file a ∧
      (loadMem file a = some (memT (tabOf (I.resultsWithLowering lower stage)) a) ∨
        RelocAtWithResults I (I.resultsWithLowering lower stage) a) := by
  have himg : imgB (tabOf (I.resultsWithLowering lower stage)) = true :=
    okRWith_global stage hI
      ("imgCode: the image reads back", imgB (tabOf (I.resultsWithLowering lower stage)))
      (by simp [globalChks])
  exact img_bytesWithResults hB himg ha

end E2E.BinCheck
