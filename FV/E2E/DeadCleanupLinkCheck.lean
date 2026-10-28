import FV.E2E.PipelineCheck

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver

def pipeCleanup (f : Clif.Function) (k : Nat) (base : BitVec 64) (o : Lean.Json) : Except String Art :=
  pipeWithLowering Backend.Stock.D0.defaultLower cleanupStage f k base o

theorem pipeCleanup_spec {f : Clif.Function} {k : Nat} {base : BitVec 64} {o : Lean.Json} {a : Art}
    (h : pipeCleanup f k base o = .ok a) :
    lowerFunction f = .ok a.vc ∧ prepare (cleanupStage f a.vc) = .ok a.vcp ∧ lowerRFunc a.vcp a.rf = .ok a.af ∧
      emitFunc a.k a.af = .ok a.fa ∧ a.fa.layout = .ok a.fb ∧ a.k = k ∧ a.base = base := by
  unfold pipeCleanup pipeWithLowering at h
  rw [Backend.Stock.D0.defaultLower_eq_legacy] at h
  rcases h1 : lowerFunction f with _ | vc <;> simp only [h1, bind, Except.bind] at h
  · cases h
  rcases h2 : prepare (cleanupStage f vc) with _ | vcp <;> simp only [h2] at h
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

/-- **The compiler's pipeline** on `f` (index `k` in its file, `lean-regalloc`'s output `o`)
loaded at `base`: `lowerFunction`, `prepare`, `lowerAllocReady` (regalloc2's allocation if
accepted and emittable, else the spill allocation), `emitFunc`, `layout`. The artifact's
allocation is the one lowered, `allocResult vcp (readyAnswer vcp ra)` (`lowerAllocReady_eq`). -/
def pipeCleanupT (f : Clif.Function) (k : Nat) (base : BitVec 64) (o : Lean.Json) : Except String Art :=
  pipeTWithLowering Backend.Stock.D0.defaultLower cleanupStage f k base o

theorem pipeCleanupT_spec {f : Clif.Function} {k : Nat} {base : BitVec 64} {o : Lean.Json} {a : Art}
    (h : pipeCleanupT f k base o = .ok a) :
    lowerFunction f = .ok a.vc ∧ prepare (cleanupStage f a.vc) = .ok a.vcp ∧
      a.rf = allocResult a.vcp (readyAnswer a.vcp (raAnswer a.vcp o)) ∧
      lowerRFunc a.vcp a.rf = .ok a.af ∧ emitFunc a.k a.af = .ok a.fa ∧ a.fa.layout = .ok a.fb ∧
      a.k = k ∧ a.base = base := by
  unfold pipeCleanupT pipeTWithLowering at h
  rw [Backend.Stock.D0.defaultLower_eq_legacy] at h
  rcases h1 : lowerFunction f with _ | vc <;> simp only [h1, bind, Except.bind] at h
  · cases h
  rcases h2 : prepare (cleanupStage f vc) with _ | vcp <;> simp only [h2] at h
  · cases h
  rcases h3 : lowerAllocReady vcp (raAnswer vcp o) with _ | af <;> simp only [h3] at h
  · cases h
  rcases h4 : emitFunc k af with _ | fa <;> simp only [h4] at h
  · cases h
  rcases h5 : fa.layout with _ | fb <;> simp only [h5] at h
  · cases h
  cases h
  exact ⟨rfl, h2, rfl, lowerAlloc_eq ((lowerAllocReady_eq _ _).symm.trans h3), h4, h5, rfl, rfl⟩


/-- The same allocator choice as the legacy checker, with the cleanup stage before prepare. -/
def LinkInput.pipeCleanupOf (I : LinkInput) (fi : FnInput) : Except String Art :=
  cond I.fallback pipeCleanupT pipeCleanup fi.func fi.k
    (BitVec.ofNat 64 (I.baseOf fi.func.name)) (raJ fi.ra fi.j)

def LinkInput.resultsCleanup (I : LinkInput) : Res :=
  I.funcs.map fun fi => (fi.func, I.pipeCleanupOf fi)

theorem resultsCleanup_ok (I : LinkInput) :
    ResOkWith cleanupStage I I.resultsCleanup := by
  intro e he a ha
  obtain ⟨fi, _, rfl⟩ := List.mem_map.1 he
  cases hfb : I.fallback <;>
    simp only [LinkInput.pipeCleanupOf, hfb, Bool.cond_false, Bool.cond_true] at ha
  · obtain ⟨hl, hp, hlr, hem, hla, _, hb⟩ := pipeCleanup_spec ha
    exact ⟨hl, hp, hlr, hem, hla, hb⟩
  · obtain ⟨hl, hp, _, hlr, hem, hla, _, hb⟩ := pipeCleanupT_spec ha
    exact ⟨hl, hp, hlr, hem, hla, hb⟩

def okBCleanup (I : LinkInput) : Bool := okRWith cleanupStage I I.resultsCleanup

theorem okBCleanup_global {I : LinkInput} (h : okBCleanup I = true)
    (c : String × Bool) (hc : c ∈ globalChks I (progOf I.resultsCleanup) (tabOf I.resultsCleanup)) :
    c.2 = true := okRWith_global cleanupStage h c hc

theorem okBCleanup_names {I : LinkInput} (h : okBCleanup I = true) :
    ((progOf I.resultsCleanup).funcs.map (·.name)).Nodup := okRWith_names cleanupStage h

theorem factsCleanup {I : LinkInput} (h : okBCleanup I = true) {g : Clif.Function}
    (hg : g ∈ (progOf I.resultsCleanup).funcs) :
    FactsWith cleanupStage I I.resultsCleanup g (artOf I.resultsCleanup g) :=
  factsRWith cleanupStage (resultsCleanup_ok I) h hg

def LinkSys.ofInputCleanup (I : LinkInput) (B : BaseEnv) (F : BitVec 64 → Prop) : LinkSys :=
  ofRes I I.resultsCleanup B F

/-- The cleanup checker proves the same linked system contract, with no additional
base-environment, ABI, source or observable-state premise. -/
theorem okBCleanup_sound {I : LinkInput} (hI : okBCleanup I = true) {B : BaseEnv}
    {F : BitVec 64 → Prop} (hB : BaseOk (LinkSys.ofInputCleanup I B F))
    (hF : ∀ a, (LinkSys.ofInputCleanup I B F).Img a → F a) :
    (LinkSys.ofInputCleanup I B F).Ok :=
  okRWith_sound cleanupStage (.inr rfl) (resultsCleanup_ok I) hI hB hF

/-- The legacy crate statement with the cleanup pipeline's concrete artifacts. -/
def CrateStmtCleanup (I : LinkInput) (n : String) : Prop :=
  ∀ (B : BaseEnv) (F : BitVec 64 → Prop), BaseOk (LinkSys.ofInputCleanup I B F) →
    (∀ a, (LinkSys.ofInputCleanup I B F).Img a → F a) →
      ProgStmt (LinkSys.ofInputCleanup I B F) n

theorem crate_correct_cleanup {I : LinkInput} (hI : okBCleanup I = true) (n : String) :
    CrateStmtCleanup I n :=
  fun _ _ hB hF f hf M _ _ _ _ _ hent hres hFeq hgfree himg hbe hargs hcs hsav hrel hpl htr =>
    backend_correct_program _ (okBCleanup_sound hI hB hF) (Clif.Program.func?_some hf).1 M hent hres
      hFeq hgfree himg hbe hargs hcs hsav hrel hpl htr

def globalBCleanup (I : LinkInput) : Bool :=
  let R := I.resultsCleanup
  (globalChks I (progOf R) (tabOf R)).all (·.2)

/-- The per-function checks (`chks`: `staticChks ++ linkChks`) of the functions `fs` (a slice of
the input's) against the input's program. A crate's proof decides `okBCleanup` by one `native_decide`
per slice, in separate modules that Lake builds in parallel (`okBCleanup_of`, `fnsBCleanup_append`). -/
def fnsBCleanup (I : LinkInput) (fs : List FnInput) : Bool :=
  let R := I.resultsCleanup
  let P := progOf R
  let T := tabOf R
  fs.all fun fi => (chksWith cleanupStage I P T fi.func (I.pipeCleanupOf fi)).all (·.2)

theorem fnsBCleanup_append (I : LinkInput) (l₁ l₂ : List FnInput) :
    fnsBCleanup I (l₁ ++ l₂) = (fnsBCleanup I l₁ && fnsBCleanup I l₂) := by
  simp only [fnsBCleanup, List.all_append]

/-- `okBCleanup` from its parts: `globalBCleanup` and `fnsBCleanup` of all the functions. -/
theorem okBCleanup_of {I : LinkInput} (hg : globalBCleanup I = true) (hf : fnsBCleanup I I.funcs = true) :
    okBCleanup I = true := by
  simp only [okBCleanup, okRWith, Bool.and_eq_true]
  refine ⟨hg, ?_⟩
  simp only [fnsBCleanup] at hf
  simp only [LinkInput.resultsCleanup, List.all_map]
  exact hf


theorem baseOk_closedCleanup {I : LinkInput} {F : BitVec 64 → Prop}
    (htls : ∀ g ∈ (progOf I.resultsCleanup).funcs, hasTls g = false) :
    BaseOk (LinkSys.ofInputCleanup I closedBase F) :=
  baseOk_closedR htls

/-- The cleanup results of the typed pipeline (`pipeCleanupT`) of every function. -/
def LinkInput.resultsCleanupT (I : LinkInput) : Res :=
  I.funcs.map fun fi => (fi.func, pipeCleanupT fi.func fi.k
    (BitVec.ofNat 64 (I.baseOf fi.func.name)) (raJ fi.ra fi.j))

theorem LinkInput.resultsCleanup_fallback {I : LinkInput} (h : I.fallback = true) :
    I.resultsCleanup = I.resultsCleanupT := by
  simp only [LinkInput.resultsCleanup, LinkInput.resultsCleanupT, LinkInput.pipeCleanupOf,
    h, Bool.cond_true]

end E2E.LinkCheck
