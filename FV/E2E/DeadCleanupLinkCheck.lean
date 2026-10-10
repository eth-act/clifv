import FV.E2E.PipelineCheck

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver

def pipeCleanup (f : Clif.Function) (k : Nat) (base : BitVec 64) (o : Lean.Json) : Except String Art := do
  let vc ← lowerFunction f
  let vcp ← prepare (DeadCleanup.prune vc)
  let o ← parseRAOut o
  let rf ← buildRFunc vcp o
  let af ← lowerRFunc vcp rf
  let fa ← emitFunc k af
  let fb ← fa.layout
  pure ⟨k, vc, vcp, rf, af, fa, fb, base⟩

theorem pipeCleanup_spec {f : Clif.Function} {k : Nat} {base : BitVec 64} {o : Lean.Json} {a : Art}
    (h : pipeCleanup f k base o = .ok a) :
    lowerFunction f = .ok a.vc ∧ prepare (DeadCleanup.prune a.vc) = .ok a.vcp ∧ lowerRFunc a.vcp a.rf = .ok a.af ∧
      emitFunc a.k a.af = .ok a.fa ∧ a.fa.layout = .ok a.fb ∧ a.k = k ∧ a.base = base := by
  unfold pipeCleanup at h
  rcases h1 : lowerFunction f with _ | vc <;> simp only [h1, bind, Except.bind] at h
  · cases h
  rcases h2 : prepare (DeadCleanup.prune vc) with _ | vcp <;> simp only [h2] at h
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
def pipeCleanupT (f : Clif.Function) (k : Nat) (base : BitVec 64) (o : Lean.Json) : Except String Art := do
  let vc ← lowerFunction f
  let vcp ← prepare (DeadCleanup.prune vc)
  let ra := raAnswer vcp o
  let af ← lowerAllocReady vcp ra
  let fa ← emitFunc k af
  let fb ← fa.layout
  pure ⟨k, vc, vcp, allocResult vcp (readyAnswer vcp ra), af, fa, fb, base⟩

theorem pipeCleanupT_spec {f : Clif.Function} {k : Nat} {base : BitVec 64} {o : Lean.Json} {a : Art}
    (h : pipeCleanupT f k base o = .ok a) :
    lowerFunction f = .ok a.vc ∧ prepare (DeadCleanup.prune a.vc) = .ok a.vcp ∧
      a.rf = allocResult a.vcp (readyAnswer a.vcp (raAnswer a.vcp o)) ∧
      lowerRFunc a.vcp a.rf = .ok a.af ∧ emitFunc a.k a.af = .ok a.fa ∧ a.fa.layout = .ok a.fb ∧
      a.k = k ∧ a.base = base := by
  unfold pipeCleanupT at h
  rcases h1 : lowerFunction f with _ | vc <;> simp only [h1, bind, Except.bind] at h
  · cases h
  rcases h2 : prepare (DeadCleanup.prune vc) with _ | vcp <;> simp only [h2] at h
  · cases h
  rcases h3 : lowerAllocReady vcp (raAnswer vcp o) with _ | af <;> simp only [h3] at h
  · cases h
  rcases h4 : emitFunc k af with _ | fa <;> simp only [h4] at h
  · cases h
  rcases h5 : fa.layout with _ | fb <;> simp only [h5] at h
  · cases h
  cases h
  exact ⟨rfl, h2, rfl, lowerAlloc_eq ((lowerAllocReady_eq _ _).symm.trans h3), h4, h5, rfl, rfl⟩


/-- The same allocator choice as the legacy checker, with cleanup before prepare. -/
def LinkInput.pipeCleanupOf (I : LinkInput) (fi : FnInput) : Except String Art :=
  cond I.fallback pipeCleanupT pipeCleanup fi.func fi.k
    (BitVec.ofNat 64 (I.baseOf fi.func.name)) (raJ fi.ra fi.j)

def LinkInput.resultsCleanup (I : LinkInput) : Res :=
  I.funcs.map fun fi => (fi.func, I.pipeCleanupOf fi)

theorem resultsCleanup_ok (I : LinkInput) :
    ResOkWith DeadCleanup.prune I I.resultsCleanup := by
  intro e he a ha
  obtain ⟨fi, _, rfl⟩ := List.mem_map.1 he
  cases hfb : I.fallback <;>
    simp only [LinkInput.pipeCleanupOf, hfb, Bool.cond_false, Bool.cond_true] at ha
  · obtain ⟨hl, hp, hlr, hem, hla, _, hb⟩ := pipeCleanup_spec ha
    exact ⟨hl, hp, hlr, hem, hla, hb⟩
  · obtain ⟨hl, hp, _, hlr, hem, hla, _, hb⟩ := pipeCleanupT_spec ha
    exact ⟨hl, hp, hlr, hem, hla, hb⟩

def okBCleanup (I : LinkInput) : Bool := okRWith DeadCleanup.prune I I.resultsCleanup

def LinkSys.ofInputCleanup (I : LinkInput) (B : BaseEnv) (F : BitVec 64 → Prop) : LinkSys :=
  ofRes I I.resultsCleanup B F

/-- The cleanup checker proves the same linked system contract, with no additional
base-environment, ABI, source or observable-state premise. -/
theorem okBCleanup_sound {I : LinkInput} (hI : okBCleanup I = true) {B : BaseEnv}
    {F : BitVec 64 → Prop} (hB : BaseOk (LinkSys.ofInputCleanup I B F))
    (hF : ∀ a, (LinkSys.ofInputCleanup I B F).Img a → F a) :
    (LinkSys.ofInputCleanup I B F).Ok :=
  okRWith_sound DeadCleanup.prune (.inr rfl) (resultsCleanup_ok I) hI hB hF

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

end E2E.LinkCheck
