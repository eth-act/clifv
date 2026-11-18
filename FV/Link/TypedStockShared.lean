import FV.Link.SemanticCompileT
import FV.Link.Placed

/-! # `lean-link`'s typed Stock route with the per-function pipeline shared (#1062)

On a typed input whose units hold Stock code (#691, #722), `lean-link` computes, per function,
the cleanup layout `DeadCleanup.placedPar` (`pipeCleanupT`: `lowerFunction`'s pipeline), whether
`lean-backend` took a Stock lowering (`stockDiffersB`: the Stock lowering and `lowerFunction`
again), the Stock placement `placedProductionWith lower true` (the Stock route's pipeline) and
`SemanticCompilerWith.attemptT lower` on it (that pipeline again, at the placed addresses). The
definitions here compute the same values with one `lowerFunction` pipeline and one Stock lowering
per function, plus the Stock route's pipeline only where its lowering differs from
`lowerFunction`'s:

* the pipeline reads its lowering's result only (`pipeTFrom`), and its load address is a field
  it does not read (`pipeTFrom_base`): the results at the placed addresses are the results at
  address 0 moved there;
* where the Stock lowering's code is `lowerFunction`'s, the Stock route's pipeline result is the
  cleanup pipeline's (`stockStep`).

`cleanupArts_placed`, `stockSteps_fst`, `stockSteps_placed` and `attemptTFrom_eq` state that each
value equals the one computed before; `lean-link` (FVTest/Link/LeanLinkMain.lean) uses these
definitions, so what it writes is `attemptT lower (S.placedProductionWith lower true) file0`.
-/

set_option autoImplicit false
namespace Link.TypedStockShared
open E2E E2E.LinkCheck Backend

/-- `pipeTWithLowering` from the lowering's result `vr` (`pipeTWithLowering_from`). -/
def pipeTFrom (vr : Except String VCode) (stage : Clif.Function → VCode → VCode)
    (f : Clif.Function) (k : Nat) (base : BitVec 64) (o : Lean.Json) : Except String Art := do
  let vc ← vr
  let vcp ← prepare (stage f vc)
  let ra := raAnswer vcp o
  let af ← lowerAllocReady vcp ra
  let fa ← emitFunc k af
  let fb ← fa.layout
  pure ⟨k, vc, vcp, allocResult vcp (readyAnswer vcp ra), af, fa, fb, base⟩

theorem pipeTWithLowering_from (lower : Clif.Function → Except String VCode)
    (stage : Clif.Function → VCode → VCode) (f : Clif.Function) (k : Nat) (base : BitVec 64)
    (o : Lean.Json) :
    pipeTWithLowering lower stage f k base o = pipeTFrom (lower f) stage f k base o := rfl

/-- The artifact `a` loaded at `b`. -/
def artAt (b : BitVec 64) (a : Art) : Art := { a with base := b }

/-- **The load address is a field of the result**: the pipeline at `b` is the pipeline at `0`
loaded at `b`. -/
theorem pipeTFrom_base (vr : Except String VCode) (stage : Clif.Function → VCode → VCode)
    (f : Clif.Function) (k : Nat) (b : BitVec 64) (o : Lean.Json) :
    pipeTFrom vr stage f k b o = (pipeTFrom vr stage f k 0 o).map (artAt b) := by
  unfold pipeTFrom
  rcases vr with _ | vc
  · rfl
  simp only [bind, Except.bind]
  rcases h1 : prepare (stage f vc) with _ | vcp
  · rfl
  simp only
  rcases h2 : lowerAllocReady vcp (raAnswer vcp o) with _ | af
  · rfl
  simp only
  rcases h3 : emitFunc k af with _ | fa
  · rfl
  simp only
  rcases h4 : fa.layout with _ | fb
  · rfl
  rfl

/-- A result of the pipeline holds its lowering's code. -/
theorem pipeTFrom_ok {vr : Except String VCode} {stage : Clif.Function → VCode → VCode}
    {f : Clif.Function} {k : Nat} {b : BitVec 64} {o : Lean.Json} {a : Art}
    (h : pipeTFrom vr stage f k b o = .ok a) : vr = .ok a.vc := by
  unfold pipeTFrom at h
  rcases vr with _ | vc
  · cases h
  simp only [bind, Except.bind] at h
  rcases h1 : prepare (stage f vc) with _ | vcp <;> simp only [h1] at h
  · cases h
  rcases h2 : lowerAllocReady vcp (raAnswer vcp o) with _ | af <;> simp only [h2] at h
  · cases h
  rcases h3 : emitFunc k af with _ | fa <;> simp only [h3] at h
  · cases h
  rcases h4 : fa.layout with _ | fb <;> simp only [h4, pure, Except.pure] at h
  · cases h
  cases h; rfl

/-- Whether `lean-backend` compiled `g` with a Stock lowering other than `lowerFunction` (#691):
as it does, `lower` (the Stock routes, `lowerCheckedParameterCfgNI`'s chain) on a function
without `try_call` (`compileFileParameterCfgNIWhen`), and a different `VCode` from
`lowerFunction`'s (`Stock.D0.defaultLower`, `pipeCleanupT`'s); a function on which `lower`
fails takes `lowerFunction` in both. -/
def stockDiffersB (lower : Clif.Function → Except String VCode) (g : Clif.Function) : Bool :=
  !(g.blocks.any fun b => b.term.isTry) &&
    match lower g with
    | .error _ => false
    | .ok vc => match Stock.D0.defaultLower g with
      | .ok vl => !decide (vc = vl)
      | .error _ => true

/-- The cleanup pipeline's result at address `0` (`DeadCleanup.placedPar`'s). -/
def cleanupArt (fi : FnInput) : Except String Art := pipeCleanupT fi.func fi.k 0 (raJ fi.ra fi.j)

/-- **The Stock route's result at address `0`**: the pipeline from the Stock lowering, else
`lowerFunction`'s, both with the dead cleanup (`pipeProductionWith_eq`). -/
def stockArt (lower : ProductionLowering) (fi : FnInput) : Except String Art :=
  let f := fi.func
  let o := raJ fi.ra fi.j
  match pipeTFrom (lower f) cleanupStage f fi.k 0 o with
  | .ok a => .ok a
  | .error _ => pipeTFrom (Stock.D0.defaultLower f) cleanupStage f fi.k 0 o

/-- **The Stock route's pipeline, on any input with the compiler's pipeline (`fallback`)**: the
result at address `0` loaded at the function's address. -/
theorem pipeProductionWith_eq (lower : ProductionLowering) (I : LinkInput) (h : I.fallback = true)
    (fi : FnInput) :
    I.pipeProductionWith lower true fi =
      (stockArt lower fi).map (artAt (BitVec.ofNat 64 (I.baseOf fi.func.name))) := by
  unfold LinkInput.pipeProductionWith LinkInput.pipeOfWithLowering stockArt
  simp only [h, cond, pipeTWithLowering_from]
  rw [pipeTFrom_base (lower fi.func), pipeTFrom_base (Stock.D0.defaultLower fi.func)]
  have hs : productionStage true = cleanupStage := rfl
  rw [hs]
  rcases pipeTFrom (lower fi.func) cleanupStage fi.func fi.k 0 (raJ fi.ra fi.j) with _ | a <;> rfl

/-- The lowering `lowerFunction` gave, read from the cleanup result `ac` when it has one. -/
def lowerOf (f : Clif.Function) (ac : Except String Art) : Except String VCode :=
  match ac with
  | .ok a => .ok a.vc
  | .error _ => Stock.D0.defaultLower f

/-- **One function's step on the typed Stock route**, from its cleanup result `ac`: whether its
units hold Stock code (`stockDiffersB`, `stockStep_fst`), the function, and the Stock route's
result at address `0` (`stockArt`, `stockStep_snd`): `ac` itself where the Stock lowering's code
is `lowerFunction`'s, so the Stock pipeline runs only where the two lowerings differ. -/
def stockStep (lower : ProductionLowering) (fi : FnInput) (ac : Except String Art) :
    Bool × Clif.Function × Except String Art :=
  let f := fi.func
  let o := raJ fi.ra fi.j
  let lv := lower f
  let dv := lowerOf f ac
  let differs := !(f.blocks.any fun b => b.term.isTry) &&
    match lv with
    | .error _ => false
    | .ok vc => match dv with
      | .ok vl => !decide (vc = vl)
      | .error _ => true
  let stock (vc : VCode) : Except String Art :=
    match pipeTFrom (.ok vc) cleanupStage f fi.k 0 o with
    | .ok a => .ok a
    | .error _ => ac
  let as := match lv with
    | .error _ => ac
    | .ok vc => match ac with
      | .ok a => if decide (a.vc = vc) then ac else stock vc
      | .error _ => stock vc
  (differs, f, as)

/-- The cleanup result's lowering is `lowerFunction`'s. -/
theorem cleanupArt_lower {fi : FnInput} {a : Art} (h : cleanupArt fi = .ok a) :
    Stock.D0.defaultLower fi.func = .ok a.vc :=
  pipeTFrom_ok (vr := Stock.D0.defaultLower fi.func) h

theorem lowerOf_cleanup (fi : FnInput) : lowerOf fi.func (cleanupArt fi) = Stock.D0.defaultLower fi.func := by
  unfold lowerOf
  cases h : cleanupArt fi with
  | ok a => exact (cleanupArt_lower h).symm
  | error e => rfl

theorem stockStep_fst (lower : ProductionLowering) (fi : FnInput) :
    (stockStep lower fi (cleanupArt fi)).1 = stockDiffersB lower fi.func := by
  simp only [stockStep, lowerOf_cleanup, stockDiffersB]

theorem stockStep_snd (lower : ProductionLowering) (fi : FnInput) :
    (stockStep lower fi (cleanupArt fi)).2 = (fi.func, stockArt lower fi) := by
  simp only [stockStep, stockArt]
  have hc : pipeTFrom (Stock.D0.defaultLower fi.func) cleanupStage fi.func fi.k 0 (raJ fi.ra fi.j) =
      cleanupArt fi := rfl
  rw [hc]
  congr 1
  cases hl : lower fi.func with
  | error e => rfl
  | ok vc =>
    simp only
    cases h : cleanupArt fi with
    | error e => rfl
    | ok a =>
      simp only
      by_cases hv : a.vc = vc
      · subst hv
        have hp : pipeTFrom (.ok a.vc) cleanupStage fi.func fi.k 0 (raJ fi.ra fi.j) = .ok a := by
          rw [← cleanupArt_lower h]; exact h
        simp only [decide_true, ite_true, hp]
      · simp only [hv, decide_false]
        rfl

/-! ## The whole program -/

/-- The cleanup results of `S`'s functions (`cleanupArts_placed`). -/
def cleanupArts (S : LinkSpec) : List (Except String Art) := S.funcs.map cleanupArt

/-- `S` with the sizes of the results `A`. -/
def placedFrom (S : LinkSpec) (A : List (Except String Art)) : LinkSpec :=
  S.withSizes (A.map fun r => (getOk r).fb.words.size)

/-- **The cleanup layout from the cleanup results.** -/
theorem cleanupArts_placed (S : LinkSpec) :
    placedFrom S (cleanupArts S) = DeadCleanup.placedPar S := by
  simp only [placedFrom, cleanupArts, cleanupArt, DeadCleanup.placedPar, LinkSpec.withSizes,
    parMap_eq, List.map_map]
  rfl

/-- The steps of `S`'s functions from their cleanup results `A`. -/
def stockSteps (lower : ProductionLowering) (S : LinkSpec) (A : List (Except String Art)) :
    List (Bool × Clif.Function × Except String Art) :=
  (S.funcs.zip A).map fun p => stockStep lower p.1 p.2

theorem zip_map_self {α β γ : Type} (l : List α) (g : α → β) (h : α × β → γ) :
    (l.zip (l.map g)).map h = l.map fun x => h (x, g x) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.zip_cons_cons, ih]

theorem stockSteps_cleanup (lower : ProductionLowering) (S : LinkSpec) :
    stockSteps lower S (cleanupArts S) =
      S.funcs.map fun fi => (stockDiffersB lower fi.func, fi.func, stockArt lower fi) := by
  simp only [stockSteps, cleanupArts, zip_map_self]
  congr 1
  funext fi
  rw [← stockStep_fst lower fi, ← stockStep_snd lower fi]

/-- **Which functions hold Stock code**, from the steps. -/
theorem stockSteps_fst (lower : ProductionLowering) (S : LinkSpec) :
    (stockSteps lower S (cleanupArts S)).map (·.1) = S.funcs.map fun fi => stockDiffersB lower fi.func := by
  rw [stockSteps_cleanup, List.map_map]
  rfl

/-- `S` with the sizes of the steps' Stock results. -/
def placedStock (S : LinkSpec) (st : List (Bool × Clif.Function × Except String Art)) : LinkSpec :=
  S.withSizes (st.map fun s => (getOk s.2.2).fb.words.size)

theorem getOk_map_artAt (b : BitVec 64) (r : Except String Art) :
    (getOk (r.map (artAt b))).fb = (getOk r).fb := by
  cases r <;> rfl

/-- **The Stock placement from the steps.** -/
theorem stockSteps_placed (lower : ProductionLowering) (S : LinkSpec) :
    placedStock S (stockSteps lower S (cleanupArts S)) = S.placedProductionWith lower true := by
  rw [stockSteps_cleanup]
  simp only [placedStock, LinkSpec.placedProductionWith, List.map_map]
  congr 1

/-- **The Stock route's results at the placed addresses**, from the steps' results at address `0`
(the link map looked up in a hash map; `stockRes_eq`). -/
def stockRes (SP : LinkSpec) (st : List (Bool × Clif.Function × Except String Art)) : Res :=
  let m := assocMap SP.input0.addrs
  st.map fun s => (s.2.1, s.2.2.map (artAt (BitVec.ofNat 64 ((m[s.2.1.name]?).getD 0))))

theorem stockRes_eq (lower : ProductionLowering) (S : LinkSpec) :
    stockRes (S.placedProductionWith lower true) (stockSteps lower S (cleanupArts S)) =
      (S.placedProductionWith lower true).input0.resultsProductionWith lower true := by
  have hf : (S.placedProductionWith lower true).input0.funcs = S.funcs := rfl
  rw [stockRes, stockSteps_cleanup, List.map_map]
  simp only [LinkInput.resultsProductionWith, hf]
  apply List.map_congr_left
  intro fi _
  simp only [Function.comp, assocMap_get]
  rw [pipeProductionWith_eq lower _ rfl fi]
  rfl

/-- **`attemptT` from the Stock route's results `R`** (`attemptTFrom_eq`): `attemptTFast` with
`R` for the pipeline's. -/
def attemptTFrom (SP : LinkSpec) (file0 : ByteArray) (R : Res) : Except String ByteArray :=
  if okRWithTS (productionStage true) (SP.input0.withDepth R) R then
    leanLinkWithResults SP file0 (fun _ => R)
  else .error SemanticCompilerWith.outOkTSMsg

/-- **`lean-link`'s typed Stock route writes `attemptT`'s output.** -/
theorem attemptTFrom_eq (lower : ProductionLowering) (S : LinkSpec) (file0 : ByteArray) :
    attemptTFrom (S.placedProductionWith lower true) file0
        (stockRes (S.placedProductionWith lower true) (stockSteps lower S (cleanupArts S))) =
      SemanticCompilerWith.attemptT lower (S.placedProductionWith lower true) file0 := by
  rw [SemanticCompilerWith.attemptT_eq_fast, stockRes_eq]
  rfl

end Link.TypedStockShared
