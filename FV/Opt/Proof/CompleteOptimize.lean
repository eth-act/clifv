module

public import FV.Opt.Proof.CompleteGuards
public import FV.Opt.Proof.PipelineX

@[expose] public section

/-!
# Completeness of the mid-end pipeline (M1)

`Opt.optimizeReport_complete`: if the input is well formed once its unreachable blocks are
removed (`check (removeUnreachable f0) = .ok i`), no stage of `Opt.optimizeReport` stops (every
pass output passes `check` and its validator: `gvn_complete`, `dce_complete`, `licm_complete`,
and for simplify the hypothesis `Opt.SimpStageOk`), the final backend-subset guard accepts
(`KeepsB` through every stage, `FV/Opt/Proof/CompleteGuards.lean`), and the result is the
unvalidated pipeline `Opt.runStages cfg (removeUnreachable f0)`: the same stage list and enabled
flags, every pass applied unconditionally. Without simplify (`cfg.simplify = false`) there is no
hypothesis: `Opt.optimize_complete_noSimp`. `Opt.optimizeExe_complete`: for inputs with
`shapeSafeB`, the fresh-value guard (`freshOkB_of_check`) and the shape guard (`ShapeK` through
every stage) accept too.

The stage loop (a `forIn` with a `break` on `stop`) is handled by `Opt.forIn_pre_bind`, an
invariant over the processed prefix of the stage list: `stop` stays `false`, no pass error is
recorded, and the current function is the prefix's `runStages` fold, well formed with its own
`coreInfo`.
-/

namespace Opt

open Clif

/-- The stages of `optimizeReport`. -/
def stageList (cfg : Config) : List String :=
  (List.replicate cfg.rounds ["simplify", "gvn", "dce"]).flatten ++ ["licm", "gvn", "dce"]

/-- Is a stage enabled (`optimizeReport`)? -/
def stageOn (cfg : Config) (stage : String) : Bool :=
  match stage with
  | "simplify" => cfg.simplify | "gvn" => cfg.gvn | "dce" => cfg.dce | _ => cfg.licm

/-- GVN's per-block instructions (`optimizeReport`). -/
def gvnLocal (cfg : Config) (i : Inst) : Bool :=
  cfg.rematConst && match i with
    | .iconst .. => true
    | _ => false

/-- The simplify stage's simplifier run (`f`: the pipeline's input). -/
abbrev simpRun (cfg : Config) (f g : Function) (info : Info) : Function × SimplifyStats × SimpCert :=
  simplify cfg.simplifyFn cfg.skeletonFn (allowedIn f) (skelAllowedIn f) cfg.rematConst g info

/-- One stage without validation (`f`: the pipeline's input, whose `allowedIn` simplify uses). -/
def runStage (cfg : Config) (f : Function) (stage : String) (g : Function) : Function :=
  match stage with
  | "simplify" => removeUnreachable (simpRun cfg f g (coreInfo g)).1
  | "gvn" => (gvnFull g (coreInfo g) (gvnLocal cfg)).1
  | "dce" => (dce g).1
  | _ => (licm cfg.hoistConst g (coreInfo g)).1

/-- One step of the stage loop. -/
def stageStep (cfg : Config) (f : Function) (g : Function) (stage : String) : Function :=
  if stageOn cfg stage then runStage cfg f stage g else g

/-- **The unvalidated pipeline**: the stage loop of `optimizeReport` from `f`, every enabled pass
applied unconditionally. -/
def runStages (cfg : Config) (f : Function) : Function :=
  (stageList cfg).foldl (stageStep cfg f) f

theorem forIn_pre {α σ : Type} (l : List α) (init : σ) (f : α → σ → Id (ForInStep σ))
    (P : List α → σ → Prop) (h0 : P [] init)
    (hf : ∀ pre a rest s, l = pre ++ a :: rest → P pre s →
      ∃ s', f a s = pure (.yield s') ∧ P (pre ++ [a]) s') :
    P l (forIn l init f).run := by
  suffices ∀ rest pre init, l = pre ++ rest → P pre init → P l (forIn rest init f).run from
    this l [] init (by simp) h0
  intro rest
  induction rest with
  | nil => intro pre init hl h; simp only [List.append_nil] at hl; subst hl; exact h
  | cons a rest ih =>
    intro pre init hl h
    obtain ⟨s', hs', hP⟩ := hf pre a rest init hl h
    rw [List.forIn_cons, hs']
    exact ih (pre ++ [a]) s' (by simp [hl]) hP

theorem coreInfo_of_check {g : Function} {info : Info} (h : check g = .ok info) :
    info = coreInfo g :=
  ((check_ok_iff g info).1 h).2.1

theorem forIn_pre_bind {α σ β : Type} (l : List α) (init : σ) (f : α → σ → Id (ForInStep σ))
    (k : σ → Id β) (P : List α → σ → Prop) (Q : β → Prop) (h0 : P [] init)
    (hf : ∀ pre a rest s, l = pre ++ a :: rest → P pre s →
      ∃ s', f a s = pure (.yield s') ∧ P (pre ++ [a]) s')
    (hk : ∀ s, P l s → Q (k s).run) : Q (forIn l init f >>= k).run := by
  rw [Id.run_bind]
  exact hk _ (forIn_pre l init f P h0 hf)

/-! ## The stages on well-formed functions -/

/-- **The hypothesis on the simplify stage** (discharged by the simplify completeness proof): on
a well-formed function the simplifier's output passes `simpOk`, `check` accepts it after
`removeUnreachable`, and it has the guard facts `SimpGuard`. -/
def SimpStageOk (cfg : Config) : Prop :=
  ∀ (f g : Function) (info : Info), check g = .ok info →
    simpOk g (simpRun cfg f g info).1 info (simpRun cfg f g info).2.2 = true ∧
      (∃ i, check (removeUnreachable (simpRun cfg f g info).1) = .ok i) ∧
      SimpGuard f g (simpRun cfg f g info).1

/-- Every enabled stage keeps well-formedness and the guard relations `KeepsB f0 ·` and
`ShapeK f0 ·` (`f`: the pipeline's input, with `KeepsB f0 f`). -/
theorem stageStep_ok {cfg : Config} (hS : cfg.simplify = false ∨ SimpStageOk cfg)
    {f0 f g : Function} (hf : KeepsB f0 f) (hg : check g = .ok (coreInfo g)) (hK : KeepsB f0 g)
    (hSh : ShapeK f0 g) (st : String) :
    check (stageStep cfg f g st) = .ok (coreInfo (stageStep cfg f g st)) ∧
      KeepsB f0 (stageStep cfg f g st) ∧ ShapeK f0 (stageStep cfg f g st) := by
  unfold stageStep
  by_cases hon : stageOn cfg st = true
  · simp only [hon, ite_true]
    by_cases h1 : st = "simplify"
    · subst h1
      have hen : cfg.simplify = true := by simpa [stageOn] using hon
      have hSS : SimpStageOk cfg := by
        rcases hS with h | h
        · rw [hen] at h; cases h
        · exact h
      obtain ⟨-, ⟨i1, hc1⟩, hG⟩ := hSS f g (coreInfo g) hg
      simp only [runStage]
      refine ⟨by rw [hc1, ← coreInfo_of_check hc1], (keepsB_simp' hf hK hG).trans
        (keepsB_removeUnreachable _), hSh.trans ((shapeK_simp hG).trans (shapeK_removeUnreachable _))⟩
    by_cases h2 : st = "gvn"
    · subst h2
      simp only [runStage]
      exact ⟨(gvn_complete hg _).1, hK.trans (keepsB_gvn hg _), hSh.trans (shapeK_gvn hg _)⟩
    by_cases h3 : st = "dce"
    · subst h3
      simp only [runStage]
      exact ⟨(dce_complete hg).1, hK.trans (keepsB_dce _), hSh.trans (shapeK_dce _)⟩
    · simp only [runStage]
      exact ⟨(licm_complete hg _).1, hK.trans (keepsB_licm_of_check hg _),
        hSh.trans (shapeK_licm_of_check hg _)⟩
  · simp only [hon, Bool.false_eq_true, ite_false]
    exact ⟨hg, hK, hSh⟩

theorem foldl_stageStep_ok {cfg : Config} (hS : cfg.simplify = false ∨ SimpStageOk cfg)
    {f0 f : Function} (hf : KeepsB f0 f) :
    ∀ (L : List String) (g : Function), check g = .ok (coreInfo g) → KeepsB f0 g → ShapeK f0 g →
      check (L.foldl (stageStep cfg f) g) = .ok (coreInfo (L.foldl (stageStep cfg f) g)) ∧
        KeepsB f0 (L.foldl (stageStep cfg f) g) ∧ ShapeK f0 (L.foldl (stageStep cfg f) g) := by
  intro L
  induction L with
  | nil => intro g hg hK hSh; exact ⟨hg, hK, hSh⟩
  | cons st L ih =>
    intro g hg hK hSh
    obtain ⟨h1, h2, h3⟩ := stageStep_ok hS hf hg hK hSh st
    exact ih _ h1 h2 h3

/-- **The unvalidated pipeline keeps well-formedness and the guard relations.** -/
theorem runStages_ok {cfg : Config} (hS : cfg.simplify = false ∨ SimpStageOk cfg) {f0 : Function}
    {i : Info} (h : check (removeUnreachable f0) = .ok i) :
    check (runStages cfg (removeUnreachable f0)) = .ok (coreInfo (runStages cfg (removeUnreachable f0))) ∧
      KeepsB f0 (runStages cfg (removeUnreachable f0)) ∧
      ShapeK f0 (runStages cfg (removeUnreachable f0)) := by
  have hf := keepsB_removeUnreachable f0
  exact foldl_stageStep_ok hS hf _ _ (by rw [h, ← coreInfo_of_check h]) hf
    (shapeK_removeUnreachable f0)

/-! ## The pipeline -/

theorem beq_simplify_false {a : String} (h : a ≠ "simplify") : (a == "simplify") = false := by
  simpa using h

/-- **Completeness of the mid-end**: on an input whose unreachable blocks removed it is well formed,
no stage of `optimizeReport` stops (no validator rejects, every output passes `check`), the final
backend-subset guard accepts, and the result is the unvalidated pipeline `runStages` — given the
simplify stage's facts `SimpStageOk` when simplify is enabled. -/
theorem optimizeReport_complete (cfg : Config) (f0 : Function)
    (h : ∃ i, check (removeUnreachable f0) = .ok i) (hS : cfg.simplify = false ∨ SimpStageOk cfg) :
    (optimizeReport cfg f0).2.passError = none ∧
      (optimizeReport cfg f0).1 = runStages cfg (removeUnreachable f0) := by
  obtain ⟨i, h⟩ := h
  have hfin := runStages_ok hS h
  unfold optimizeReport
  simp only [Id.run, h, pure_bind]
  refine forIn_pre_bind _ _ _ _ (P := fun pre (s : Report × Function × Info × Bool) =>
    s.2.2.2 = false ∧ s.1.passError = none ∧ s.2.1 = pre.foldl (stageStep cfg (removeUnreachable f0))
      (removeUnreachable f0) ∧ check s.2.1 = .ok s.2.2.1)
    (Q := fun x : Function × Report => x.2.passError = none ∧ x.1 = runStages cfg (removeUnreachable f0))
    ⟨rfl, rfl, rfl, h⟩ ?_ ?_
  · rintro pre a rest ⟨r, g, info, stop⟩ - ⟨h1, h2, h3, h4⟩
    simp only at h1 h2 h3 h4
    subst h1
    have hi := coreInfo_of_check h4
    subst hi
    simp only [Bool.false_eq_true, ite_false]
    have hnext : ∀ g', g' = stageStep cfg (removeUnreachable f0) g a →
        g' = (pre ++ [a]).foldl (stageStep cfg (removeUnreachable f0)) (removeUnreachable f0) := by
      rintro g' rfl; rw [List.foldl_append, ← h3]; rfl
    by_cases ha1 : a = "simplify"
    · subst ha1
      simp only []
      by_cases hen : cfg.simplify = true
      · have hSS : SimpStageOk cfg := by
          rcases hS with h' | h'
          · rw [hen] at h'; cases h'
          · exact h'
        obtain ⟨hok, ⟨i1, hc1⟩, -⟩ := hSS (removeUnreachable f0) g (coreInfo g) h4
        simp only [hen, Bool.not_true, Bool.false_eq_true, ite_false]
        split
        · rename_i i' heq
          split
          · refine ⟨_, rfl, rfl, h2, hnext _ ?_, heq⟩
            simp only [stageStep, stageOn, runStage, hen, ite_true]
          · rename_i hrej
            exact absurd hok (by simp at hrej)
        · rename_i e heq
          exact absurd (hc1.symm.trans heq) (by simp)
      · simp only [hen, Bool.not_false, ite_true]
        exact ⟨_, rfl, rfl, h2, hnext _ (by simp [stageStep, stageOn, hen]), h4⟩
    by_cases ha2 : a = "gvn"
    · subst ha2
      simp only []
      by_cases hen : cfg.gvn = true
      · obtain ⟨hc', hv⟩ := gvn_complete h4 (gvnLocal cfg)
        simp only [hen, Bool.not_true, Bool.false_eq_true, ite_false]
        split
        · rename_i i' heq
          have hi' : coreInfo (gvnFull g (coreInfo g) (gvnLocal cfg)).1 = i' := by
            have := hc'.symm.trans heq; injection this
          subst hi'
          try simp only [beq_simplify_false (by decide : ("gvn" : String) ≠ "simplify"),
            Bool.false_eq_true, ite_false]
          split
          · refine ⟨_, rfl, rfl, h2, hnext _ ?_, heq⟩
            simp only [stageStep, stageOn, runStage, hen, ite_true]
            rfl
          · rename_i hrej
            exact absurd hv hrej
        · rename_i e heq
          exact absurd (hc'.symm.trans heq) (by simp)
      · simp only [hen, Bool.not_false, ite_true]
        exact ⟨_, rfl, rfl, h2, hnext _ (by simp [stageStep, stageOn, hen]), h4⟩
    by_cases ha3 : a = "dce"
    · subst ha3
      simp only []
      by_cases hen : cfg.dce = true
      · obtain ⟨hc', hv⟩ := dce_complete h4
        simp only [hen, Bool.not_true, Bool.false_eq_true, ite_false]
        split
        · rename_i i' heq
          have hi' : coreInfo (dce g).1 = i' := by have := hc'.symm.trans heq; injection this
          subst hi'
          try simp only [beq_simplify_false (by decide : ("dce" : String) ≠ "simplify"),
            Bool.false_eq_true, ite_false]
          split
          · refine ⟨_, rfl, rfl, h2, hnext _ ?_, heq⟩
            simp only [stageStep, stageOn, runStage, hen, ite_true]
          · rename_i hrej
            exact absurd hv hrej
        · rename_i e heq
          exact absurd (hc'.symm.trans heq) (by simp)
      · simp only [hen, Bool.not_false, ite_true]
        exact ⟨_, rfl, rfl, h2, hnext _ (by simp [stageStep, stageOn, hen]), h4⟩
    · simp only []
      by_cases hen : cfg.licm = true
      · obtain ⟨hc', hv⟩ := licm_complete h4 cfg.hoistConst
        simp only [hen, Bool.not_true, Bool.false_eq_true, ite_false]
        split
        · rename_i i' heq
          have hi' : coreInfo (licm cfg.hoistConst g (coreInfo g)).1 = i' := by
            have := hc'.symm.trans heq; injection this
          subst hi'
          try simp only [beq_simplify_false ha1, Bool.false_eq_true, ite_false]
          split
          · refine ⟨_, rfl, rfl, h2, hnext _ ?_, heq⟩
            simp only [stageStep, stageOn, runStage, hen, ite_true]
          · rename_i hrej
            exact absurd hv hrej
        · rename_i e heq
          exact absurd (hc'.symm.trans heq) (by simp)
      · simp only [hen, Bool.not_false, ite_true]
        exact ⟨_, rfl, rfl, h2, hnext _ (by simp [stageStep, stageOn, hen]), h4⟩
  · rintro ⟨r, g, info, stop⟩ ⟨-, h2, h3, -⟩
    simp only at h2 h3
    have hg : g = runStages cfg (removeUnreachable f0) := h3
    subst hg
    simp only [keepsBackendSubset_of_keepsB hfin.2.1, ite_true]
    exact ⟨h2, rfl⟩

/-! ## `optimize` and `optimizeExe` -/

/-- **Completeness of `optimize`** (`optimizeReport_complete`). -/
theorem optimize_complete (cfg : Config) (f0 : Function)
    (h : ∃ i, check (removeUnreachable f0) = .ok i) (hS : cfg.simplify = false ∨ SimpStageOk cfg) :
    optimize f0 cfg = runStages cfg (removeUnreachable f0) :=
  (optimizeReport_complete cfg f0 h hS).2

/-- **Completeness of the mid-end without simplify** (no hypothesis on the stages). -/
theorem optimize_complete_noSimp (cfg : Config) (hs : cfg.simplify = false) (f0 : Function)
    (h : ∃ i, check (removeUnreachable f0) = .ok i) :
    (optimizeReport cfg f0).2.passError = none ∧ optimize f0 cfg = runStages cfg (removeUnreachable f0) :=
  optimizeReport_complete cfg f0 h (.inl hs)

/-- **Completeness of the executable mid-end**: on an input that is well formed once its
unreachable blocks are removed and that has `shapeSafeB`, neither the fresh-value guard nor the
shape guard fires, and `optimizeExe` is the unvalidated pipeline. -/
theorem optimizeExe_complete (cfg : Config) (f0 : Function)
    (h : ∃ i, check (removeUnreachable f0) = .ok i) (hS : cfg.simplify = false ∨ SimpStageOk cfg)
    (hsafe : shapeSafeB f0 = true) :
    optimizeExe f0 cfg = runStages cfg (removeUnreachable f0) := by
  obtain ⟨i, hi⟩ := h
  have hX : optimizeX f0 cfg = runStages cfg (removeUnreachable f0) := by
    simp only [optimizeX, freshOkB_of_check hi, ite_true]
    exact optimize_complete cfg f0 ⟨i, hi⟩ hS
  simp only [optimizeExe, hX, keepsShapeB_of_shapeK hsafe (runStages_ok hS hi).2.2, ite_true]

/-- `optimizeExe_complete` without simplify (no hypothesis on the stages). -/
theorem optimizeExe_complete_noSimp (cfg : Config) (hs : cfg.simplify = false) (f0 : Function)
    (h : ∃ i, check (removeUnreachable f0) = .ok i) (hsafe : shapeSafeB f0 = true) :
    optimizeExe f0 cfg = runStages cfg (removeUnreachable f0) :=
  optimizeExe_complete cfg f0 h (.inl hs) hsafe

end Opt

namespace Opt.CompleteOptimizeWitness

open Clif

/-- `v4` recomputes `v0` (GVN), `v5` is dead (DCE), and the loop `block1` computes the invariant
`v2 = iconst 7` (LICM). -/
def fn : Function where
  name := "w"
  sig := {}
  blocks := [
    { id := 0, body := [{ results := [0], inst := .iconst .i32 5 }, { results := [4], inst := .iconst .i32 5 },
        { results := [5], inst := .iconst .i32 9 }],
      term := .jump { block := 1, args := [4] } },
    { id := 1, params := [(1, .i32)],
      body := [{ results := [2], inst := .iconst .i32 7 }, { results := [3], inst := .binary .iadd .i32 1 2 }],
      term := .brif 3 { block := 1, args := [3] } { block := 2 } },
    { id := 2, term := .ret [] }]

def cfg : Config := { simplify := false }
def exeCfg : Config := { exeConfig with simplify := false }

theorem checks : (match check (removeUnreachable fn) with
    | .ok _ => true
    | .error _ => false) = true := by native_decide

theorem wellFormed : ∃ i, check (removeUnreachable fn) = .ok i := by
  have h := checks
  split at h
  · exact ⟨_, ‹_›⟩
  · cases h

/-- The validated pipeline removes `v4` (GVN) and `v5` (DCE) and hoists `v2` (LICM). -/
theorem stats : (optimizeReport cfg fn).2.gvnRemoved = 1 ∧ (optimizeReport cfg fn).2.dceRemoved = 1 ∧
    (optimizeReport cfg fn).2.hoisted = 1 ∧ instCount fn = 5 ∧ instCount (optimize fn cfg) = 3 ∧
    shapeSafeB fn = true := by native_decide

/-- Non-vacuity of `optimize_complete_noSimp` and `optimizeExe_complete_noSimp`: on `fn`, where
GVN, DCE and LICM each change the function, no stage stops, and `optimize` (default
configuration without simplify) and `optimizeExe` (the executable configuration without simplify)
are the unvalidated pipeline. -/
theorem witness : (optimizeReport cfg fn).2.passError = none ∧
    optimize fn cfg = runStages cfg (removeUnreachable fn) ∧
    optimizeExe fn exeCfg = runStages exeCfg (removeUnreachable fn) ∧
    instCount (optimize fn cfg) < instCount fn ∧ (optimizeReport cfg fn).2.hoisted = 1 := by
  obtain ⟨hg, hd, hh, h5, h3, hs⟩ := stats
  obtain ⟨h1, h2⟩ := optimize_complete_noSimp cfg rfl fn wellFormed
  exact ⟨h1, h2, optimizeExe_complete_noSimp exeCfg rfl fn wellFormed hs, by omega, hh⟩

end Opt.CompleteOptimizeWitness
