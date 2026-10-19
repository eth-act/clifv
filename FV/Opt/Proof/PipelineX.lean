import FV.Opt.Proof.SimpSimX
import FV.Opt.Proof.UnreachableX
import FV.Opt.Proof.SimpPass

/-!
# The pipeline refines, `call_indirect` and `try_call` included (`Opt.optimizeX_simX`)

`Opt.optimizeReport_sim` (`FV/Opt/Proof/Pipeline.lean`) for `FunSimX`: the stages keep the
signature declarations (`*_sigDecls`, read by `call_indirect` and `try_call`), the validated
stages simulate (`removeUnreachable_simX`, `editOk_simX`, `simpOk_simX`), and `FunSimX`
composes. The first `removeUnreachable` needs `freshOkB` (the guard of `optimizeX`); after each
simplify stage the function is well formed, so every operand is below its fresh value
(`closedB_of_check`).
-/

namespace Opt

open Clif

/-! ## The stages keep the signature declarations -/

theorem Subst.apply_sigDecls (s : Subst) (f : Function) : (s.apply f).sigDecls = f.sigDecls := by
  unfold Subst.apply; split <;> rfl

theorem dce_sigDecls (f : Function) : (dce f).1.sigDecls = f.sigDecls := rfl

theorem gvnFull_sigDecls (f : Function) (info : Info) (l : Inst → Bool) :
    (gvnFull f info l).1.sigDecls = f.sigDecls := by
  unfold gvnFull
  exact Subst.apply_sigDecls _ _

theorem simplify_sigDecls (rules : SimplifyFn) (skel : SkeletonFn) (a s : Inst → Bool) (r : Bool)
    (f : Function) (info : Info) : (simplify rules skel a s r f info).1.sigDecls = f.sigDecls := by
  unfold simplify
  exact Subst.apply_sigDecls _ _

theorem licm_sigDecls (h : Bool) (f : Function) (info : Info) :
    (licm h f info).1.sigDecls = f.sigDecls := by
  unfold licm
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  apply forIn_bind_inv (P := fun s => s.1.sigDecls = f.sigDecls)
    (Q := fun x : Function × Nat => x.1.sigDecls = f.sigDecls)
  · rfl
  · intro a s hs
    split <;> exact hs
  · intro s hs; exact hs

/-! ## Well-formed functions read only defined values -/

theorem closedB_of_check {g : Function} {info : Info} (h : check g = .ok info) : closedB g = true := by
  have hW := wf_of_check h
  simp only [closedB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  intro b hb
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hb
  refine ⟨fun st hst v hv => ?_, fun v hv => avail_lt hW (hW.termUses i b hi v hv)⟩
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hst
  exact avail_lt hW (hW.uses i b hi j st hj v hv)

theorem freshOkB_of_check {g : Function} {info : Info} (h : check (removeUnreachable g) = .ok info) :
    freshOkB g = true := by
  simp [freshOkB, closedB_of_check h]

/-! ## The simplify stage -/

/-- `SimplifyPassSim` for `FunSimX`. -/
def SimplifyPassSimX (rules : SimplifyFn) (skel : SkeletonFn) : Prop :=
  ∀ allowed skelOk remat g info, check g = .ok info →
    simpOk g (simplify rules skel allowed skelOk remat g info).1 info
      (simplify rules skel allowed skelOk remat g info).2.2 = true →
    FunSimX g (simplify rules skel allowed skelOk remat g info).1

/-- **The simplify stage refines** for sound rule sets, `call_indirect` and `try_call`
included. -/
theorem simplifyPassSimX {rules : SimplifyFn} {skel : SkeletonFn} (hS : SimplifySound rules)
    (hK : SkeletonSound skel) : SimplifyPassSimX rules skel := by
  intro allowed skelOk remat g info hg hok
  exact simpOk_simX hg hok (simplify_facts hS hK hg) (simplify_sigDecls _ _ _ _ _ _ _)

/-- The proven rule sets satisfy the simplify stage's hypothesis. -/
theorem simplifyPassSimX_proven {cfg : Config} (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven) : SimplifyPassSimX cfg.simplifyFn cfg.skeletonFn := by
  cases cfg
  simp only at hr ha
  subst hr ha
  exact simplifyPassSimX Proof.simplifySound_proven Proof.skeletonSound_proven

/-! ## The pipeline -/

/-- **The mid-end pipeline refines**, `call_indirect` and `try_call` included, for inputs
passing the fresh-value guard. -/
theorem optimizeReport_simX (cfg : Config)
    (hS : SimplifyPassSimX cfg.simplifyFn cfg.skeletonFn) (f0 : Function)
    (hok : freshOkB f0 = true) :
    FunSimX f0 (optimizeReport cfg f0).1 ∧ (optimizeReport cfg f0).1.sigDecls = f0.sigDecls := by
  have hU := removeUnreachable_simX f0 hok
  have hsdU := removeUnreachable_sigDecls f0
  unfold optimizeReport
  simp only [Id.run]
  split
  · rename_i i hc
    simp only [pure_bind]
    apply forIn_bind_inv (P := fun s : Report × Function × Info × Bool =>
      FunSimX f0 s.2.1 ∧ check s.2.1 = .ok s.2.2.1 ∧ s.2.1.sigDecls = f0.sigDecls)
      (Q := fun x : Function × Report => FunSimX f0 x.1 ∧ x.1.sigDecls = f0.sigDecls)
    · exact ⟨hU, hc, hsdU⟩
    · intro stage s hs
      obtain ⟨hsim, hchk, hsd⟩ := hs
      obtain ⟨r, g, info, stop⟩ := s
      simp only at hsim hchk hsd
      simp only [Id.run]
      repeat' split
      all_goals simp only [pure, ForInStep.value]
      all_goals first
        | with_reducible exact ⟨hsim, hchk, hsd⟩
        | (exfalso; rename_i h _; simp at h; done)
        | (exfalso; rename_i h _; exact absurd (beq_iff_eq.1 h) ‹_›)
        | (rename_i hck' _ hv
           have h1 := hS (allowedIn (removeUnreachable f0)) (skelAllowedIn (removeUnreachable f0))
             cfg.rematConst g info hchk hv
           exact ⟨hsim.trans (h1.trans (removeUnreachable_simX _ (freshOkB_of_check hck'))), hck',
             by rw [removeUnreachable_sigDecls, simplify_sigDecls, hsd]⟩)
        | (rename_i hck' _ hv
           exact ⟨hsim.trans (editOk_simX hchk hck' hv (by
             first
             | rw [gvnFull_sigDecls]
             | rw [dce_sigDecls]
             | rw [licm_sigDecls])), hck', by
             first
             | rw [gvnFull_sigDecls, hsd]
             | rw [dce_sigDecls, hsd]
             | rw [licm_sigDecls, hsd]⟩)
    · intro s hs
      simp only [Id.run, pure]
      split
      · exact ⟨hs.1, hs.2.2⟩
      · exact ⟨FunSimX.refl f0, rfl⟩
  · exact ⟨hU, hsdU⟩

/-- **The mid-end with the fresh-value guard refines**, `call_indirect` and `try_call`
included, every function. -/
theorem optimizeX_simX (cfg : Config) (hS : SimplifyPassSimX cfg.simplifyFn cfg.skeletonFn)
    (f : Function) : FunSimX f (optimizeX f cfg) := by
  unfold optimizeX
  split
  · exact (optimizeReport_simX cfg hS f ‹_›).1
  · exact FunSimX.refl f

/-- The proven rule sets. -/
theorem optimizeX_simX_proven {cfg : Config} (hr : cfg.rules = .cranelift)
    (ha : cfg.ruleAllow = .proven) (f : Function) : FunSimX f (optimizeX f cfg) :=
  optimizeX_simX cfg (simplifyPassSimX_proven hr ha) f

/-- `optimizeX` keeps the signature declarations. -/
theorem optimizeX_sigDecls (cfg : Config) (f : Function) :
    (optimizeX f cfg).sigDecls = f.sigDecls := by
  unfold optimizeX
  split
  · -- the pipeline's stages keep them (the guard only selects the input)
    unfold optimize optimizeReport
    simp only [Id.run]
    split
    · simp only [pure_bind]
      apply forIn_bind_inv (P := fun s : Report × Function × Info × Bool =>
        s.2.1.sigDecls = f.sigDecls)
        (Q := fun x : Function × Report => x.1.sigDecls = f.sigDecls)
      · exact removeUnreachable_sigDecls f
      · intro stage s hs
        obtain ⟨r, g, info, stop⟩ := s
        simp only at hs
        simp only [Id.run]
        repeat' split
        all_goals simp only [pure, ForInStep.value]
        all_goals first
          | with_reducible exact hs
          | (exfalso; rename_i h _; simp at h; done)
          | (exfalso; rename_i h _; exact absurd (beq_iff_eq.1 h) ‹_›)
          | (rw [removeUnreachable_sigDecls, simplify_sigDecls, hs])
          | (rw [gvnFull_sigDecls, hs])
          | (rw [dce_sigDecls, hs])
          | (rw [licm_sigDecls, hs])
      · intro s hs
        simp only [Id.run, pure]
        split
        · exact hs
        · rfl
    · exact removeUnreachable_sigDecls f
  · rfl

/-- **The mid-end of the executable compiler refines**, `call_indirect` and `try_call`
included, every function. -/
theorem optimizeExe_simX (cfg : Config) (hS : SimplifyPassSimX cfg.simplifyFn cfg.skeletonFn)
    (f : Function) : FunSimX f (optimizeExe f cfg) := by
  unfold optimizeExe
  dsimp only
  split
  · exact optimizeX_simX cfg hS f
  · exact FunSimX.refl f

theorem optimizeExe_sigDecls (cfg : Config) (f : Function) :
    (optimizeExe f cfg).sigDecls = f.sigDecls := by
  unfold optimizeExe
  dsimp only
  split
  · exact optimizeX_sigDecls cfg f
  · rfl

/-- The executable compiler's configuration has the proven rule sets. -/
theorem simplifyPassSimX_exe : SimplifyPassSimX exeConfig.simplifyFn exeConfig.skeletonFn :=
  simplifyPassSimX_proven rfl rfl

/-! ## Programs -/

theorem initState_relX {p q : Program} (hP : FunsSimX p.funcs q.funcs) {f : String}
    {args : List Val} {mem : Mem} {s : State} (h : initState p f args mem = .ok s) :
    ∃ s', initState q f args mem = .ok s' ∧ SRX s.mem.symbols s s' := by
  simp only [initState, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.pure_eq_ok] at h
  obtain ⟨fn, hfn, ⟨fr, mem'⟩, he, rfl⟩ := h
  obtain ⟨g, hg, hfg⟩ := (hP.findP (· == f)).1 fn hfn
  obtain ⟨fr', he', hgr, -⟩ := funSimX_entry (syms := mem'.symbols) hfg he
  refine ⟨⟨fr', [], mem'⟩, ?_, rfl, rfl, hgr, .nil _⟩
  simp only [initState, Program.func?] at hg ⊢
  simp [hg, he']

/-- **Program refinement by the executable compiler's mid-end**: whenever `Clif.run` of a
program returns or traps, `Clif.run` of the optimised program does the same — `call_indirect`
and `try_call`/`try_call_indirect` included (no premise on the program). -/
theorem optimizeProgramExe_refines (cfg : Config)
    (hS : SimplifyPassSimX cfg.simplifyFn cfg.skeletonFn) {env : Env}
    (hE : EnvKeepsSymbols env) (p : Program) (f : String) (args : List Val) (fuel : Nat) :
    ∃ fuel', OutcomeRefines (run env p f args fuel)
      (run env (optimizeProgramExe p cfg) f args fuel') := by
  have hP : FunsSimX p.funcs (optimizeProgramExe p cfg).funcs :=
    FunsSimX.map (T := (optimizeExe · cfg)) (optimizeExe_simX cfg hS)
  have hd : (optimizeProgramExe p cfg).initMem = p.initMem := by
    have hn : ∀ g : Function, (optimizeExe g cfg).name = g.name :=
      fun g => (optimizeExe_simX cfg hS g).name
    have hx : ∀ g : Function, (optimizeExe g cfg).externs = g.externs :=
      fun g => (optimizeExe_simX cfg hS g).externs
    simp only [Program.initMem, optimizeProgramExe, List.map_map, List.flatMap_map,
      Function.comp_def, hn, hx]
  simp only [run, hd]
  cases hm : p.initMem with
  | trap c => exact ⟨0, ⟨fun _ _ h => h, fun _ h => h⟩⟩
  | stuck m => exact ⟨0, ⟨fun _ _ h => h, fun _ h => h⟩⟩
  | ok mem =>
    simp only [runWith]
    cases hi : initState p f args mem with
    | trap c =>
      have : initState p f args mem ≠ .trap c := by
        intro h
        unfold initState at h
        cases hx : p.func? f with
        | none => simp [hx, Res.ofOption, bind, Res.bind] at h
        | some fn =>
          simp only [hx, Res.ofOption, Res.ok_bind] at h
          cases he : enterFunc fn args mem with
          | ok x => simp [he, bind, Res.bind, pure] at h
          | trap c' => exact enterFunc_not_trap _ _ _ _ he
          | stuck m => simp [he, bind, Res.bind] at h
      exact absurd hi this
    | stuck m => exact ⟨0, ⟨(fun _ _ h => by cases h), (fun _ h => by cases h)⟩⟩
    | ok s =>
      obtain ⟨s', hi', hr⟩ := initState_relX hP hi
      obtain ⟨n', hn', -⟩ := runLoop_refinesX hE hP fuel s s' hr
      exact ⟨n', by simp only [hi']; exact hn'⟩

end Opt
