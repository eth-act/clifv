import FV.Opt.Proof.GvnEdit
import FV.Opt.Proof.Unreachable
import FV.Opt.Optimize

/-!
# The pipeline refines (`Opt.optimize_sim`)

`Opt.optimizeReport` runs `removeUnreachable` (self-validating, `Opt.removeUnreachable_sim`),
then `check`, then each stage followed by `check` and — for GVN, DCE and LICM — the edit
validator (`Opt.editOk_sim`), keeping the last accepted function. The loop invariant is
`FunSim f0 g ∧ check g = .ok info`; FunSim composes (`FunSim.trans`).

The simplify stage is covered by the hypothesis `SimplifyPassSim`: the pass (for any rule
sets satisfying the rule obligations, `FV/Opt/Proof/Simplify*.lean`) refines on checked inputs.
-/

namespace Opt

open Clif

/-- Invariants of `forIn` over a list in `Id`, followed by a continuation. -/
theorem forIn_bind_inv {α σ β : Type} (l : List α) (init : σ) (f : α → σ → Id (ForInStep σ))
    (k : σ → Id β) (P : σ → Prop) (Q : β → Prop) (h0 : P init)
    (hf : ∀ a s, P s → P (f a s).run.value) (hk : ∀ s, P s → Q (k s).run) :
    Q ((forIn l init f >>= k).run) := by
  induction l generalizing init with
  | nil => simpa using hk init h0
  | cons a as ih =>
    rw [List.forIn_cons]
    have := hf a init h0
    cases hfa : f a init with
    | done b =>
      rw [hfa] at this
      simp only [bind_assoc, Id.run_bind, hfa]
      exact hk b this
    | yield b =>
      rw [hfa] at this
      simp only [bind_assoc, Id.run_bind, hfa]
      exact ih b this

/-- The simplify stage refines on checked inputs (for the given rule sets). -/
def SimplifyPassSim (rules : SimplifyFn) (skel : SkeletonFn) : Prop :=
  ∀ allowed skelOk remat g info, check g = .ok info →
    FunSim g (simplify rules skel allowed skelOk remat g info).1

/-- **The mid-end pipeline refines**, for every function (ill-formed inputs are returned with
only unreachable blocks removed, validated). -/
theorem optimizeReport_sim (cfg : Config)
    (hS : SimplifyPassSim cfg.simplifyFn cfg.skeletonFn) (f0 : Function) :
    FunSim f0 (optimizeReport cfg f0).1 := by
  have hU := removeUnreachable_sim f0
  unfold optimizeReport
  simp only [Id.run]
  split
  · rename_i i hc
    simp only [pure_bind]
    apply forIn_bind_inv (P := fun s : Report × Function × Info × Bool =>
      FunSim f0 s.2.1 ∧ check s.2.1 = .ok s.2.2.1)
      (Q := fun x : Function × Report => FunSim f0 x.1)
    · exact ⟨hU, hc⟩
    · intro stage s hs
      obtain ⟨hsim, hchk⟩ := hs
      obtain ⟨r, g, info, stop⟩ := s
      simp only at hsim hchk
      simp only [Id.run]
      repeat' split
      all_goals simp only [pure, ForInStep.value]
      all_goals first
        | exact ⟨hsim, hchk⟩
        | exact ⟨hsim.trans ((hS _ _ _ _ _ hchk).trans (removeUnreachable_sim _)), ‹_›⟩
        | (rename_i hchk' hcond
           simp only [Bool.or_eq_true, beq_iff_eq] at hcond
           rcases hcond with hcond | hcond
           · first | (simp at hcond; done) | exact absurd hcond ‹_›
           · exact ⟨hsim.trans (editOk_sim hchk hchk' hcond), hchk'⟩)
    · intro s hs
      simp only [Id.run, pure]
      split
      · exact hs.1
      · exact FunSim.refl f0
  · exact hU

/-- What the output of `optimizeReport` is: the (validated) `removeUnreachable f0`, or a
function accepted by the final guard `keepsBackendSubset f0`, or `f0`. -/
theorem optimizeReport_out (cfg : Config) (f0 : Function) (Q : Function → Prop) (h0 : Q f0)
    (hrm : Q (removeUnreachable f0)) (hg : ∀ g, keepsBackendSubset f0 g = true → Q g) :
    Q (optimizeReport cfg f0).1 := by
  unfold optimizeReport
  simp only [Id.run]
  split
  · simp only [pure_bind]
    apply forIn_bind_inv (P := fun _ : Report × Function × Info × Bool => True)
      (Q := fun x : Function × Report => Q x.1)
    · trivial
    · intro _ _ _; trivial
    · intro s _
      simp only [Id.run, pure]
      split
      · exact hg _ ‹_›
      · exact h0
  · exact hrm

theorem mem_callees {f : Function} {fn : FnRef} :
    fn ∈ callees f ↔ ∃ b ∈ f.blocks, ∃ st ∈ b.body, ∃ args, st.inst = .call fn args := by
  simp only [callees, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, st, hst, h⟩
    split at h
    · cases h; exact ⟨b, hb, st, hst, _, ‹_›⟩
    · cases h
  · rintro ⟨b, hb, st, hst, args, h⟩
    exact ⟨b, hb, st, hst, by simp [h]⟩

/-- The facts of the output the backend theorem uses (`E2E.backend_correct_opt`). -/
structure BackendFacts (f g : Function) : Prop where
  name : g.name = f.name
  sig : g.sig = f.sig
  slots : g.slots = f.slots
  globals : g.globals = f.globals
  externs : g.externs = f.externs
  subsetE : Compile.functionE f = true → Compile.functionE g = true
  callees : ∀ fn ∈ callees g, fn ∈ callees f

theorem removeUnreachable_facts (f : Function) : BackendFacts f (removeUnreachable f) := by
  unfold removeUnreachable
  simp only []
  split
  · rename_i hok
    obtain ⟨hn, hs, hsl, hgl, hex, -, -⟩ := unreachableOk_spec hok
    have hbl : ∀ b ∈ (removeUnreachableRaw f).blocks, b ∈ f.blocks := by
      simp only [unreachableOk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hok
      exact fun b hb => (hok.2 b hb).1
    refine ⟨hn, hs, hsl, hgl, hex, fun hE => ?_, fun fn hfn => ?_⟩
    · simp only [Compile.functionE, Bool.and_eq_true, List.all_eq_true] at hE ⊢
      rw [hs, hgl, hex]
      exact ⟨⟨⟨hE.1.1.1, hE.1.1.2⟩, hE.1.2⟩, fun b hb => hE.2 b (hbl b hb)⟩
    · obtain ⟨b, hb, st, hst, args, h⟩ := mem_callees.1 hfn
      exact mem_callees.2 ⟨b, hbl b hb, st, hst, args, h⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, id, fun _ h => h⟩

theorem keepsBackendSubset_facts {f g : Function} (h : keepsBackendSubset f g = true) :
    BackendFacts f g := by
  simp only [keepsBackendSubset, sameHeader, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.contains_iff_mem, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨hn, hs⟩, hsl⟩, hgl⟩, hex⟩, hE⟩, hc⟩ := h
  refine ⟨hn, hs, hsl, hgl, hex, fun h1 => ?_, hc⟩
  rcases hE with h2 | h2
  · rw [h1] at h2; cases h2
  · exact h2

theorem optimize_facts (cfg : Config) (f : Function) : BackendFacts f (optimize f cfg) :=
  optimizeReport_out cfg f (BackendFacts f) ⟨rfl, rfl, rfl, rfl, rfl, id, fun _ h => h⟩
    (removeUnreachable_facts f) (fun _ h => keepsBackendSubset_facts h)

theorem optimize_sim (cfg : Config) (hS : SimplifyPassSim cfg.simplifyFn cfg.skeletonFn)
    (f : Function) : FunSim f (optimize f cfg) :=
  optimizeReport_sim cfg hS f

/-- Initial states of related programs are related. -/
theorem initState_rel {p q : Program} (hP : FunsSim p.funcs q.funcs) {f : String}
    {args : List Val} {mem : Mem} {s : State} (h : initState p f args mem = .ok s) :
    ∃ s', initState q f args mem = .ok s' ∧ SR s.mem.symbols s s' := by
  simp only [initState, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.pure_eq_ok] at h
  obtain ⟨fn, hfn, ⟨fr, mem'⟩, he, rfl⟩ := h
  obtain ⟨g, hg, hfg⟩ := (hP.find f).1 fn hfn
  obtain ⟨fr', he', hgr, -⟩ := funSim_entry (syms := mem'.symbols) hfg he
  refine ⟨⟨fr', [], mem'⟩, ?_, rfl, rfl, hgr, .nil _⟩
  simp only [initState, Program.func?] at hg ⊢
  simp [hg, he']

/-- **Program refinement by the mid-end**: whenever `Clif.run` of a program returns or traps,
`Clif.run` of the optimised program (every function optimised) does the same. -/
theorem optimizeProgram_refines (cfg : Config)
    (hS : SimplifyPassSim cfg.simplifyFn cfg.skeletonFn) {env : Env}
    (hE : EnvKeepsSymbols env) (p : Program) (f : String) (args : List Val) (fuel : Nat) :
    ∃ fuel', OutcomeRefines (run env p f args fuel) (run env (optimizeProgram p cfg) f args fuel') := by
  have hP : FunsSim p.funcs (optimizeProgram p cfg).funcs :=
    FunsSim.map (T := (optimize · cfg)) (optimize_sim cfg hS)
  have hd : (optimizeProgram p cfg).initMem = p.initMem := rfl
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
      obtain ⟨s', hi', hr⟩ := initState_rel hP hi
      obtain ⟨n', hn'⟩ := runLoop_refines hE hP fuel s s' hr
      exact ⟨n', by simp only [hi']; exact hn'⟩

end Opt
