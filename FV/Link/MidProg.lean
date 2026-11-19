import FV.Link.MidSource

/-! # Two programs through the mid-end validator (#1119, plumbing layer 2)

`Link.midSource{,_depth}` for any two programs `P0 Q` whose functions are related by
`Opt.MidVal.Validated P0.funcs Q.funcs` (decided by `Link.midValidatedB`), not only the source
programs of two link inputs: the binary check's theorems (`E2E.*.binary_correct_exec_*_mid`) take
`Q = prog I`, the compiled program, and the routes' `…Mid` theorems `P0 = I0.srcProg`,
`Q = I1.srcProg`.

* `midProg_sim`: the functions named `n` of the two programs simulate (`Opt.FunSimMU`; in
  particular the same signature);
* **`midProg`**: a run of `P0` from `f`'s entry `cs` that returns (traps) is a run of `Q` from `g`'s
  entry `midEntry g cs` (same registers, slots and memory) with the same results and memory (the
  same trap);
* **`midProg_depth`**: the same, keeping the call depth (`Clif.DepthLe`).
-/

namespace Link

open E2E E2E.LinkCheck

/-- The functions of the same name of two validated programs simulate. -/
theorem midProg_sim {P0 Q : Clif.Program} (hv : Opt.MidVal.Validated P0.funcs Q.funcs) {n : String}
    {f g : Clif.Function} (hf : P0.func? n = some f) (hg : Q.func? n = some g) :
    Opt.FunSimMU f g := by
  obtain ⟨g', hg', hsim⟩ := validated_find hv hf
  have hg2 : Q.funcs.find? (·.name == n) = some g := hg
  have hgg : g' = g := Option.some.inj (hg'.symm.trans hg2)
  rw [hgg] at hsim
  exact hsim

/-- **A program refines through the mid-end validator**: for programs `P0`, `Q` whose functions
are validated (`Opt.MidVal.Validated`), a run of `P0` from `f`'s entry `cs` that returns is a
return of `Q` from the entry `midEntry g cs` of its function `g` named `f`'s name, on the same
arguments, with the same slots, memory, results and final memory; a trap is the same trap. -/
theorem midProg {P0 Q : Clif.Program} (hv : Opt.MidVal.Validated P0.funcs Q.funcs)
    {B : Clif.Env} (hkeep : Opt.EnvKeepsSymbols B) {n : String} {f g : Clif.Function}
    (hf : P0.func? n = some f) (hg : Q.func? n = some g)
    {args : List Clif.Val} {cs : Clif.State} (hcs : ClifEntry f args cs) (M : Nat) :
    ClifEntry g args (midEntry g cs) ∧ (midEntry g cs).frame.slots = cs.frame.slots ∧
      (midEntry g cs).mem = cs.mem ∧
    (∀ vals cm, Clif.runLoop B P0 M cs = .returned vals cm →
      ∃ m, Clif.runLoop B Q m (midEntry g cs) = .returned vals cm) ∧
    (∀ c, Clif.runLoop B P0 M cs = .trapped c →
      ∃ m, Clif.runLoop B Q m (midEntry g cs) = .trapped c) := by
  have hsim := midProg_sim hv hf hg
  obtain ⟨hcs', hsl, hmem, hSR⟩ := midEntry_srMU hsim hcs
  obtain ⟨n', hn⟩ := Opt.runLoopX_refinesSRMU (envKeepsSymbolsX_toX hkeep) hv.funsSimMU M _ _ hSR
  rw [Clif.runLoopX_toX, Clif.runLoopX_toX] at hn
  have hr := outcomeRefines_of_toX hn
  exact ⟨hcs', hsl, hmem, fun vals cm h => ⟨n', hr.1 vals cm h⟩, fun c h => ⟨n', hr.2 c h⟩⟩

/-- **`midProg` keeping the call depth**: if the run of `P0` from `cs` has call depth at most `d`
(`Clif.DepthLe`) and returns (traps), so has the run of `Q` from `midEntry g cs`. -/
theorem midProg_depth {P0 Q : Clif.Program} (hv : Opt.MidVal.Validated P0.funcs Q.funcs)
    {B : Clif.Env} (hkeep : Opt.EnvKeepsSymbols B) {n : String} {f g : Clif.Function}
    (hf : P0.func? n = some f) (hg : Q.func? n = some g)
    {args : List Clif.Val} {cs : Clif.State} (hcs : ClifEntry f args cs)
    {d : Nat} (hd : Clif.DepthLe B P0 d cs) (M : Nat) :
    ClifEntry g args (midEntry g cs) ∧ (midEntry g cs).frame.slots = cs.frame.slots ∧
      (midEntry g cs).mem = cs.mem ∧
    (∀ vals cm, Clif.runLoop B P0 M cs = .returned vals cm →
      (∃ m, Clif.runLoop B Q m (midEntry g cs) = .returned vals cm) ∧
        Clif.DepthLe B Q d (midEntry g cs)) ∧
    (∀ c, Clif.runLoop B P0 M cs = .trapped c →
      (∃ m, Clif.runLoop B Q m (midEntry g cs) = .trapped c) ∧
        Clif.DepthLe B Q d (midEntry g cs)) := by
  have hsim := midProg_sim hv hf hg
  obtain ⟨hcs', hsl, hmem, hSR⟩ := midEntry_srMU hsim hcs
  obtain ⟨n', hn, hdep⟩ :=
    Opt.runLoopX_refinesSRMU_depth (envKeepsSymbolsX_toX hkeep) hv.funsSimMU M _ _ hSR
  have hdT : (∀ msg, Clif.runLoopX B.toX P0 M cs.toX ≠ .stuck msg) →
      Clif.runLoopX B.toX P0 M cs.toX ≠ .outOfFuel →
      Clif.DepthLe B Q d (midEntry g cs) := by
    intro h1 h2 u hu
    obtain ⟨ts', hx⟩ := Opt.reachesX_toX_of_reaches hu ((midEntry g cs).callers.map fun _ => none)
    exact hdep h1 h2 d (fun ys hy => hd _ (Opt.reaches_of_reachesX_toX hy)) _ hx
  rw [Clif.runLoopX_toX, Clif.runLoopX_toX] at hn
  have hr := outcomeRefines_of_toX hn
  refine ⟨hcs', hsl, hmem, fun vals cm h => ?_, fun c h => ?_⟩
  · have hx : Clif.runLoopX B.toX P0 M cs.toX = .returned vals cm := by
      rw [Clif.runLoopX_toX]; exact congrArg Clif.Outcome.toX h
    exact ⟨⟨n', hr.1 vals cm h⟩,
      hdT (fun msg he => by rw [hx] at he; cases he) (fun he => by rw [hx] at he; cases he)⟩
  · have hx : Clif.runLoopX B.toX P0 M cs.toX = .trapped c := by
      rw [Clif.runLoopX_toX]; exact congrArg Clif.Outcome.toX h
    exact ⟨⟨n', hr.2 c h⟩,
      hdT (fun msg he => by rw [hx] at he; cases he) (fun he => by rw [hx] at he; cases he)⟩

end Link
