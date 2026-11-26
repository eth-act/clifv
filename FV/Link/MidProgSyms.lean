import FV.Link.MidProg
import FV.Link.MidPairSyms

/-! # Two programs through the mid-end validator at one symbol table (#1119, hoisting)

`Link.midProg{,_depth}` from pointwise simulations at the symbol table `syms` of the run only
(`Opt.FunsSimMUAt syms P0.funcs Q.funcs`, decided by `Link.midValidatedSymsB syms`), for a run
whose memory has that table (`cs.mem.symbols = syms`; at the executable level the outside call
premise's `symbols` field). The `…_midS` binary theorems (`FV/E2E/MidValExecProvenSyms.lean`)
take `Q = prog I` and `syms = I.syms.lookup`, the routes' `…MidS` theorems
(`FV/Link/MidSourceRoutesSyms.lean`, `FV/Link/MidSourceTBSyms.lean`) the route input's table.

* `midEntry_srMUAt`: `Link.midEntry_srMU` from `Opt.FunSimMUAt syms f g`;
* `midProgAt_sim`: the functions named `n` of the two programs simulate at `syms`;
* **`midProgAt`**, **`midProgAt_depth`**: the conclusions of `midProg`, `midProg_depth`.
-/

namespace Link

open E2E E2E.LinkCheck

/-- **`midEntry_srMU` at one symbol table**: the entry of `g` matching the entry of `f`, and the
related states, for `Opt.FunSimMUAt syms f g` and an entry memory with the symbols `syms`. -/
theorem midEntry_srMUAt {syms : String → Option Nat} {f g : Clif.Function}
    (hsim : Opt.FunSimMUAt syms f g) {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs) (hsy : cs.mem.symbols = syms) :
    ClifEntry g args (midEntry g cs) ∧
      (midEntry g cs).frame.slots = cs.frame.slots ∧ (midEntry g cs).mem = cs.mem ∧
      Opt.SRMU syms cs.toX (midEntry g cs).toX := by
  obtain ⟨b, hb, hbody, hterm, hty, hregs⟩ := hcs.entry
  obtain ⟨R, hR, hent⟩ := hsim.sim
  obtain ⟨b', hb', hpar, hrel⟩ := hent b hb
  have hoe : midEntry g cs =
      ⟨⟨g, cs.frame.regs, cs.frame.slots, b'.body, b'.term⟩, [], cs.mem⟩ := by
    simp [midEntry, hb']
  have hcx : cs.toX = ⟨cs, []⟩ := by simp [Clif.State.toX, hcs.callers]
  rw [hoe, hcx]
  refine ⟨⟨rfl, rfl, by rw [hsim.sig]; exact hcs.sig, ⟨b', hb', rfl, rfl, by rw [hpar]; exact hty,
    by rw [hpar]; exact hregs⟩, by rw [hsim.slots]; exact hcs.slotIds⟩, rfl, rfl,
    rfl, hsy, Opt.GRMU.of hR ?_, ?_⟩
  · show R cs.frame ⟨g, cs.frame.regs, cs.frame.slots, b'.body, b'.term⟩ cs.mem
    rw [ClifEntry.frame_eq hcs hbody hterm]
    exact hrel args cs.frame.regs cs.frame.slots cs.mem hty.symm hregs hcs.slotIds hsy
  · show Opt.CallersRelMU _ _ cs.callers [] [] []
    rw [hcs.callers]; exact .nil _

/-- The functions of the same name of two programs simulating at `syms` simulate at `syms`. -/
theorem midProgAt_sim {syms : String → Option Nat} {P0 Q : Clif.Program}
    (hv : Opt.FunsSimMUAt syms P0.funcs Q.funcs) {n : String}
    {f g : Clif.Function} (hf : P0.func? n = some f) (hg : Q.func? n = some g) :
    Opt.FunSimMUAt syms f g := by
  obtain ⟨g', hg', hsim⟩ := (hv.findP (· == n)).1 f hf
  have hg2 : Q.funcs.find? (·.name == n) = some g := hg
  have hgg : g' = g := Option.some.inj (hg'.symm.trans hg2)
  rw [hgg] at hsim
  exact hsim

/-- **`midProg` at the run's symbol table** (module doc): for programs `P0`, `Q` whose functions
simulate at `syms` and a run of `P0` from `f`'s entry `cs` whose memory has the symbols `syms`, a
return is a return of `Q` from the entry `midEntry g cs` of its function `g` named `f`'s name, on
the same arguments, with the same slots, memory, results and final memory; a trap is the same
trap. -/
theorem midProgAt {syms : String → Option Nat} {P0 Q : Clif.Program}
    (hv : Opt.FunsSimMUAt syms P0.funcs Q.funcs)
    {B : Clif.Env} (hkeep : Opt.EnvKeepsSymbols B) {n : String} {f g : Clif.Function}
    (hf : P0.func? n = some f) (hg : Q.func? n = some g)
    {args : List Clif.Val} {cs : Clif.State} (hcs : ClifEntry f args cs)
    (hsy : cs.mem.symbols = syms) (M : Nat) :
    ClifEntry g args (midEntry g cs) ∧ (midEntry g cs).frame.slots = cs.frame.slots ∧
      (midEntry g cs).mem = cs.mem ∧
    (∀ vals cm, Clif.runLoop B P0 M cs = .returned vals cm →
      ∃ m, Clif.runLoop B Q m (midEntry g cs) = .returned vals cm) ∧
    (∀ c, Clif.runLoop B P0 M cs = .trapped c →
      ∃ m, Clif.runLoop B Q m (midEntry g cs) = .trapped c) := by
  have hsim := midProgAt_sim hv hf hg
  obtain ⟨hcs', hsl, hmem, hSR⟩ := midEntry_srMUAt hsim hcs hsy
  obtain ⟨n', hn⟩ := Opt.runLoopX_refinesSRMUAt (envKeepsSymbolsX_toX hkeep) hv M _ _ hSR
  rw [Clif.runLoopX_toX, Clif.runLoopX_toX] at hn
  have hr := outcomeRefines_of_toX hn
  exact ⟨hcs', hsl, hmem, fun vals cm h => ⟨n', hr.1 vals cm h⟩, fun c h => ⟨n', hr.2 c h⟩⟩

/-- **`midProgAt` keeping the call depth**: if the run of `P0` from `cs` has call depth at most `d`
(`Clif.DepthLe`) and returns (traps), so has the run of `Q` from `midEntry g cs`. -/
theorem midProgAt_depth {syms : String → Option Nat} {P0 Q : Clif.Program}
    (hv : Opt.FunsSimMUAt syms P0.funcs Q.funcs)
    {B : Clif.Env} (hkeep : Opt.EnvKeepsSymbols B) {n : String} {f g : Clif.Function}
    (hf : P0.func? n = some f) (hg : Q.func? n = some g)
    {args : List Clif.Val} {cs : Clif.State} (hcs : ClifEntry f args cs)
    (hsy : cs.mem.symbols = syms) {d : Nat} (hd : Clif.DepthLe B P0 d cs) (M : Nat) :
    ClifEntry g args (midEntry g cs) ∧ (midEntry g cs).frame.slots = cs.frame.slots ∧
      (midEntry g cs).mem = cs.mem ∧
    (∀ vals cm, Clif.runLoop B P0 M cs = .returned vals cm →
      (∃ m, Clif.runLoop B Q m (midEntry g cs) = .returned vals cm) ∧
        Clif.DepthLe B Q d (midEntry g cs)) ∧
    (∀ c, Clif.runLoop B P0 M cs = .trapped c →
      (∃ m, Clif.runLoop B Q m (midEntry g cs) = .trapped c) ∧
        Clif.DepthLe B Q d (midEntry g cs)) := by
  have hsim := midProgAt_sim hv hf hg
  obtain ⟨hcs', hsl, hmem, hSR⟩ := midEntry_srMUAt hsim hcs hsy
  obtain ⟨n', hn, hdep⟩ :=
    Opt.runLoopX_refinesSRMUAt_depth (envKeepsSymbolsX_toX hkeep) hv M _ _ hSR
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
