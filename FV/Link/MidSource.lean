import FV.E2E.MidValPass
import FV.E2E.SrcScopeDefs
import FV.Opt.Proof.SemSimMUDepth

/-! # The bundle's program through the mid-end validator (#1119, plumbing layer 2)

With `--midval-opt`, `lean-link` compiles Cranelift's optimised function `g` (cg_clif's
`.opt.clif`) in place of cg_clif's source function `f` (`.unopt.clif`) where the mid-end
validator accepts it, and every other function unchanged. The routes' executable theorems are
stated about the source program of the **compiled** inputs `I1.srcProg`; this file carries them to
the bundle's source program `I0.srcProg` when the two programs' functions are related by
`Opt.MidVal.Validated` (the same function, or a `g` with `checkCert (ConstPhi.run f) g cert`
decided).

* `midEntry_srMU`: `E2E.midval_sr` from a memory-aware function simulation `Opt.FunSimMU f g`;
* `validated_find`: the function of the validated program with the source function's name, and
  its simulation;
* **`midSource`**: a run of `I0.srcProg` from `f`'s entry `cs` that returns (traps) is a run of
  `I1.srcProg` from `g`'s entry `midEntry g cs` (same registers, slots and memory) with the same
  results and memory (the same trap) (`Opt.runLoopX_refinesSRMU`, as `E2E.midval_entry`);
* **`midSource_depth`**: the same, keeping the call depth (`Clif.DepthLe`,
  `Opt.runLoopX_refinesSRMU_depth`).

The refinement is proven over base environments keeping the link-time symbols
(`Opt.EnvKeepsSymbols`), as `Link.cpSource`.
-/

namespace Link

open E2E E2E.LinkCheck

/-- **`E2E.midval_sr` from a function simulation**: the entry of `g` matching the entry of `f`,
and the related states, for `Opt.FunSimMU f g`. -/
theorem midEntry_srMU {f g : Clif.Function} (hsim : Opt.FunSimMU f g)
    {args : List Clif.Val} {cs : Clif.State} (hcs : ClifEntry f args cs) :
    ClifEntry g args (midEntry g cs) ∧
      (midEntry g cs).frame.slots = cs.frame.slots ∧ (midEntry g cs).mem = cs.mem ∧
      Opt.SRMU cs.mem.symbols cs.toX (midEntry g cs).toX := by
  obtain ⟨b, hb, hbody, hterm, hty, hregs⟩ := hcs.entry
  obtain ⟨R, hR, hent⟩ := hsim.sim cs.mem.symbols
  obtain ⟨b', hb', hpar, hrel⟩ := hent b hb
  have hoe : midEntry g cs =
      ⟨⟨g, cs.frame.regs, cs.frame.slots, b'.body, b'.term⟩, [], cs.mem⟩ := by
    simp [midEntry, hb']
  have hcx : cs.toX = ⟨cs, []⟩ := by simp [Clif.State.toX, hcs.callers]
  rw [hoe, hcx]
  refine ⟨⟨rfl, rfl, by rw [hsim.sig]; exact hcs.sig, ⟨b', hb', rfl, rfl, by rw [hpar]; exact hty,
    by rw [hpar]; exact hregs⟩, by rw [hsim.slots]; exact hcs.slotIds⟩, rfl, rfl,
    rfl, rfl, Opt.GRMU.of hR ?_, ?_⟩
  · show R cs.frame ⟨g, cs.frame.regs, cs.frame.slots, b'.body, b'.term⟩ cs.mem
    rw [ClifEntry.frame_eq hcs hbody hterm]
    exact hrel args cs.frame.regs cs.frame.slots cs.mem hty.symm hregs hcs.slotIds rfl
  · show Opt.CallersRelMU _ _ cs.callers [] [] []
    rw [hcs.callers]; exact .nil _

/-- The function of a validated list with a source function's name, simulating it. -/
theorem validated_find {fs gs : List Clif.Function} (hv : Opt.MidVal.Validated fs gs) {n : String}
    {f : Clif.Function} (hf : fs.find? (·.name == n) = some f) :
    ∃ g, gs.find? (·.name == n) = some g ∧ Opt.FunSimMU f g :=
  (hv.funsSimMU.findP (· == n)).1 f hf

/-- **The bundle's program refines through the mid-end validator**: for inputs `I0` (the
bundle's) and `I1` whose source programs' functions are validated (`Opt.MidVal.Validated`), a run
of `I0`'s source program from `f`'s entry `cs` that returns is a return of `I1`'s source program
from the entry `midEntry g cs` of its function `g` named `f`'s name, on the same arguments, with
the same slots, memory, results and final memory; a trap is the same trap. -/
theorem midSource {I0 I1 : LinkInput} (hv : Opt.MidVal.Validated I0.srcProg.funcs I1.srcProg.funcs)
    {B : Clif.Env} (hkeep : Opt.EnvKeepsSymbols B) {n : String} {f g : Clif.Function}
    (hf : I0.srcProg.func? n = some f) (hg : I1.srcProg.func? n = some g)
    {args : List Clif.Val} {cs : Clif.State} (hcs : ClifEntry f args cs) (M : Nat) :
    ClifEntry g args (midEntry g cs) ∧ (midEntry g cs).frame.slots = cs.frame.slots ∧
      (midEntry g cs).mem = cs.mem ∧
    (∀ vals cm, Clif.runLoop B I0.srcProg M cs = .returned vals cm →
      ∃ m, Clif.runLoop B I1.srcProg m (midEntry g cs) = .returned vals cm) ∧
    (∀ c, Clif.runLoop B I0.srcProg M cs = .trapped c →
      ∃ m, Clif.runLoop B I1.srcProg m (midEntry g cs) = .trapped c) := by
  obtain ⟨g', hg', hsim⟩ := validated_find hv hf
  have hg2 : I1.srcProg.funcs.find? (·.name == n) = some g := hg
  have hgg : g' = g := Option.some.inj (hg'.symm.trans hg2)
  rw [hgg] at hsim
  obtain ⟨hcs', hsl, hmem, hSR⟩ := midEntry_srMU hsim hcs
  obtain ⟨n', hn⟩ := Opt.runLoopX_refinesSRMU (envKeepsSymbolsX_toX hkeep) hv.funsSimMU M _ _ hSR
  rw [Clif.runLoopX_toX, Clif.runLoopX_toX] at hn
  have hr := outcomeRefines_of_toX hn
  exact ⟨hcs', hsl, hmem, fun vals cm h => ⟨n', hr.1 vals cm h⟩, fun c h => ⟨n', hr.2 c h⟩⟩

/-- **`midSource` keeping the call depth**: if the run of the bundle's program from `cs` has call
depth at most `d` (`Clif.DepthLe`) and returns (traps), so has the run of `I1`'s source program
from `midEntry g cs`. -/
theorem midSource_depth {I0 I1 : LinkInput}
    (hv : Opt.MidVal.Validated I0.srcProg.funcs I1.srcProg.funcs)
    {B : Clif.Env} (hkeep : Opt.EnvKeepsSymbols B) {n : String} {f g : Clif.Function}
    (hf : I0.srcProg.func? n = some f) (hg : I1.srcProg.func? n = some g)
    {args : List Clif.Val} {cs : Clif.State} (hcs : ClifEntry f args cs)
    {d : Nat} (hd : Clif.DepthLe B I0.srcProg d cs) (M : Nat) :
    ClifEntry g args (midEntry g cs) ∧ (midEntry g cs).frame.slots = cs.frame.slots ∧
      (midEntry g cs).mem = cs.mem ∧
    (∀ vals cm, Clif.runLoop B I0.srcProg M cs = .returned vals cm →
      (∃ m, Clif.runLoop B I1.srcProg m (midEntry g cs) = .returned vals cm) ∧
        Clif.DepthLe B I1.srcProg d (midEntry g cs)) ∧
    (∀ c, Clif.runLoop B I0.srcProg M cs = .trapped c →
      (∃ m, Clif.runLoop B I1.srcProg m (midEntry g cs) = .trapped c) ∧
        Clif.DepthLe B I1.srcProg d (midEntry g cs)) := by
  obtain ⟨g', hg', hsim⟩ := validated_find hv hf
  have hg2 : I1.srcProg.funcs.find? (·.name == n) = some g := hg
  have hgg : g' = g := Option.some.inj (hg'.symm.trans hg2)
  rw [hgg] at hsim
  obtain ⟨hcs', hsl, hmem, hSR⟩ := midEntry_srMU hsim hcs
  obtain ⟨n', hn, hdep⟩ :=
    Opt.runLoopX_refinesSRMU_depth (envKeepsSymbolsX_toX hkeep) hv.funsSimMU M _ _ hSR
  have hdT : (∀ msg, Clif.runLoopX B.toX I0.srcProg M cs.toX ≠ .stuck msg) →
      Clif.runLoopX B.toX I0.srcProg M cs.toX ≠ .outOfFuel →
      Clif.DepthLe B I1.srcProg d (midEntry g cs) := by
    intro h1 h2 u hu
    obtain ⟨ts', hx⟩ := Opt.reachesX_toX_of_reaches hu ((midEntry g cs).callers.map fun _ => none)
    exact hdep h1 h2 d (fun ys hy => hd _ (Opt.reaches_of_reachesX_toX hy)) _ hx
  rw [Clif.runLoopX_toX, Clif.runLoopX_toX] at hn
  have hr := outcomeRefines_of_toX hn
  refine ⟨hcs', hsl, hmem, fun vals cm h => ?_, fun c h => ?_⟩
  · have hx : Clif.runLoopX B.toX I0.srcProg M cs.toX = .returned vals cm := by
      rw [Clif.runLoopX_toX]; exact congrArg Clif.Outcome.toX h
    exact ⟨⟨n', hr.1 vals cm h⟩,
      hdT (fun msg he => by rw [hx] at he; cases he) (fun he => by rw [hx] at he; cases he)⟩
  · have hx : Clif.runLoopX B.toX I0.srcProg M cs.toX = .trapped c := by
      rw [Clif.runLoopX_toX]; exact congrArg Clif.Outcome.toX h
    exact ⟨⟨n', hr.2 c h⟩,
      hdT (fun msg he => by rw [hx] at he; cases he) (fun he => by rw [hx] at he; cases he)⟩

end Link
