import FV.Link.ConstPhiCompile
import FV.Link.ConstPhiPair
import FV.Link.OptExe

/-! # Constant-phi removal in the linked compiler: the composition (#990)

`LinkSpec.cp S` (`FV/Link/ConstPhiCompile.lean`) replaces each function of `S` by its
constant-phi removal or keeps it (`FnInput.cp_func`). Pointwise the pass's output simulates its
input and keeps its shape (`Opt.ConstPhi.run_pair`), so the programs of `S` and `S.cp` are
`OptRel`-related (`LinkSpec.cpRel`, `cpRel_prog`), as the mid-end's input and output are
(`FV/Link/OptFacts.lean`):

* `cpRun`: the run of `S.cp`'s program from the entry `cs'` of its function named `n` refines the
  run of `S`'s program from the entry `cs` of `S`'s function named `n` with the same registers,
  slots and memory (returns, traps, and the call depth of a finished run);
* **`cp_lift`**: so every theorem about an executable compiled from `S.cp` (`lean-link`'s routes,
  `compileExe{,T,U,Tail,Opt}_correct…` instantiated at `S.cp`) whose conclusion `R` holds for
  every outcome of `S.cp`'s run from `cs'` gives `R` for every outcome of `S`'s run from `cs`
  (`R` holding for the outcomes without a claim, `stuck`/`outOfFuel`, as `ExecRefines` does);
  the source domain composes the legalisation's refinement (`legalProg_refines`) in front;
* `withSizes_cp`: `withSizes` and `cp` commute (the layout of the totality theorems).
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.Binary E2E.ExecBytes Backend LinkSpec

/-- `FnInput.func` of a printed function is `Opt.ConstPhi.reparse`. -/
theorem _root_.E2E.LinkCheck.FnInput.func_reparse (fi : FnInput) (g : Clif.Function) :
    ({ fi with clif := clifHeader fi.clif ++ g.print, k := 0 } : FnInput).func =
      Opt.ConstPhi.reparse (clifHeader fi.clif) g := by
  unfold FnInput.func Opt.ConstPhi.reparse
  dsimp only
  cases (Opt.Legalize128.parsedFile128
      (Clif.parseFile (clifHeader fi.clif ++ g.print))).file.funcs[0]? with
  | none => rfl
  | some p => rcases p with ⟨_, _ | _, _⟩ <;> rfl

/-- What `FnInput.cp` does to the function. -/
theorem _root_.E2E.LinkCheck.FnInput.cp_func (fi : FnInput) :
    fi.cp.func = Opt.ConstPhi.run fi.func ∨ fi.cp.func = fi.func := by
  unfold FnInput.cp
  split
  · rename_i h
    simp only [Opt.ConstPhi.keeps, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .inl ((fi.func_reparse _).trans h.2)
  · exact .inr rfl

/-- The constant-phi-removed function and the function: a simulation keeping the shape. -/
theorem _root_.E2E.LinkCheck.FnInput.cp_pair (fi : FnInput) : OptPair fi.func fi.cp.func := by
  rcases fi.cp_func with h | h <;> rw [h]
  · exact Opt.ConstPhi.run_pair _
  · exact ⟨Opt.FunSimX.refl _, ShapeFacts.refl _⟩

theorem LinkSpec.cpRel (S : LinkSpec) : OptRel S.input.prog S.cp.input.prog := by
  show Opt.Pw2 OptPair (S.funcs.map FnInput.func) ((S.funcs.map FnInput.cp).map FnInput.func)
  rw [List.map_map]
  induction S.funcs with
  | nil => exact .nil
  | cons fi fs ih => exact .cons fi.cp_pair ih

/-- The constant-phi-removed program and the input's program. -/
theorem cpRel_prog (S : LinkSpec) : OptRel (prog S.input) (prog S.cp.input) := by
  rw [prog_input, prog_input]; exact S.cpRel

/-- The constant-phi-removed program's run from `cs'` refines the input program's from the input
function's entry `cs` with the same registers, slots and memory. -/
theorem cpRun {S : LinkSpec} {B : Clif.Env} (hE : Opt.EnvKeepsSymbols B) {n : String}
    {f f' : Clif.Function} (hf : (prog S.input).func? n = some f)
    (hf' : (prog S.cp.input).func? n = some f') {args : List Clif.Val} {cs cs' : Clif.State}
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry f' args cs')
    (hregs : cs.frame.regs = cs'.frame.regs) (hsl : cs.frame.slots = cs'.frame.slots)
    (hmem : cs.mem = cs'.mem) (k : Nat) :
    ∃ m, (∀ v cm, Clif.runLoop B (prog S.input) k cs = .returned v cm →
        Clif.runLoop B (prog S.cp.input) m cs' = .returned v cm) ∧
      (∀ c, Clif.runLoop B (prog S.input) k cs = .trapped c →
        Clif.runLoop B (prog S.cp.input) m cs' = .trapped c) ∧
      (Opt.Final (Clif.runLoop B (prog S.input) k cs) → ∀ d,
        Clif.DepthLe B (prog S.input) d cs → Clif.DepthLe B (prog S.cp.input) d cs') := by
  have hR := cpRel_prog S
  obtain ⟨cs0, hcs0, hr0, hs0, hm0, -, hSR⟩ := hR.entry hf hf' hcs'
  have : cs = cs0 := clifEntry_eq hcs hcs0 (hregs.trans hr0.symm) (hsl.trans hs0.symm)
    (hmem.trans hm0.symm)
  subst this
  exact hR.refines hE hSR k

/-- **Every claim about the constant-phi-removed input lifts to the input**: a predicate `R` of
outcomes that holds for every run of `S.cp`'s program from the entry `cs'` of its function named
`n` (and for the outcomes without a claim) holds for every run of `S`'s program from the entry
`cs` of its function named `n` with the same registers, slots and memory. -/
theorem cp_lift {S : LinkSpec} {B : Clif.Env} (hE : Opt.EnvKeepsSymbols B) {n : String}
    {f f' : Clif.Function} (hf : (prog S.input).func? n = some f)
    (hf' : (prog S.cp.input).func? n = some f') {args : List Clif.Val} {cs cs' : Clif.State}
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry f' args cs')
    (hregs : cs.frame.regs = cs'.frame.regs) (hsl : cs.frame.slots = cs'.frame.slots)
    (hmem : cs.mem = cs'.mem) {R : Clif.Outcome → Prop}
    (hR : ∀ m, R (Clif.runLoop B (prog S.cp.input) m cs'))
    (hstuck : ∀ e, R (.stuck e)) (hfuel : R .outOfFuel) (k : Nat) :
    R (Clif.runLoop B (prog S.input) k cs) := by
  obtain ⟨m, h1, h2, -⟩ := cpRun hE hf hf' hcs hcs' hregs hsl hmem k
  cases hrun : Clif.runLoop B (prog S.input) k cs with
  | returned v cm => rw [← h1 v cm hrun]; exact hR m
  | trapped c => rw [← h2 c hrun]; exact hR m
  | stuck e => exact hstuck e
  | outOfFuel => exact hfuel

/-- `withSizes` and `cp` commute. -/
theorem withSizes_cp (S : LinkSpec) (z : List Nat) : (S.withSizes z).cp = S.cp.withSizes z := by
  obtain ⟨funcs, names, sizes, outside, data, symNames, R⟩ := S
  simp only [LinkSpec.withSizes, LinkSpec.cp, LinkSpec.mk.injEq, List.map_map, true_and,
    and_true]
  exact List.map_congr_left fun fi _ => fi.cp_pair.2.name.symm

end Link
