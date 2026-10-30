import FV.Link.ExeUnwind
import FV.Link.OptExe
import FV.Link.DeadCleanupExeSource
import FV.Link.ExeInputCleanup
import FV.E2E.OptUnwind

/-!
# The optimising executable compiler on the exceptional edges (S10g, #404)

`compileExeOptU S file0`: the optimising executable compiler `compileExeOpt` (`compileExe` on the
optimised input `S.opt`, `lake exe lean-link --opt`, `cargo fv --lean-link --opt-proven-only`),
then `unwOkB` of the optimised input on the written executable — `compileExeU S.opt`, what
`lean-link --opt` decides.

* `compileExeOpt_correct_unwind`: `compileExe_correct_unwind`'s statement (`UnwindStmt`) for the
  optimised input: the unwinder reads the compiled functions' tables from the file, and the
  linked machine with unwinding refines the optimised program's runs with unwinding.
* **`compileExeOpt_correct_unwind_peak`**: through the mid-end. For a function `f` of the
  input's program (after the `i128` legalisation, before the mid-end) and its optimisation `f'`
  (same name) entered with the same registers, slots and memory, the linked machine with
  unwinding of the optimised program, of depth `d` (a bound on the call depth of the optimised
  program's run with unwinding), refines **every** run with unwinding of the input's program from
  `f`'s entry: a return is an ABI return with the same values and memory, a trap the same trap,
  an exception leaving `f` an ABI return to the caller with the exception object in x0 and the same
  memory. The mid-end's simulation with handler edges (`Opt.runLoopX_refinesU`,
  `FnInput.opt_simU`) matches each such outcome by the optimised run's, and
  `compileExe_correct_unwind_peak` at that run's fuel closes the chain.
-/

namespace Link.DeadCleanup

set_option autoImplicit false

open E2E E2E.LinkCheck E2E.DeadCleanupBinary Backend Backend.Proof Backend.Proof.Driver

/-- **The optimising executable compiler with the unwind tables checked**: `compileExeOpt`, then
`unwOkB` of the optimised input on the written executable. -/
def compileExeOptU (S : LinkSpec) (file0 : ByteArray) : Except String ByteArray :=
  compileExeU S.opt file0

theorem compileExeOptU_spec {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOptU S file0 = .ok file) :
    compileExeOpt S file0 = .ok file ∧ unwOkB S.opt file = true :=
  compileExeU_spec h

/-- **What `lean-link --opt` decides is `compileExeOptU`**: its compiler input is the optimised
functions' layout `placed S.opt`, the theorems' `S.withSizes (sizesOf S.opt)` optimised. -/
theorem compileExeOptU_placed (S : LinkSpec) (file0 : ByteArray) :
    compileExeOptU (S.withSizes (sizesOf S.opt)) file0 = compileExeU (placed S.opt) file0 := by
  rw [compileExeOptU, withSizes_opt]
  rfl

/-- **The optimising executable compiler is correct on the exceptional edges, about the
optimised program**: `compileExe_correct_unwind`'s statement for the optimised input. -/
theorem compileExeOpt_correct_unwind {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOptU S file0 = .ok file) : UnwindStmt S.opt file :=
  unwindStmt_of h

/-- The optimised input's function simulates the input's, the handler edges included. -/
theorem _root_.E2E.LinkCheck.FnInput.opt_simU (fi : FnInput) :
    Opt.FunSimU fi.func fi.opt.func := by
  rcases fi.opt_func with h | h <;> rw [h]
  · exact Opt.optimizeExe_simU _ (Opt.simplifyPassSimU_proven rfl rfl) _
  · exact Opt.FunSimU.refl _

/-- The optimised program's functions simulate the input program's, pointwise. -/
theorem funsSimU_prog (S : LinkSpec) :
    Opt.FunsSimU (prog S.inputCleanup).funcs (prog S.opt.inputCleanup).funcs := by
  rw [prog_eq, prog_eq]
  show Opt.FunsSimU (S.funcs.map FnInput.func) ((S.funcs.map FnInput.opt).map FnInput.func)
  rw [List.map_map]
  induction S.funcs with
  | nil => exact .nil
  | cons fi fs ih => exact .cons fi.opt_simU ih

/-- Entries of `f` and of `f'` simulating it, with the same registers, slots and memory, are
related with unwinding. -/
theorem sru_entry {f f' : Clif.Function} (hp : Opt.FunSimU f f') {args : List Clif.Val}
    {cs cs' : Clif.State} (hcs : ClifEntry f args cs) (hcs' : ClifEntry f' args cs')
    (hregs : cs.frame.regs = cs'.frame.regs) (hsl : cs.frame.slots = cs'.frame.slots)
    (hmem : cs.mem = cs'.mem) : Opt.SRU cs.mem.symbols cs.toX cs'.toX := by
  obtain ⟨b, hb, hbody, hterm, hty, hregs0⟩ := hcs.entry
  obtain ⟨b', hb', hbody', hterm', -, -⟩ := hcs'.entry
  obtain ⟨R, hR, hent⟩ := hp.sim cs.mem.symbols
  obtain ⟨b'', hb'', -, hrel⟩ := hent b hb
  rw [hb'] at hb''
  cases hb''
  have hcx : cs.toX = ⟨cs, []⟩ := by simp [Clif.State.toX, hcs.callers]
  have hcx' : cs'.toX = ⟨cs', []⟩ := by simp [Clif.State.toX, hcs'.callers]
  rw [hcx, hcx']
  refine ⟨hmem.symm, rfl, Opt.GRU.of hR ?_, ?_⟩
  · have hfr : cs.frame = ⟨f, cs.frame.regs, cs.frame.slots, b.body, b.term⟩ := by
      have h1 := hcs.func
      cases hfr0 : cs.frame with
      | mk fu re sl bo te =>
        rw [hfr0] at h1 hbody hterm
        simp only at h1 hbody hterm
        rw [h1, hbody, hterm]
    have hfr' : cs'.frame = ⟨f', cs'.frame.regs, cs'.frame.slots, b'.body, b'.term⟩ := by
      have h1 := hcs'.func
      cases hfr0 : cs'.frame with
      | mk fu re sl bo te =>
        rw [hfr0] at h1 hbody' hterm'
        simp only at h1 hbody' hterm'
        rw [h1, hbody', hterm']
    show R cs.frame cs'.frame
    rw [hfr, hfr', ← hregs, ← hsl]
    exact hrel args cs.frame.regs cs.frame.slots hty.symm hregs0 hcs.slotIds
  · show Opt.CallersRelU _ _ cs.callers [] cs'.callers []
    rw [hcs.callers, hcs'.callers]
    exact .nil _

/-- **The optimising executable compiler is correct on the exceptional edges, through the
mid-end, for the run's peak call depth**: for `compileExeOptU S file0 = .ok file`, the linked
program with unwinding `L` of the optimised input (premises as in
`compileExe_correct_unwind_peak`; its CLIF environment keeps the link-time symbols,
`Opt.EnvKeepsSymbolsX`), a function `f` of the input's program and its optimisation `f'` (named
`n`) entered with the same registers, slots and memory, and a bound `d` on the call depth of the
optimised program's run with unwinding: the unwinder reads every compiled function's tables
from `file`, and for every fuel `k` the linked machine with unwinding of depth `d` refines the
input program's run with unwinding of `k` steps from `f`'s entry (`ArmRefinesU`: a return, a
trap, an exception leaving `f`). -/
theorem compileExeOpt_correct_unwind_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOptU S file0 = .ok file) (B : BaseEnv) (F : BitVec 64 → Prop)
    (hB : BaseOk (LinkSys.ofInputCleanup S.opt.inputCleanup B F))
    (hF : ∀ a, (LinkSys.ofInputCleanup S.opt.inputCleanup B F).Img a → F a)
    (L : LinkSysU) (hLs : L.toLinkSys = LinkSys.ofInputCleanup S.opt.inputCleanup B F)
    (hb : BaseU L) (hNI : L.OkUNI) (hkeep : Opt.EnvKeepsSymbolsX L.envX)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {n : String} {f f' : Clif.Function}
    (hf : (prog S.inputCleanup).func? n = some f)
    (hf' : (prog S.opt.inputCleanup).func? n = some f') (d : Nat) {ra : BitVec 64}
    {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs cs' : Clif.State}
    (hent : AbiEntry (L.A f').fb (L.A f').base ra s) (hres : StackAvail (κ d f') (L.A f').af s)
    (hFw : L.F = frameWG (κ d f') (RAFrame.compute (L.A f').vcp (L.A f').rf).intBase
      (RAFrame.compute (L.A f').vcp (L.A f').rf).size (L.A f').af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f').af + κ d f') (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f').af s w₀) (hargs : ArgsIn f'.sig args s)
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry f' args cs')
    (hregs : cs.frame.regs = cs'.frame.regs) (hsl : cs.frame.slots = cs'.frame.slots)
    (hmem : cs.mem = cs'.mem) (hsav : StackArgsAvoid L.Img f'.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f').af.slotBase,
      (RAFrame.compute (L.A f').vcp (L.A f').rf).intBase⟩ f' cs'.frame.slots cs'.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs'.mem (spv w₀))
    (hd : Clif.DepthLeX L.envX L.P d cs'.toX)
    (htr : ∀ Fu, TrapsExplicitX ((L.peakX Fu).envRX d f') L.P.bare cs') (k : Nat) :
    (∀ g ∈ L.P.funcs, ∀ pc, (L.A g).base.toNat ≤ pc → pc < (L.A g).base.toNat + (L.A g).fb.size →
        EhCheck.unwTables file pc = some ((L.A g).base.toNat, (L.A g).tables)) ∧
      ArmRefinesU (L.A f').fb (L.A f').base ra (L.machU d f') s
        (Clif.runLoopX L.envX (prog S.inputCleanup) k cs.toX) := by
  have hP : L.P = prog S.opt.inputCleanup := by rw [hLs]; rfl
  have hf'P : f' ∈ L.P.funcs := by rw [hP]; exact (Clif.Program.func?_some hf').1
  have hpair : Opt.FunSimU f f' := by
    obtain ⟨g, hg, hfg⟩ := ((funsSimU_prog S).findP (· == n)).1 f hf
    have : (prog S.opt.inputCleanup).func? n = some g := hg
    rw [hf'] at this
    cases this
    exact hfg
  obtain ⟨m, hm⟩ := Opt.runLoopX_refinesU hkeep (funsSimU_prog S) k cs.toX cs'.toX
    (sru_entry hpair hcs hcs' hregs hsl hmem)
  have hpk := fun Fu => compileExe_correct_unwind_peak h B F hB hF L hLs hb hNI hκ hf'P Fu d hent
    hres hFw hgfree himg hbe hargs hcs' hsav hrel hpl hd (htr Fu)
  refine ⟨(hpk 0).1, ?_⟩
  rw [← hP] at hm
  cases m with
  | zero =>
    refine armRefinesU_of_outcome hm ?_
    rw [Clif.runLoopX]
    trivial
  | succ Fu => exact armRefinesU_of_outcome hm (hpk Fu).2

end Link.DeadCleanup
