import FV.Front.RawExe
import FV.Link.ExeUnwind

/-!
# The executable compiler with unwinding on cg_clif's program (S10f)

`bundle_correct_raw_unwind`: for the `LinkSpec` `lean-link` builds from the bundle and an
executable `compileExeU` writes (what `lake exe lean-link` decides), and a function `f` of
cg_clif's program `rawLink us sc` (as in `FV/Front/RawExe.lean`):

* `compileExe S file0 = .ok file`, so `bundle_correct_raw`/`_peak` (the normal edges, about
  cg_clif's program's runs) apply to `file`;
* `f`'s compiled function — its legalisation under the linked names,
  `legalize (f.rename σ.fwd)` — is a function of the compiled program `prog S.inputCleanup`;
* `Link.DeadCleanup.UnwindStmt S file`: for every function of the compiled program (so for `f`'s),
  the unwinder reads its tables from `file` and the linked machine with unwinding refines its
  whole-program run with unwinding (`compileExe_correct_unwind`).

The exceptional edges are about the compiled (legalised, renamed) program's runs;
`FV/Front/RawExeUnwindRen.lean` carries them to cg_clif's program's runs for programs without
`i128` (renaming invariance of `Clif.runLoopX`).
-/

namespace Front

open Clif E2E E2E.LinkCheck E2E.DeadCleanupBinary Link Opt.Legalize128

/-- `f`'s compiled function is a function of the compiled program. -/
theorem mem_prog_raw {b : Bundle} {S : LinkSpec} (hb : buildSpec b = .ok S)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} (hraw : RawScopingOk us sc) {σ : Clif.Ren}
    (hσ : link us (finOf us) = (rawLink us sc).rename σ.fwd)
    {n : String} {f : Clif.Function} (hf : (rawLink us sc).func? n = some f) :
    legalize (f.rename σ.fwd) ∈ (prog S.inputCleanup).funcs := by
  obtain ⟨-, he⟩ := rawLink_eq_link (units_ok hus) hraw
  rw [← he] at hσ hf
  have hP : S.inputCleanup.srcProg = (link us (rawPull us sc)).rename σ.fwd := by
    obtain ⟨us', hus', -, hs⟩ := buildSpec_srcProg hb
    rw [hus] at hus'; cases hus'
    rw [← hσ, ← hs]; rfl
  have hf' : S.inputCleanup.srcProg.func? (σ.fwd n) = some (f.rename σ.fwd) := by
    rw [hP, Clif.Program.rename_func?, hf]; rfl
  rw [Link.DeadCleanup.prog_eq_legal, E2E.LegalProgram.legalProg_funcs]
  exact List.mem_map.2 ⟨_, (Clif.Program.func?_some hf').1, rfl⟩

/-- **The shipped executable compiler with the unwind tables checked, on cg_clif's program**:
`compileExe`'s success (`bundle_correct_raw`'s premise), `f`'s compiled function in the compiled
program, and the exceptional-edge statement `UnwindStmt` of the executable. -/
theorem bundle_correct_raw_unwind {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExeU S file0 = .ok file)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} (hraw : RawScopingOk us sc) {σ : Clif.Ren}
    (hσ : link us (finOf us) = (rawLink us sc).rename σ.fwd)
    {n : String} {f : Clif.Function} (hf : (rawLink us sc).func? n = some f) :
    Link.DeadCleanup.compileExe S file0 = .ok file ∧
      legalize (f.rename σ.fwd) ∈ (prog S.inputCleanup).funcs ∧
      Link.DeadCleanup.UnwindStmt S file :=
  ⟨(Link.DeadCleanup.compileExeU_spec h).1, mem_prog_raw hb hus hraw hσ hf,
    Link.DeadCleanup.unwindStmt_of h⟩

end Front
