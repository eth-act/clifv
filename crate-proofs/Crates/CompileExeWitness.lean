import Crates.LeanLinkWitness
import FV.Link.Exe
import FV.Link.ExeTotal

/-! # Non-vacuity of the executable compiler's theorems (L1) on a survey crate

`Link.compileExe` succeeds on `a_arith`'s 58 functions (`Crates.LeanLinkWitness.spec`, with the
placeholder executable `file0`): `compile_eq`. `compileExe_correct`'s per-program premises are
then all discharged inside the theorem; its remaining premises are instantiated here for the
closed base environment (`BaseOk`, `HooksSim`) and a function of the program with no reachable
call cycle (`entry`): `correct_closed` leaves only the per-run premises of an outside call (the
boundary contract, the reference CLIF run, `TrapsExplicit`, the loader's image), which
`Crates.BinaryExecWitness` shows satisfiable for the panic=abort build of `a_arith`.
`total_witness`: every hypothesis of `compileExe_total` holds on this input.
-/

namespace Crates.CompileExeWitness

open E2E E2E.LinkCheck E2E.Binary E2E.ExecBytes Link Crates.LeanLinkWitness

/-- **The executable compiler compiles `a_arith`.** -/
theorem compile_eq : compileExe spec file0 = .ok file := by
  have h : InScopeP spec.input0 = true := by rw [← LinkSpec.inScope_input]; exact inScope
  simp only [compileExe, inScopePar_eq, h, ↓reduceIte, link_eq]

/-- No function of the program uses TLS (the closed base environment has none). -/
theorem noTls : (progOf spec.input.results).funcs.all (fun g => !Backend.hasTls g) = true := by
  native_decide

/-- The closed base environment's premises. -/
theorem base_closed : BaseOk (sys spec.input closedBase) :=
  baseOk_closedR fun g hg => by simpa using List.all_eq_true.1 noTls g hg

/-- A function of the program from which no call cycle is reachable. -/
def n : String := (spec.names.find? fun m => StackBound.goodN spec.input m).getD ""

theorem good : StackBound.goodN spec.input n = true := by native_decide

theorem entry : ∃ f, (prog spec.input).func? n = some f ∧
    ¬ StackBound.CycleFrom (StackBound.Calls spec.input spec.input.results) f :=
  (StackBound.goodN_iff (okB_leanLink inScope link_eq)).1 good

/-- **`compileExe_correct` on `a_arith`** with the closed base environment: for the entry `f`,
every outside call satisfying the per-run premises is refined by the executable's run. -/
theorem correct_closed : ∃ f, (prog spec.input).func? n = some f ∧
    ∀ (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State},
      (imageOf file).Intact r →
      OutsideCall spec.input (BinCheck.roByte spec.input spec.data) f
        (StackBound.stackFn spec.input f) r args cs.mem →
      ClifRun spec.input closedBase f r args cs →
      TrapsExplicit (Clif.linkEnvN (prog spec.input) closedBase.env M)
        ((prog spec.input).only f) cs →
      ExecRefines (art spec.input f).fb (art spec.input f).base (xreg 30 r)
        (step spec.input closedBase file) r (BinCheck.RelocAt spec.input)
        (Clif.runLoop closedBase.env (prog spec.input) (M + 1) cs) := by
  obtain ⟨f, hf, hc⟩ := entry
  exact ⟨f, hf, fun M _ _ _ hX ho hr htr =>
    compileExe_correct compile_eq closedBase base_closed (hooksSim_closed _) hf hc M hX ho hr htr⟩

/-- The output's program headers. -/
def phs : List Elf.Phdr := (Elf.phdrs (Elf.fileRd file0)).getD []

theorem hph : Elf.phdrs (Elf.fileRd file0) = some phs := by native_decide

theorem placeOk : spec.placeOkB = true := by native_decide

theorem rangeB : (tabOf spec.input.resultsT).all (fun e =>
    e.2.fb.relocs.all (relocRangeB spec.input (Elf.tpOff phs) e.2)) = true := by native_decide

theorem regionOk : regionOkB file0 spec.R (regionOf spec (Elf.tpOff phs)).size
    (offsetOf phs spec.R) = true := by native_decide

theorem outsideOk : outsideOkB spec.input spec.data
    (patch file0 (offsetOf phs spec.R) (regionOf spec (Elf.tpOff phs))) = true := by native_decide

theorem names : spec.names = spec.funcs.map (·.func.name) := by native_decide

theorem sizes : spec.sizes = spec.sizesOf := by native_decide

/-- **Non-vacuity of `compileExe_total`**: its hypotheses hold on `a_arith`. -/
theorem total_witness :
    compileExe spec file0 = .ok (patch file0 (offsetOf phs spec.R) (regionOf spec (Elf.tpOff phs))) :=
  compileExe_total (by rw [← LinkSpec.inScope_input]; exact inScope) (by native_decide) placeOk
    names sizes (fun e he r hr => List.all_eq_true.1 (List.all_eq_true.1 rangeB e he) r hr) hph
    regionOk outsideOk

end Crates.CompileExeWitness
