import Crates.InScopeInputs.AArith
import Crates.InScopeInputs.FvDemo
import FV.E2E.SpillDefined

/-! # Non-vacuity of `crate_correct_inScope` (L2a) on survey crates

`E2E.LinkCheck.crate_correct_inScope` (`FV/E2E/LinkScope.lean`) needs of a crate only the input
conditions `InScopeP` and the linker's facts `linkerOkB` (its program-independent hypothesis
`SpillDefinedHyp` is proven: `crate_correct_inScope_proven`, used by `crate_correct_proven`). Both hold
for the survey crate `a_arith` (`Crates.InScopeInputs.AArith.input`, 58
functions) and for `fv-demo` (`Crates.InScopeInputs.FvDemo.input`, 551 functions): decided by
`native_decide` (`fvcheck` holds the compiled code of `FV.E2E.LinkScopeDefs`). The closed
base environment satisfies the
base premises of `a_arith`'s linked system (`base_closedT`), so the theorem is not vacuous in them
either.

The inputs are the 2026-10-04 ones, frozen in `Crates.InScopeInputs` (#709): `linkerOkB` lays out
`LinkInput.resultsT`, which the shipped routed compiler no longer emits; an `inScope` theorem for
the routed compiler is open. -/

namespace Crates.InScopeWitness

open E2E E2E.LinkCheck

/-- The input conditions of `a_arith`. -/
theorem inScope_input : InScopeP Crates.InScopeInputs.AArith.input = true := by native_decide

/-- The linker's facts of `a_arith`'s executable for the compiler's results. -/
theorem linker_input : linkerOkB Crates.InScopeInputs.AArith.input = true := by native_decide

/-- No function of `a_arith` has a `tls_value`. -/
theorem noTls : Crates.InScopeInputs.AArith.input.prog.funcs.all (fun g => !Backend.hasTls g) = true := by
  native_decide

/-- **`backend_correct_program` for every function of `a_arith`**, without `okB`. -/
theorem crate_correct (hD : SpillDefinedHyp) (n : String) : CrateStmtT Crates.InScopeInputs.AArith.input n :=
  crate_correct_inScope hD inScope_input linker_input n

/-- `crate_correct` under definite assignment of `lowerFunction`'s VCode (`LowerDefinedHyp`). -/
theorem crate_correct_lower (hM : LowerDefinedHyp) (n : String) : CrateStmtT Crates.InScopeInputs.AArith.input n :=
  crate_correct_inScope_lower hM inScope_input linker_input n

/-- `crate_correct` under the facts of the ISLE runs (`DefRunsHyp`, which give `LowerDefinedHyp`). -/
theorem crate_correct_runs (hR : Backend.Proof.DefRun.DefRunsHyp) (n : String) :
    CrateStmtT Crates.InScopeInputs.AArith.input n :=
  crate_correct_inScope_runs hR inScope_input linker_input n

/-- **`crate_correct` without open hypotheses** (`crate_correct_inScope_proven`). -/
theorem crate_correct_proven (n : String) : CrateStmtT Crates.InScopeInputs.AArith.input n :=
  crate_correct_inScope_proven inScope_input linker_input n

/-- The closed base environment satisfies the base premises of `a_arith`'s linked system. -/
theorem base_closedT (F : BitVec 64 → Prop) :
    BaseOk (LinkSys.ofInputT Crates.InScopeInputs.AArith.input closedBase F) :=
  baseOk_closedT fun g hg => by simpa using List.all_eq_true.1 noTls g hg

/-- The input conditions of `fv-demo`. -/
theorem inScope_fvDemo : InScopeP Crates.InScopeInputs.FvDemo.input = true := by native_decide

/-- The linker's facts of `fv-demo`'s executable for the compiler's results. -/
theorem linker_fvDemo : linkerOkB Crates.InScopeInputs.FvDemo.input = true := by native_decide

/-- **`backend_correct_program` for every function of `fv-demo`**, without `okB`. -/
theorem crate_correct_fvDemo (hD : SpillDefinedHyp) (n : String) : CrateStmtT Crates.InScopeInputs.FvDemo.input n :=
  crate_correct_inScope hD inScope_fvDemo linker_fvDemo n

/-- `crate_correct_fvDemo` under definite assignment of `lowerFunction`'s VCode. -/
theorem crate_correct_fvDemo_lower (hM : LowerDefinedHyp) (n : String) :
    CrateStmtT Crates.InScopeInputs.FvDemo.input n :=
  crate_correct_inScope_lower hM inScope_fvDemo linker_fvDemo n

/-- `crate_correct_fvDemo` under the facts of the ISLE runs. -/
theorem crate_correct_fvDemo_runs (hR : Backend.Proof.DefRun.DefRunsHyp) (n : String) :
    CrateStmtT Crates.InScopeInputs.FvDemo.input n :=
  crate_correct_inScope_runs hR inScope_fvDemo linker_fvDemo n

/-- **`crate_correct_fvDemo` without open hypotheses**. -/
theorem crate_correct_fvDemo_proven (n : String) : CrateStmtT Crates.InScopeInputs.FvDemo.input n :=
  crate_correct_inScope_proven inScope_fvDemo linker_fvDemo n

end Crates.InScopeWitness
