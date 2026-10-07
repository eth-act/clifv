import Crates.AArith.Input
import Crates.FvDemo.Input
import FV.E2E.SpillDefined

/-! # Non-vacuity of `crate_correct_inScope` (L2a) on survey crates

`E2E.LinkCheck.crate_correct_inScope` (`FV/E2E/LinkScope.lean`) needs of a crate only the input
conditions `InScopeP` and the linker's facts `linkerOkB` (besides the program-independent open
fact `SpillDefinedHyp`, which follows from `LowerDefinedHyp`: `crate_correct_lower`). Both hold
for the survey crate `a_arith` (`Crates.AArith.input`, 58
functions) and for `fv-demo` (`Crates.FvDemo.input`, 551 functions): decided by
`native_decide` (`fvcheck` holds the compiled code of `FV.E2E.LinkScopeDefs`). The closed
base environment satisfies the
base premises of `a_arith`'s linked system (`base_closedT`), so the theorem is not vacuous in them
either. -/

namespace Crates.InScopeWitness

open E2E E2E.LinkCheck

/-- The input conditions of `a_arith`. -/
theorem inScope_input : InScopeP Crates.AArith.input = true := by native_decide

/-- The linker's facts of `a_arith`'s executable for the compiler's results. -/
theorem linker_input : linkerOkB Crates.AArith.input = true := by native_decide

/-- No function of `a_arith` has a `tls_value`. -/
theorem noTls : Crates.AArith.input.prog.funcs.all (fun g => !Backend.hasTls g) = true := by
  native_decide

/-- **`backend_correct_program` for every function of `a_arith`**, without `okB`. -/
theorem crate_correct (hD : SpillDefinedHyp) (n : String) : CrateStmtT Crates.AArith.input n :=
  crate_correct_inScope hD inScope_input linker_input n

/-- The entry blocks of `a_arith`'s functions have their signatures' parameters. -/
theorem entryParams_input :
    Crates.AArith.input.prog.funcs.all Backend.Proof.Spill.entryParamsB = true := by
  native_decide

/-- `crate_correct` under `SpillDefinedHypE` (`SpillDefinedHyp` is false:
`E2E.not_spillDefinedHyp`). -/
theorem crate_correctE (hD : SpillDefinedHypE) (n : String) : CrateStmtT Crates.AArith.input n :=
  crate_correct_inScopeE hD inScope_input entryParams_input linker_input n

/-- `crate_correct` under definite assignment of `lowerFunction`'s VCode (`LowerDefinedHyp`). -/
theorem crate_correct_lower (hM : LowerDefinedHyp) (n : String) : CrateStmtT Crates.AArith.input n :=
  crate_correct_inScope_lower hM inScope_input entryParams_input linker_input n

/-- The closed base environment satisfies the base premises of `a_arith`'s linked system. -/
theorem base_closedT (F : BitVec 64 → Prop) :
    BaseOk (LinkSys.ofInputT Crates.AArith.input closedBase F) :=
  baseOk_closedT fun g hg => by simpa using List.all_eq_true.1 noTls g hg

/-- The input conditions of `fv-demo`. -/
theorem inScope_fvDemo : InScopeP Crates.FvDemo.input = true := by native_decide

/-- The linker's facts of `fv-demo`'s executable for the compiler's results. -/
theorem linker_fvDemo : linkerOkB Crates.FvDemo.input = true := by native_decide

/-- **`backend_correct_program` for every function of `fv-demo`**, without `okB`. -/
theorem crate_correct_fvDemo (hD : SpillDefinedHyp) (n : String) : CrateStmtT Crates.FvDemo.input n :=
  crate_correct_inScope hD inScope_fvDemo linker_fvDemo n

/-- The entry blocks of `fv-demo`'s functions have their signatures' parameters. -/
theorem entryParams_fvDemo :
    Crates.FvDemo.input.prog.funcs.all Backend.Proof.Spill.entryParamsB = true := by
  native_decide

/-- `crate_correct_fvDemo` under `SpillDefinedHypE`. -/
theorem crate_correct_fvDemoE (hD : SpillDefinedHypE) (n : String) :
    CrateStmtT Crates.FvDemo.input n :=
  crate_correct_inScopeE hD inScope_fvDemo entryParams_fvDemo linker_fvDemo n

/-- `crate_correct_fvDemo` under definite assignment of `lowerFunction`'s VCode. -/
theorem crate_correct_fvDemo_lower (hM : LowerDefinedHyp) (n : String) :
    CrateStmtT Crates.FvDemo.input n :=
  crate_correct_inScope_lower hM inScope_fvDemo entryParams_fvDemo linker_fvDemo n

end Crates.InScopeWitness
