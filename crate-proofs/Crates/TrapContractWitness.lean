import FV.Link.DeadCleanupExeTrapContract
import FV.Link.DeadCleanupExeTrapWitness

/-! # Non-vacuity of the trap-contract theorems (A5, #411)

The program, executable and run of `Link.DeadCleanup.TrapWitness` (`f` calling the function `h`
of the program, whose division by zero traps; the shipped compiler with the unwind tables
checked). No run of the `g_u128` unit traps, so the trap-contract family is witnessed on this
program; the runtime-contract part is the same structure as the `g_u128` witness's
(`Crates.FrontendBundleWitnessContract`).

* **`trap_contract_traps`**: `Link.DeadCleanup.compileExe_correct_trap_contract` instantiated:
  for every machine state `r` meeting the trap contract (`Link.DeadCleanup.TrapContract`: the
  outside code's contracts, the program's no-`try_call` fact, the loader's and the caller's) and
  the CLIF view of the entry, the run of the written executable `file` from `r` reaches a state
  at a trap with `int_divz` (`TrapAtE`).
-/

namespace Crates.TrapContractWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes E2E.EntryContract Backend
  Opt.Legalize128
open Link.DeadCleanup.TrapWitness

/-- **Per-run non-vacuity of `Link.DeadCleanup.compileExe_correct_trap_contract`**: as
`Link.DeadCleanup.TrapWitness.exec_traps`, with the trap contract `TrapContract` and the CLIF
view `hv` in place of the entry premises (`Image.Intact`, `OutsideCall`, `ClifRun`). -/
theorem trap_contract_traps {r : Arm.ArmState}
    (hl : Loader file (DeadCleanupStackBound.stackFn spec.inputCleanup fF) r)
    (hcl : Caller spec.inputCleanup file fF r [v41, v0])
    (hv : ClifView spec.inputCleanup closedBase fF
      (DeadCleanupStackBound.stackFn spec.inputCleanup fF) r [v41, v0] cs0) :
    ∃ k, TrapAtE spec.inputCleanup closedBase .intDivz
      (runX (step spec.inputCleanup closedBase file) k r) := by
  have hC : Link.DeadCleanup.TrapContract spec closedBase file fF
      (DeadCleanupStackBound.stackFn spec.inputCleanup fF) r [v41, v0] :=
    { base := baseOk, hooks := hooksSim_closed _, traps := baseTrapsOk,
      noTry := fun g hg => (funcs_facts g hg).2, loader := hl, caller := hcl }
  have := Link.DeadCleanup.compileExe_correct_trap_contract compile_eq closedBase hf hc 9 hC hv
    cs0_trapsD
  rw [run_traps] at this
  exact this

end Crates.TrapContractWitness
