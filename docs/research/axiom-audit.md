# Axiom audit of the compiler theorems (2026-10-16, `origin/main` = `7d795a6`)

Method: one Lean file importing every module of `FV` (1838 modules) walks the closure of every
constant declared in an `FV.*` module (252,419 constants, 199,192 theorems) through types, values
and constructors, and records the axioms each depends on (the computation `#print axioms` does,
memoised over the whole library). The same walk over the 80 `crate-proofs/Crates` modules covers
the witnesses. Gates run on the same commit are listed in the PR that adds this file.

## Result

* `sorryAx`: in no constant of `FV`.
* No hand-written `axiom` in `FV` (no `axiom` declaration in the sources; the only axioms in the
  environment are the 51 that Lean generates for `bv_decide`/`native_decide` proofs).
* Every theorem listed below (the compiler's correctness and totality theorems, per function and
  per executable, and the frontend theorems) depends on `propext`, `Classical.choice`,
  `Quot.sound` at most.
* Generated `native_decide` axioms (39) occur only in non-vacuity witnesses and in counterexamples
  to earlier statements (`FV/E2E/NonVacuity*.lean`, `*Witness*.lean`, `SpillDefinedFalse.lean`,
  `SpillCtlWitness.lean`, the `*_witness` theorems of `AllocDirect`/`AllocTotal`/`EmitTotal`/
  `EmitTotalIn`/`SizeIn`/`RelaxTotal`/`LowerDirect`/`FinalDirect`/`SpillAvail`/`SpillKillFree`/
  `SpillLocalWitness`, `Opt.Legal.Complete.Witness` in `FV/Opt/Proof/LegalPre.lean`).
* Generated `bv_decide` axioms (12) occur in eight lemmas of the Arm model ported from LNSym
  (`FV/Arm/Insts/Common.lean`: `Aligned_AddWithCarry_64_4`, `Aligned_BitVecAdd_64_4`,
  `Aligned_BitVecSub_64_4`, `sgt_iff_n_eq_v_and_z_eq_0_{32,64}`,
  `sle_iff_not_n_eq_v_and_z_eq_0_{32,64}`; `FV/Arm/Insts/DPSFP/Advanced_simd_copy.lean`:
  `DPSFP.dup_aux_0_4_32`) and in `CheckSPAlignment_AddWithCarry_64_4`, which uses one of them.
  No other constant of `FV` depends on them, so no compiler theorem does.
* `crate-proofs`: the witnesses (`Crates.*Witness*`, `Crates.FvDemo*`) and the generated per-crate
  files use `native_decide` (by design: they evaluate a concrete program); none of the theorems
  below depends on them.

## The theorems

"standard": `propext`, `Classical.choice`, `Quot.sound`.

### Frontend bundle → `LinkSpec`, and the source theorems (`FV/Front`)

| Theorem | Module | Axioms |
| --- | --- | --- |
| `Front.buildSpec_spec` | `FV.Front.BundleProof` | standard |
| `Front.buildSpec_srcProg` | `FV.Front.BundleProof` | standard |
| `Front.data_complete` | `FV.Front.BundleProof` | standard |
| `Front.link_alpha` | `FV.Front.BundleProof` | standard |
| `Front.parseUnit_raw` | `FV.Front.BundleProof` | standard |
| `Front.bundle_correct_source` | `FV.Front.Exe` | standard |
| `Front.bundle_correct_source_baseline` | `FV.Front.Exe` | standard |
| `Front.bundle_correct_source_peak` | `FV.Front.Exe` | standard |
| `Front.bundle_correct_source_peak_baseline` | `FV.Front.Exe` | standard |
| `Front.decodeFn_spec` | `FV.Front.Raw` | standard |
| `Front.bundle_correct_raw` | `FV.Front.RawExe` | standard |
| `Front.bundle_correct_raw_baseline` | `FV.Front.RawExe` | standard |
| `Front.bundle_correct_raw_peak` | `FV.Front.RawExe` | standard |
| `Front.bundle_correct_raw_peak_baseline` | `FV.Front.RawExe` | standard |
| `Front.rawLink_eq_link` | `FV.Front.RawProof` | standard |
| `Clif.runLoop_ren` | `FV.Front.RenameRun` | standard |

### Executable compiler (`FV/Link`)

| Theorem | Module | Axioms |
| --- | --- | --- |
| `Link.binOk_leanLink` | `FV.Link.Correct` | standard |
| `Link.DeadCleanup.binOk_leanLink` | `FV.Link.DeadCleanupCorrect` | standard |
| `Link.DeadCleanup.compileExe_correct` | `FV.Link.DeadCleanupExe` | standard |
| `Link.DeadCleanup.compileExe_correct_peak` | `FV.Link.DeadCleanupExePeak` | standard |
| `Link.DeadCleanup.compileExe_correct_source` | `FV.Link.DeadCleanupExeSource` | standard |
| `Link.DeadCleanup.compileExe_correct_source_peak` | `FV.Link.DeadCleanupExeSource` | standard |
| `Link.DeadCleanup.compileExe_total` | `FV.Link.DeadCleanupExeTotal` | standard |
| `Link.DeadCleanup.leanLink_linkerOk` | `FV.Link.DeadCleanupLayoutProof` | standard |
| `Link.compileExe_correct` | `FV.Link.Exe` | standard |
| `Link.compileExe_correct_depth` | `FV.Link.Exe` | standard |
| `Link.compileExe_correct_peak` | `FV.Link.Exe` | standard |
| `Link.compileExe_total_input` | `FV.Link.ExeInput` | standard |
| `Link.DeadCleanup.compileExe_total_input` | `FV.Link.ExeInputCleanup` | standard |
| `Link.compileExe_total_reach` | `FV.Link.ExeInputReach` | standard |
| `Link.relocOk_tab` | `FV.Link.ExeInputReach` | standard |
| `Link.DeadCleanup.compileExe_total_reach` | `FV.Link.ExeInputReachCleanup` | standard |
| `Link.DeadCleanup.relocOk_tab` | `FV.Link.ExeInputReachCleanup` | standard |
| `Link.compileExe_correct_source` | `FV.Link.ExeSource` | standard |
| `Link.compileExe_correct_source_peak` | `FV.Link.ExeSource` | standard |
| `Link.compileExe_total` | `FV.Link.ExeTotal` | standard |
| `Link.leanLink_linkerOk` | `FV.Link.LayoutProof` | standard |

### Per function, linking, executable bytes (`FV/E2E`)

| Theorem | Module | Axioms |
| --- | --- | --- |
| `E2E.backend_correct_final_alloc` | `FV.E2E.AllocDirect` | standard |
| `E2E.backend_correct_final_total` | `FV.E2E.AllocTotal` | standard |
| `E2E.lowerRFunc_spillAlloc` | `FV.E2E.AllocTotal` | standard |
| `E2E.backend_correct_program_stackX` | `FV.E2E.BinaryGood` | standard |
| `E2E.DeadCleanupExecBytes.binary_correct_exec` | `FV.E2E.DeadCleanupExecBytes` | standard |
| `E2E.DeadCleanupExecBytes.binary_correct_exec_of_good` | `FV.E2E.DeadCleanupExecBytes` | standard |
| `E2E.DeadCleanupExecBytes.binary_correct_exec_of_got` | `FV.E2E.DeadCleanupExecGoodReads` | standard |
| `E2E.DeadCleanupExecBytes.binary_correct_exec_of_reads` | `FV.E2E.DeadCleanupExecGoodRun` | standard |
| `E2E.DeadCleanupExecBytes.binary_correct_exec_of_insn` | `FV.E2E.DeadCleanupExecGot` | standard |
| `E2E.DeadCleanupExecBytes.binary_correct_exec_peak_proven` | `FV.E2E.DeadCleanupExecPeak` | standard |
| `E2E.DeadCleanupExecBytes.binary_correct_exec_proven` | `FV.E2E.DeadCleanupExecProven` | standard |
| `E2E.DeadCleanupExecBytes.binary_correct_exec_staticN` | `FV.E2E.DeadCleanupExecRunN` | standard |
| `E2E.DeadCleanupExecBytes.binary_correct_exec_static` | `FV.E2E.DeadCleanupExecStatic` | standard |
| `E2E.backend_correct_final_cleanup` | `FV.E2E.DeadCleanupFinal` | standard |
| `E2E.backend_correct_final_cleanup_ex` | `FV.E2E.DeadCleanupFinal` | standard |
| `E2E.backend_correct_legal_callFree_cleanup` | `FV.E2E.DeadCleanupLegal` | standard |
| `E2E.backend_correct_legal_cleanup` | `FV.E2E.DeadCleanupLegal` | standard |
| `E2E.backend_correct_legal_env_cleanup` | `FV.E2E.DeadCleanupLegal` | standard |
| `E2E.backend_correct_legal_direct_cleanup` | `FV.E2E.DeadCleanupLegalDirect` | standard |
| `E2E.backend_correct_opt_proven_cleanup` | `FV.E2E.DeadCleanupOptProven` | standard |
| `E2E.backend_correct_final_cleanup_total_emit_input` | `FV.E2E.DeadCleanupSize` | standard |
| `E2E.DeadCleanupStackBound.goodN_iff` | `FV.E2E.DeadCleanupStackBound` | standard |
| `E2E.DeadCleanupStackBound.stackB_isSome_iff` | `FV.E2E.DeadCleanupStackBound` | standard |
| `E2E.backend_correct_final_cleanup_total` | `FV.E2E.DeadCleanupTotal` | standard |
| `E2E.backend_correct_final_cleanup_total_emit` | `FV.E2E.DeadCleanupTotal` | standard |
| `E2E.backend_correct_final_cleanup_total_emit_in` | `FV.E2E.DeadCleanupTotal` | standard |
| `E2E.backend_correct_final_cleanup_total_ready` | `FV.E2E.DeadCleanupTotal` | standard |
| `E2E.backend_correct_final_total_emit` | `FV.E2E.EmitTotal` | standard |
| `E2E.backend_correct_final_total_ready` | `FV.E2E.EmitTotal` | standard |
| `E2E.emitReady_spill` | `FV.E2E.EmitTotal` | standard |
| `E2E.backend_correct_final_total_emit_in` | `FV.E2E.EmitTotalIn` | standard |
| `E2E.ExecBytes.binary_correct_exec` | `FV.E2E.ExecBytes` | standard |
| `E2E.ExecBytes.binary_correct_exec_of_good` | `FV.E2E.ExecBytes` | standard |
| `E2E.ExecBytes.binary_correct_exec_of_got` | `FV.E2E.ExecGoodReads` | standard |
| `E2E.ExecBytes.binary_correct_exec_of_reads` | `FV.E2E.ExecGoodRun` | standard |
| `E2E.ExecBytes.binary_correct_exec_of_insn` | `FV.E2E.ExecGot` | standard |
| `E2E.ExecBytes.binary_correct_exec_depth_proven` | `FV.E2E.ExecProven` | standard |
| `E2E.ExecBytes.binary_correct_exec_peak_proven` | `FV.E2E.ExecProven` | standard |
| `E2E.ExecBytes.binary_correct_exec_proven` | `FV.E2E.ExecProven` | standard |
| `E2E.ExecBytes.binary_correct_exec_staticN` | `FV.E2E.ExecRunN` | standard |
| `E2E.ExecBytes.binary_correct_exec_static` | `FV.E2E.ExecStatic` | standard |
| `E2E.backend_correct_final` | `FV.E2E.Final` | standard |
| `E2E.backend_correct_final_ex` | `FV.E2E.Final` | standard |
| `E2E.backend_correct_final_indirectFree` | `FV.E2E.Final` | standard |
| `E2E.backend_correct_final_of_lower` | `FV.E2E.FinalDirect` | standard |
| `E2E.backend_correct_final_of_lower_ex` | `FV.E2E.FinalDirect` | standard |
| `E2E.backend_correct_legal` | `FV.E2E.Legal` | standard |
| `E2E.backend_correct_legal_callFree` | `FV.E2E.Legal` | standard |
| `E2E.backend_correct_legal_env` | `FV.E2E.Legal` | standard |
| `E2E.LegalProgram.legalProg_refines_depth` | `FV.E2E.LegalDepth` | standard |
| `E2E.backend_correct_legal_direct` | `FV.E2E.LegalDirect` | standard |
| `E2E.LegalProgram.legalProg_refines` | `FV.E2E.LegalProgram` | standard |
| `E2E.backend_correct_program` | `FV.E2E.LinkArm` | standard |
| `E2E.backend_correct_program_budget` | `FV.E2E.LinkArm` | standard |
| `E2E.backend_correct_program_core` | `FV.E2E.LinkArm` | standard |
| `E2E.backend_correct_program_peak` | `FV.E2E.LinkArm` | standard |
| `E2E.backend_correct_program_returned` | `FV.E2E.LinkArm` | standard |
| `E2E.backend_correct_program_returned_budget` | `FV.E2E.LinkArm` | standard |
| `E2E.backend_correct_program_budgetX` | `FV.E2E.LinkGood` | standard |
| `E2E.backend_correct_program_coreX` | `FV.E2E.LinkGood` | standard |
| `E2E.backend_correct_program_peakX` | `FV.E2E.LinkGood` | standard |
| `E2E.backend_correct_final_id` | `FV.E2E.NonVacuity` | standard |
| `E2E.backend_correct_opt_proven` | `FV.E2E.OptProven` | standard |
| `E2E.backend_correct_final_total_relaxed` | `FV.E2E.RelaxTotal` | standard |
| `E2E.backend_correct_final_total_emit_input` | `FV.E2E.SizeIn` | standard |
| `E2E.LinkCheck.crate_correct_inScope_proven` | `FV.E2E.SpillDefined` | standard |
| `E2E.backend_correct_final_alloc_proven` | `FV.E2E.SpillKillFree` | standard |
| `E2E.spillAccepted` | `FV.E2E.SpillKillFree` | standard |
| `E2E.StackBound.budOkW_budMap` | `FV.E2E.StackBound` | standard |
| `E2E.StackBound.goodN_iff` | `FV.E2E.StackBound` | standard |
| `E2E.StackBound.stackB_isSome_iff` | `FV.E2E.StackBound` | standard |
| `E2E.backend_correct_program_stack` | `FV.E2E.StackBound` | standard |

### Backend passes (`FV/Backend`)

| Theorem | Module | Axioms |
| --- | --- | --- |
| `Backend.Insn.decode_encode` | `FV.Backend.Proof.Encode` | standard |
| `Backend.Proof.Driver.formsCovered_complete` | `FV.Backend.Proof.FormsCoverComplete` | standard |
| `Backend.Proof.Driver.lowerCheck_complete` | `FV.Backend.Proof.LowerComplete` | standard |
| `Backend.Proof.Driver.prepDomain_of_lower` | `FV.Backend.Proof.LowerLoop` | standard |
| `Backend.Proof.Prep.prepCheck_complete` | `FV.Backend.Proof.PrepareComplete` | standard |
| `Backend.Proof.Prep.prepare_correct` | `FV.Backend.Proof.PrepareDirect` | standard |

### Mid-end and `i128` legalisation (`FV/Opt`)

| Theorem | Module | Axioms |
| --- | --- | --- |
| `Opt.Legal.Complete.check_complete_of_preB` | `FV.Opt.Proof.LegalPre` | standard |
| `Opt.Legal.Complete.preB_iff` | `FV.Opt.Proof.LegalPre` | standard |
| `Opt.Proof.simplifyRulesCorrect_proven` | `FV.Opt.Proof.RuleAll` | standard |
| `Opt.optimize_sim_proven` | `FV.Opt.Proof.SimpPass` | standard |

### Their non-vacuity witnesses in `FV`

| Theorem | Module | Axioms |
| --- | --- | --- |
| `E2E.backend_correct_final_alloc_witness` | `FV.E2E.AllocDirect` | standard + 3 generated `native_decide` |
| `E2E.backend_correct_final_total_witness` | `FV.E2E.AllocTotal` | standard + 3 generated `native_decide` |
| `E2E.backend_correct_final_total_emit_witness` | `FV.E2E.EmitTotal` | standard + 4 generated `native_decide` |
| `E2E.backend_correct_final_total_emit_in_witness` | `FV.E2E.EmitTotalIn` | standard + 5 generated `native_decide` |
| `E2E.backend_correct_final_try_witness` | `FV.E2E.NonVacuity` | standard |
| `E2E.backend_correct_final_witness` | `FV.E2E.NonVacuity` | standard |
| `E2E.LinkWitness.backend_correct_program_witness` | `FV.E2E.NonVacuityLink` | standard + 11 generated `native_decide` |
| `E2E.backend_correct_final_total_relaxed_witness` | `FV.E2E.RelaxTotal` | standard + 3 generated `native_decide` |
| `E2E.backend_correct_final_total_emit_input_witness` | `FV.E2E.SizeIn` | standard + 6 generated `native_decide` |
| `E2E.backend_correct_final_alloc_proven_witness` | `FV.E2E.SpillKillFree` | standard + 4 generated `native_decide` |
| `Link.DeadCleanup.SourceWitness.compileExe_correct_source_helper` | `FV.Link.NonVacuityDeadCleanupExeSource` | standard |
| `Link.DeadCleanup.SourceWitness.compileExe_correct_source_peak_helper` | `FV.Link.NonVacuityDeadCleanupExeSource` | standard |
| `Link.SourceWitness.compileExe_correct_source_helper` | `FV.Link.NonVacuityExeSource` | standard |
| `Link.SourceWitness.compileExe_correct_source_peak_helper` | `FV.Link.NonVacuityExeSource` | standard |
