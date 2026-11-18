import FV.Link.CpSource
import FV.Link.ReturnPinExeSourceCp
import FV.Link.SemanticExeSourceCp
import FV.Link.TypedCompileSourceCp
import FV.Link.DeadCleanupExeSourceCp
import FV.Link.ExeSourceCp
import FV.Link.DeadCleanupExeSourceTCp
import FV.Link.OptExeSourceCp
import FV.Link.DeadCleanupOptExeSourceCp
import FV.Link.CpSourceWitness
import FV.Link.SemanticExeSourceTCp
import FV.Link.CpSourceTWitness
import FV.Front.ExeTCp

-- #1052: the source theorems about the bundle's program, through the `i128` legalisation and
-- constant-phi removal (`lean-link --verified` names them on every route; on `attemptT` since #1100)
#print axioms E2E.LinkCheck.LinkInput.cpRel
#print axioms Link.srcCtx_cp
#print axioms Link.cpSource
#print axioms Link.cpSource_depth
#print axioms Link.ReturnPinCompilerWith.attempt_correct_sourceCp
#print axioms Link.ReturnPinCompilerWith.attempt_correct_source_peakCp
#print axioms Link.SemanticCompilerWith.attempt_correct_sourceCp
#print axioms Link.SemanticCompilerWith.attempt_correct_source_peakCp
#print axioms Link.TypedCompilerWith.attempt_correct_sourceCp
#print axioms Link.TypedCompilerWith.attempt_correct_source_peakCp
#print axioms Link.DeadCleanup.compileExe_correct_sourceCp
#print axioms Link.DeadCleanup.compileExe_correct_source_peakCp
#print axioms Link.compileExe_correct_sourceCp
#print axioms Link.compileExe_correct_source_peakCp
#print axioms Link.DeadCleanup.compileExe_correct_source_okTCp
#print axioms Link.DeadCleanup.compileExe_correct_source_peak_okTCp
#print axioms Link.DeadCleanup.compileExeT_correct_sourceCp
#print axioms Link.DeadCleanup.compileExeT_correct_source_peakCp
#print axioms Link.compileExeOpt_correct_sourceCp
#print axioms Link.compileExeOpt_correct_source_peakCp
#print axioms Link.DeadCleanup.compileExeOpt_correct_sourceCp
#print axioms Link.DeadCleanup.compileExeOpt_correct_source_peakCp
#print axioms Link.CpSourceWitness.checks_true -- witness: native_decide
#print axioms Link.CpSourceWitness.hcp
#print axioms Link.CpSourceWitness.parts -- witness: native_decide
#print axioms Link.CpSourceWitness.correct_sourceCp_applies -- witness: native_decide
#print axioms Link.SemanticCompilerWith.attemptT_correct_sourceCp
#print axioms Link.SemanticCompilerWith.attemptT_correct_source_peakCp
#print axioms Link.CpSourceTWitness.checks_true -- witness: native_decide
#print axioms Link.CpSourceTWitness.hcp
#print axioms Link.CpSourceTWitness.parts -- witness: native_decide
#print axioms Link.CpSourceTWitness.correct_sourceCp_applies -- witness: native_decide

-- #1088: the typed frontend theorems through constant-phi removal (lean-link names them on the
-- compileExeT route; witnesses: Crates.FrontendBundleWitnessTCp, unchanged functions, and
-- Crates.FrontendBundleWitnessTCpChanged, a function constant-phi removal changes, in crate-proofs/)
#print axioms Front.placedFrom_cp_funcs
#print axioms Front.bundle_correct_sourceTCp
#print axioms Front.bundle_correct_source_peakTCp
#print axioms Front.bundle_correct_rawTCp
#print axioms Front.bundle_correct_raw_peakTCp
