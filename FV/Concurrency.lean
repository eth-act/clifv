/-
Root of the memory-model layer (T2, #38; `docs/plans/atomics.md`): execution graphs, the Armv8
axiomatic model restricted to the instructions Cranelift emits, the Cranelift contract for CLIF
atomics, the soundness of Cranelift's mapping (`Mapping.armv8_to_clif`), DRF-SC
(`ClifMM.drf_sc`, `Mapping.armv8_drf_sc`), SC executions as interleavings
(`Mapping.armv8_interleaving`), the mapping table of the emitted code (`Code.lines_kinds`), and
the per-thread event semantics of the Arm model with an exclusive monitor and failing store
exclusives (`ArmThread.TStep`; the single-core model as its special case, `ArmThread.run_sc_stepi`),
Rust/C++20 orderings (RC11) and the soundness of cg_clif's strengthening
(`RC11.strength_sound`) with Cranelift's SC fences on Armv8 (`Mapping.armv8_to_clifF`), and the
program level: the multi-threaded `Clif.run` (`ClifThread.MTRun`), replay of SC executions
(`Prog.replay`) and `ProgE2E.program_correct` under the per-thread contract `ProgE2E.Realizes`,
with race-freedom over the executions with fences (`ProgE2E.program_correctF`) or of the Rust
program (`ProgE2E.program_correct_rust`); `Realizes` follows from per-thread refinements with
interference (`ThreadRefine.realizes_of_threads`), the obligation of the backend layers (T2h);
its first layer: precise footprints of every Arm instruction (`ArmInstFoot.footprint_exec_inst`)
and of VCode under `csem` (`VCodeThread.ifoot_csem`), the VCode thread semantics
(`VCodeThread.VTStep`) and its event kinds (`VCodeEvents.cEvs_kinds`); precise Arm labels
(`ArmPrecise.ATStepP`), private coherence from Armv8 coherence with per-thread private sets
(`PrivCoh.privCoh_of_consistent`, `PrivCoh.realizes_of_threads_priv`), `prepare` and register
allocation with interference (`PrepThread.prep_refines_csem`, `AllocThread.alloc_refines`),
per-statement frame sets (`FrameMono.vtrun_mono`), and the run level of the Arm machine against
the allocated code (`ArmAllocThread.refines_of_itemSim`: per-item obligations give `Refines`
with the Arm trace's monitor pairs; discharged for the functions without memory instructions,
`ArmAllocThread.arm_alloc_refines_noev`; with `fence`, `ldar`, `stlr`:
`ArmAllocThread.arm_alloc_refines_mem`; with the allocation's moves, under the run condition
`ArmAllocThread.OkPriv`: `ArmAllocThread.arm_alloc_refines_mv`), and `Realizes` for the threads
of compiled code (`RealizeCompiled.realizes_compiled`; on the compiled `atomic_load` through its
`ldar`: `RealizeCompiled.WitnessL.realizes_load`; on the compiled `atomic_store` through its
`stlr`: `RealizeCompiled.WitnessS.realizes_store`; for both as two threads passing a message
through location 0: `RealizeCompiled.WitnessMP.realizes_mp`, `RealizeCompiled.WitnessMP.mp_reads`); calls by the linking induction
(`CallCompose.link_compose`: the callee's events through its own refinement, composed along the
call; external callees under the trusted event contract `CallCompose.ExtEvContract`).
Layer 4b from the ABI entry, through the prologue: `ArmAllocThread.arm_alloc_refines_entry`.
A compiled callee's contract in a linked thread: `CallThread.funReal_callee` (from
`CallThread.thread_compiled_entry`, lifted under the caller's frames by `ClifLift.crun_pushC`);
callees with LL/SC loops entered with the open monitor: `CallSeg.funReal_calleeX`. A compiled
caller calling the compiled `atomic_load`, as a thread: `CallSeg.WitnessC.funReal_call`,
`CallSeg.WitnessC.realizes_call`; its whole run through the callee's return and its own
(`CallSeg.resumeQ`): `CallSeg.WitnessC.funReal_callFull`, `CallSeg.WitnessC.realizes_call_full`.
A compiled caller of the compiled `atomic_rmw` (entered with the open monitor,
`CallSeg.prun_privF_mon`): `CallSeg.WitnessCR.funReal_call`, `CallSeg.WitnessCR.realizes_call`.
Layer 4b of a caller pausing at its calls and its return, at related configurations:
`ArmAllocThread.arm_alloc_refines_lsC` (`refines_of_itemSimQ`, `itemSim_lsC`).
The realized prefix covers the whole run: it is the whole Arm run or ends where the CLIF thread
stops (`ThreadProgress.arm_isel_refines_full`, `RealizeCompiled.realizes_compiledLS_full`).
The fragment model is weaker than the whole `aarch64.cat` (`Armv8Full.consistent_frag`); LSE
atomics map by the same table (`Lse.lse_maps`). Nothing here changes the Arm model of `FV/Arm`.
-/
import FV.Concurrency.Rel
import FV.Concurrency.Exec
import FV.Concurrency.Armv8
import FV.Concurrency.ClifMM
import FV.Concurrency.Mapping
import FV.Concurrency.Interleave
import FV.Concurrency.Code
import FV.Concurrency.Witness
import FV.Concurrency.ArmFootprint
import FV.Concurrency.ArmThread
import FV.Concurrency.ArmThreadWitness
import FV.Concurrency.Program
import FV.Concurrency.Replay
import FV.Concurrency.ClifThread
import FV.Concurrency.ProgramE2E
import FV.Concurrency.ProgramWitness
import FV.Concurrency.RC11
import FV.Concurrency.ArmFence
import FV.Concurrency.RC11Witness
import FV.Concurrency.ProgramE2EF
import FV.Concurrency.ProgramFWitness
import FV.Concurrency.Armv8Full
import FV.Concurrency.Lse
import FV.Concurrency.ThreadRefine
import FV.Concurrency.ThreadRefineWitness
import FV.Concurrency.ArmInstFoot
import FV.Concurrency.VCodeThread
import FV.Concurrency.VCodeThreadWitness
import FV.Concurrency.VCodeEvents
import FV.Concurrency.ArmPrecise
import FV.Concurrency.PrivCoh
import FV.Concurrency.PrepThread
import FV.Concurrency.AllocThread
import FV.Concurrency.FrameMono
import FV.Concurrency.ThreadLayerWitness
import FV.Concurrency.VCodeAddr
import FV.Concurrency.VCodeAddrAtomic
import FV.Concurrency.VCodeFrame
import FV.Concurrency.VCodeFrameWitness
import FV.Concurrency.ArmAllocThread
import FV.Concurrency.ArmAllocThreadWitness
import FV.Concurrency.ArmAllocSeg
import FV.Concurrency.ArmAllocSegWitness
import FV.Concurrency.ArmAllocLines
import FV.Concurrency.ArmAllocItem
import FV.Concurrency.ArmAllocStraight
import FV.Concurrency.ArmAllocWitness
import FV.Concurrency.SiteAtAnyWitness
import FV.Concurrency.ArmAllocMem
import FV.Concurrency.ArmAllocMemWitness
import FV.Concurrency.ArmAllocMemLS
import FV.Concurrency.SegRun
import FV.Concurrency.IselVary
import FV.Concurrency.IselFoot
import FV.Concurrency.IselClif
import FV.Concurrency.IselClifWitness
import FV.Concurrency.SegShape
import FV.Concurrency.SegShapeWitness
import FV.Concurrency.ClifCStep
import FV.Concurrency.ClifCStepWitness
import FV.Concurrency.IselCover
import FV.Concurrency.IselCoverWitness
import FV.Concurrency.VCodeSize
import FV.Concurrency.VCodeSizeWitness
import FV.Concurrency.SegFoot
import FV.Concurrency.SegFootWitness
import FV.Concurrency.IselStep
import FV.Concurrency.IselSeg
import FV.Concurrency.IselCheck
import FV.Concurrency.CorrRefine
import FV.Concurrency.ClifCStepTerm
import FV.Concurrency.IselThread
import FV.Concurrency.IselMem
import FV.Concurrency.IselMemAux
import FV.Concurrency.IselMemAuxWitness
import FV.Concurrency.CEvsInv
import FV.Concurrency.CEvsInvWitness
import FV.Concurrency.IselVar
import FV.Concurrency.IselMemSeg
import FV.Concurrency.IselMemHelp
import FV.Concurrency.IselThreadWitnessData
import FV.Concurrency.IselMemLower
import FV.Concurrency.IselMemMain
import FV.Concurrency.IselRefines
import FV.Concurrency.IselEntry
import FV.Concurrency.IselRefinesWitness
import FV.Concurrency.ThreadCompose
import FV.Concurrency.ThreadComposeWitness
import FV.Concurrency.ThreadProgress
import FV.Concurrency.MoveEvs
import FV.Concurrency.ArmAllocMove
import FV.Concurrency.RealizeCompiled
import FV.Concurrency.RealizeWitness
import FV.Concurrency.ArmAllocFwd
import FV.Concurrency.RealizeWitnessFence
import FV.Concurrency.RealizeExec
import FV.Concurrency.ArmLoopRun
import FV.Concurrency.ArmLoopSpec
import FV.Concurrency.ArmAllocLoop
import FV.Concurrency.ArmAllocLoopMem
import FV.Concurrency.ArmAllocLoopWitness
import FV.Concurrency.ArmAllocLoopFwd
import FV.Concurrency.RealizeWitnessLoad
import FV.Concurrency.ArmAllocBranch
import FV.Concurrency.ArmAllocBranchWitness
import FV.Concurrency.ArmAllocLS
import FV.Concurrency.ArmAllocLSWitness
import FV.Concurrency.ArmAllocLSX
import FV.Concurrency.ArmAllocLSXWitness
import FV.Concurrency.RealizeCompiledLSX
import FV.Concurrency.RealizeWitnessStore
import FV.Concurrency.RealizeWitnessMP
import FV.Concurrency.RealizeWitnessRmw
import FV.Concurrency.RealizeWitnessCas
import FV.Concurrency.CallCompose
import FV.Concurrency.CallComposeWitness
import FV.Concurrency.ArmAllocEntry
import FV.Concurrency.ArmAllocEntryWitness
import FV.Concurrency.ArmProgram
import FV.Concurrency.ClifLift
import FV.Concurrency.CallThread
import FV.Concurrency.CallThreadWitness
import FV.Concurrency.CallSeg
import FV.Concurrency.CallXClosedWitness
import FV.Concurrency.CallLoadData
import FV.Concurrency.CallLoadWitness
import FV.Concurrency.RealizeWitnessCasFull
import FV.Concurrency.CallResume
import FV.Concurrency.CallLoadFull
import FV.Concurrency.CallLLSCEntry
import FV.Concurrency.CallLoadResume
import FV.Concurrency.CallRmwData
import FV.Concurrency.CallRmwWitness
import FV.Concurrency.ArmAllocPause
import FV.Concurrency.ArmAllocPauseWitness
import FV.Concurrency.ArmAllocLinked
import FV.Concurrency.ArmAllocLinkedWitness
import FV.Concurrency.IselDriverT
import FV.Concurrency.IselCall
import FV.Concurrency.IselCallWitness
import FV.Concurrency.IselResume
import FV.Concurrency.CallResumeQ
import FV.Concurrency.CallResumeLayers
import FV.Concurrency.CallLayers
import FV.Concurrency.CallResumeWitness
import FV.Concurrency.IselRetT
import FV.Concurrency.IselCallRet
import FV.Concurrency.CallEntryWitness
import FV.Concurrency.CallRets
import FV.Concurrency.CallRetsAlloc
import FV.Concurrency.CallRetsEnd
import FV.Concurrency.CallRetsWitness
import FV.Concurrency.CallPopWitness
import FV.Concurrency.FrameDisj
import FV.Concurrency.FrameDisjWitness
import FV.Concurrency.ClifThreadI
import FV.Concurrency.ClifThreadIWitness
import FV.Concurrency.PrivCohT
import FV.Concurrency.PrivCohTWitness
import FV.Concurrency.CallComposeT
import FV.Concurrency.CallComposeTWitness
import FV.Concurrency.CallRetResume
import FV.Concurrency.CallRetResumeWitness
import FV.Concurrency.CallRetPremises
import FV.Concurrency.CallRetPremisesWitness
import FV.Concurrency.CallRetsN
import FV.Concurrency.CallRetsNWitness
import FV.Concurrency.CallEntryPremises
import FV.Concurrency.CallEntryPremisesWitness
import FV.Concurrency.CallCalleeRet
import FV.Concurrency.CallCalleeRetWitness
import FV.Concurrency.LinkedMachine
import FV.Concurrency.LinkedMachineWitness
import FV.Concurrency.CallResumeAll
import FV.Concurrency.CallResumeAllWitness
import FV.Concurrency.CallEnterArm
import FV.Concurrency.CallEnterArmWitness
import FV.Concurrency.CStepSConv
import FV.Concurrency.CStepSConvWitness
import FV.Concurrency.CallEnterClif
import FV.Concurrency.CallEnterClifWitness
import FV.Concurrency.CallResumeChecks
import FV.Concurrency.CallResumeChecksWitness
import FV.Concurrency.CallArity
import FV.Concurrency.CallArityWitness
import FV.Concurrency.CallArgsAt
import FV.Concurrency.CallArgsAtWitness
import FV.Concurrency.CallArgsL2
import FV.Concurrency.CallArgsL2Witness
import FV.Concurrency.CallArgsEntry
import FV.Concurrency.CallArgsEntryWitness
import FV.Concurrency.CallSegAbi
import FV.Concurrency.CallSegAbiWitness
import FV.Concurrency.CallSegT
import FV.Concurrency.CallSegTWitness
import FV.Concurrency.CallEntryLink
import FV.Concurrency.CallEntryLinkWitness
import FV.Concurrency.CallRetLink
import FV.Concurrency.CallRetLinkWitness
import FV.Concurrency.CallValid
import FV.Concurrency.CallValidWitness
import FV.Concurrency.CallSegLift
import FV.Concurrency.CallSegLiftWitness
import FV.Concurrency.CallStepT
import FV.Concurrency.CallStepTWitness
import FV.Concurrency.CallRetT
import FV.Concurrency.CallRetTWitness
import FV.Concurrency.CallSegGeo
import FV.Concurrency.CallSegGeoWitness
import FV.Concurrency.CallSegOkG
import FV.Concurrency.CallSegOkGWitness
import FV.Concurrency.CallSegOkGActWitness
import FV.Concurrency.CallSegCall
import FV.Concurrency.CallSegCallWitness
import FV.Concurrency.CallEntryRel
import FV.Concurrency.CallEntryRelWitness
import FV.Concurrency.CallSegEnt
import FV.Concurrency.CallSegRun
import FV.Concurrency.CallSegLive
import FV.Concurrency.CallSegPc
import FV.Concurrency.CallSegExt
import FV.Concurrency.CallSegOkGT
import FV.Concurrency.CallSegOkGTWitness
import FV.Concurrency.CallSegOkGTFull
import FV.Concurrency.CallSegOkGTRmw
import FV.Concurrency.CallSegOkGTExtWitness
import FV.Concurrency.CallSegOkGTExtFull
import FV.Concurrency.CallSegOkGTMix
