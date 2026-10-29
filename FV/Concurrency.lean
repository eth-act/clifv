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
module

public import FV.Concurrency.Rel
public import FV.Concurrency.Exec
public import FV.Concurrency.Armv8
public import FV.Concurrency.ClifMM
public import FV.Concurrency.Mapping
public import FV.Concurrency.Interleave
public import FV.Concurrency.Code
public import FV.Concurrency.Witness
public import FV.Concurrency.ArmFootprint
public import FV.Concurrency.ArmThread
public import FV.Concurrency.ArmThreadWitness
public import FV.Concurrency.Program
public import FV.Concurrency.Replay
public import FV.Concurrency.ClifThread
public import FV.Concurrency.ProgramE2E
public import FV.Concurrency.ProgramWitness
public import FV.Concurrency.RC11
public import FV.Concurrency.ArmFence
public import FV.Concurrency.RC11Witness
public import FV.Concurrency.ProgramE2EF
public import FV.Concurrency.ProgramFWitness
public import FV.Concurrency.Armv8Full
public import FV.Concurrency.Lse
public import FV.Concurrency.ThreadRefine
public import FV.Concurrency.ThreadRefineWitness
public import FV.Concurrency.ArmInstFoot
public import FV.Concurrency.VCodeThread
public import FV.Concurrency.VCodeThreadWitness
public import FV.Concurrency.VCodeEvents
public import FV.Concurrency.ArmPrecise
public import FV.Concurrency.PrivCoh
public import FV.Concurrency.PrepThread
public import FV.Concurrency.AllocThread
public import FV.Concurrency.FrameMono
public import FV.Concurrency.ThreadLayerWitness
public import FV.Concurrency.VCodeAddr
public import FV.Concurrency.VCodeAddrAtomic
public import FV.Concurrency.VCodeFrame
public import FV.Concurrency.VCodeFrameWitness
public import FV.Concurrency.ArmAllocThread
public import FV.Concurrency.ArmAllocThreadWitness
public import FV.Concurrency.ArmAllocSeg
public import FV.Concurrency.ArmAllocSegWitness
public import FV.Concurrency.ArmAllocLines
public import FV.Concurrency.ArmAllocItem
public import FV.Concurrency.ArmAllocStraight
public import FV.Concurrency.ArmAllocWitness
public import FV.Concurrency.ArmAllocMem
public import FV.Concurrency.ArmAllocMemWitness
public import FV.Concurrency.ArmAllocMemLS
public import FV.Concurrency.SegRun
public import FV.Concurrency.IselVary
public import FV.Concurrency.IselFoot
public import FV.Concurrency.IselClif
public import FV.Concurrency.IselClifWitness
public import FV.Concurrency.SegShape
public import FV.Concurrency.SegShapeWitness
public import FV.Concurrency.ClifCStep
public import FV.Concurrency.ClifCStepWitness
public import FV.Concurrency.IselCover
public import FV.Concurrency.IselCoverWitness
public import FV.Concurrency.VCodeSize
public import FV.Concurrency.VCodeSizeWitness
public import FV.Concurrency.SegFoot
public import FV.Concurrency.SegFootWitness
public import FV.Concurrency.IselStep
public import FV.Concurrency.IselSeg
public import FV.Concurrency.IselCheck
public import FV.Concurrency.CorrRefine
public import FV.Concurrency.ClifCStepTerm
public import FV.Concurrency.IselThread
public import FV.Concurrency.IselMem
public import FV.Concurrency.IselMemAux
public import FV.Concurrency.IselMemAuxWitness
public import FV.Concurrency.CEvsInv
public import FV.Concurrency.CEvsInvWitness
public import FV.Concurrency.IselVar
public import FV.Concurrency.IselMemSeg
public import FV.Concurrency.IselMemHelp
public import FV.Concurrency.IselThreadWitnessData
public import FV.Concurrency.IselMemLower
public import FV.Concurrency.IselMemMain
public import FV.Concurrency.IselRefines
public import FV.Concurrency.IselEntry
public import FV.Concurrency.IselRefinesWitness
public import FV.Concurrency.ThreadCompose
public import FV.Concurrency.ThreadComposeWitness
public import FV.Concurrency.ThreadProgress
public import FV.Concurrency.MoveEvs
public import FV.Concurrency.ArmAllocMove
public import FV.Concurrency.RealizeCompiled
public import FV.Concurrency.RealizeWitness
public import FV.Concurrency.ArmAllocFwd
public import FV.Concurrency.RealizeWitnessFence
public import FV.Concurrency.RealizeExec
public import FV.Concurrency.ArmLoopRun
public import FV.Concurrency.ArmLoopSpec
public import FV.Concurrency.ArmAllocLoop
public import FV.Concurrency.ArmAllocLoopMem
public import FV.Concurrency.ArmAllocLoopWitness
public import FV.Concurrency.ArmAllocLoopFwd
public import FV.Concurrency.RealizeWitnessLoad
public import FV.Concurrency.ArmAllocBranch
public import FV.Concurrency.ArmAllocBranchWitness
public import FV.Concurrency.ArmAllocLS
public import FV.Concurrency.ArmAllocLSWitness
public import FV.Concurrency.ArmAllocLSX
public import FV.Concurrency.ArmAllocLSXWitness
public import FV.Concurrency.RealizeCompiledLSX
public import FV.Concurrency.RealizeWitnessStore
public import FV.Concurrency.RealizeWitnessMP
public import FV.Concurrency.RealizeWitnessRmw
public import FV.Concurrency.RealizeWitnessCas
public import FV.Concurrency.CallCompose
public import FV.Concurrency.CallComposeWitness
public import FV.Concurrency.ArmAllocEntry
public import FV.Concurrency.ArmAllocEntryWitness
public import FV.Concurrency.ArmProgram
public import FV.Concurrency.ClifLift
public import FV.Concurrency.CallThread
public import FV.Concurrency.CallThreadWitness
public import FV.Concurrency.CallSeg
public import FV.Concurrency.CallXClosedWitness
public import FV.Concurrency.CallLoadData
public import FV.Concurrency.CallLoadWitness
public import FV.Concurrency.RealizeWitnessCasFull
public import FV.Concurrency.CallResume
public import FV.Concurrency.CallLoadFull
public import FV.Concurrency.CallLLSCEntry
public import FV.Concurrency.CallLoadResume
public import FV.Concurrency.CallRmwData
public import FV.Concurrency.CallRmwWitness
public import FV.Concurrency.ArmAllocPause
public import FV.Concurrency.ArmAllocPauseWitness
public import FV.Concurrency.ArmAllocLinked
public import FV.Concurrency.ArmAllocLinkedWitness
public import FV.Concurrency.IselDriverT
public import FV.Concurrency.IselCall
public import FV.Concurrency.IselCallWitness
public import FV.Concurrency.IselResume
public import FV.Concurrency.CallResumeQ
public import FV.Concurrency.CallResumeLayers
public import FV.Concurrency.CallLayers
public import FV.Concurrency.CallResumeWitness
public import FV.Concurrency.IselRetT
public import FV.Concurrency.IselCallRet
public import FV.Concurrency.CallEntryWitness
public import FV.Concurrency.CallRets
public import FV.Concurrency.CallRetsAlloc
public import FV.Concurrency.CallRetsEnd
public import FV.Concurrency.CallRetsWitness
public import FV.Concurrency.CallPopWitness
public import FV.Concurrency.FrameDisj
public import FV.Concurrency.FrameDisjWitness
public import FV.Concurrency.ClifThreadI
public import FV.Concurrency.ClifThreadIWitness
public import FV.Concurrency.PrivCohT
public import FV.Concurrency.PrivCohTWitness
public import FV.Concurrency.CallComposeT
public import FV.Concurrency.CallComposeTWitness
public import FV.Concurrency.CallRetResume
public import FV.Concurrency.CallRetResumeWitness
public import FV.Concurrency.CallRetPremises
public import FV.Concurrency.CallRetPremisesWitness
public import FV.Concurrency.CallRetsN
public import FV.Concurrency.CallRetsNWitness
public import FV.Concurrency.CallEntryPremises
public import FV.Concurrency.CallEntryPremisesWitness
public import FV.Concurrency.CallCalleeRet
public import FV.Concurrency.CallCalleeRetWitness
public import FV.Concurrency.LinkedMachine
public import FV.Concurrency.LinkedMachineWitness
public import FV.Concurrency.CallResumeAll
public import FV.Concurrency.CallResumeAllWitness
public import FV.Concurrency.CallEnterArm
public import FV.Concurrency.CallEnterArmWitness
public import FV.Concurrency.CStepSConv
public import FV.Concurrency.CStepSConvWitness
public import FV.Concurrency.CallEnterClif
public import FV.Concurrency.CallEnterClifWitness
public import FV.Concurrency.CallResumeChecks
public import FV.Concurrency.CallResumeChecksWitness
public import FV.Concurrency.CallArity
public import FV.Concurrency.CallArityWitness
public import FV.Concurrency.CallArgsAt
public import FV.Concurrency.CallArgsAtWitness
public import FV.Concurrency.CallArgsL2
public import FV.Concurrency.CallArgsL2Witness
public import FV.Concurrency.CallArgsEntry
public import FV.Concurrency.CallArgsEntryWitness
public import FV.Concurrency.CallSegAbi
public import FV.Concurrency.CallSegAbiWitness
public import FV.Concurrency.CallSegT
public import FV.Concurrency.CallSegTWitness
public import FV.Concurrency.CallEntryLink
public import FV.Concurrency.CallEntryLinkWitness
public import FV.Concurrency.CallRetLink
public import FV.Concurrency.CallRetLinkWitness
public import FV.Concurrency.CallValid
public import FV.Concurrency.CallValidWitness
public import FV.Concurrency.CallSegLift
public import FV.Concurrency.CallSegLiftWitness
public import FV.Concurrency.CallStepT
public import FV.Concurrency.CallStepTWitness
public import FV.Concurrency.CallRetT
public import FV.Concurrency.CallRetTWitness
public import FV.Concurrency.CallSegGeo
public import FV.Concurrency.CallSegGeoWitness
public import FV.Concurrency.CallSegOkG
public import FV.Concurrency.CallSegOkGWitness
public import FV.Concurrency.CallSegOkGActWitness
public import FV.Concurrency.CallSegCall
public import FV.Concurrency.CallSegCallWitness
public import FV.Concurrency.CallEntryRel
public import FV.Concurrency.CallEntryRelWitness
public import FV.Concurrency.CallSegEnt
public import FV.Concurrency.CallSegRun
public import FV.Concurrency.CallSegLive
public import FV.Concurrency.CallSegPc
public import FV.Concurrency.CallSegExt
public import FV.Concurrency.CallSegOkGT
public import FV.Concurrency.CallSegOkGTWitness
public import FV.Concurrency.CallSegOkGTFull
public import FV.Concurrency.CallSegOkGTRmw
public import FV.Concurrency.CallSegOkGTExtWitness
public import FV.Concurrency.CallSegOkGTExtFull
public import FV.Concurrency.CallSegOkGTMix

@[expose] public section
