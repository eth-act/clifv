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
(`VCodeThread.VTStep`).
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
