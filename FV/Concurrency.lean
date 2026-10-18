/-
Root of the memory-model layer (T2, #38; `docs/plans/atomics.md`): execution graphs, the Armv8
axiomatic model restricted to the instructions Cranelift emits, the Cranelift contract for CLIF
atomics, the soundness of Cranelift's mapping (`Mapping.armv8_to_clif`), DRF-SC
(`ClifMM.drf_sc`, `Mapping.armv8_drf_sc`), SC executions as interleavings
(`Mapping.armv8_interleaving`), and the mapping table of the emitted code (`Code.lines_kinds`).
Nothing here changes the Arm model of `FV/Arm`.
-/
import FV.Concurrency.Rel
import FV.Concurrency.Exec
import FV.Concurrency.Armv8
import FV.Concurrency.ClifMM
import FV.Concurrency.Mapping
import FV.Concurrency.Interleave
import FV.Concurrency.Code
import FV.Concurrency.Witness
