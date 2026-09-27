import FV.Compile
import Corpus.All

/-!
# The emitter and the harness reduce in the kernel

M2 proves `compile_correct` by computing through `compile`, `Clif.run` and the harness, so
these must stay kernel-reducible (structural recursion, no well-founded definitions such as
`List.mergeSort`). Checked with `decide +kernel` (no extra axioms) on straight-line code with
an error path, a loop, and map externs (`Compile.mapEnv`).
-/

set_option maxRecDepth 100000

example : Compile.runCompiled Corpus.addU8.ast (200, 55, ()) 1000 = some (.ok 255) := by
  decide +kernel

example : Compile.runCompiled Corpus.addU8.ast (200, 56, ()) 1000 = some (.error .overflow) := by
  decide +kernel

example : Compile.runCompiled Corpus.sumChecked.ast (#v[1, 2, 3, 4], ()) 1000 = some (.ok 10) := by
  decide +kernel

example : Compile.runCompiled Corpus.lookup.ast (3, 10, 20, ()) 1000 = some (.error .notFound) := by
  decide +kernel
