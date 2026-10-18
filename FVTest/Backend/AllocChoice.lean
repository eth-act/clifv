import FV.Backend
import FV.Backend.LinearScan

/-!
The register allocators the command-line tools (`lean-backend`, `lean-backend-armrun`) offer:
`lean` (the Lean allocator `leanAlloc`, `FV/Backend/LinearScan.lean`, checked by `checkAlloc`
with the spill allocation as fallback: `allocateLean`), and those of `Allocator.ofName?`
(`regalloc2`, `regalloc2-small`, `spill`, `stack`).
-/

namespace Backend

/-- The batch allocator named `n` (`compileFileWith`'s argument). -/
def allocRunOfName? (n : String) : IO (Option (Array VCode → IO (Array (Except String AFunc)))) := do
  if n == "lean" then return some fun vcs => pure (allocateLean vcs)
  return (← Allocator.ofName? n).map (·.run)

end Backend
