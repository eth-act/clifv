import FV.Backend
import FV.Backend.LinearScan

/-!
The register allocators the command-line tools (`lean-backend`, `lean-backend-armrun`) offer:
`lean` (the default: the Lean allocator `leanAlloc`, `FV/Backend/LinearScan.lean`, checked by
`checkAlloc` with the spill allocation as fallback: `allocateLean`), and those of
`Allocator.ofName?` (`regalloc2`, `regalloc2-small`, `spill`, `stack`).

With `lean`, if `$FV_RA_OUT` is set (`cargo fv --keep-temps`), the answers are written there
in the schema of `lean-regalloc`'s output (`allocateLeanAnswers`), for `cargo fv link-proof` and
`lean-link`, which rebuild the allocations from it.
-/

namespace Backend

/-- The batch allocator named `n` (`compileFileWith`'s argument). -/
def allocRunOfName? (n : String) : IO (Option (Array VCode → IO (Array (Except String AFunc)))) := do
  if n == "lean" then
    return some fun vcs => do
      let (afs, ans) := allocateLeanAnswers vcs
      if let some p ← IO.getEnv "FV_RA_OUT" then
        IO.FS.writeFile p ("{\"functions\":[" ++ ",".intercalate ans.toList ++ "]}\n")
      pure afs
  return (← Allocator.ofName? n).map (·.run)

end Backend
