import Lake.Build.Trace

def main (args : List String) : IO UInt32 := do
  for path in args do
    let binary ← Lake.computeFileHash (System.FilePath.mk path) false
    let text ← if path.endsWith ".lean" then Lake.computeFileHash (System.FilePath.mk path) true else pure binary
    IO.println s!"{path}\t{binary}\t{text}"
  return 0
