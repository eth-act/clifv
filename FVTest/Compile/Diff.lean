import FV.Compile
import FVTest.Compile.Cases

/-!
# `compile-diff`: `denote` vs `Clif.run (compile f)` on every corpus vector

For every test vector of `FVTest.Compile.cases` (`Corpus.all ++ Corpus.emitTests`): the vector's expected result, `DSL.denote`, and
`Compile.runCompiled` (the compiled program under `Clif.runWith` with the map model
`Compile.mapEnv`, arguments encoded by `Compile.setupCall`, result decoded by
`Compile.decodeResult`) must all agree. Also checks `Compile.onlySubsetE` on every compiled
program. Exit status 0 iff everything agrees.
-/

open DSL

namespace CompileDiff

def showM {t : Ty} (r : M t.denote) : String :=
  have := Ty.instRepr t
  match r with
  | .ok x => s!"ok {reprStr x}"
  | .error e => s!"error {reprStr e}"

structure Tally where
  vectors : Nat := 0
  agree : Nat := 0
  fns : Nat := 0
  subsetOk : Nat := 0

def runCase (verbose : Bool) (tc : TestCase) (t : Tally) : IO Tally := do
  let p := Compile.compile tc.fn
  let sub := Compile.onlySubsetE p
  unless sub do
    IO.println s!"FAIL {tc.fn.name}: emitted opcode outside subset E"
  let mut t := { t with fns := t.fns + 1, subsetOk := t.subsetOk + (if sub then 1 else 0) }
  let mut i := 0
  for v in tc.vectors do
    have := Ty.decEq tc.τ
    let d := denote tc.fn v.args
    let c := Compile.runCompiled tc.fn v.args
    let ok := decide (d = v.expected) && decide (c = some d)
    t := { t with vectors := t.vectors + 1, agree := t.agree + (if ok then 1 else 0) }
    if !ok || verbose then
      let cs := match c with | some r => showM r | none => "none (not a decodable outcome)"
      IO.println s!"{if ok then "ok  " else "FAIL"} {tc.fn.name} #{i}: expected {showM v.expected}, denote {showM d}, compiled {cs}"
    i := i + 1
  pure t

end CompileDiff

open CompileDiff in
def main (args : List String) : IO UInt32 := do
  let verbose := args.contains "-v"
  let mut t : Tally := {}
  for tc in FVTest.Compile.cases do
    t ← runCase verbose tc t
  IO.println s!"functions: {t.fns}, onlySubsetE: {t.subsetOk}/{t.fns}"
  IO.println s!"vectors: {t.vectors}, denote = Clif.run (compile f) = expected: {t.agree}/{t.vectors}"
  pure (if t.agree == t.vectors && t.subsetOk == t.fns then 0 else 1)
