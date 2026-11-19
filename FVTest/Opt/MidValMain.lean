import FV.Front.Raw
import FV.Opt.ConstPhi
import FV.Opt.MidVal

/-! # `lake exe midval-check DIR...`: the mid-end validator on cg_clif's dump pairs (#1119)

Every `X.unopt.clif` of each dump directory `DIR` (a `<unit>.clif/` written by the patched
cg_clif, or `cargo fv --keep-temps`' `c.clif/`) with an `X.opt.clif` next to it is decoded like
`clif-decode` does (`Front.readDump`, `Front.unitTable [d]`, `Front.decodeFn`); the unoptimised
function goes through `Opt.ConstPhi.run` (as `lean-backend` compiles it) and is checked against
the optimised one (`Opt.MidVal.check`). One tab-separated line per pair on stdout:

`DIR  X  accept|reject  reason  insts(f)  insts(g)  microseconds(check)`

Measurement tool only: it states no theorem.
-/

open Front

def decodeOne (p : System.FilePath) : IO (Except String Clif.Function) := do
  let src ← IO.FS.readFile p
  pure do
    let d ← readDump src
    let ρ ← unitTable [d]
    decodeFn ρ d

def firstWord (s : String) : String := (s.splitOn " ").headD s

/-- Constant-phi removal and the check, evaluated inside the call (timing). -/
@[noinline] def runCheck (f0 g : Clif.Function) : IO (Clif.Function × Except String Unit) := do
  let f := Opt.ConstPhi.run f0
  let r := Opt.MidVal.check f g
  match r with
  | .ok () => pure (f, r)
  | .error _ => pure (f, r)

def main (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  for dir in args do
    let mut stems : Array String := #[]
    for e in ← System.FilePath.readDir dir do
      if e.fileName.endsWith ".unopt.clif" then
        stems := stems.push (e.fileName.dropEnd ".unopt.clif".length).toString
    for stem in stems.qsort (· < ·) do
      let gp := System.FilePath.mk dir / s!"{stem}.opt.clif"
      if !(← gp.pathExists) then
        out.putStrLn s!"{dir}\t{stem}\treject\tinput:no-opt-dump\t0\t0\t0"
        continue
      let fr ← decodeOne (System.FilePath.mk dir / s!"{stem}.unopt.clif")
      let gr ← decodeOne gp
      match fr, gr with
      | .error e, _ =>
        out.putStrLn s!"{dir}\t{stem}\treject\tinput:decode-f {firstWord e}\t0\t0\t0"
      | _, .error e =>
        out.putStrLn s!"{dir}\t{stem}\treject\tinput:decode-g {firstWord e}\t0\t0\t0"
      | .ok f0, .ok g =>
        let t0 ← IO.monoNanosNow
        let (f, r) ← runCheck f0 g
        let t1 ← IO.monoNanosNow
        let verdict := match r with
          | .ok () => "accept\t-"
          | .error e => s!"reject\t{e}"
        out.putStrLn s!"{dir}\t{stem}\t{verdict}\t{Opt.instCount f}\t{Opt.instCount g}\t{(t1 - t0) / 1000}"
  return 0
