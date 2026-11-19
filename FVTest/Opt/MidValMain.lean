import FV.Front.Raw
import FV.Opt.ConstPhi
import FV.Opt.MidValCert

/-! # `lake exe midval-check DIR...`: the mid-end validator on cg_clif's dump pairs (#1119)

Every `X.unopt.clif` of each dump directory `DIR` (a `<unit>.clif/` written by the patched
cg_clif, or `cargo fv --keep-temps`' `c.clif/`) with an `X.opt.clif` next to it is decoded like
`clif-decode` does (`Front.readDump`, `Front.unitTable [d]`, `Front.decodeFn`); the unoptimised
function goes through `Opt.ConstPhi.run` (as `lean-backend` compiles it) and is checked against
the optimised one (`Opt.MidVal.check`). One tab-separated line per pair on stdout:

`DIR  X  accept|reject  reason  insts(f)  insts(g)  microseconds(check)`

With `--cert`, two more columns: the re-check of the emitted certificate
(`Opt.MidVal.checkCert f g (emit f g)`: `ok` when it gives `check`'s verdict, `MISMATCH`
otherwise, `-` for a rejected pair) and its microseconds (`checkCert` alone, not the emission).
The normaliser is the validator's default (`Opt.MidVal.Norm.std`, constant evaluation); with
`--norm-id`, stage 1's identity. With `--hoist`, the hoisting mode (`check … (hoist := true)`, re-checked by `checkCertSyms`,
whose theorem assumes the function's global values resolve).

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

/-- The normaliser: the validator's default `Norm.std` (constant evaluation), or with
`--norm-id` stage 1's identity (`Norm.id`, for before/after measurements). -/
def normOf (normId : Bool) : Opt.MidVal.Norm :=
  if normId then Opt.MidVal.Norm.id else Opt.MidVal.Norm.std

/-- Constant-phi removal and the check, evaluated inside the call (timing). -/
@[noinline] def runCheck (normId hoist : Bool) (f0 g : Clif.Function) :
    IO (Clif.Function × Except String Unit) := do
  let f := Opt.ConstPhi.run f0
  let r := Opt.MidVal.check f g (normOf normId) hoist
  match r with
  | .ok () => pure (f, r)
  | .error _ => pure (f, r)

/-- The certificate of an accepted pair (`Opt.MidVal.emit`). -/
@[noinline] def runEmit (normId hoist : Bool) (f g : Clif.Function) :
    IO (Except String Opt.MidVal.Cert) :=
  pure (Opt.MidVal.emit f g (normOf normId) hoist)

/-- The re-check (`Opt.MidVal.checkCert`, or `checkCertSyms` in the hoisting mode), evaluated
inside the call (timing). -/
@[noinline] def runRecheck (normId hoist : Bool) (f g : Clif.Function) (cert : Opt.MidVal.Cert) :
    IO Bool :=
  pure (if hoist then Opt.MidVal.checkCertSyms f g cert (normOf normId)
    else Opt.MidVal.checkCert f g cert (normOf normId))

/-- `ok`/`MISMATCH`/`-` and the microseconds of `checkCert` (`f` after constant-phi removal). -/
def recheck (normId hoist : Bool) (f g : Clif.Function) (accepted : Bool) : IO String := do
  if !accepted then return "-\t0"
  match ← runEmit normId hoist f g with
  | .error e => return s!"MISMATCH(emit {e})\t0"
  | .ok cert =>
    let t0 ← IO.monoNanosNow
    let ok ← runRecheck normId hoist f g cert
    let t1 ← IO.monoNanosNow
    return s!"{if ok then "ok" else "MISMATCH"}\t{(t1 - t0) / 1000}"

/-- `--pair F G`: the first function of each plain CLIF file (`Clif.parseFile`; tests). -/
def pairMode (fp gp : String) : IO UInt32 := do
  let one (p : String) : IO Clif.Function := do
    match (Clif.parseFile (← IO.FS.readFile p)).funcs[0]? with
    | some pf => match pf.func with
      | .ok f => pure f
      | .error e => throw (IO.userError s!"{p}: {e}")
    | none => throw (IO.userError s!"{p}: no function")
  let g ← one gp
  let (f, r) ← runCheck false false (← one fp) g
  match r with
  | .ok () => IO.println s!"accept\trecheck {← recheck false false f g true}"; return 0
  | .error e => IO.println s!"reject\t{e}"; return 1

def main (args : List String) : IO UInt32 := do
  if let ["--pair", fp, gp] := args then return ← pairMode fp gp
  -- `--norm-id`: stage 1's identity normaliser instead of the default `Opt.MidVal.Norm.std`
  let normId := args.contains "--norm-id"
  -- `--cert`: re-check the emitted certificate of every accepted pair (`Opt.MidVal.checkCert`)
  let cert := args.contains "--cert"
  -- `--hoist`: the hoisting mode (`Opt.MidVal.checkCertSyms`)
  let hoist := args.contains "--hoist"
  let out ← IO.getStdout
  for dir in args.filter (fun a => a != "--norm-id" && a != "--cert" && a != "--hoist") do
    let mut stems : Array String := #[]
    for e in ← System.FilePath.readDir dir do
      if e.fileName.endsWith ".unopt.clif" then
        stems := stems.push (e.fileName.dropEnd ".unopt.clif".length).toString
    for stem in stems.qsort (· < ·) do
      let gp := System.FilePath.mk dir / s!"{stem}.opt.clif"
      if !(← gp.pathExists) then
        out.putStrLn s!"{dir}\t{stem}\treject\tinput:no-opt-dump\t0\t0\t0{if cert then "\t-\t0" else ""}"
        continue
      let fr ← decodeOne (System.FilePath.mk dir / s!"{stem}.unopt.clif")
      let gr ← decodeOne gp
      match fr, gr with
      | .error e, _ =>
        out.putStrLn s!"{dir}\t{stem}\treject\tinput:decode-f {firstWord e}\t0\t0\t0{if cert then "\t-\t0" else ""}"
      | _, .error e =>
        out.putStrLn s!"{dir}\t{stem}\treject\tinput:decode-g {firstWord e}\t0\t0\t0{if cert then "\t-\t0" else ""}"
      | .ok f0, .ok g =>
        let t0 ← IO.monoNanosNow
        let (f, r) ← runCheck normId hoist f0 g
        let t1 ← IO.monoNanosNow
        let verdict := match r with
          | .ok () => "accept\t-"
          | .error e => s!"reject\t{e}"
        let rc ← if cert then do pure s!"\t{← recheck normId hoist f g r.isOk}" else pure ""
        out.putStrLn s!"{dir}\t{stem}\t{verdict}\t{Opt.instCount f}\t{Opt.instCount g}\t{(t1 - t0) / 1000}{rc}"
  return 0
