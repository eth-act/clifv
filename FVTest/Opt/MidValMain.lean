import FV.Front.Raw
import FV.Opt.ConstPhi
import FV.Opt.MidValSyms

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
The normaliser is the validator's default (`Opt.MidVal.Norm.stdT f`: constant evaluation, the
single-node algebraic rules, the typed rules with `f`'s atom types, then family 4: neutral and
affine constants, constants on the right, narrowed `ireduce`); with `--norm-std`, the
untyped `Norm.std`; with `--norm-id`, stage 1's identity; with `--norm-const`, constant
evaluation alone. With `--hoist`, the hoisting mode (`check … (hoist := true)`, re-checked by
`checkCertSyms`, whose theorem assumes the function's global values resolve; with `--cond`, by
`Opt.MidVal.symsCopy`, and one more column: `resolves` when the accepted copy's global values
resolve in the table of the names `g` itself references (`globalsResolve`; every image linking `g`
defines them), else `unresolved`). With `--cond`,
family 3 (branch conditions): `Opt.MidVal.checkC`, re-checked by `checkCertC` with the hints
`emitC` gives (the `hints` column after the re-check: the number of hinted blocks).

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

/-- The normaliser for `f`: the validator's default `Norm.stdT f`, or (before/after
measurements) with `--norm-std` the untyped `Norm.std`, with `--norm-id` stage 1's identity
(`Norm.id`), with `--norm-const` constant evaluation alone. -/
def normOf (normId normConst normStd : Bool) (f : Clif.Function) : Opt.MidVal.Norm :=
  if normId then Opt.MidVal.Norm.id
  else if normConst then Opt.MidVal.evalConst
  else if normStd then Opt.MidVal.Norm.std else Opt.MidVal.Norm.stdT f

/-- Constant-phi removal and the check (`checkC` with `cond`), evaluated inside the call
(timing). -/
@[noinline] def runCheck (nm : Clif.Function → Opt.MidVal.Norm) (hoist cond : Bool)
    (f0 g : Clif.Function) : IO (Clif.Function × Except String Unit) := do
  let f := Opt.ConstPhi.run f0
  let r := if cond then (Opt.MidVal.checkC f g (nm f) hoist).map fun _ => ()
    else Opt.MidVal.check f g (nm f) hoist
  match r with
  | .ok () => pure (f, r)
  | .error _ => pure (f, r)

/-- The certificate and hints of an accepted pair (`Opt.MidVal.emit`, `emitC` with `cond`). -/
@[noinline] def runEmit (nm : Clif.Function → Opt.MidVal.Norm) (hoist cond : Bool)
    (f g : Clif.Function) :
    IO (Except String (Opt.MidVal.Cert × List (Clif.BlockId × List Opt.MidVal.Wrap))) :=
  pure (if cond then Opt.MidVal.emitC f g (nm f) hoist
    else (Opt.MidVal.emit f g (nm f) hoist).map fun c => (c, []))

/-- The re-check (`Opt.MidVal.checkCert`, or `checkCertSyms` in the hoisting mode; with hints
`checkCertC`/`symsCopy`), evaluated inside the call (timing): the verdict and, in the hoisting
mode with hints, the copy of `f` accepted against. -/
@[noinline] def runRecheck (nm : Clif.Function → Opt.MidVal.Norm) (hoist cond : Bool)
    (f g : Clif.Function) (cert : Opt.MidVal.Cert)
    (h : List (Clif.BlockId × List Opt.MidVal.Wrap)) : IO (Bool × Option Clif.Function) :=
  pure (if hoist && cond then
      let c := Opt.MidVal.symsCopy f g cert h (nm f)
      (c.isSome, c)
    else if hoist then (Opt.MidVal.checkCertSymsC f g cert h (nm f), none)
    else (Opt.MidVal.checkCertC f g cert h (nm f), none))

/-- The symbol table of the names `g` references (its symbol globals and externs). -/
def ownSyms (g : Clif.Function) (n : String) : Option Nat :=
  if g.globals.any (fun p => match p.2 with
      | .symbol s _ _ | .tlsSymbol s _ _ => s == n
      | _ => false) || g.externs.any (·.2.name == n) then some 0 else none

/-- `ok`/`MISMATCH`/`-`, the microseconds of the re-check (`f` after constant-phi removal) and,
with `cond`, the number of hinted blocks (in the hoisting mode also `resolves`/`unresolved`). -/
def recheck (nm : Clif.Function → Opt.MidVal.Norm) (hoist cond : Bool) (f g : Clif.Function)
    (accepted : Bool) : IO String := do
  let sfx := if cond then (if hoist then "\t0\t-" else "\t0") else ""
  if !accepted then return s!"-\t0{sfx}"
  match ← runEmit nm hoist cond f g with
  | .error e => return s!"MISMATCH(emit {e})\t0{sfx}"
  | .ok (cert, h) =>
    let t0 ← IO.monoNanosNow
    let (ok, c) ← runRecheck nm hoist cond f g cert h
    let t1 ← IO.monoNanosNow
    let res := if hoist && cond then
        s!"\t{if c.any (Opt.MidVal.globalsResolve · (ownSyms g)) then "resolves" else "unresolved"}"
      else ""
    return s!"{if ok then "ok" else "MISMATCH"}\t{(t1 - t0) / 1000}{if cond then s!"\t{h.length}" else ""}{res}"

/-- `--pair F G`: the first function of each plain CLIF file (`Clif.parseFile`; tests). -/
def pairMode (fp gp : String) : IO UInt32 := do
  let one (p : String) : IO Clif.Function := do
    match (Clif.parseFile (← IO.FS.readFile p)).funcs[0]? with
    | some pf => match pf.func with
      | .ok f => pure f
      | .error e => throw (IO.userError s!"{p}: {e}")
    | none => throw (IO.userError s!"{p}: no function")
  let g ← one gp
  let (f, r) ← runCheck Opt.MidVal.Norm.stdT false true (← one fp) g
  match r with
  | .ok () => IO.println s!"accept\trecheck {← recheck Opt.MidVal.Norm.stdT false true f g true}"; return 0
  | .error e => IO.println s!"reject\t{e}"; return 1

def main (args : List String) : IO UInt32 := do
  if let ["--pair", fp, gp] := args then return ← pairMode fp gp
  -- `--norm-id`: stage 1's identity normaliser instead of the default `Opt.MidVal.Norm.stdT f`
  let normId := args.contains "--norm-id"
  -- `--norm-const`: constant evaluation alone (`Opt.MidVal.evalConst`, family 1); `--norm-std`:
  -- the untyped `Opt.MidVal.Norm.std` (families 1–2, without the typed rules)
  let nm := normOf normId (args.contains "--norm-const") (args.contains "--norm-std")
  -- `--cert`: re-check the emitted certificate of every accepted pair (`Opt.MidVal.checkCert`)
  let cert := args.contains "--cert"
  -- `--hoist`: the hoisting mode (`Opt.MidVal.checkCertSyms`)
  let hoist := args.contains "--hoist"
  -- `--cond`: family 3, branch conditions (`Opt.MidVal.checkC`, `checkCertC`)
  let cond := args.contains "--cond"
  let noRc := if cert then (if cond then (if hoist then "\t-\t0\t0\t-" else "\t-\t0\t0") else "\t-\t0") else ""
  let out ← IO.getStdout
  for dir in args.filter (fun a => !a.startsWith "--") do
    let mut stems : Array String := #[]
    for e in ← System.FilePath.readDir dir do
      if e.fileName.endsWith ".unopt.clif" then
        stems := stems.push (e.fileName.dropEnd ".unopt.clif".length).toString
    for stem in stems.qsort (· < ·) do
      let gp := System.FilePath.mk dir / s!"{stem}.opt.clif"
      if !(← gp.pathExists) then
        out.putStrLn s!"{dir}\t{stem}\treject\tinput:no-opt-dump\t0\t0\t0{noRc}"
        continue
      let fr ← decodeOne (System.FilePath.mk dir / s!"{stem}.unopt.clif")
      let gr ← decodeOne gp
      match fr, gr with
      | .error e, _ =>
        out.putStrLn s!"{dir}\t{stem}\treject\tinput:decode-f {firstWord e}\t0\t0\t0{noRc}"
      | _, .error e =>
        out.putStrLn s!"{dir}\t{stem}\treject\tinput:decode-g {firstWord e}\t0\t0\t0{noRc}"
      | .ok f0, .ok g =>
        let t0 ← IO.monoNanosNow
        let (f, r) ← runCheck nm hoist cond f0 g
        let t1 ← IO.monoNanosNow
        let verdict := match r with
          | .ok () => "accept\t-"
          | .error e => s!"reject\t{e}"
        let rc ← if cert then do pure s!"\t{← recheck nm hoist cond f g r.isOk}" else pure ""
        out.putStrLn s!"{dir}\t{stem}\t{verdict}\t{Opt.instCount f}\t{Opt.instCount g}\t{(t1 - t0) / 1000}{rc}"
  return 0
