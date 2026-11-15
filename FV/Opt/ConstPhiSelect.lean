import FV.Opt.ConstPhi
import FV.Opt.Legalize128Pass
import FV.Clif.Print

/-! # Where `lean-backend` applies constant-phi removal (#990)

`lean-backend` compiles every function after the `i128` legalisation and constant-phi removal
(`Opt.ConstPhi.run`). The linked compiler's input is CLIF text (`E2E.LinkCheck.FnInput`), so
`link-check` and `lean-link` compile the transformed function printed after the file's header
lines (`FnInput.cp`, `FV/Link/ConstPhiCompile.lean`). Both take this module's decision, so they
compile what `lean-backend` compiled:

* `reparse header g`: the function of the text `header ++ g.print` (index 0, after the `i128`
  legalisation), as `FnInput.func` reads it (`header`: the file's header lines, `Link.clifHeader`, here so that
  `lean-backend` reads them without the linker's modules);
* `keeps header f`: the pass changes `f` and the printed result parses back to itself;
* `select header f`: `run f` when `keeps`, else `f` (`lean-backend`'s function).

Kept free of proofs; `lean-backend` imports it without the linker's modules.
-/

namespace Link

/-- The header lines of a CLIF file (before the first `function`), each with its newline. -/
def clifHeader (t : String) : String :=
  ((t.splitOn "\n").takeWhile (fun l => !l.startsWith "function")).foldl
    (fun acc l => acc ++ l ++ "\n") ""

end Link

namespace Opt.ConstPhi

open Clif

/-- The function of the CLIF text `header ++ g.print` at index 0, after the `i128` legalisation
(`FnInput.func` of that text). -/
def reparse (header : String) (g : Function) : Function :=
  match (Legalize128.parsedFile128 (parseFile (header ++ g.print))).file.funcs[0]? with
  | some p => match p.func with
    | .ok f => f
    | .error _ => default
  | none => default

/-- **The decision**: the pass changes `f`, and `run f` printed after `header` parses back to it. -/
def keeps (header : String) (f : Function) : Bool :=
  let g := run f
  !decide (g = f) && decide (reparse header g = g)

/-- The function `lean-backend` compiles: `run f` when `keeps header f`, else `f`. -/
def select (header : String) (f : Function) : Function :=
  if keeps header f then run f else f

/-- `select` on every function of a parsed file. -/
def selectFile (header : String) (pf : ParsedFile) : ParsedFile :=
  { pf with funcs := pf.funcs.map fun p => { p with func := p.func.map (select header) } }

end Opt.ConstPhi
