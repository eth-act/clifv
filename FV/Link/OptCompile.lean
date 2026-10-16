import FV.Link.Compile
import FV.Link.DeadCleanupCompile
import FV.Opt.OptimizeX
import FV.Clif.Print

/-! # The optimising executable compiler: the definition

`compileExeOpt S file0`: the executable compiler `compileExe` on the input whose functions are
optimised by the mid-end of the executable compiler (`Opt.optimizeExe` with `Opt.exeConfig`: the
Cranelift rules restricted to the proven ones, `lean-backend --opt-proven-only`). Its pipeline
on a function is parse → `i128` legalisation (`FnInput.func`) → mid-end → backend (`pipeT`).

The input of `compileExe` is CLIF text (`FnInput.clif`, parsed by `FnInput.func`): the
optimised function `g` is printed (`Clif.Function.print`) after the file's header lines, and the
printed input is used only when it parses (and legalises) back to `g` exactly (`FnInput.opt`,
as the frontend checks its renamed functions, `Front.mkInput`); otherwise the function keeps
its unoptimised input. Either way the input's function is the optimised function or the
original one, both of which refine it (`FV/Link/OptExe.lean`).

`compileExeOpt` and `DeadCleanup.compileExeOpt` (the shipped backend with the dead-instruction
cleanup) are `lake exe lean-link --opt`'s compilers; kept free of proofs.
-/

namespace Link

open E2E.LinkCheck

/-- The header lines of a CLIF file (before the first `function`), each with its newline. -/
def clifHeader (t : String) : String :=
  ((t.splitOn "\n").takeWhile (fun l => !l.startsWith "function")).foldl
    (fun acc l => acc ++ l ++ "\n") ""

/-- **The optimised input of a function**: its function optimised by `Opt.optimizeExe`
(`Opt.exeConfig`), printed after the file's header, when that text parses back to the optimised
function; the input itself otherwise. -/
def _root_.E2E.LinkCheck.FnInput.opt (fi : FnInput) : FnInput :=
  let f := fi.func
  let g := Opt.optimizeExe f Opt.exeConfig
  if decide (g = f) then fi else
    let fi' : FnInput := { fi with clif := clifHeader fi.clif ++ g.print, k := 0 }
    if decide (fi'.func = g) then fi' else fi

/-- The input with every function optimised (`FnInput.opt`). -/
def LinkSpec.opt (S : LinkSpec) : LinkSpec := { S with funcs := S.funcs.map FnInput.opt }

/-- The functions whose optimised input fell back to the unoptimised one (printing and parsing
did not give the optimised function back), by name. -/
def LinkSpec.optFallbacks (S : LinkSpec) : List String :=
  S.funcs.filterMap fun fi =>
    let f := fi.func
    if decide (Opt.optimizeExe f Opt.exeConfig = f) then none
    else if decide ((FnInput.opt fi).func = f) then some f.name else none

/-- **The optimising executable compiler**: `compileExe` on the optimised input. -/
def compileExeOpt (S : LinkSpec) (file0 : ByteArray) : Except String ByteArray :=
  compileExe S.opt file0

namespace DeadCleanup

/-- **The optimising executable compiler** (the shipped backend). -/
def compileExeOpt (S : LinkSpec) (file0 : ByteArray) : Except String ByteArray :=
  compileExe S.opt file0

end DeadCleanup

end Link
