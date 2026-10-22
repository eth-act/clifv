import FV.Link.OptCompile
import FV.Opt.TailLoop

/-! # The executable compiler with self tail calls as loops: the definition (S8, #32)

`Link.DeadCleanup.compileExeT S file0`: the shipped executable compiler
`Link.DeadCleanup.compileExe` on the input whose functions have their self `return_call`s turned
into loops (`Opt.TailLoop.loop`, `FV/Opt/TailLoop.lean`): the frame is reused, so a self tail call
does not grow the stack. As for the optimising compiler (`FnInput.opt`, `FV/Link/OptCompile.lean`),
the input of `compileExe` is CLIF text: the transformed function is printed after the file's
header lines and used only when the printed text parses (and legalises) back to it; otherwise the
function keeps its input (`LinkSpec.tailFallbacks` lists those). A function without a self
`return_call` (`Opt.TailLoop.eligB` false) keeps its input, so `compileExeT S = compileExe S` for
an input without one. Theorems: `FV/Link/TailExe.lean`. Kept free of proofs.
-/

namespace Link

open E2E.LinkCheck

/-- **The tail-loop input of a function**: `Opt.TailLoop.loop` of its function, printed after the
file's header, when that text parses back to it; the input itself otherwise. -/
def _root_.E2E.LinkCheck.FnInput.tail (fi : FnInput) : FnInput :=
  let f := fi.func
  if !Opt.TailLoop.eligB f then fi else
    let g := Opt.TailLoop.loop f
    let fi' : FnInput := { fi with clif := clifHeader fi.clif ++ g.print, k := 0 }
    if decide (fi'.func = g) then fi' else fi

/-- The input with every function's self tail calls as loops (`FnInput.tail`). -/
def LinkSpec.tail (S : LinkSpec) : LinkSpec := { S with funcs := S.funcs.map FnInput.tail }

/-- The functions of `S` with a self `return_call` whose transformed input fell back to the
untransformed one (printing and parsing did not give the transformed function back). -/
def LinkSpec.tailFallbacks (S : LinkSpec) : List String :=
  S.funcs.filterMap fun fi =>
    if Opt.TailLoop.eligB fi.func && fi.tail.clif == fi.clif then some fi.func.name else none

/-- The functions of `S` whose self tail calls become loops. -/
def LinkSpec.tailLoops (S : LinkSpec) : List String :=
  S.funcs.filterMap fun fi =>
    if Opt.TailLoop.eligB fi.func && fi.tail.clif != fi.clif then some fi.func.name else none

namespace DeadCleanup

/-- **The executable compiler with self tail calls as loops** (the shipped backend). -/
def compileExeT (S : LinkSpec) (file0 : ByteArray) : Except String ByteArray :=
  compileExe S.tail file0

end DeadCleanup

end Link
