import FV.Opt.MidValCond

/-!
# The hoisting mode at a symbol table (#1119, `placement:symbol_value`)

Cranelift's loop-invariant code motion moves a `symbol_value` (also `tls_value`, `func_addr`: no
operands, pure) out of a loop into its preheader, so `g` evaluates it on paths where `f` leaves
the loop first. `Clif.run` is `stuck` on a symbol the image lacks, so no simulation holding at
every symbol table relates such a pair (`neg_symhoist`, `FVTest/Opt/MidValNegWitness.lean`). The
hoisting mode (`checkCertSyms`, `check_soundSyms`) relates them at every symbol table where the
compared copy of `f`'s global values resolve (`globalsResolve`); only a tool holding the image's
symbol table (`link-check`, `lean-link`) can decide that.

* `symsCopy f g cert hints`: the hoisting mode of `checkCertC` (branch-condition hints, fold
  requests): the copy of `f` that `g` (or `condPrep g hints`) is re-checked against when the
  re-check `checkCertSyms` accepts, else `none`: `f` itself without fold requests, else
  `foldPre f bs` or `foldPreK f bs` (`bs = foldBlocks hints`), or the same on the forwarding copy
  `fwdPre f` when `fwdOk f` (`FV/Opt/MidValFwd.lean`), as `checkCertC` tries them.
  Its value does not depend on a symbol table: `lean-backend` decides it per function.
* `checkCertSymsAt syms f g cert hints`: `symsCopy` accepts and that copy's global values resolve
  in `syms` (`globalsResolve`); decided where `syms` is known. Soundness:
  `Opt.MidVal.checkCertSymsAt_sound` (`FV/Opt/Proof/MidValSymsSim.lean`).

`checkC`/`emitC` with `hoist := true` try the fold, division and block-parameter prep as without
it (`FV/Opt/MidValCond.lean`).
-/

namespace Opt.MidVal

open Clif

/-- **The copy of `f` the hoisting-mode re-check with hints accepts `g` against** (module doc). -/
def symsCopy (f g : Function) (cert : Cert) (hints : List (BlockId × List Wrap))
    (norm : Norm := Norm.stdD f) : Option Function :=
  if hints.isEmpty then (if checkCertSyms f g cert norm then some f else none)
  else if (foldBlocks hints).isEmpty then
    (if refsOk g && checkCertSyms f (condPrep g hints) cert norm then some f else none)
  else if refsOk g && checkCertSyms (foldPre f (foldBlocks hints)) (condPrep g hints) cert then
    some (foldPre f (foldBlocks hints))
  else if refsOk g && checkCertSyms (foldPreK f (foldBlocks hints)) (condPrep g hints) cert then
    some (foldPreK f (foldBlocks hints))
  else if refsOk g && fwdOk f &&
      checkCertSyms (foldPre (fwdPre f) (foldBlocks hints)) (condPrep g hints) cert then
    some (foldPre (fwdPre f) (foldBlocks hints))
  else if refsOk g && fwdOk f &&
      checkCertSyms (foldPreK (fwdPre f) (foldBlocks hints)) (condPrep g hints) cert then
    some (foldPreK (fwdPre f) (foldBlocks hints))
  else none

/-- **The hoisting-mode re-check at the symbol table `syms`** (module doc). -/
def checkCertSymsAt (syms : String → Option Nat) (f g : Function) (cert : Cert)
    (hints : List (BlockId × List Wrap)) (norm : Norm := Norm.stdD f) : Bool :=
  match symsCopy f g cert hints norm with
  | some f' => globalsResolve f' syms
  | none => false

end Opt.MidVal
