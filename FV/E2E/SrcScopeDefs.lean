import FV.E2E.LinkScopeDefs
import FV.Opt.Legalize128Pre

/-!
# The source domain of an input, decided (S2/S3; the definitions)

`FnInput.src`: the function an input file holds, as parsed (before the `i128` legalisation);
`LinkInput.srcProg`: the input's **source program**. `SrcScopeB I`: the source domain of an
input, decided on its parsed functions — every function in `legalOkB`, no `return_call`, the
declarations of the program's functions with their signatures, no function named like a
`__*ti3` helper. Kept free of proofs so that `lake exe lean-link --verified` decides it; the
theorems about them are in `FV/E2E/LegalSource.lean`.
-/

namespace E2E.LinkCheck

open Clif Opt.Legalize128

/-- The function the file holds at index `k`, as parsed (before the `i128` legalisation). -/
def FnInput.src (fi : FnInput) : Clif.Function :=
  match (Clif.parseFile fi.clif).funcs[fi.k]? with
  | some p => getOk p.func
  | none => default

/-- **The source program** of an input: its parsed functions. -/
def LinkInput.srcProg (I : LinkInput) : Clif.Program := { funcs := I.funcs.map (·.src) }

/-- No function of `P` is named like a `__*ti3` helper. -/
def helperFreeB (P : Clif.Program) : Bool :=
  [DivOp.udiv, DivOp.sdiv, DivOp.urem, DivOp.srem].all fun op => (P.func? (divHelper op)).isNone

/-- **The source domain of an input** (decided on its parsed functions): every function in
`legalOkB`, no `return_call`, the declarations of the program's functions with their
signatures, no function named like a `__*ti3` helper. -/
def SrcScopeB (I : LinkInput) : Bool :=
  I.srcProg.funcs.all legalOkB && I.srcProg.funcs.all linkFreeB &&
    I.srcProg.funcs.all (declSigB I.srcProg) && helperFreeB I.srcProg

end E2E.LinkCheck
