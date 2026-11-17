import FV.E2E.SrcScopeDefs
import FV.Opt.Legalize128PreT

/-!
# The source domain of an input, `try_call_indirect` included (#1076; the definition)

`SrcScopeTB I`: `SrcScopeB I` (`FV/E2E/SrcScopeDefs.lean`) with every function in `legalOkTB`
instead of `legalOkB`: a function that mentions `i128` may have `try_call_indirect` terminators,
and its indirect calls have `i128`-free call-site signatures (Rust's `Box<dyn Any>::downcast`).
Kept free of proofs so that `lake exe lean-link --verified` decides it; the theorems about it are
in `FV/E2E/LegalSourceT.lean` (`srcCtxT`, `srcScopeTB_of_srcScopeB`).
-/

namespace E2E.LinkCheck

open Clif Opt.Legalize128

/-- **The source domain of an input, `try_call_indirect` included** (decided on its parsed
functions): every function in `legalOkTB`, no `return_call`, the declarations of the program's
functions with their signatures, no function named like a `__*ti3` helper. -/
def SrcScopeTB (I : LinkInput) : Bool :=
  I.srcProg.funcs.all legalOkTB && I.srcProg.funcs.all linkFreeB &&
    I.srcProg.funcs.all (declSigB I.srcProg) && helperFreeB I.srcProg

end E2E.LinkCheck
