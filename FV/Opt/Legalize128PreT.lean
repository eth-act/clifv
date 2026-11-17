import FV.Opt.Legalize128Pre

/-!
# `Opt.Legalize128`: the source domain with `i128`-free indirect calls (#1076)

`legalOkB` (`FV/Opt/Legalize128Pre.lean`) is the domain of the pre-S4 validator `check`: an
`i128` function has no `try_call_indirect` at all and no `call_indirect` with an `i128`
call-site signature (`Pre`, `indOldB`). Rust's `Box<dyn Any>::downcast` is outside it: it
compares two `TypeId`s with `load.i128` and calls `type_id` through the vtable with a
`try_call_indirect` whose signature has no `i128`.

`indTB f`: no indirect call of `f` (`call_indirect` or `try_call_indirect`) has an `i128`
call-site signature. `preBT f := preBW f && indTB f` (`preBW`: the decidable completeness
precondition of the validator `checkW` that `lean-backend` runs). `legalOkTB f`: the pass
succeeds and `f` does not mention `i128` or meets `preBT`. `legalOkB f` implies `legalOkTB f`.

Kept free of proofs so that the driver can evaluate them.
-/

namespace Opt.Legalize128

open Clif

/-- No indirect call of `f` (`call_indirect` or `try_call_indirect`) has a call-site signature
with an `i128` parameter or return. -/
def indTB (f : Function) : Bool :=
  f.blocks.all fun b =>
    b.body.all (fun s => match s.inst with
      | .callIndirect sig _ _ => match f.sigDecls.lookup sig with
        | some d => !sig128 d
        | none => true
      | _ => true) &&
    match b.term with
    | .tryCallIndirect _ _ et => match f.sigDecls.lookup et.sig with
      | some d => !sig128 d
      | none => true
    | _ => true

/-- `preBW` (the validator `checkW`'s completeness precondition) and `i128`-free indirect call
sites. -/
def preBT (f : Function) : Bool := preBW f && indTB f

/-- **The source domain of one function, with `i128`-free indirect calls**: the pass succeeds,
and it is the identity (`f` does not mention `i128`) or `preBT f` holds. -/
def legalOkTB (f : Function) : Bool :=
  (function128Cert f).toBool && (!mentions128 f || preBT f)

end Opt.Legalize128
