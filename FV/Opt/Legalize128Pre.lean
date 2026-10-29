module

public import FV.Opt.Legalize128Pass

@[expose] public section

/-!
# `Opt.Legalize128`: the decidable source domain (S6)

`preB f`: the preconditions `Opt.Legal.Complete.Pre f` of the validator's completeness, decided
on `f` alone (`Opt.Legal.Complete.preB_iff`, `FV/Opt/Proof/LegalPre.lean`): `f` mentions `i128`,
its definitions are distinct, every value id is below `maxValueId f`, no statement reads its own
result, no `call_indirect` has an `i128` signature, no `try_call_indirect`. `preBW f` decides
`Opt.Legal.Complete.PreW f` (the same without the two indirect-call conditions; the validator
`Opt.Legal.checkW` accepts such calls).

`legalOkB f`: the source domain of one function — the pass succeeds (`function128Cert f = .ok _`)
and either `f` does not mention `i128` (the pass is the identity) or `preB f` holds (the
legalisation is proven correct without a validator premise, `Opt.Legal.legalize_refines`).

`legalize f`: the function the pass gives for `f` (`f` itself when the pass fails, as
`parsedFile128` keeps it).

Kept free of proofs so that the driver can evaluate them.
-/

namespace Opt.Legalize128

open Clif Opt.Legal

/-- **The decidable `Opt.Legal.Complete.PreW`** (`Opt.Legal.Complete.preBW_iff`). -/
def preBW (f : Function) : Bool :=
  mentions128 f && decide (((defsOf f).map (·.1)).Nodup) &&
  (idsOf f).all (· < maxValueId f) &&
  f.blocks.all (fun b => b.body.all fun s => (instOps s.inst).all fun x => !s.results.contains x)

/-- **The decidable `Opt.Legal.Complete.Pre`** (`Opt.Legal.Complete.preB_iff`). -/
def preB (f : Function) : Bool :=
  mentions128 f && decide (((defsOf f).map (·.1)).Nodup) &&
  (idsOf f).all (· < maxValueId f) &&
  f.blocks.all (fun b => b.body.all fun s => (instOps s.inst).all fun x => !s.results.contains x) &&
  f.blocks.all (fun b => b.body.all fun s => match s.inst with
    | .callIndirect sig _ _ => match f.sigDecls.lookup sig with
      | some d => !sig128 d
      | none => true
    | _ => true) &&
  f.blocks.all (fun b => match b.term with
    | .tryCallIndirect .. => false
    | _ => true)

/-- The function the pass gives for `f` (`f` itself when it fails). -/
def legalize (f : Function) : Function :=
  match function128Cert f with
  | .ok (g, _) => g
  | .error _ => f

/-- **The source domain of one function**: the pass succeeds, and it is the identity (`f` does
not mention `i128`) or its result is proven correct (`preB`). -/
def legalOkB (f : Function) : Bool :=
  (function128Cert f).toBool && (!mentions128 f || preB f)

end Opt.Legalize128
