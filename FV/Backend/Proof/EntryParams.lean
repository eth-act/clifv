import FV.Clif.Syntax

/-!
# Entry parameters (an input condition of definite assignment)

`entryParamsB f`: the entry block has as many parameters as the signature (Cranelift's verifier
rule "entry block parameters must match the function signature"). `lowerFunction` defines the
entry block's parameters from the signature's parameter locations (`entryParams`: the block's
parameters zipped with `locsOf f.sig`), so a parameter beyond them would never be defined
(`E2E.not_spillDefinedHyp`). Executable, for the crate proofs' `native_decide`.
-/

namespace Backend.Proof.Spill

/-- The entry block has as many parameters as the signature. -/
def entryParamsB (f : Clif.Function) : Bool :=
  match f.blocks with
  | [] => true
  | B0 :: _ => B0.params.length == f.sig.params.length

end Backend.Proof.Spill
