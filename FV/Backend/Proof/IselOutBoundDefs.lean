import FV.Backend.Isel

/-!
# The outgoing-area input condition (S10g, #404)

`outBoundLe Bd f`: every `call`/`call_indirect` statement and every
`try_call`/`try_call_indirect` terminator of `f` passes at most `Bd` bytes on the stack
(`stackBytes` of the extern's signature, of the `call_indirect`'s signature, or of the exception
table's signature). Decidable on the CLIF function alone; `IselOutBoundRun` proves that it bounds
the outgoing area of `lowerFunction`'s VCode (`lowerFunction_outgoing_le`). `outBoundB` is the
bound 32560 bytes (what #514's frame needed for its save slots).
-/

namespace Backend.Proof.OutBound

open Backend

/-- **The outgoing-area input condition** (see the module doc). -/
def outBoundLe (Bd : Nat) (f : Clif.Function) : Bool :=
  f.blocks.all fun B =>
    B.body.all (fun st => match st.inst with
      | .call fn _ => match f.extern? fn with
        | some e => decide (stackBytes e.sig ≤ Bd)
        | none => true
      | .callIndirect sg _ _ => match f.sigDecls.lookup sg with
        | some s => decide (stackBytes s ≤ Bd)
        | none => true
      | _ => true) &&
    match B.term with
    | .tryCall _ _ et | .tryCallIndirect _ _ et => match f.sigDecls.lookup et.sig with
      | some s => decide (stackBytes s ≤ Bd)
      | none => true
    | _ => true

/-- `outBoundLe` for the bound 32560 bytes (what #514's frame needed for its save slots). -/
def outBoundB (f : Clif.Function) : Bool := outBoundLe 32560 f

end Backend.Proof.OutBound
