import FV.Compile.SubsetT
import FV.Backend.Proof.IselContract

/-! `TermIntPos`, for the typed terminator facts (`IselTermFactsTy`) and the typed lowering
contract (`LowerContractT`). Its own module, so that the latter need not wait for the former. -/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-- The operands of terminator `t` in integer positions (a `brif` condition, a `br_table`
index, a `try_call`'s callee and arguments) are in integer positions of `ctx`. -/
def TermIntPos (ctx : Ctx) (t : Clif.Terminator) : Prop :=
  ∀ x ∈ Compile.termIntOperands t, IntPos ctx x

end Backend.Proof
