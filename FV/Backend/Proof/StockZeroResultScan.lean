import FV.Backend.Proof.StockPolicy
import FV.Backend.Proof.IselGeneric
import FV.Arm.MinTheory
import FV.Backend.Proof.IselInterp
import FV.Backend.Proof.PrepareCheck

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- An ordinary unsunk instruction with no results and no mandatory effect
is omitted independently of register demand or opportunistic definitions. -/
theorem scan_zero_results {ctx : Ctx} {block i ti : Nat} {isBranch : Bool} {input : State}
    (safe : input.sunk[i]! = false) (ordinary : i ≠ ti)
    (results : ctx.insts[i]!.results = []) (quiet : ctx.insts[i]!.clif.any mustLower = false) :
    scanInstruction ctx block i ti isBranch input = .ok
      ⟨scanState input i,some ⟨block,i,.omitted,scanState input i,scanState input i,[],[],#[]⟩,#[]⟩ := by
  simp [scanInstruction,safe,ordinary,results,quiet]

private def nopCtx : Ctx := {sinkCtx with insts := #[⟨.op .unit,[],[],some .nop⟩]}

/-- A real nop and its full scan state inhabit zero-result omission. -/
theorem scan_zero_results_witness :
    scanInstruction nopCtx 0 0 1 false sinkState = .ok
      ⟨scanState sinkState 0,some ⟨0,0,.omitted,scanState sinkState 0,scanState sinkState 0,[],[],#[]⟩,#[]⟩ :=
  scan_zero_results rfl (by decide) rfl rfl

end Backend.Stock.Proof
