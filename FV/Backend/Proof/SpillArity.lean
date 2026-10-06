import FV.Backend.Proof.DriverCheck

/-!
# Branch arity (an input condition of the spill allocator's CFG facts, V4)

`ArityOk f`: every destination of a `jump`/`brif`/`br_table` passes as many arguments as its
target block has parameters (Cranelift's verifier rule). `lowerFunction` checks the count only
for destinations with arguments (`blockArgRegs`); an argument-less `brif`/`br_table` edge goes
straight to its target, so without this condition a block without branch arguments could have a
successor with parameters (`EdgesOk.noArgs` fails). `arityOkB` decides it (`arityOk_of`).
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof.Driver

/-- **Branch arity**: every branch destination's argument count is its target's parameter
count. -/
def ArityOk (f : Clif.Function) : Prop :=
  ∀ B ∈ f.blocks, ∀ bc ∈ dests B.term, ∀ tb, f.block? bc.block = some tb →
    tb.params.length = bc.args.length

/-- `ArityOk`, decided. -/
def arityOkB (f : Clif.Function) : Bool :=
  f.blocks.all fun B => (dests B.term).all fun bc => match f.block? bc.block with
    | some tb => tb.params.length == bc.args.length
    | none => true

theorem arityOk_of {f : Clif.Function} (h : arityOkB f = true) : ArityOk f := by
  intro B hB bc hbc tb htb
  have := List.all_eq_true.mp (List.all_eq_true.mp h B hB) bc hbc
  rw [htb] at this
  simpa using this

end Backend.Proof.Spill
