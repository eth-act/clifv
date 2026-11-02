import Lean

/-!
# Simp set for the isel proofs

`isel_data`: generated facts about the exported ISLE program (`FV/Backend/Proof/IselData.lean`:
`program.term?`, `program.rulesOf`, term fields) and the extern-helper lemmas
(`FV/Backend/Proof/IselExtern.lean`). Symbolic execution of the interpreter uses
`simp only [isel_data, …]` so that no proof ever unfolds `Isle.Aarch64.program`.
-/

register_simp_attr isel_data

/-- Monad laws and propositional/`Nat` literal normalisation used between interpreter steps. -/
register_simp_attr isel_monad
