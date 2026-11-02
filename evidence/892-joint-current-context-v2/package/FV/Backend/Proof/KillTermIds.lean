import FV.Isle.Generated.Program
import FV.Isle.Interp

set_option Elab.async false

/-! Facts about the exported program's term table, for the killed-vreg proofs (`KillTab`,
`KillDriver`) and their users: `termOf` reads `program.term?`, and every term's id is its index.
Their own module, so that their users need not wait for `KillTab`'s kernel checks. -/

namespace Backend.Proof.Kill

open Backend Backend.Proof Isle Isle.Interp Isle.Aarch64

theorem termOf_program_eq {t : TermId} {term : Term} (h : termOf program t = .ok term) :
    program.term? t = some term := by
  unfold termOf at h
  split at h
  · rename_i term' h'
    cases h
    exact h'
  · cases h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
set_option cbv.maxSteps 4000000 in
theorem termIds_ok : (List.range program.terms.size).all
    (fun i => (program.term? i).all (·.id == i)) = true := by
  decide_cbv

/-- A term of the program has its index as id. -/
theorem termOf_id_eq {t : TermId} {term : Term} (h : termOf program t = .ok term) : term.id = t := by
  have ht := termOf_program_eq h
  have hlt : t < program.terms.size := by
    unfold Program.term? at ht
    exact (Array.getElem?_eq_some_iff.mp ht).1
  have := List.all_eq_true.mp termIds_ok t (List.mem_range.mpr hlt)
  rw [ht] at this
  simpa using this

end Backend.Proof.Kill
