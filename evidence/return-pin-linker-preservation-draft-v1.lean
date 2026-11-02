namespace Link.ReturnPinCompilerWith
open Backend E2E E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false
variable {lower : ProductionLowering}

/-- Keep every successful previous attempt with the same complete linked bytes. -/
theorem accepts_previous {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (previous : SemanticCompilerWith.attempt lower S file0 cleanup = .ok file) :
    attempt lower S file0 cleanup = .ok file := by
  cases cleanup <;> simp only [attempt,SemanticCompilerWith.attempt] at previous ⊢
  all_goals
    split at previous
    · cases previous
    · rename_i scope
      rw [if_neg scope]
      split at previous
      · rename_i checked
        have accepted := ReturnPinBinary.okB_previous checked
        rw [if_pos accepted]
        exact previous
      · cases previous

#print axioms accepts_previous
end Link.ReturnPinCompilerWith
