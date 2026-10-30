import FV.Link.UnwCondIn
import FV.Link.ExeLdInWitness

/-! # Witness: `compileExeU_total_ldCond`'s premises hold together (S10g, #404)

On `Link.DeadCleanup.LdInWitness`'s link inputs: `compileExe_total_ldIn`'s premises and
`unwCondsInB` of the compiled functions hold (`native_decide`).
-/

namespace Link.DeadCleanup.ULdCondWitness

open Link Link.Ld E2E E2E.LinkCheck Link.DeadCleanup.LdInWitness

/-- `compileExeU_total_ldCond`'s premises, decided on the inputs. -/
def premisesCB : Bool :=
  match resolve (o.entry :: o.undefs) ins with
  | .ok st => match st.gc (o.entry :: o.undefs) o.gc with
    | .ok g => layRefsB o st g && relsInB o st g && fitsB o st g && specPreB (ldSpec S0 o st g) o st g &&
        InScopeIn (ldSpec S0 o st g).input0 && (ldSpec S0 o st g).layoutOkB &&
        (ldSpec S0 o st g).reachOkB &&
        EhCheck.Complete.unwCondsInB (parResultsCleanupT (ldSpec S0 o st g).input0)
    | .error _ => false
  | .error _ => false

theorem premisesC : premisesCB = true := by native_decide

/-- **`compileExeU_total_ldCond`'s premises hold together on real link inputs**. -/
theorem compileExeU_total_ldCond_witness :
    ∃ st g, ∃ r, link o ins = .ok r ∧ ∃ file, compileExe (ldSpec S0 o st g) r.img.write = .ok file ∧
      (EhCheck.ehOkR (parResultsCleanupT (ldSpec S0 o st g).input0) file = true →
        compileExeU (ldSpec S0 o st g) r.img.write = .ok file) := by
  have h := premisesC
  unfold premisesCB at h
  split at h
  · rename_i st hres
    split at h
    · rename_i g hgc
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨hrefs, hrels⟩, hfit⟩, hsp⟩, hin⟩, hl⟩, hreach⟩, hU⟩ := h
      obtain ⟨r, hr, hc, hu⟩ :=
        compileExeU_total_ldCond (S := S0) hres hgc hrefs hrels hfit hsp hin hl hreach hU
      exact ⟨st, g, r, hr, _, hc, hu⟩
    · cases h
  · cases h

end Link.DeadCleanup.ULdCondWitness
