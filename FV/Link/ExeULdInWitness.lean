module

public import FV.Link.ExeULdIn
public import FV.Link.ExeLdInWitness

@[expose] public section

/-! # Witness: `compileExeU_total_ldIn`'s premises hold together (S10g, #404)

On `Link.DeadCleanup.LdInWitness`'s link inputs (`_start` and the region object of `%add1`):
`compileExe_total_ldIn`'s premises and `unwCondsB` of the compiled functions hold
(`native_decide`), so `compileExeU_total_ldIn` applies.
-/

namespace Link.DeadCleanup.ULdInWitness

open Link Link.Ld E2E E2E.LinkCheck Link.DeadCleanup.LdInWitness

/-- `compileExeU_total_ldIn`'s premises, decided on the inputs. -/
def premisesUB : Bool :=
  match resolve (o.entry :: o.undefs) ins with
  | .ok st => match st.gc (o.entry :: o.undefs) o.gc with
    | .ok g => layRefsB o st g && relsInB o st g && fitsB o st g && specPreB (ldSpec S0 o st g) o st g &&
        InScopeIn (ldSpec S0 o st g).input0 && (ldSpec S0 o st g).layoutOkB &&
        (ldSpec S0 o st g).reachOkB &&
        EhCheck.Complete.unwCondsB (parResultsCleanupT (ldSpec S0 o st g).input0)
    | .error _ => false
  | .error _ => false

theorem premisesU : premisesUB = true := by native_decide

/-- **`compileExeU_total_ldIn`'s premises hold together on real link inputs**. -/
theorem compileExeU_total_ldIn_witness :
    ∃ st g, ∃ r, link o ins = .ok r ∧ ∃ file, compileExe (ldSpec S0 o st g) r.img.write = .ok file ∧
      (EhCheck.ehOkR (parResultsCleanupT (ldSpec S0 o st g).input0) file = true →
        compileExeU (ldSpec S0 o st g) r.img.write = .ok file) := by
  have h := premisesU
  unfold premisesUB at h
  split at h
  · rename_i st hres
    split at h
    · rename_i g hgc
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨hrefs, hrels⟩, hfit⟩, hsp⟩, hin⟩, hl⟩, hreach⟩, hU⟩ := h
      obtain ⟨r, hr, hc, hu⟩ :=
        compileExeU_total_ldIn (S := S0) hres hgc hrefs hrels hfit hsp hin hl hreach hU
      exact ⟨st, g, r, hr, _, hc, hu⟩
    · cases h
  · cases h

end Link.DeadCleanup.ULdInWitness
