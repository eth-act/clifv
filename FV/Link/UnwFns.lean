import FV.Link.Image
import FV.Backend.Proof.LowerSimUCheck
import FV.E2E.RegLevelUTry
import FV.E2E.RegLevelCallSite
import FV.E2E.RegLevelFrameSaved

/-!
# The per-function unwinding checks of the compiled functions (S10f)

`E2E.LinkSysU.OkU`'s per-function premises, decided at link time on the compiled functions `R`
(`unwFnsB`, one task per function): the lowering's unwinding validator (`unwCheck`; with the
pipeline's `lowerCheck`, `lowerCheckU`), the call-site and row tables (`callSites`,
`unwindRows`), the landing pads at non-zero offsets (`padsNonzeroB`), the frame's saved registers
(`savedCheck`). Since #622 the calls of the last block need no check (`siteAt_any`): `fnUnwB` no
longer decides `lastCallsOk`, and `unwFnsB_sound` (statement changed with the check; name kept)
no longer concludes it.
-/

namespace Link.EhCheck

set_option autoImplicit false

open E2E E2E.LinkCheck Backend Backend.Proof Backend.Proof.Driver

/-- The unwinding checks of the compiled function `a` of `g`. -/
def fnUnwB (g : Clif.Function) (a : Art) : Bool :=
  unwCheck g a.vc && (callSites a.af a.fa).toBool && (unwindRows a.af a.fa).toBool &&
    padsNonzeroB a.af a.fa && savedCheck a.vcp a.rf

/-- **The unwinding checks of every compiled function** (in parallel, `Link.parMap`). -/
def unwFnsB (R : Res) : Bool := (parMap (fun g => fnUnwB g (artOf R g)) (progOf R).funcs).all id

theorem ok_of_toBool {ε α : Type} {e : Except ε α} (h : e.toBool = true) : ∃ x, e = .ok x := by
  cases e with
  | error _ => cases h
  | ok x => exact ⟨x, rfl⟩

/-- What `unwFnsB` decides. -/
theorem unwFnsB_sound {R : Res} (h : unwFnsB R = true) {g : Clif.Function}
    (hg : g ∈ (progOf R).funcs) :
    unwCheck g (artOf R g).vc = true ∧
      (∃ l, callSites (artOf R g).af (artOf R g).fa = .ok l) ∧
      (∃ rows, unwindRows (artOf R g).af (artOf R g).fa = .ok rows) ∧
      padsNonzeroB (artOf R g).af (artOf R g).fa = true ∧
      savedCheck (artOf R g).vcp (artOf R g).rf = true := by
  rw [unwFnsB, parMap_eq, List.all_map] at h
  have hf := List.all_eq_true.1 h g hg
  simp only [Function.comp_apply, id, fnUnwB, Bool.and_eq_true] at hf
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h6⟩ := hf
  exact ⟨h1, ok_of_toBool h2, ok_of_toBool h3, h4, h6⟩

end Link.EhCheck
