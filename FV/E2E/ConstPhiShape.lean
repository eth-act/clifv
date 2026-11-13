import FV.E2E.OptX
import FV.Opt.Proof.ConstPhiSimU

/-!
# Constant-phi removal keeps the shape (#990): `Opt.ConstPhi.run_shape`

`E2E.ShapeFacts f (Opt.ConstPhi.run f)`: the pass keeps what the backend's and the linker's
theorems read of a function, as the mid-end does (`E2E.optimizeExe_shape`): the header and the
signature declarations, the backend subset E, the callees (`Opt.ConstPhi.runCore_facts`), and,
by the guard of `run` (`Opt.keepsShapeB`), the `try_call` callees, the indirect-call signatures
and the presence of `return_call` and indirect calls.
-/

namespace Opt.ConstPhi

open E2E

/-- **The pass keeps the shape.** -/
theorem run_shape (f : Clif.Function) : ShapeFacts f (run f) := by
  show ShapeFacts f (if keepsShapeB f (runCore f) then runCore f else f)
  split
  · rename_i hk
    have hF := runCore_facts f
    obtain ⟨h1, h2, h3, h4, h5⟩ := keepsShapeB_spec hk
    exact ⟨hF.name, hF.sig, hF.slots, hF.externs, runCore_sigDecls f, hF.subsetE, hF.callees,
      h1, h2, h3, h4, h5⟩
  · exact ShapeFacts.refl f

end Opt.ConstPhi
