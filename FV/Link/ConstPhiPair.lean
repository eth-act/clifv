import FV.Link.OptFacts
import FV.E2E.ConstPhiShape

/-!
# Constant-phi removal as a pair of the executable compiler's input (#990)

`Link.OptPair f (Opt.ConstPhi.run f)`: the pass's output simulates its input
(`Opt.ConstPhi.run_simX`) and keeps its shape (`Opt.ConstPhi.run_shape`), as the mid-end's
(`FnInput.opt_pair`); the linked-program composition reads only this pair.
-/

namespace Opt.ConstPhi

/-- **The pass's output and input are an `OptPair`.** -/
theorem run_pair (f : Clif.Function) : Link.OptPair f (run f) :=
  ⟨run_simX f, run_shape f⟩

end Opt.ConstPhi
