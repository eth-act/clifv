import FV.Arm.MinTheory
import FV.E2E.LinkPlace

/-! Non-vacuity of the restored slotless `keepsPlace` lemmas: the empty program over the empty
environment meets every premise. -/

namespace Clif

theorem linkEnvN_keepsPlace_witness : EnvKeepsPlace (linkEnvN { funcs := [] } Env.empty 0) :=
  linkEnvN_keepsPlace (by simp) (by simp) (by intro n g h; simp [Env.empty] at h)

end Clif
