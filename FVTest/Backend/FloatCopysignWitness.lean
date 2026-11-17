import FV.Backend.Proof.IselFamily

/-!
# #35 `fcopysign`: witnesses

The statements restated under their names because `instData` (and its name mirror
`fFmt`/`fOpc`) now builds `Binary`/`Fcopysign` for an `fcopysign.f32/f64`: their old forms are
false.
-/

namespace Backend.Proof.FloatCopysignWitness

open Backend Backend.Proof

/-- The old `fOpc_mem` (without `"Fcopysign"`) is false: `fOpc .fcopysign = "Fcopysign"`. -/
theorem fOpc_mem_old_false :
    ¬ ∀ op : Clif.FOp, fOpc op ∈ ["Fadd", "Fsub", "Fmul", "Fdiv", "Fmin", "Fmax", "Sqrt", "Fneg",
      "Fabs", "Fpromote", "Fdemote", "Ceil", "Floor", "Trunc", "Nearest", "FcvtFromUint",
      "FcvtFromSint", "FcvtToUintSat", "FcvtToSintSat", "Fcmp", ""] := fun h => by
  have := h .fcopysign
  simp [fOpc] at this

/-- The old `fOpc_eq_false` is false at `op = .fcopysign`, `s = "Fcopysign"`. -/
theorem fOpc_eq_false_old_false :
    ¬ ∀ {op : Clif.FOp} {s : String}, s ∉ ["Fadd", "Fsub", "Fmul", "Fdiv", "Fmin", "Fmax",
      "Sqrt", "Fneg", "Fabs", "Fpromote", "Fdemote", "Ceil", "Floor", "Trunc", "Nearest",
      "FcvtFromUint", "FcvtFromSint", "FcvtToUintSat", "FcvtToSintSat", "Fcmp", ""] →
      (fOpc op = s ↔ False) := fun h =>
  (@h .fcopysign "Fcopysign" (by decide)).mp rfl

/-- The old `eq_fOpc_false` is false at `op = .fcopysign`, `s = "Fcopysign"`. -/
theorem eq_fOpc_false_old_false :
    ¬ ∀ {op : Clif.FOp} {s : String}, s ∉ ["Fadd", "Fsub", "Fmul", "Fdiv", "Fmin", "Fmax",
      "Sqrt", "Fneg", "Fabs", "Fpromote", "Fdemote", "Ceil", "Floor", "Trunc", "Nearest",
      "FcvtFromUint", "FcvtFromSint", "FcvtToUintSat", "FcvtToSintSat", "Fcmp", ""] →
      (s = fOpc op ↔ False) := fun h =>
  (@h .fcopysign "Fcopysign" (by decide)).mp rfl

end Backend.Proof.FloatCopysignWitness
