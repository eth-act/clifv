import FV.Backend.Proof.IselFamily
import FV.Backend.Proof.StockScopePartition

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

open Isle Isle.Aarch64 in
/-- The old `stock_source_root_partition_counts` (192 source-closure roots, 325 excluded) is
false: the `fcopysign` root `rule_lower_685` (id 712) is a closure root now (193/324). -/
theorem stock_source_root_partition_counts_old_false :
    ¬ ((program.rulesOf TId.lower).length = 517 ∧
      Backend.Stock.Proof.sourceClosureRoots.length = 192 ∧
      Backend.Stock.Proof.excludedSourceRoots.length = 325) := fun h => by
  have := Backend.Stock.Proof.stock_source_root_partition_counts
  omega

open Isle Isle.Aarch64 in
/-- The old `stock_source_root_partition_witness` (with 192/325) is false, for the same reason. -/
theorem stock_source_root_partition_witness_old_false :
    ¬ (rule_lower_53 ∈ Backend.Stock.Proof.sourceClosureRoots ∧
      rule_lower_58 ∈ Backend.Stock.Proof.excludedSourceRoots ∧
      (program.rulesOf TId.lower).length = 517 ∧
      Backend.Stock.Proof.sourceClosureRoots.length = 192 ∧
      Backend.Stock.Proof.excludedSourceRoots.length = 325) := fun h =>
  stock_source_root_partition_counts_old_false h.2.2

end Backend.Proof.FloatCopysignWitness
