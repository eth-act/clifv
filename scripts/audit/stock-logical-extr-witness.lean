import FV.E2E.StockLogicalExtrMatchWitness
import FV.E2E.StockLogicalExtrWitness
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name,_) in env.constants.toList do
    if !(name.toString.contains "StockLogicalExtrWitness") then continue
    for ax in ← collectAxioms name do
      unless #[``propext,``Classical.choice,``Quot.sound,
        ``E2E.StockLogicalExtrWitness.checks_true._native.native_decide.ax_1,
        ``E2E.StockLogicalExtrWitness.match_checks_true._native.native_decide.ax_1].contains ax do
        throwError "unexpected axiom {ax} in {name}"
    count := count+1
  logInfo m!"STOCK_LOGICAL_EXTR_FIXED_WITNESS_AUDIT {count}"
