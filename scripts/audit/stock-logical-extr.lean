import FV.Backend.Proof.StockLogicalExtrValuesWitness
import FV.Backend.Proof.StockLogicalExtrMatch
import FV.Backend.Proof.StockLogicalExtrSemantics
import FV.Backend.Proof.StockLogicalExtrRhs
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name,_) in env.constants.toList do
    if !(name.toString.contains "LogicalExtr") then continue
    for ax in ← collectAxioms name do
      unless #[``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {name}"
    count := count+1
  logInfo m!"STOCK_LOGICAL_EXTR_CORE_STANDARD_ONLY {count}"
