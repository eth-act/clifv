import FV.Backend.Lowering.StockReplay

/-! Native stress test for block scan and replay. Run with
`FV_MEMCAP=6G scripts/memcap.sh lake env lean --run FVTest/Backend/Lowering/ScanReplay.lean`.
One hundred thousand transitions exercise stack usage independently of ISLE.
Sparse emitted chunks check order without quadratic growth in the test data. -/

namespace StockScanReplayTest

open Backend Backend.Stock

def transition (i : Nat) (input : State) : Scan :=
  ⟨{ input with current := some i }, none,
    if i % 100 == 0 then #[.jump i] else #[]⟩

def exec (i : Nat) (input : State) : Except String Scan := .ok (transition i input)

def checker (i : Nat) (input : State) (scan : Scan) : Bool :=
  decide (transition i input = scan)

def run : IO Unit := do
  let input : State := default
  let indices := (List.range 100000).reverse
  let .ok output := runScans exec indices input | throw (IO.userError "scan failed")
  unless output.records.length == 100000 && output.code.size == 1000 &&
      output.state.current == some 0 && output.code[0]? == some (.jump 0) &&
      output.code[999]? == some (.jump 99900) do
    throw (IO.userError "scan length, state or chunk order differs")
  unless checkScans checker indices input output do
    throw (IO.userError "replay rejected scan")
  let first := output.records.head!
  let second := output.records.tail.head!
  let broken := { second with input := input }
  let changedLink := { output with records := first :: broken :: output.records.drop 2 }
  for changed in [
      { output with state := input },
      { output with records := output.records.tail },
      { output with records := output.records.reverse },
      { output with code := output.code.reverse },
      changedLink] do
    if checkScans checker indices input changed then
      throw (IO.userError "replay accepted a changed certificate")
  IO.println "100000 transitions, 1000 chunks: replay accepts; five changed certificates rejected"

end StockScanReplayTest

def main : IO Unit := StockScanReplayTest.run
