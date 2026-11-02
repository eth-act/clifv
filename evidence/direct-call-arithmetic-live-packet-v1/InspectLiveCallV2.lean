import FV.Backend.Lowering.StockArithmetic
import FV.Backend.LinearScan
import FV.Clif.Parse

open Backend
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def callerText : String := "function %stock_live_call_add(i64) -> i64 system_v {\n    fn0 = colocated %stock_clobber_add(i64) -> i64 system_v\nblock0(v7: i64):\n    v31 = call fn0(v7)\n    v79 = iadd v31, v7\n    return v79\n}\n"
def calleeText : String := "function %stock_clobber_add(i64) -> i64 system_v {\nblock0(v101: i64):\n    v109 = iconst.i64 13\n    v121 = iadd v101, v109\n    return v121\n}\n"

def main : IO Unit := do
  for text in [callerText,calleeText] do
    let parsed := Clif.parseFile text
    for pf in parsed.funcs do
      let f ← match pf.func with
        | .ok f => pure f
        | .error message => throw (IO.userError s!"{message}")
      let result ← match Stock.lower f with
        | .ok result => pure result
        | .error message => throw (IO.userError message)
      IO.println s!"FUNCTION {f.name}"
      for block in result.code.blocks do
        IO.println s!"CODE {repr block.insts}"
      for scan in result.blockScans do
        IO.println s!"SCANNED {repr scan.output.code}"
        for record in scan.output.records do
          IO.println s!"RECORD {record.inst}: {repr record.output.emitted}"
      for source in [7,31,79,101,121] do
        IO.println s!"VALUE {source}: {repr (result.ctx.valueReg? source)}"
      for cleanup in [false,true] do
        let prepared ← match prepare (Stock.Arithmetic.stage cleanup result.code) with
          | .ok prepared => pure prepared
          | .error message => throw (IO.userError message)
        let allocated ← match leanAlloc prepared with
          | .ok allocated => pure allocated
          | .error message => throw (IO.userError message)
        IO.println s!"ALLOC {cleanup}: {repr allocated}"
