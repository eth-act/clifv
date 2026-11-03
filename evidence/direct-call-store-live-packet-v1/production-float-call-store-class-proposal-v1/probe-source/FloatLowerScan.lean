import FV.Clif.Parse
import FV.Backend.Proof.StockAliasSemantics

open Backend Backend.Stock.Proof

def main : IO Unit := do
  let files : List String := ["/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-store-live-packet-v1/original-caller.clif", "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-store-live-packet-v1/original-callee.clif", "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-store-live-packet-v1/float-call-store-fixture-source-v1/caller.clif", "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-store-live-packet-v1/float-call-store-fixture-source-v1/callee.clif"]
  for path in files do
    IO.println s!"fixture {path}"
    let program ← match Clif.parse (← IO.FS.readFile path) with
      | .error message => throw (IO.userError message)
      | .ok program => pure program
    IO.println s!"parsed-functions {program.funcs.length}"
    for function in program.funcs do
      let result ← match Backend.Stock.lower function with
        | .error message => throw (IO.userError message)
        | .ok result => pure result
      IO.println s!"lowered {reprStr result.code}"
      IO.println s!"final-alias {reprStr result.final.alias}"
      for event in result.blockScans do
        IO.println s!"block {event.block} scan {reprStr event.output.code}"
        for value in [7,11,31] do
          IO.println s!"value {value} register {reprStr (event.ctx.valueReg? value)}"
        match event.ctx.valueReg? 7, event.output.code.toList with
        | some (.vreg pointer pointerClass), .call info :: _ =>
          for definition in info.defs do
            match definition.2 with
            | .vreg destination destinationClass =>
              let pointerRoot := aliasNum result.final.alias pointer
              let destinationRoot := aliasNum result.final.alias destination
              IO.println s!"call-physical {reprStr definition.1}"
              IO.println s!"pointer-class {reprStr pointerClass} result-class {reprStr destinationClass}"
              IO.println s!"pointer-root {pointerRoot} result-root {destinationRoot} distinct {pointerRoot != destinationRoot}"
            | _ => pure ()
        | _, _ => pure ()
