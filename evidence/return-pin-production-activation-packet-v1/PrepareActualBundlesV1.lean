import FV.Front.Read
import FV.E2E.ProductionBoundaryWitness
import FV.E2E.PreparedReturnPinCallsWitness
import FV.Backend.Lowering.StockVoidCallNI

open Backend E2E E2E.LinkCheck Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def main (args : List String) : IO Unit := do
  let root : System.FilePath := args.headD "/tmp/worker-o-bundles"
  IO.FS.createDirAll root
  let mut cases : Array Json := #[]
  for cleanup in [false,true] do
    for captured in [false,true] do
      let fis : List FnInput := if captured then PreparedReturnPinCallsWitness.input.funcs
        else ProductionBoundaryWitness.initial.funcs
      let label := "WorkerOActual" ++ (if captured then "Captured" else "Previous") ++
        (if cleanup then "Cleanup" else "Raw")
      let dir := root / label
      IO.FS.createDirAll dir
      let initial : Link.LinkSpec := {funcs := fis,names := [],sizes := [],outside := [],
        symNames := fis.map (fun fi => fi.func.name),R := 0x200160}
      let S := initial.placedProductionWith Stock.VoidCall.NI.lowerValidated cleanup
      let image ← match Link.Ld.assemble (ProductionBoundaryWitness.plan S) with
        | .ok image => pure image.write
        | .error msg => throw (IO.userError msg)
      let exe := dir / "program.elf"
      IO.FS.writeBinFile exe image
      let mut functions : Array Json := #[]
      for (fi,index) in fis.zipIdx do
        let dump := dir / s!"fn{index}.clif"
        let ra := dir / s!"fn{index}.ra.json"
        IO.FS.writeFile dump fi.clif
        IO.FS.writeFile ra fi.ra
        functions := functions.push (Json.mkObj [("name",toJson fi.func.name),
          ("dump",toJson dump.toString),("ra",toJson ra.toString)])
      let data := dir / "data.txt"
      IO.FS.writeFile data ""
      let bundle := Json.mkObj [("format",toJson "clifv-frontend-bundle"),("version",toJson (2:Nat)),
        ("exe",toJson exe.toString),("units",Json.arr #[Json.mkObj [("tag",toJson label),
          ("functions",Json.arr functions),("data",toJson data.toString),
          ("locals",toJson ([] : List (String × String))),("names",Json.mkObj []),
          ("local_addrs",toJson ([] : List (String × Nat)))]]),
        ("symbols",toJson S.addrs),("markers",toJson S.addrs),
        ("skipped",toJson ([] : List (String × String)))]
      IO.FS.writeFile (dir / "bundle.json") bundle.pretty
      let (b,_) ← Front.readBundle dir []
      let .ok assembled := Front.assemble b | throw (IO.userError s!"bundle parse failed: {label}")
      unless assembled.funcs.map (·.func) == fis.map (·.func) do
        throw (IO.userError s!"original function changed through actual bundle reader: {label}")
      let input := dir / "input.clif"
      IO.FS.writeFile input (String.join (fis.map (·.clif)))
      cases := cases.push (Json.mkObj [("module",toJson label),("cleanup",toJson cleanup),
        ("captured",toJson captured),("dir",toJson dir.toString),("exe",toJson exe.toString),
        ("input",toJson input.toString),("entries",toJson (fis.map (·.func.name)))])
  IO.FS.writeFile (root / "manifest.json") (Json.arr cases).pretty
