import FV.Link.ReturnPinCompileDefs
import FV.Front.Read
import FV.E2E.ProductionBoundaryWitness
import FV.Backend.Lowering.StockResultCallRoutes
import FV.Backend.Proof.StockDirectCallResultFixture

open Backend E2E E2E.LinkCheck Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def originalCaller : FnInput := { clif := "function %stock_source_call_result(i64) -> i64 system_v {\n    fn0 = colocated %stock_source_identity(i64) -> i64 system_v\nblock0(v7: i64):\n    v31 = call fn0(v7)\n    return v31\n}\n", ra := "null" }
def originalCallee : FnInput := { clif := "function %stock_source_identity(i64) -> i64 system_v {\nblock0(v101: i64):\n    return v101\n}\n", ra := "null" }
def originalFloat : FnInput := { clif := "function %float_leaf(f64) -> f64 {\nblock0(v0: f64):\n return v0\n}\n", ra := "null" }

def main (args : List String) : IO Unit := do
  let root : System.FilePath := args.headD "/tmp/worker-o-bundles"
  IO.FS.createDirAll root
  let mut cases : Array Json := #[]
  for cleanup in [false,true] do
    for typed in [false,true] do
      unless originalCaller.func == Stock.Proof.DirectCallResultFixture.caller &&
          originalCallee.func == Stock.Proof.DirectCallResultFixture.callee do
        throw (IO.userError "Original caller or callee changed")
      let fis : List FnInput := [originalCaller,originalCallee] ++ if typed then [originalFloat] else []
      let label := "WorkerOResultCall" ++ (if typed then "Typed" else "Pair") ++
        (if cleanup then "Cleanup" else "Raw")
      let dir := root / label
      IO.FS.createDirAll dir
      let initial : Link.LinkSpec := {
        funcs := fis
        names := []
        sizes := []
        outside := []
        symNames := fis.map (fun fi => fi.func.name)
        R := 0x200160 }
      let S := initial.placedProductionWith Stock.ResultCall.lowerValidated cleanup
      let image ← match Link.Ld.assemble (ProductionBoundaryWitness.plan S) with
        | .ok image => pure image.write
        | .error msg => throw (IO.userError msg)
      let exe := dir / "program.elf"
      IO.FS.writeBinFile exe image
      let mut functions : Array Json := #[]
      for (fi,index) in fis.zipIdx do
        let dump := dir / s!"fn{index}.clif"
        let ra := dir / s!"fn{index}.ra.json"
        let raw := (fis.zipIdx).foldl (fun text (entry,index) =>
          text.replace ("%" ++ entry.func.name) s!"u0:{index}") fi.clif
        let declarations := String.join ((fis.zipIdx).map fun (entry,index) =>
          s!"; decl u0:{index} func Export \"{entry.func.name}\"\n")
        IO.FS.writeFile dump (raw ++ "; clifv-extnames 1\n" ++ declarations ++ "; end clifv-extnames\n")
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
      let assembled ← match Front.assemble b with
        | .ok a => pure a
        | .error msg => throw (IO.userError s!"bundle parse failed: {label}: {msg}")
      unless assembled.funcs.map (·.func) == fis.map (·.func) do
        throw (IO.userError s!"original function changed through actual bundle reader: {label}")
      let input := dir / "input.clif"
      IO.FS.writeFile input (String.join (fis.map (·.clif)))
      cases := cases.push (Json.mkObj [("module",toJson label),("cleanup",toJson cleanup),
        ("typed",toJson typed),("dir",toJson dir.toString),("exe",toJson exe.toString),
        ("input",toJson input.toString),("entries",toJson (fis.map (·.func.name)))])
  IO.FS.writeFile (root / "manifest.json") (Json.arr cases).pretty
