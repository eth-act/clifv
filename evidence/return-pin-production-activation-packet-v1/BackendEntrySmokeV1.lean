import FVTest.Backend.Main
import FV.E2E.ReturnPinProductionWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
#eval do
  let dir : System.FilePath := "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/return-pin-production-activation-packet-v1/entrypoint-smoke-v1"
  IO.FS.createDirAll dir
  let original := String.join (E2E.PreparedReturnPinCallsWitness.input.funcs.map (·.clif))
  let mixed := original ++ "\nfunction %float_leaf(f64) -> f64 {\nblock0(v0: f64):\n return v0\n}\n"
  for (name,src) in [("original",original),("mixed",mixed)] do
    let input := dir / (name ++ ".clif")
    IO.FS.writeFile input src
    for cleanup in [false,true] do
      let label := name ++ (if cleanup then "-cleanup" else "-raw")
      let output := dir / (label ++ ".o")
      let code ← main [input.toString,output.toString,"--regalloc","lean",
        if cleanup then "--dead-cleanup" else "--no-dead-cleanup"]
      unless code == 0 do throw (IO.userError s!"production CLI failed: {label}: {code}")
      let pf := (Opt.Legalize128.parsedFile128 (Clif.parseFile src)).file
      let expected := Id.run (Backend.compileFileReturnPinWhen true
        (fun vcs => pure (Backend.allocateLean vcs)) pf [] cleanup)
      let bytes ← IO.FS.readBinFile output
      let .ok wanted := expected.object | throw (IO.userError s!"expected object failed: {label}")
      unless bytes == wanted do throw (IO.userError s!"actual CLI bytes differ: {label}")
      if name == "mixed" then
        let previous := Id.run (Backend.compileFileMemoryCapturedCopyNIWhen true
          (fun vcs => pure (Backend.allocateLean vcs)) pf [] cleanup)
        unless expected.object == previous.object do throw (IO.userError s!"complete previous bytes differ: {label}")
      IO.println s!"ACTUAL BACKEND {label}: object bytes exact"
