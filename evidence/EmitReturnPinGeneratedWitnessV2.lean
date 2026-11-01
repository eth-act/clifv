import FVTest.E2E.ReturnPinLinkProofWith
import FV.Link.ReturnPinRetryWitness

open Backend E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Lean
set_option autoImplicit false

/-- Generate proofs from the actual unchanged linked caller/callee fixture. -/
def main (args : List String) : IO Unit := do
  let root : System.FilePath := args.headD "/tmp/worker-o-return-pin-generated"
  IO.FS.createDirAll root
  let mut manifest : Array Json := #[]
  for cleanup in [false,true] do
    for mixed in [false,true] do
      let I : SemanticStackBound.CompilerInput := if mixed then
          Link.ReturnPinCompilerWith.input Link.ReturnPinRetryWitness.lower
            (Link.ReturnPinRetryWitness.spec cleanup) cleanup
        else ProductionBoundaryWitness.input cleanup
      let image := if mixed then Link.ReturnPinRetryWitness.file cleanup else ProductionBoundaryWitness.file cleanup
      let entry := if mixed then "sret_caller" else ProductionBoundaryWitness.name
      let lower := if mixed then "Backend.Stock.VoidCall.NI.lowerValidated" else "Backend.Stock.Production.lower"
      let index := symIndex image
      let cert := I.addrs.filterMap fun p => (index.get? (symName p.1,p.2)).map (p.1,·)
      for split in (if mixed then [false,true] else [false]) do
        let limit := if split then 1 else sliceSize
        let count := max ((I.funcs.length + limit - 1) / limit) 1
        let ex : Excerpt := [(0,image)]
        let bg : BinGen := ⟨ex,List.replicate count ex,ex,ex,cert,[]⟩
        for allStack in [false,true] do
          let label := "WorkerOReturnPinGenerated" ++ (if mixed then "Mixed" else "Previous") ++
            (if cleanup then "Clean" else "Raw") ++ (if split then "Split" else "Single") ++
            (if allStack then "All" else "Entry")
          let output := root / "Crates" / (label ++ ".lean")
          let stack := if allStack then SemanticStackBound.stackB I else none
          if allStack && stack.isNone then throw (IO.userError "The original fixture must have a finite stack bound")
          let files := FVTest.E2E.ReturnPinLinkProofWith.leanFilesReturnPinWith
            lower I.toLinkInput (I.funcs.map (·.func.name))
            [entry] output.toString label (if mixed then "original-mixed-caller-sret.elf" else "original-identity.elf") cleanup true stack
            [entry] bg (sliceLimit := limit)
          for (path,text) in files do
            let path : System.FilePath := path
            if let some parent := path.parent then IO.FS.createDirAll parent
            IO.FS.writeFile path text
          manifest := manifest.push (Json.mkObj [("module",toJson label),("mixed",toJson mixed),("cleanup",toJson cleanup),
            ("split",toJson split),("all_stack",toJson allStack),("files",toJson (files.map (·.1)))])
  IO.FS.writeFile (root / "manifest.json") (Json.arr manifest).pretty
